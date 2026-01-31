/*
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Robin Arnez

Interpreter for Lean bytecode.
*/
#include <string>
#include <vector>
#include <shared_mutex>
#ifdef LEAN_WINDOWS
#include <windows.h>
#include <psapi.h>
#else
#include <dlfcn.h>
#endif
#include "library/bytecode_interpreter.h"
#include "runtime/flet.h"
#include "runtime/apply.h"
#include "runtime/interrupt.h"
#include "runtime/io.h"
#include "runtime/option_ref.h"
#include "runtime/array_ref.h"
#include "kernel/trace.h"
#include "library/constants.h"
#include "library/time_task.h"
#include "library/ir_types.h"
#include "library/init_attribute.h"
#include "util/nat.h"
#include "util/option_declarations.h"
#include "util/name_hash_map.h"

#ifndef LEAN_DEFAULT_INTERPRETER_PREFER_NATIVE
#define LEAN_DEFAULT_INTERPRETER_PREFER_NATIVE true
#endif

namespace lean {
namespace interpreter {
// C++ wrappers of Lean data types

/** \brief Value stored in an interpreter variable slot */
union value {
    // NOTE: the IR type system guarantees that we always access the active union member
    uint64   m_num; // big enough for any unboxed integral type
    static_assert(sizeof(size_t) <= sizeof(uint64), "uint64 should be the largest unboxed type"); // NOLINT
    double   m_float;
    float    m_float32;
    object * m_obj;

    value() {}
    // too convenient to make explicit
    value(uint64 num): m_num(num) {}
    value(object * o): m_obj(o) {}

    // would overlap with `value(uint64)` as a constructor
    static value from_float(double f) {
        value v;
        v.m_float = f;
        return v;
    }

    static value from_float32(float f) {
        value v;
        v.m_float32 = f;
        return v;
    }
};

static_assert(sizeof(value) == sizeof(uint64), "value should be 64 bits in length"); // NOLINT

struct symbol_cache_entry {
    // amount of parameters the function expects for m_arity != 0, m_arity == 0 for a constant
    unsigned m_arity;
    // reference to native symbol address; `nullptr` if no native symbol is available
    void * m_native;
    // reference to object value (for constants) or bytecode object (for functions)
    // `nullptr` for native functions without bytecode
    object * m_object;
};

struct symbol_cache {
    // 0 = not loaded, 1 = loaded, 2 = locked
    atomic<uint8> m_loaded;
    size_t m_count;
    symbol_cache_entry m_entries[];
};

external_object_class g_symbol_cache_external_class;

void symbol_cache_finalize(void * val) {
    symbol_cache * cache = reinterpret_cast<symbol_cache *>(val);
    for (size_t i = 0; i < cache->m_count; i++) {
        object * val = cache->m_entries[i].m_object;
        if (val != nullptr) {
            dec(val);
        }
    }
    free(cache);
}

void symbol_cache_foreach(void * val, object * fn) {
    symbol_cache * cache = reinterpret_cast<symbol_cache *>(val);
    for (size_t i = 0; i < cache->m_count; i++) {
        object * val = cache->m_entries[i].m_object;
        if (val != nullptr) {
            inc(fn);
            inc(val);
            apply_1(fn, val);
        }
    }
    free(cache);
}

extern "C" object * lean_bytecode_mk_initial_cache(b_obj_arg symbols) {
    size_t count = array_size(symbols);
    size_t sz = sizeof(symbol_cache) + sizeof(symbol_cache_entry)*count;
    symbol_cache * cache = static_cast<symbol_cache *>(malloc(sz));
    // We populate the cache on demand
    // The cache is bound to the symbol array with dependent typing so there's no risk of
    // using it with the wrong count, so no need to store it here
    cache->m_loaded.store(false);
    cache->m_count = 0;
}

// reuse the compiler's name mangling to compute native symbol names
/* getSymbolStem (env : Environment) (fn : Name) :  String */
extern "C" obj_res lean_get_symbol_stem(obj_arg env, obj_arg fn);
string_ref get_symbol_stem(elab_environment const & env, name const & fn) {
    return string_ref(lean_get_symbol_stem(env.to_obj_arg(), fn.to_obj_arg()));
}

void * lookup_symbol_in_cur_exe(char const * sym) {
#ifdef LEAN_WINDOWS
    std::vector<HMODULE> hmods(128);
    DWORD bytes_needed;
    lean_always_assert(EnumProcessModules(GetCurrentProcess(), &hmods[0], hmods.size() * sizeof(HMODULE), &bytes_needed));
    unsigned num_mods = bytes_needed / sizeof(HMODULE);
    if (num_mods > hmods.size()) {
        hmods.resize(num_mods);
        lean_always_assert(EnumProcessModules(GetCurrentProcess(), &hmods[0], hmods.size() * sizeof(HMODULE), &bytes_needed));
    } else {
        hmods.resize(num_mods);
    }
    for (HMODULE hmod : hmods) {
        void * addr = reinterpret_cast<void *>(GetProcAddress(hmod, sym));
        if (addr) {
            return addr;
        }
    }
    return nullptr;
#else
    return dlsym(RTLD_DEFAULT, sym);
#endif
}

symbol_cache_entry fill_cache_entry(elab_environment const & env, object_ref const & symbol) {
    symbol_cache_entry result = {0};
    nat const & arity = cnstr_get_ref_t<nat>(symbol, 0);
    name const & decl_name = cnstr_get_ref_t<name>(symbol, 1);
    string_ref mangled = get_symbol_stem(env, decl_name);
    if (!arity.is_small() || arity.get_small_value() > UINT_MAX) {
        return result;
    }
    result.m_arity = static_cast<unsigned>(arity.get_small_value());
    if (void * p = lookup_symbol_in_cur_exe(mangled.data())) {
        result.m_native = p;
    }
    return result;
}

void fill_cache(elab_environment const & env, array_ref<object_ref> const & symbols, symbol_cache * cache) {
    if (LEAN_LIKELY(cache->m_loaded.load() == 1)) {
        return;
    }
    for (;;) {
        uint8 value = cache->m_loaded.exchange(2);
        if (value == 0) {
            // No one waiting
            break;
        } else if (value == 1) {
            // Another thread has loaded the cache, make sure to keep the status
            cache->m_loaded.exchange(1);
            return;
        }
        // Another thread has the lock, spin
    }
    // Lock acquired
    size_t count = symbols.size();
    for (size_t i = 0; i < count; i++) {
        cache->m_entries[i] = fill_cache_entry(env, symbols[i]);
    }
    cache->m_count = count;

    // Finished loading
    cache->m_loaded.store(1);
}

struct interpreter {};
LEAN_THREAD_PTR(interpreter, g_interpreter);

enum instruction_type : uint32 {
    NCONST = 0U << 26,
    PROJ = 1U << 26,
    UPROJ = 2U << 26,
    SPROJ = 3U << 26,
    ALLOC_CTOR = 4U << 26,
    SET = 5U << 26,
    USET = 6U << 26,
    SSET = 7U << 26,
    BOX_SMALL = 8U << 26,
    BOX_UINT32 = 10U << 26,
    BOX_UINT64 = 11U << 26,
    BOX_USIZE = 12U << 26,
    BOX_FLOAT = 13U << 26,
    BOX_FLOAT32 = 14U << 26,
    UNBOX_SMALL = 15U << 26,
    UNBOX_UINT32 = 16U << 26,
    UNBOX_UINT64 = 17U << 26,
    UNBOX_USIZE = 18U << 26,
    UNBOX_FLOAT = 19U << 26,
    UNBOX_FLOAT32 = 20U << 26,
    INC_N = 21U << 26,
    DEC_N = 22U << 26,
};

void eval_loop(interpreter * interp) {

}

void initialize_bytecode_interpreter() {
    register_external_object_class(symbol_cache_finalize, symbol_cache_foreach);
}

void finalize_bytecode_interpreter() {
}
}
}
