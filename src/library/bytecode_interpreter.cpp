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
#include "util/nat.h"
#include "util/option_declarations.h"
#include "util/name_hash_map.h"

namespace lean {
namespace interpreter {

#define INTERPRETER_STACK_SIZE (1 << 20)
#define INTERPRETER_FRAME_COUNT (1 << 16)

typedef lean_interpreter_value value;

static_assert(sizeof(size_t) <= sizeof(uint64), "uint64 should be the largest unboxed type"); // NOLINT
static_assert(sizeof(value) == sizeof(uint64), "value should be 64 bits in length"); // NOLINT

typedef lean_interp_decl_cache_entry decl_cache_entry;
typedef lean_interp_decl_cache_object decl_cache;

extern "C" LEAN_EXPORT object * lean_bytecode_mk_initial_cache(b_obj_arg _decl_name, b_obj_arg symbols) {
    size_t count = array_size(symbols);
    //size_t sz = sizeof(decl_cache) + sizeof(decl_cache_entry)*count;
    size_t sz = lean_usize_add_checked(sizeof(decl_cache), lean_usize_mul_checked(sizeof(decl_cache_entry), count));
    decl_cache * cache = (decl_cache *) lean_alloc_object(sz);
    lean_set_st_header((lean_object*) cache, LeanInterpCache, 0);
    cache->m_once_cell.lock = 0;
    cache->m_once_cell.state = 0;
    cache->m_value = box(0);
    cache->m_count = count;
    for (size_t i = 0; i < count; i++) {
        cache->m_entries[i].m_arity = 0;
        cache->m_entries[i].m_native = nullptr;
        cache->m_entries[i].m_object = box(0);
    }
    return (lean_object*) cache;
}

// reuse the compiler's name mangling to compute native symbol names
/* getSymbolStem (env : Environment) (fn : Name) :  String */
extern "C" obj_res lean_get_symbol_stem(obj_arg env, obj_arg fn);

// Environment -> Name -> Option Name
extern "C" obj_res lean_get_export_name_for(obj_arg env, obj_arg fn);

// Environment -> Name -> USize
extern "C" size_t lean_ir_decl_arity(obj_arg env, obj_arg fn);

// Environment -> Name -> Option RuntimeBytecodeDecl
extern "C" obj_res lean_find_bytecode_decl(obj_arg env, obj_arg fn);

// Environment -> Name -> Bool
extern "C" uint8 lean_has_init_attr(obj_arg env, obj_arg fn);

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

#define INTERP_DECL_MASK (1U << 31)

// env : Environment, decl_name : Name
decl_cache_entry fill_cache_entry(b_obj_arg env, b_obj_arg decl_name) {
    decl_cache_entry result = { .m_arity = 0, .m_native = nullptr, .m_object = box(0) };
    // For lean_ir_decl_arity, lean_find_bytecode_decl, lean_get_symbol_stem
    lean_inc_n(env, 3); lean_inc_n(decl_name, 3);
    size_t arity = lean_ir_decl_arity(env, decl_name);
    if (arity >= INTERP_DECL_MASK) {
        dec(env); dec(decl_name);
        dec(env); dec(decl_name);
        return result;
    }
    object * decl = lean_find_bytecode_decl(env, decl_name); // Option Name
    if (!lean_is_scalar(decl)) {
        result.m_object = lean_ctor_get(decl, 0);
        inc(result.m_object);
        dec(decl);
        arity = lean_unbox(lean_ctor_get(result.m_object, 6));
        /*if (!lean_has_init_attr(env, decl_name)) {
            result.m_arity = static_cast<unsigned>(arity);
            return result;
        }*/
        //inc(env);
        //inc(decl_name);
    }
    object * mangled = lean_get_symbol_stem(env, decl_name); // String
    inc(mangled);
    result.m_arity = static_cast<unsigned>(arity);
    object * suffix = mk_string("_0interp"); // String
    object * mangled_interp = string_append(mangled, suffix); // String
    dec(suffix);
    if (void * p = lookup_symbol_in_cur_exe(lean_string_cstr(mangled_interp))) {
        result.m_native = p;
        result.m_arity |= INTERP_DECL_MASK;
        dec(mangled);
    } else {
        inc(env); inc(decl_name);
        object * res = lean_get_export_name_for(env, decl_name); // Option Name
        if (!lean_is_scalar(res)) {
            object * export_name = lean_ctor_get(res, 0); // Name
            if (lean_obj_tag(export_name) == 1) {
                dec(mangled);
                mangled = lean_ctor_get(export_name, 1); // String
                inc(mangled);
            }
            dec(res);
        }
        if (void * p = lookup_symbol_in_cur_exe(lean_string_cstr(mangled))) {
            result.m_native = p;
        }
        dec(mangled);
    }
    dec(mangled_interp);
    return result;
}

void lock_simple_atomic(std::atomic<int>& lock) {
    while (true) {
        lock.wait(1);
        int should = 0;
        if (lock.compare_exchange_strong(should, 1)) {
            break;
        }
    }
}

void unlock_simple_atomic(std::atomic<int>& lock) {
    lock.store(0);
    lock.notify_one();
}

// Fills the cache if not already done before. If this function returns true, the cache has
// been filled already. Otherwise, the cache is locked and needs to be unlocked by the caller.
bool fill_cache(b_obj_arg env, b_obj_arg symbols, decl_cache * cache) {
    if (LEAN_LIKELY(cache->m_once_cell.state != 0)) {
        return true;
    }
    lock_simple_atomic(cache->m_once_cell.lock);
    if (cache->m_once_cell.state != 0) {
        unlock_simple_atomic(cache->m_once_cell.lock);
        return true;
    }
    // Lock acquired
    size_t count = lean_array_size(symbols);
    for (size_t i = 0; i < count; i++) {
        cache->m_entries[i] = fill_cache_entry(env, lean_array_get_core(symbols, i));
    }
    cache->m_count = count;
    // Keep lock upon return
    return false;
}

struct frame {
    value * m_stack_base;
    uint32 * m_code;
    object * m_decl; // borrowed
    decl_cache_entry * m_cache;
};

struct interpreter {
    object * m_env;
    value * m_stack_start;
    value * m_stack_end;
    value * m_stack_top;
    frame * m_frame_start;
    frame * m_frame_end;
    frame * m_frame_top;

    interpreter() : m_env(box(0)) {}
};

LEAN_THREAD_PTR(interpreter, g_interpreter);

static void init_interpreter(interpreter * interp, value * value_stack, frame * frame_stack) {
    interp->m_stack_start = value_stack;
    interp->m_stack_top = value_stack;
    interp->m_stack_end = value_stack + INTERPRETER_STACK_SIZE;
    interp->m_frame_start = frame_stack;
    interp->m_frame_top = frame_stack;
    interp->m_frame_end = frame_stack + INTERPRETER_FRAME_COUNT;
    g_interpreter = interp;
}

extern "C" LEAN_EXPORT void lean_interpreter_backtrace() {
    frame * frame_begin = g_interpreter->m_frame_start;
    frame * frame_ptr = g_interpreter->m_frame_top;
    std::cerr << "Interpreter backtrace (potentially incomplete)" << std::endl;
    size_t i = 0;
    while (frame_ptr > frame_begin) {
        frame_ptr--;
        object * decl = frame_ptr->m_decl;
        name nm = name(lean_ctor_get(decl, 0), true);
        object * bytecode_obj = lean_ctor_get(decl, 1); // ByteArray
        uint32 * bytecode = reinterpret_cast<uint32 *>(sarray_cptr(bytecode_obj));
        size_t off = frame_ptr->m_code - bytecode;
        std::cerr << "#" << i << ": " << nm << " + " << off << std::endl;
        i++;
    }
}

enum instruction_type {
    UCONST,
    MOVE,
    RET,
    CALL,
    RETCALL,
    COMPUTE_SCALAR,
    ALLOC_CTOR,
    PROJ,
    UPROJ,
    SPROJ8,
    SPROJ16,
    SPROJ32,
    SPROJ64,
    SET,
    USET,
    SSET8,
    SSET16,
    SSET32,
    SSET64,
    BOX_SMALL,
    BOX_UINT32,
    BOX_UINT64,
    BOX_USIZE,
    BOX_FLOAT,
    BOX_FLOAT32,
    UNBOX_SMALL,
    UNBOX_UINT32,
    UNBOX_UINT64,
    UNBOX_USIZE,
    UNBOX_FLOAT,
    UNBOX_FLOAT32,
    INC_N,
    DEC_N,
    IS_SHARED,
    LOAD_TAG,
    JUMP_TABLE,
    SET_TAG,
    LOAD_CONST,
    IF_TAG,
    JUMP,
    APP,
    PAP,
    DEL,
    RESET,
    REUSE,
    STORE_CACHE,
    SKIP_WHEN_CACHED,
    DECL_CONST,
    UNREACHABLE,
};

frame call_init(interpreter * interp, b_obj_arg decl, bool is_constant) {
    object * bytecode_obj = lean_ctor_get(decl, 1); // ByteArray
    object * stack_reserved_obj = lean_ctor_get(decl, 2); // Nat
    object * stack_space_obj = lean_ctor_get(decl, 3); // Nat
    object * symbols_array = lean_ctor_get(decl, 4); // Array Name
    object * cache_obj = lean_ctor_get(decl, 5); // DeclCache symbols

    uint32 * bytecode = reinterpret_cast<uint32 *>(sarray_cptr(bytecode_obj));
    size_t stack_reserved = lean_unbox(stack_reserved_obj);
    if (interp->m_stack_top + stack_reserved >= interp->m_stack_end || interp->m_frame_top >= interp->m_frame_end) {
        lean_internal_panic("interpreter stack overflow");
    }

    decl_cache * cache = lean_to_interp_cache(cache_obj);
    bool already_done = fill_cache(interp->m_env, symbols_array, cache);
    if (already_done) {
        if (is_constant) {
            interp->m_stack_top->m_obj = cache->m_value;
        }
    } else {
        if (lean_is_mt(cache_obj) || lean_is_persistent(cache_obj)) {
            for (size_t i = 0; i < cache->m_count; i++) {
                lean_mark_mt(cache->m_entries[i].m_object);
            }
        }
        if (is_constant) {
            interp->m_stack_top->m_obj = nullptr;
            // we keep the lock for constants
            // and unlock once we run `store_value_and_unlock`
        } else if (!already_done) {
            cache->m_once_cell.state = 1;
            unlock_simple_atomic(cache->m_once_cell.lock);
        }
    }

    frame f;
    f.m_code = bytecode;
    f.m_decl = decl;
    f.m_stack_base = interp->m_stack_top;
    f.m_cache = cache->m_entries;
    interp->m_stack_top += lean_unbox(stack_space_obj);
    return f;
}

void store_value_and_unlock(object * decl, object * value) {
    object * cache_obj = lean_ctor_get(decl, 5);
    decl_cache * cache = lean_to_interp_cache(cache_obj);
    if (lean_is_mt(cache_obj) || lean_is_persistent(cache_obj)) {
        lean_mark_mt(value);
    }
    cache->m_value = value;
    cache->m_once_cell.state = 1;
    unlock_simple_atomic(cache->m_once_cell.lock);
}

// Panic with an unknown declaration error. Note: this is not recoverable
void report_unknown_declaration(object_ref const & decl, unsigned symbol_idx) {
    array_ref<name> const & symbols_array = cnstr_get_ref_t<array_ref<name>>(decl, 4);
    name const & symbol = symbols_array[symbol_idx];
    std::string error = (sstream() << "(interpreter) unknown declaration '" << symbol << "'").str();
    lean_internal_panic(error.c_str());
}

typedef void (*stack_function)(value * values);

value eval_loop(interpreter * interp, frame start_frame);

// static closure stub
static object * stub_m_aux(object ** args) {
    interpreter interp;
    object * env = args[0];
    object * decl = args[1];
    if (lean_is_scalar(env)) {
        size_t arity = unbox(env); // oh no it's not actually the environment then, it's the arity
        value * value_stack = reinterpret_cast<value *>(LEAN_ALLOCA(sizeof(value) * arity));
        stack_function fn = reinterpret_cast<stack_function>(lean_unbox_usize(decl));
        dec(decl);
        for (size_t i = 0; i < arity; i++) {
            value_stack[i].m_obj = args[i + 2];
        }
        (*fn)(value_stack);
        return value_stack[0].m_obj;
    }
    bool need_cleanup = false;
    if (g_interpreter == nullptr) {
        value * value_stack = reinterpret_cast<value *>(LEAN_ALLOCA(sizeof(value) * INTERPRETER_STACK_SIZE));
        frame * frame_stack = reinterpret_cast<frame *>(LEAN_ALLOCA(sizeof(frame) * INTERPRETER_FRAME_COUNT));
        init_interpreter(&interp, value_stack, frame_stack);
        need_cleanup = true;
    }
    object * old_env = g_interpreter->m_env;

    g_interpreter->m_env = env;
    object * arity_obj = lean_ctor_get(decl, 6); // Nat
    size_t arity = lean_unbox(arity_obj);
    frame f = call_init(g_interpreter, decl, false);
    for (size_t i = 0; i < arity; i++) {
        f.m_stack_base[i].m_obj = args[i + 2];
    }
    value res = eval_loop(g_interpreter, f);
    dec(env); dec(decl);

    g_interpreter->m_env = old_env;
    if (need_cleanup) g_interpreter = nullptr;
    return res.m_obj;
}

// python3 -c 'for i in range(1,17): print(f"    static object * stub_{i}_aux(" + ", ".join([f"object * x_{j}" for j in range(1,i+1)]) + ") { object * args[] = { " + ", ".join([f"x_{j}" for j in range(1,i+1)]) + " }; return stub_m_aux(args); }")'
static object * stub_1_aux(object * x_1) { object * args[] = { x_1 }; return stub_m_aux(args); }
static object * stub_2_aux(object * x_1, object * x_2) { object * args[] = { x_1, x_2 }; return stub_m_aux(args); }
static object * stub_3_aux(object * x_1, object * x_2, object * x_3) { object * args[] = { x_1, x_2, x_3 }; return stub_m_aux(args); }
static object * stub_4_aux(object * x_1, object * x_2, object * x_3, object * x_4) { object * args[] = { x_1, x_2, x_3, x_4 }; return stub_m_aux(args); }
static object * stub_5_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5) { object * args[] = { x_1, x_2, x_3, x_4, x_5 }; return stub_m_aux(args); }
static object * stub_6_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6 }; return stub_m_aux(args); }
static object * stub_7_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7 }; return stub_m_aux(args); }
static object * stub_8_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8 }; return stub_m_aux(args); }
static object * stub_9_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9 }; return stub_m_aux(args); }
static object * stub_10_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10 }; return stub_m_aux(args); }
static object * stub_11_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11 }; return stub_m_aux(args); }
static object * stub_12_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11, object * x_12) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12 }; return stub_m_aux(args); }
static object * stub_13_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11, object * x_12, object * x_13) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13 }; return stub_m_aux(args); }
static object * stub_14_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11, object * x_12, object * x_13, object * x_14) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14 }; return stub_m_aux(args); }
static object * stub_15_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11, object * x_12, object * x_13, object * x_14, object * x_15) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15 }; return stub_m_aux(args); }
static object * stub_16_aux(object * x_1, object * x_2, object * x_3, object * x_4, object * x_5, object * x_6, object * x_7, object * x_8, object * x_9, object * x_10, object * x_11, object * x_12, object * x_13, object * x_14, object * x_15, object * x_16) { object * args[] = { x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16 }; return stub_m_aux(args); }

void * get_stub(unsigned params) {
    switch (params) {
        case 0: lean_unreachable();
        case 1: return reinterpret_cast<void *>(stub_1_aux);
        case 2: return reinterpret_cast<void *>(stub_2_aux);
        case 3: return reinterpret_cast<void *>(stub_3_aux);
        case 4: return reinterpret_cast<void *>(stub_4_aux);
        case 5: return reinterpret_cast<void *>(stub_5_aux);
        case 6: return reinterpret_cast<void *>(stub_6_aux);
        case 7: return reinterpret_cast<void *>(stub_7_aux);
        case 8: return reinterpret_cast<void *>(stub_8_aux);
        case 9: return reinterpret_cast<void *>(stub_9_aux);
        case 10: return reinterpret_cast<void *>(stub_10_aux);
        case 11: return reinterpret_cast<void *>(stub_11_aux);
        case 12: return reinterpret_cast<void *>(stub_12_aux);
        case 13: return reinterpret_cast<void *>(stub_13_aux);
        case 14: return reinterpret_cast<void *>(stub_14_aux);
        case 15: return reinterpret_cast<void *>(stub_15_aux);
        case 16: return reinterpret_cast<void *>(stub_16_aux);
        default: return reinterpret_cast<void *>(stub_m_aux);
    }
}

static object * apply_n_interpreter(object * f, unsigned n, value * as) {
switch (n) {
case 0: lean_unreachable();
case 1: return lean_apply_1(f, as[0].m_obj);
case 2: return lean_apply_2(f, as[0].m_obj, as[1].m_obj);
case 3: return lean_apply_3(f, as[0].m_obj, as[1].m_obj, as[2].m_obj);
case 4: return lean_apply_4(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj);
case 5: return lean_apply_5(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj);
case 6: return lean_apply_6(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj);
case 7: return lean_apply_7(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj);
case 8: return lean_apply_8(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj);
case 9: return lean_apply_9(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj);
case 10: return lean_apply_10(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj);
case 11: return lean_apply_11(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj);
case 12: return lean_apply_12(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj, as[11].m_obj);
case 13: return lean_apply_13(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj, as[11].m_obj, as[12].m_obj);
case 14: return lean_apply_14(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj, as[11].m_obj, as[12].m_obj, as[13].m_obj);
case 15: return lean_apply_15(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj, as[11].m_obj, as[12].m_obj, as[13].m_obj, as[14].m_obj);
case 16: return lean_apply_16(f, as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj, as[11].m_obj, as[12].m_obj, as[13].m_obj, as[14].m_obj, as[15].m_obj);
default:
    object ** args = static_cast<object **>(LEAN_ALLOCA(n*sizeof(object *))); // NOLINT
    for (unsigned i = 0; i < n; i++) {
        args[i] = as[i].m_obj;
    }
    return lean_apply_m(f, n, args);
}
}

typedef object* (*fn1)(object*); // NOLINT
typedef object* (*fn2)(object*, object*); // NOLINT
typedef object* (*fn3)(object*, object*, object*); // NOLINT
typedef object* (*fn4)(object*, object*, object*, object*); // NOLINT
typedef object* (*fn5)(object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fn6)(object*, object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fn7)(object*, object*, object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fn8)(object*, object*, object*, object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fn9)(object*, object*, object*, object*, object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fn10)(object*, object*, object*, object*, object*, object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fn11)(object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fn12)(object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fn13)(object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fn14)(object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fn15)(object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fn16)(object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*, object*); // NOLINT
typedef object* (*fnn)(object**); // NOLINT

static object * curry_interpreter(void * f, unsigned n, value * as) {
switch (n) {
case 0: lean_unreachable();
case 1: return reinterpret_cast<fn1>(f)(as[0].m_obj);
case 2: return reinterpret_cast<fn2>(f)(as[0].m_obj, as[1].m_obj);
case 3: return reinterpret_cast<fn3>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj);
case 4: return reinterpret_cast<fn4>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj);
case 5: return reinterpret_cast<fn5>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj);
case 6: return reinterpret_cast<fn6>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj);
case 7: return reinterpret_cast<fn7>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj);
case 8: return reinterpret_cast<fn8>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj);
case 9: return reinterpret_cast<fn9>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj);
case 10: return reinterpret_cast<fn10>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj);
case 11: return reinterpret_cast<fn11>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj);
case 12: return reinterpret_cast<fn12>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj, as[11].m_obj);
case 13: return reinterpret_cast<fn13>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj, as[11].m_obj, as[12].m_obj);
case 14: return reinterpret_cast<fn14>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj, as[11].m_obj, as[12].m_obj, as[13].m_obj);
case 15: return reinterpret_cast<fn15>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj, as[11].m_obj, as[12].m_obj, as[13].m_obj, as[14].m_obj);
case 16: return reinterpret_cast<fn16>(f)(as[0].m_obj, as[1].m_obj, as[2].m_obj, as[3].m_obj, as[4].m_obj, as[5].m_obj, as[6].m_obj, as[7].m_obj, as[8].m_obj, as[9].m_obj, as[10].m_obj, as[11].m_obj, as[12].m_obj, as[13].m_obj, as[14].m_obj, as[15].m_obj);
default:
    object ** args = static_cast<object **>(LEAN_ALLOCA(n*sizeof(object *))); // NOLINT
    for (unsigned i = 0; i < n; i++) {
        args[i] = as[i].m_obj;
    }
    return reinterpret_cast<fnn>(f)(args);
}
}


value eval_loop(interpreter * interp, frame start_frame) {
    value * base = start_frame.m_stack_base;
    uint32 * pc = start_frame.m_code;
    decl_cache_entry * cache = start_frame.m_cache;
    object * decl = start_frame.m_decl;
    unsigned scalar_pos = 0;
    frame * orig_frame = interp->m_frame_top;
    while (1) {
        uint32 instr = *pc;

        /*char buf[8192];
        object_ref const & bytecode_obj = cnstr_get_ref(decl, 1);
        uint32 * bytecode = reinterpret_cast<uint32 *>(sarray_cptr(bytecode_obj.raw()));
        fprintf(stderr, "Running instruction %x with base: %lu and top: %lu. Cache: %p, declaration: %p, relative: %lx, frame: %lu, original frame: %lu\n",
            instr, (base - interp->m_stack_start),
            (interp->m_stack_top - interp->m_stack_start), cache, decl, (pc - bytecode),
            (interp->m_frame_top - interp->m_frame_start),
            (orig_frame - interp->m_frame_start));
        for (size_t i = 0; i < 8; i++) {
            fprintf(stderr, "%zx: %p\n", i, base[i].m_obj);
        }
        for (size_t i = 128; i < 136; i++) {
            fprintf(stderr, "%zx: %p\n", i, base[i].m_obj);
        }*/
        //io_eprintln(mk_string(buf));

        pc++;
        switch (instr >> 26) {
            case instruction_type::UCONST: {
                uint32 target = (instr >> 18) & 0xFF;
                uint32 val = instr & 0x3FFFF;
                base[target].m_num = val;
                break;
            }
            case instruction_type::MOVE: {
                uint32 target = (instr >> 13) & 0x1FFF;
                uint32 source = instr & 0x1FFF;
                base[target] = base[source];
                break;
            }
            case instruction_type::RET: {
                uint32 source = instr & 0xFFFF;
                value val = base[source];
                *base = val;
                interp->m_stack_top = base;
                if (interp->m_frame_top <= orig_frame) {
                    return val;
                }
                interp->m_frame_top--;
                frame * new_frame = interp->m_frame_top;
                base = new_frame->m_stack_base;
                pc = new_frame->m_code;
                cache = new_frame->m_cache;
                decl = new_frame->m_decl;
                break;
            }
            case instruction_type::SKIP_WHEN_CACHED: {
                if (base->m_obj != nullptr) {
                    pc += instr & 0x3FF'FFFF;
                }
                break;
            }
            case instruction_type::STORE_CACHE: {
                uint32 source = instr & 0xFF;
                value val = base[source];
                *base = val;
                store_value_and_unlock(decl, val.m_obj);
                break;
            }
            case instruction_type::CALL: {
                uint32 fn_id = instr & 0xFFFF;
                decl_cache_entry fn = cache[fn_id];
                if (fn.m_native != nullptr) {
                    if (fn.m_arity & INTERP_DECL_MASK) {
                        ((stack_function) fn.m_native)(interp->m_stack_top);
                    } else {
                        object * res = curry_interpreter(fn.m_native, fn.m_arity, interp->m_stack_top);
                        interp->m_stack_top[0].m_obj = res;
                    }
                } else if (!lean_is_scalar(fn.m_object)) {
                    interp->m_frame_top->m_stack_base = base;
                    interp->m_frame_top->m_cache = cache;
                    interp->m_frame_top->m_code = pc;
                    interp->m_frame_top->m_decl = decl;
                    interp->m_frame_top++;

                    frame new_frame = call_init(interp, fn.m_object, false);
                    base = new_frame.m_stack_base;
                    pc = new_frame.m_code;
                    cache = new_frame.m_cache;
                    decl = new_frame.m_decl;
                } else {
                    report_unknown_declaration(object_ref(decl, true), fn_id);
                }
                break;
            }
            case instruction_type::RETCALL: {
                uint32 fn_id = instr & 0xFFFF;
                decl_cache_entry fn = cache[fn_id];
                interp->m_stack_top = base;
                if (fn.m_native != nullptr) {
                    if (fn.m_arity & INTERP_DECL_MASK) {
                        ((stack_function) fn.m_native)(base);
                    } else {
                        object * res = curry_interpreter(fn.m_native, fn.m_arity, base);
                        base[0].m_obj = res;
                    }
                    if (interp->m_frame_top <= orig_frame) {
                        return base[0];
                    }
                    interp->m_frame_top--;
                    frame * new_frame = interp->m_frame_top;
                    base = new_frame->m_stack_base;
                    pc = new_frame->m_code;
                    cache = new_frame->m_cache;
                    decl = new_frame->m_decl;
                } else if (!lean_is_scalar(fn.m_object)) {
                    frame new_frame = call_init(interp, fn.m_object, false);
                    base = new_frame.m_stack_base;
                    pc = new_frame.m_code;
                    cache = new_frame.m_cache;
                    decl = new_frame.m_decl;
                } else {
                    report_unknown_declaration(object_ref(decl, true), fn_id);
                }
                break;
            }
            case instruction_type::LOAD_CONST: {
                uint32 fn_id = instr & 0xFFFF;
                decl_cache_entry fn = cache[fn_id];
                if (fn.m_native != nullptr) {
                    if (fn.m_arity & INTERP_DECL_MASK) {
                        ((stack_function) fn.m_native)(base);
                    } else {
                        object ** res = static_cast<object **>(fn.m_native);
                        interp->m_stack_top[0].m_obj = *res;
                    }
                } else if (!lean_is_scalar(fn.m_object)) {
                    interp->m_frame_top->m_stack_base = base;
                    interp->m_frame_top->m_cache = cache;
                    interp->m_frame_top->m_code = pc;
                    interp->m_frame_top->m_decl = decl;
                    interp->m_frame_top++;

                    frame new_frame = call_init(interp, fn.m_object, true);
                    base = new_frame.m_stack_base;
                    pc = new_frame.m_code;
                    cache = new_frame.m_cache;
                    decl = new_frame.m_decl;
                } else {
                    report_unknown_declaration(object_ref(decl, true), fn_id);
                }
                break;
            }
            case instruction_type::COMPUTE_SCALAR: {
                uint32 usize = (instr >> 13) & 0x1FFF;
                uint32 ssize = instr & 0x1FFF;
                scalar_pos = usize * sizeof(size_t) + ssize;
                break;
            }
            case instruction_type::ALLOC_CTOR: {
                uint32 target = (instr >> 18) & 0xFF;
                uint32 tag = (instr >> 8) & 0x3FF;
                uint32 num_objs = instr & 0xFF;
                base[target].m_obj = lean_alloc_ctor(tag, num_objs, scalar_pos);
                scalar_pos = 0;
                break;
            }
            case instruction_type::PROJ: {
                uint32 target = (instr >> 16) & 0xFF;
                uint32 source = (instr >> 8) & 0xFF;
                uint32 idx = instr & 0xFF;
                base[target].m_obj = lean_ctor_get(base[source].m_obj, idx);
                break;
            }
            case instruction_type::UPROJ: {
                uint32 target = (instr >> 16) & 0xFF;
                uint32 source = (instr >> 8) & 0xFF;
                uint32 idx = instr & 0xFF;
                base[target].m_num = lean_ctor_get_usize(base[source].m_obj, idx);
                break;
            }
            case instruction_type::SPROJ8: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_num = lean_ctor_get_uint8(base[source].m_obj, scalar_pos);
                scalar_pos = 0;
                break;
            }
            case instruction_type::SPROJ16: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_num = lean_ctor_get_uint16(base[source].m_obj, scalar_pos);
                scalar_pos = 0;
                break;
            }
            case instruction_type::SPROJ32: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_num = lean_ctor_get_uint32(base[source].m_obj, scalar_pos);
                scalar_pos = 0;
                break;
            }
            case instruction_type::SPROJ64: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_num = lean_ctor_get_uint64(base[source].m_obj, scalar_pos);
                scalar_pos = 0;
                break;
            }
            case instruction_type::SET: {
                uint32 target = (instr >> 16) & 0xFF;
                uint32 source = (instr >> 8) & 0xFF;
                uint32 idx = instr & 0xFF;
                lean_ctor_set(base[target].m_obj, idx, base[source].m_obj);
                break;
            }
            case instruction_type::USET: {
                uint32 target = (instr >> 16) & 0xFF;
                uint32 source = (instr >> 8) & 0xFF;
                uint32 idx = instr & 0xFF;
                lean_ctor_set_usize(base[target].m_obj, idx, base[source].m_num);
                break;
            }
            case instruction_type::SSET8: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                lean_ctor_set_uint8(base[target].m_obj, scalar_pos, base[source].m_num);
                scalar_pos = 0;
                break;
            }
            case instruction_type::SSET16: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                lean_ctor_set_uint16(base[target].m_obj, scalar_pos, base[source].m_num);
                scalar_pos = 0;
                break;
            }
            case instruction_type::SSET32: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                lean_ctor_set_uint32(base[target].m_obj, scalar_pos, base[source].m_num);
                scalar_pos = 0;
                break;
            }
            case instruction_type::SSET64: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                lean_ctor_set_uint64(base[target].m_obj, scalar_pos, base[source].m_num);
                scalar_pos = 0;
                break;
            }
            case instruction_type::BOX_SMALL: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_obj = box(base[source].m_num);
                break;
            }
            case instruction_type::BOX_UINT32: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_obj = box_uint32(base[source].m_num);
                break;
            }
            case instruction_type::BOX_UINT64: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_obj = box_uint64(base[source].m_num);
                break;
            }
            case instruction_type::BOX_USIZE: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_obj = box_size_t(base[source].m_num);
                break;
            }
            case instruction_type::BOX_FLOAT: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_obj = box_float(base[source].m_float);
                break;
            }
            case instruction_type::BOX_FLOAT32: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_obj = box_float32(base[source].m_float32);
                break;
            }
            case instruction_type::UNBOX_SMALL: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_num = unbox(base[source].m_obj);
                break;
            }
            case instruction_type::UNBOX_UINT32: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_num = unbox(base[source].m_obj);
                break;
            }
            case instruction_type::UNBOX_UINT64: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_num = unbox_uint64(base[source].m_obj);
                break;
            }
            case instruction_type::UNBOX_USIZE: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_num = unbox_size_t(base[source].m_obj);
                break;
            }
            case instruction_type::UNBOX_FLOAT: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_float = unbox_float(base[source].m_obj);
                break;
            }
            case instruction_type::UNBOX_FLOAT32: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_float32 = unbox_float32(base[source].m_obj);
                break;
            }
            case instruction_type::INC_N: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 count = instr & 0xFF;
                lean_inc_n(base[target].m_obj, count);
                break;
            }
            case instruction_type::DEC_N: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 count = instr & 0xFF;
                while (count > 0) {
                    lean_dec(base[target].m_obj);
                    count--;
                }
                break;
            }
            case instruction_type::IS_SHARED: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_num = !lean_is_exclusive(base[source].m_obj);
                break;
            }
            case instruction_type::LOAD_TAG: {
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                base[target].m_num = lean_obj_tag(base[source].m_obj);
                break;
            }
            case instruction_type::JUMP_TABLE: {
                uint32 source = (instr >> 10) & 0xFF;
                uint32 limit = instr & 0x3FF;
                uint32 val = base[source].m_num;
                if (val < limit) {
                    pc += val;
                } else {
                    pc += limit;
                }
                break;
            }
            case instruction_type::SET_TAG: {
                uint32 target = (instr >> 10) & 0xFF;
                uint32 tag = instr & 0x3FF;
                lean_ctor_set_tag(base[target].m_obj, tag);
                break;
            }
            case instruction_type::IF_TAG: {
                uint32 source = (instr >> 18) & 0xFF;
                uint32 tag = (instr >> 8) & 0x3FF;
                uint32 offset = instr & 0xFF;
                if (base[source].m_num == tag) {
                    pc += offset - 0x80;
                }
                break;
            }
            case instruction_type::JUMP: {
                int32 offset = (instr & 0x3FF'FFFF) - 0x200'0000;
                pc += offset;
                break;
            }
            case instruction_type::APP: {
                uint32 n = (instr >> 16) & 0x3FF;
                uint32 fn = instr & 0xFFFF;
                object * res = apply_n_interpreter(base[fn].m_obj, n, interp->m_stack_top);
                interp->m_stack_top[0].m_obj = res;
                break;
            }
            case instruction_type::PAP: {
                uint32 n = (instr >> 16) & 0x3FF;
                uint32 fn_id = instr & 0xFFFF;
                decl_cache_entry fn = cache[fn_id];
                if (fn.m_native) {
                    if (fn.m_arity & INTERP_DECL_MASK) {
                        size_t arity = fn.m_arity & ~INTERP_DECL_MASK;
                        object * closure = lean_alloc_closure(get_stub(arity + 2), arity + 2, n + 2);
                        lean_closure_set(closure, 0, lean_box(arity));
                        lean_closure_set(closure, 1, lean_box_usize((size_t) fn.m_native)); // hmm
                        for (size_t i = 0; i < n; i++) {
                            lean_closure_set(closure, i + 2, interp->m_stack_top[i].m_obj);
                        }
                        interp->m_stack_top[0].m_obj = closure;
                    } else {
                        object * closure = lean_alloc_closure(fn.m_native, fn.m_arity, n);
                        for (size_t i = 0; i < n; i++) {
                            lean_closure_set(closure, i, interp->m_stack_top[i].m_obj);
                        }
                        interp->m_stack_top[0].m_obj = closure;
                    }
                } else if (!lean_is_scalar(fn.m_object)) {
                    object * closure = lean_alloc_closure(get_stub(fn.m_arity + 2), fn.m_arity + 2, n + 2);
                    inc(interp->m_env);
                    inc(fn.m_object);
                    lean_closure_set(closure, 0, interp->m_env);
                    lean_closure_set(closure, 1, fn.m_object);
                    for (size_t i = 0; i < n; i++) {
                        lean_closure_set(closure, i + 2, interp->m_stack_top[i].m_obj);
                    }
                    interp->m_stack_top[0].m_obj = closure;

                } else {
                    // Note: This leaks memory
                    report_unknown_declaration(object_ref(decl, true), fn_id);
                }
                break;
            }
            case instruction_type::DEL: {
                uint32 target = instr & 0xFF;
                lean_del_object(base[target].m_obj);
                break;
            }
            case instruction_type::RESET: {
                uint32 n = (instr >> 16) & 0xFF;
                uint32 target = (instr >> 8) & 0xFF;
                uint32 source = instr & 0xFF;
                if (lean_is_exclusive(base[source].m_obj)) {
                    object * val = base[source].m_obj;
                    for (uint32_t i = 0; i < n; i++) {
                        lean_ctor_release(val, i);
                    }
                    base[target].m_obj = val;
                } else {
                    dec(base[source].m_obj);
                    base[target].m_obj = box(0);
                }
                break;
            }
            case instruction_type::REUSE: {
                uint32 target = (instr >> 18) & 0xFF;
                uint32 tag = (instr >> 8) & 0x3FF;
                uint32 num_objs = instr & 0xFF;
                if (lean_is_scalar(base[target].m_obj)) {
                    base[target].m_obj = lean_alloc_ctor(tag, num_objs, scalar_pos);
                } else {
                    lean_ctor_set_tag(base[target].m_obj, tag);
                }
                break;
            }
            case instruction_type::DECL_CONST: {
                uint32 target = (instr >> 18) & 0xFF;
                uint32 constant = instr & 0x3FFFF;
                object * constants_obj = lean_ctor_get(decl, 7); // Array NonScalar
                object * value = lean_array_get_core(constants_obj, constant); // NonScalar
                base[target].m_obj = value;
                break;
            }
            case instruction_type::UNREACHABLE: {
                lean_interpreter_backtrace();
                name nm = name(lean_ctor_get(decl, 0), true);
                std::string msg = (sstream() << "unreachable code has been reached while interpreting " << nm).str();
                lean_internal_panic(msg.c_str());
                break;
            }
        }
    }
}

extern "C" obj_res lean_eval_bytecode_decl(b_obj_arg env, b_obj_arg decl) {
    interpreter interp;
    bool need_cleanup = false;
    if (g_interpreter == nullptr) {
        value * value_stack = reinterpret_cast<value *>(LEAN_ALLOCA(sizeof(value) * INTERPRETER_STACK_SIZE));
        frame * frame_stack = reinterpret_cast<frame *>(LEAN_ALLOCA(sizeof(frame) * INTERPRETER_FRAME_COUNT));
        init_interpreter(&interp, value_stack, frame_stack);
        need_cleanup = true;
    }
    object * old_env = g_interpreter->m_env;

    g_interpreter->m_env = env;
    frame f = call_init(g_interpreter, decl, true);
    value res = eval_loop(g_interpreter, f);
    inc(res.m_obj);

    g_interpreter->m_env = old_env;
    if (need_cleanup) g_interpreter = nullptr;
    return res.m_obj;
}

/* runModInitCore (sym : @& String) : IO Bool */
extern "C" LEAN_EXPORT obj_res lean_run_mod_init_core(b_obj_arg sym) {
    if (void * init = lookup_symbol_in_cur_exe(string_cstr(sym))) {
        auto init_fn = reinterpret_cast<object *(*)(uint8_t)>(init);
        uint8_t builtin = 0;
        object * r = init_fn(builtin);
        if (io_result_is_ok(r)) {
            dec_ref(r);
            return lean_io_result_mk_ok(box(true));
        } else {
            return r;
        }
    } else {
        return lean_io_result_mk_ok(box(false));
    }
}

extern "C" LEAN_EXPORT object * lean_bytecode_store_init_value(b_obj_arg decl, obj_arg value) {
    object * cache_obj = lean_ctor_get(decl, 5); // DeclCache symbols
    decl_cache * cache = lean_to_interp_cache(cache_obj);
    cache->m_value = value;
    cache->m_once_cell.state = 1;
    return box(0);
}

}

void initialize_bytecode_interpreter() {
}

void finalize_bytecode_interpreter() {
}

}
