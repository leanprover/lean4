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

object * box_t(value v, type t) {
    switch (t) {
    case type::Float:   return box_float(v.m_float);
    case type::Float32: return box_float32(v.m_float32);
    case type::UInt8:   return box(v.m_num);
    case type::UInt16:  return box(v.m_num);
    case type::UInt32:  return box_uint32(v.m_num);
    case type::UInt64:  return box_uint64(v.m_num);
    case type::USize:   return box_size_t(v.m_num);
    case type::Object:
    case type::Tagged:
    case type::TObject:
    case type::Irrelevant:
    case type::Void:
        return v.m_obj;
    case type::Struct:
    case type::Union:
        throw exception("not implemented yet");
    }
    lean_unreachable();
}

value unbox_t(object * o, type t) {
    switch (t) {
    case type::Float:   return value::from_float(unbox_float(o));
    case type::Float32: return value::from_float32(unbox_float32(o));
    case type::UInt8:   return unbox(o);
    case type::UInt16:  return unbox(o);
    case type::UInt32:  return unbox_uint32(o);
    case type::UInt64:  return unbox_uint64(o);
    case type::USize:   return unbox_size_t(o);
    case type::Irrelevant:
    case type::Void:
    case type::Object:
    case type::Tagged:
    case type::TObject:
        break;
    case type::Struct:
    case type::Union:
        throw exception("not implemented yet");
    }
    lean_unreachable();
}

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
    size_t count;
    symbol_cache_entry m_entries[];
};

external_object_class g_symbol_cache_external_class;

void symbol_cache_finalize(void * val) {
    symbol_cache * cache = reinterpret_cast<symbol_cache *>(val);
    for (size_t i = 0; i < cache->count; i++) {
        object * val = cache->m_entries[i].m_object;
        if (val != nullptr) {
            dec(val);
        }
    }
    free(cache);
}

void symbol_cache_foreach(void * val, object * fn) {
    symbol_cache * cache = reinterpret_cast<symbol_cache *>(val);
    for (size_t i = 0; i < cache->count; i++) {
        object * val = cache->m_entries[i].m_object;
        if (val != nullptr) {
            inc(fn);
            inc(val);
            apply_1(fn, val);
        }
    }
    free(cache);
}

class interpreter;
LEAN_THREAD_PTR(interpreter, g_interpreter);

struct native_symbol_cache_entry {
    // symbol address; `nullptr` if function does not have native code
    void * m_addr;
    // true iff we chose the boxed version of a function where the IR uses the unboxed version
    bool m_boxed;
};

void initialize_bytecode_interpreter() {
    g_interpreter_prefer_native = new name({"interpreter", "prefer_native"});
    register_bool_option(*ir::g_interpreter_prefer_native, LEAN_DEFAULT_INTERPRETER_PREFER_NATIVE, "(interpreter) whether to use precompiled code where available");
    register_external_object_class(symbol_cache_finalize, symbol_cache_foreach);
}

void finalize_bytecode_interpreter() {
}
}
}
