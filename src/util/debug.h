/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <typeinfo>
#include "util/exception.h"
#include "util/compiler_hints.h"

#ifndef __has_builtin
#define __has_builtin(x) 0
#endif

#ifdef LEAN_DEBUG
#define DEBUG_CODE(CODE) CODE
#else
#define DEBUG_CODE(CODE)
#endif

#define lean_unreachable() { DEBUG_CODE({lean::notify_assertion_violation(__FILE__, __LINE__, "UNREACHABLE CODE WAS REACHED."); lean::invoke_debugger();}) throw lean::unreachable_reached(); }

#ifdef LEAN_DEBUG
#define lean_verify(COND) if (LEAN_UNLIKELY(!(COND))) { lean::notify_assertion_violation(__FILE__, __LINE__, #COND); lean::invoke_debugger(); }
#else
#define lean_verify(COND) (COND)
#endif

// LEAN_NARG(ARGS...) return the number of arguments.
// This is a hack based on the following stackoverflow post:
// http://stackoverflow.com/questions/11317474/macro-to-count-number-of-arguments
#define LEAN_COMMASEQ_N() 1,   1,  1,  1,  1,  1,  1,  1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0
#define LEAN_RSEQ_N()     17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0
#define LEAN_ARG_N(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, N, ...) N
#define LEAN_EXPAND(x) x
#ifdef _MSC_VER
#define LEAN_AUGMENT(...) dummy, __VA_ARGS__
#define LEAN_NARG_1(...) LEAN_EXPAND(LEAN_ARG_N(__VA_ARGS__, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0))
#define LEAN_NARG(...) LEAN_NARG_1(LEAN_AUGMENT(__VA_ARGS__))
#else
#define LEAN_NARG_(ARGS...)    LEAN_ARG_N(ARGS)
#define LEAN_HASCOMMA(ARGS...) LEAN_NARG_(ARGS, LEAN_COMMASEQ_N())
#define LEAN_COMMA() ,
#define LEAN_NARG_HELPER3_01(N)    0
#define LEAN_NARG_HELPER3_00(N)    1
#define LEAN_NARG_HELPER3_11(N)    N
#define LEAN_NARG_HELPER2(a, b, N) LEAN_NARG_HELPER3_ ## a ## b(N)
#define LEAN_NARG_HELPER1(a, b, N) LEAN_NARG_HELPER2(a, b, N)
#define LEAN_NARG(ARGS...)         LEAN_NARG_HELPER1(LEAN_HASCOMMA(ARGS), LEAN_HASCOMMA(LEAN_COMMA ARGS ()), LEAN_NARG_(ARGS, LEAN_RSEQ_N()))
#endif

// Hack for LEAN_DISPLAY(ARGS...)
// It works for at most 16 arguments.
#define LEAN_DISPLAY1_CORE(V)       lean::debug::display_var(#V, V);
#define LEAN_DISPLAY2_CORE(V, ...)  lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY1_CORE(__VA_ARGS__))
#define LEAN_DISPLAY3_CORE(V, ...)  lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY2_CORE(__VA_ARGS__))
#define LEAN_DISPLAY4_CORE(V, ...)  lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY3_CORE(__VA_ARGS__))
#define LEAN_DISPLAY5_CORE(V, ...)  lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY4_CORE(__VA_ARGS__))
#define LEAN_DISPLAY6_CORE(V, ...)  lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY5_CORE(__VA_ARGS__))
#define LEAN_DISPLAY7_CORE(V, ...)  lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY6_CORE(__VA_ARGS__))
#define LEAN_DISPLAY8_CORE(V, ...)  lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY7_CORE(__VA_ARGS__))
#define LEAN_DISPLAY9_CORE(V, ...)  lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY8_CORE(__VA_ARGS__))
#define LEAN_DISPLAY10_CORE(V, ...) lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY9_CORE(__VA_ARGS__))
#define LEAN_DISPLAY11_CORE(V, ...) lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY10_CORE(__VA_ARGS__))
#define LEAN_DISPLAY12_CORE(V, ...) lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY11_CORE(__VA_ARGS__))
#define LEAN_DISPLAY13_CORE(V, ...) lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY12_CORE(__VA_ARGS__))
#define LEAN_DISPLAY14_CORE(V, ...) lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY13_CORE(__VA_ARGS__))
#define LEAN_DISPLAY15_CORE(V, ...) lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY14_CORE(__VA_ARGS__))
#define LEAN_DISPLAY16_CORE(V, ...) lean::debug::display_var(#V, V); LEAN_EXPAND(LEAN_DISPLAY15_CORE(__VA_ARGS__))
#define LEAN_DISPLAY0(...)
#define LEAN_DISPLAY1(ARG)          std::cerr << "Argument\n";  LEAN_DISPLAY1_CORE(ARG)
#define LEAN_DISPLAY2(...)          std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY2_CORE(__VA_ARGS__))
#define LEAN_DISPLAY3(...)          std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY3_CORE(__VA_ARGS__))
#define LEAN_DISPLAY4(...)          std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY4_CORE(__VA_ARGS__))
#define LEAN_DISPLAY5(...)          std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY5_CORE(__VA_ARGS__))
#define LEAN_DISPLAY6(...)          std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY6_CORE(__VA_ARGS__))
#define LEAN_DISPLAY7(...)          std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY7_CORE(__VA_ARGS__))
#define LEAN_DISPLAY8(...)          std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY8_CORE(__VA_ARGS__))
#define LEAN_DISPLAY9(...)          std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY9_CORE(__VA_ARGS__))
#define LEAN_DISPLAY10(...)         std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY10_CORE(__VA_ARGS__))
#define LEAN_DISPLAY11(...)         std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY11_CORE(__VA_ARGS__))
#define LEAN_DISPLAY12(...)         std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY12_CORE(__VA_ARGS__))
#define LEAN_DISPLAY13(...)         std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY13_CORE(__VA_ARGS__))
#define LEAN_DISPLAY14(...)         std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY14_CORE(__VA_ARGS__))
#define LEAN_DISPLAY15(...)         std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY15_CORE(__VA_ARGS__))
#define LEAN_DISPLAY16(...)         std::cerr << "Arguments\n"; LEAN_EXPAND(LEAN_DISPLAY16_CORE(__VA_ARGS__))
#define LEAN_JOIN0(A, B) A ## B
#define LEAN_JOIN(A, B) LEAN_JOIN0(A, B)
#define LEAN_DISPLAY(...) { LEAN_JOIN(LEAN_DISPLAY, LEAN_NARG(__VA_ARGS__))(__VA_ARGS__) }

#define lean_assert(COND, ...) DEBUG_CODE({if (LEAN_UNLIKELY(!(COND))) { lean::notify_assertion_violation(__FILE__, __LINE__, #COND); LEAN_DISPLAY(__VA_ARGS__); lean::invoke_debugger(); }})
#define lean_cond_assert(TAG, COND, ...) DEBUG_CODE({if (lean::is_debug_enabled(TAG) && LEAN_UNLIKELY(!(COND))) { lean::notify_assertion_violation(__FILE__, __LINE__, #COND); LEAN_DISPLAY(__VA_ARGS__); lean::invoke_debugger(); }})
#define lean_always_assert(COND, ...) { if (LEAN_UNLIKELY(!(COND))) { lean::notify_assertion_violation(__FILE__, __LINE__, #COND); LEAN_DISPLAY(__VA_ARGS__); lean_unreachable(); } }

#define lean_assert_eq(A, B) lean_assert(A == B, A, B)
#define lean_assert_ne(A, B) lean_assert(A != B, A, B)
#define lean_assert_gt(A, B) lean_assert(A > B, A, B)
#define lean_assert_lt(A, B) lean_assert(A < B, A, B)
#define lean_assert_ge(A, B) lean_assert(A >= B, A, B)
#define lean_assert_le(A, B) lean_assert(A <= B, A, B)

namespace lean {
void initialize_debug();
void finalize_debug();
void notify_assertion_violation(char const * file_name, int line, char const * condition);
void enable_debug(char const * tag);
void disable_debug(char const * tag);
bool is_debug_enabled(char const * tag);
void invoke_debugger();
bool has_violations();
void enable_debug_dialog(bool flag);
// LCOV_EXCL_START
/** \brief Exception used to sign that unreachable code was reached */
class unreachable_reached : public exception {
public:
    unreachable_reached() {}
    virtual ~unreachable_reached() noexcept {}
    virtual char const * what() const noexcept { return "'unreachable' code was reached"; }
    virtual throwable * clone() const { return new unreachable_reached(); }
    virtual void rethrow() const { throw *this; }
};
namespace debug {
template<typename T> void display_var(char const * name, T const & value) {
    // commented typeid(value).name() since the name is mangled
    std::cerr << name << /* " : " << typeid(value).name() << */ " := "
              << std::boolalpha << value << std::noboolalpha
              << std::endl; }
}
// LCOV_EXCL_STOP
}
