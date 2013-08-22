/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "test.h"
#include "lean_scanner.h"
#include "exception.h"
#include "escaped.h"
using namespace lean;

#define st scanner::token

static void scan(char const * str, list<name> const & cmds = list<name>()) {
    std::istringstream in(str);
    scanner s(in);
    for (name const & n : cmds) s.add_command_keyword(n);
    while (true) {
        st t = s.scan();
        if (t == st::Eof)
            break;
        std::cout << t;
        if (t == st::Id || t == st::CommandId)
            std::cout << "[" << s.get_name_val() << "]";
        else if (t == st::IntVal || t == st::DecimalVal)
            std::cout << "[" << s.get_num_val() << "]";
        else if (t == st::StringVal)
            std::cout << "[\"" << escaped(s.get_str_val().c_str()) << "\"]";
        std::cout << " ";
    }
    std::cout << "\n";
}

static void check(char const * str, std::initializer_list<scanner::token> const & l, list<name> const & cmds = list<name>()) {
    auto it = l.begin();
    std::istringstream in(str);
    scanner s(in);
    for (name const & n : cmds) s.add_command_keyword(n);
    while (true) {
        st t = s.scan();
        if (t == st::Eof) {
            lean_assert(it == l.end());
            return;
        }
        lean_assert(it != l.end());
        lean_assert(t == *it);
        ++it;
    }
}

static void check_name(char const * str, name const & expected) {
    std::istringstream in(str);
    scanner s(in);
    st t = s.scan();
    lean_assert(t == st::Id);
    lean_assert(s.get_name_val() == expected);
    lean_assert(s.scan() == st::Eof);
}

static void tst1() {
    scan("fun(x: Pi A : Type, A -> A), (* (* test *) *) x+1 = 2.0 λ");
    try {
        scan("(* (* foo *)");
        lean_unreachable();
    } catch (exception const & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
}

static void tst2() {
    scan("x::name");
    scan("x::10::foo");
    check("x::name", {st::Id});
    check("fun (x : Bool), x", {st::Lambda, st::LeftParen, st::Id, st::Colon, st::Id, st::RightParen, st::Comma, st::Id});
    check("+++", {st::Id});
    check("x+y", {st::Id, st::Id, st::Id});
    check("(* testing *)", {});
    check(" 2.31  ", {st::DecimalVal});
    check(" 333 22", {st::IntVal, st::IntVal});
    check("Int -> Int", {st::Id, st::Arrow, st::Id});
    check("Int --> Int", {st::Id, st::Id, st::Id});
    check("x := 10", {st::Id, st::Assign, st::IntVal});
    check("(x+1):Int", {st::LeftParen, st::Id, st::Id, st::IntVal, st::RightParen, st::Colon, st::Id});
    check("{x}", {st::LeftCurlyBracket, st::Id, st::RightCurlyBracket});
    check("\u03BB \u03A0 \u2192", {st::Lambda, st::Pi, st::Arrow});
    scan("++\u2295++x\u2296\u2296");
    check("++\u2295++x\u2296\u2296", {st::Id, st::Id, st::Id, st::Id, st::Id});
    scan("x10");
    check_name("x10", name("x10"));
    check_name("x::10", name(name("x"), 10));
    check_name("x::10::bla::0", name(name(name(name("x"), 10), "bla"), 0u));
    check("0::1", {st::IntVal, st::Colon, st::Colon, st::IntVal});
    check_name("\u2296\u2296", name("\u2296\u2296"));
    try {
        scan("x::1000000000000000000");
        lean_unreachable();
    } catch (exception const & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    scan("Theorem a : Bool Axiom b : Int", list<name>({"Theorem", "Axiom"}));
    check("Theorem a : Bool Axiom b : Int", {st::CommandId, st::Id, st::Colon, st::Id, st::CommandId, st::Id, st::Colon, st::Id}, list<name>({"Theorem", "Axiom"}));
    scan("foo \"tst\\\"\" : Int");
    check("foo \"tst\\\"\" : Int", {st::Id, st::StringVal, st::Colon, st::Id});
    try {
        scan("\"foo");
        lean_unreachable();
    } catch (exception const & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
    scan("2.13 1.2 0.5");
}

int main() {
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}
