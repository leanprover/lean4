/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <string>
#include "util/test.h"
#include "util/escaped.h"
#include "util/exception.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/parser_config.h"
#include "init/init.h"
using namespace lean;

#define tk token_kind

static void scan(char const * str, environment const & env = environment()) {
    std::istringstream in(str);
    scanner s(in, "[string]");
    while (true) {
        tk k = s.scan(env);
        if (k == tk::Eof)
            break;
        if (k == tk::Identifier)
            std::cout << "id[" << s.get_name_val() << "]";
        else if (k == tk::CommandKeyword)
            std::cout << "cmd[" << s.get_token_info().value() << "]";
        else if (k == tk::Keyword)
            std::cout << "tk[" << s.get_token_info().value() << "]";
        else if (k == tk::Decimal || k == tk::Numeral)
            std::cout << "n[" << s.get_num_val() << "]";
        else if (k == tk::String)
            std::cout << "[\"" << escaped(s.get_str_val().c_str()) << "\"]";
        std::cout << ":" << s.get_pos() << ":" << s.get_line() << " ";
    }
    std::cout << "\n";
}

static void scan_success(char const * str, environment const & env = environment()) {
    try {
        scan(str, env);
    } catch (exception & ex) {
        std::cout << "ERROR: " << ex.what() << "\n";
        lean_unreachable();
    }
}

static void scan_error(char const * str) {
    try {
        scan(str);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "expected error: " << ex.what() << "\n";
    }
}

static void check(char const * str, std::initializer_list<tk> const & l,
                  environment const & env = environment()) {
    try {
        auto it = l.begin();
        std::istringstream in(str);
        scanner s(in, "[string]");
        while (true) {
            tk k = s.scan(env);
            if (k == tk::Eof) {
                lean_assert(it == l.end());
                return;
            }
            lean_assert(it != l.end());
            lean_assert_eq(k, *it);
            ++it;
        }
    } catch (exception & ex) {
        std::cout << "ERROR: " << ex.what() << "\n";
        lean_unreachable();
    }
}

static void check_name(char const * str, name const & expected, environment const & env = environment()) {
    std::istringstream in(str);
    scanner s(in, "[string]");
    tk k = s.scan(env);
    lean_assert(k == tk::Identifier);
    lean_assert(s.get_name_val() == expected);
    lean_assert(s.scan(env) == tk::Eof);
}

static void check_keyword(char const * str, name const & expected, environment const & env = environment()) {
    std::istringstream in(str);
    scanner s(in, "[string]");
    tk k = s.scan(env);
    lean_assert(k == tk::Keyword);
    lean_assert(s.get_token_info().value() == expected);
    lean_assert(s.scan(env) == tk::Eof);
}

static void tst1() {
    environment env;
    token_table s = get_token_table(env);
    env = add_token(env, "+", 0);
    env = add_token(env, "=", 0);
    scan_success("a..a");
    check("Type.{0}", {tk::Keyword, tk::Keyword, tk::Numeral, tk::Keyword});
    env = add_token(env, "ab+cde", 0);
    env = add_token(env, "+cd", 0);
    scan_success("ab+cd", env);
    check("ab+cd", {tk::Identifier, tk::Keyword}, env);
    scan_success("ab+cde", env);
    check("ab+cde", {tk::Keyword}, env);
    scan_success("Type.{0}");
    scan_success("0.a a");
    scan_success("0.");
    scan_success("0..");
    scan_success("fun");
    scan_success("..");
    scan_success("....");
    scan_success("....\n..");
    scan_success("a", env);
    scan_success("a. b.c..");
    scan_success(".. ..");
    scan_success("....\n..");
    scan_success("fun(x: forall A : Type, A -> A), x+1 = 2.0 λvalue.foo. . . a", env);
}

static void tst2() {
    scan("x.name");
    scan("x.foo");
    check("x.name", {tk::Identifier});
    check("fun (x : Prop), x", {tk::Keyword, tk::Keyword, tk::Identifier, tk::Keyword, tk::Identifier,
                 tk::Keyword, tk::Keyword, tk::Identifier});
    check_name("x10", name("x10"));
    // check_name("x.10", name(name("x"), 10));
    check_name("x.bla", name({"x", "bla"}));

    scan_error("***");
    environment env;
    token_table s = mk_default_token_table();
    env = add_token(env, "***", 0);
    check_keyword("***", "***", env);
    env = add_token(env, "+", 0);
    check("x+y", {tk::Identifier, tk::Keyword, tk::Identifier}, env);
    check("-- testing", {});
    check("/- testing -/", {});
    check("/- /- testing\n -/ -/", {});
    check(" 2.31  ", {tk::Decimal});
    check("2.31", {tk::Decimal});
    check(" 333 22", {tk::Numeral, tk::Numeral});
    check("int -> int", {tk::Identifier, tk::Keyword, tk::Identifier});
    check("int->int", {tk::Identifier, tk::Keyword, tk::Identifier});
    check_keyword("->", "->");
    env = add_token(env, "-+->", 0);
    check("Int -+-> Int", {tk::Identifier, tk::Keyword, tk::Identifier}, env);
    check("x := 10", {tk::Identifier, tk::Keyword, tk::Numeral});
    check("{x}", {tk::Keyword, tk::Identifier, tk::Keyword});
    check("λ ∀ →", {tk::Keyword, tk::Keyword, tk::Keyword});
    check_keyword("λ", "fun");
    scan("theorem a : Prop axiom b : Int");
    check("theorem a : Prop axiom b : Int", {tk::CommandKeyword, tk::Identifier, tk::Keyword, tk::Identifier,
                tk::CommandKeyword, tk::Identifier, tk::Keyword, tk::Identifier});
    scan("foo \"ttk\\\"\" : Int");
    check("foo \"ttk\\\"\" : Int", {tk::Identifier, tk::String, tk::Keyword, tk::Identifier});
    scan_error("\"foo");
    scan("2.13 1.2 0.5");
}

static void tst3() {
    scan_error("\"\\");
    scan_error("\"\\a");
    scan("\"\naaa\"");
    scan_error("foo.* 01");
    scan("10.0.");
    scan("{ } . forall exists let in ∀ := _");
}

static void tst4(unsigned N) {
    std::string big;
    for (unsigned i = 0; i < N; i++)
        big += "aaa ";
    std::istringstream in(big);
    environment env;
    scanner s(in, "[string]");
    unsigned i = 0;
    while (true) {
        tk k = s.scan(env);
        if (k == tk::Eof)
            break;
        i++;
    }
    std::cout << i << "\n";
}

static void tst_id_escape() {
    check_name("«a»", name("a"));
    check_name("«a».b", name({"a", "b"}));
    check_name("a.«b»", name({"a", "b"}));
    check_name("a.«b».c", name({"a", "b", "c"}));

    check_name("«a.b».c", name({"a.b", "c"}));
    check_name("«a b».c", name({"a b", "c"}));
    check_name("«a🍏b».c", name({"a🍏b", "c"}));

    check_name("a«b»", "ab");
    check_name("«a»b", "ab");

    scan_error("«");
    scan_error("«a");
    scan_error("«a\nb»");
    scan_error("a.«");
}

int main() {
    save_stack_info();
    initialize();
    tst1();
    tst2();
    tst3();
    tst4(100000);
    tst_id_escape();
    finalize();
    return has_violations() ? 1 : 0;
}
