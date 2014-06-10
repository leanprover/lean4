/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "util/test.h"
#include "util/escaped.h"
#include "util/exception.h"
#include "frontends/lean/scanner.h"
using namespace lean;

#define tk scanner::token_kind

static void scan(char const * str, token_table set = mk_default_token_table()) {
    std::istringstream in(str);
    scanner s(set, in, "[string]");
    while (true) {
        tk k = s.scan();
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

static void scan_success(char const * str, token_table set = mk_default_token_table()) {
    try {
        scan(str, set);
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
                  token_table set = mk_default_token_table()) {
    try {
        auto it = l.begin();
        std::istringstream in(str);
        scanner s(set, in, "[string]");
        while (true) {
            tk k = s.scan();
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

static void check_name(char const * str, name const & expected, token_table set = mk_default_token_table()) {
    std::istringstream in(str);
    scanner s(set, in, "[string]");
    tk k = s.scan();
    lean_assert(k == tk::Identifier);
    lean_assert(s.get_name_val() == expected);
    lean_assert(s.scan() == tk::Eof);
}

static void check_keyword(char const * str, name const & expected, token_table set = mk_default_token_table()) {
    std::istringstream in(str);
    scanner s(set, in, "[string]");
    tk k = s.scan();
    lean_assert(k == tk::Keyword);
    lean_assert(s.get_token_info().value() == expected);
    lean_assert(s.scan() == tk::Eof);
}

static void tst1() {
    token_table s = mk_default_token_table();
    s = add_token(s, "+", "plus");
    s = add_token(s, "=", "eq");
    scan_success("a..a");
    check("a..a", {tk::Identifier, tk::Keyword, tk::Keyword, tk::Identifier});
    check("Type.{0}", {tk::Keyword, tk::Keyword, tk::Numeral, tk::Keyword});
    s = add_token(s, "ab+cde", "weird1");
    s = add_token(s, "+cd", "weird2");
    scan_success("ab+cd", s);
    check("ab+cd", {tk::Identifier, tk::Keyword}, s);
    scan_success("ab+cde", s);
    check("ab+cde", {tk::Keyword}, s);
    scan_success("Type.{0}");
    scan_success("0.a a");
    scan_success("0.");
    scan_success("0..");
    scan_success("0..1");
    scan_success("fun");
    scan_success("..");
    scan_success("....");
    scan_success("....\n..");
    scan_success("a", s);
    scan_success("a. b.c..");
    scan_success(".. ..");
    scan_success("....\n..");
    scan_success("fun(x: forall A : Type, A -> A), x+1 = 2.0 λvalue.foo. . . a", s);
}

static void tst2() {
    scan("x.name");
    scan("x.foo");
    check("x.name", {tk::Identifier});
    check("fun (x : Bool), x", {tk::Keyword, tk::Keyword, tk::Identifier, tk::Keyword, tk::Identifier,
                 tk::Keyword, tk::Keyword, tk::Identifier});
    check_name("x10", name("x10"));
    // check_name("x.10", name(name("x"), 10));
    check_name("x.bla", name({"x", "bla"}));

    scan_error("+++");
    token_table s = mk_default_token_table();
    s = add_token(s, "+++", "tplus");
    check_keyword("+++", "tplus", s);
    s = add_token(s, "+", "plus");
    check("x+y", {tk::Identifier, tk::Keyword, tk::Identifier}, s);
    check("-- testing", {});
    check("(-- testing --)", {});
    check("(-- (-- testing\n --) --)", {});
    check(" 2.31  ", {tk::Decimal});
    check("2.31", {tk::Decimal});
    check(" 333 22", {tk::Numeral, tk::Numeral});
    check("int -> int", {tk::Identifier, tk::Keyword, tk::Identifier});
    check("int->int", {tk::Identifier, tk::Keyword, tk::Identifier});
    check_keyword("->", "->");
    s = add_token(s, "-+->", "arrow");
    check("Int -+-> Int", {tk::Identifier, tk::Keyword, tk::Identifier}, s);
    check("x := 10", {tk::Identifier, tk::Keyword, tk::Numeral});
    check("{x}", {tk::Keyword, tk::Identifier, tk::Keyword});
    check("\u03BB \u2200 \u2192", {tk::Keyword, tk::Keyword, tk::Keyword});
    check_keyword("\u03BB", "fun");
    scan("x10 ... (* print('hello') *) have by");
    scan("0..1");
    check("0..1", {tk::Numeral, tk::Keyword, tk::Keyword, tk::Numeral});
    scan("theorem a : Bool axiom b : Int");
    check("theorem a : Bool axiom b : Int", {tk::CommandKeyword, tk::Identifier, tk::Keyword, tk::Identifier,
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
    scan_error("foo.+ 01");
    scan("10.0.");
    scan("{ } . forall exists let in \u2200 := _");
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}
