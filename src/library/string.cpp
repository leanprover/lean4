/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <algorithm>
#include "runtime/utf8.h"
#include "library/string.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/num.h"
#include "library/trace.h"

namespace lean {
static expr * g_nat                  = nullptr;
static expr * g_char                 = nullptr;
static expr * g_char_mk              = nullptr;
static expr * g_char_of_nat          = nullptr;
static expr * g_string               = nullptr;
static expr * g_empty                = nullptr;
static expr * g_str                  = nullptr;
static expr * g_fin_mk               = nullptr;

expr from_string_core(std::string const & s);

static void display_char_literal_utf8(std::ostream & out, unsigned char c, bool in_string) {
    if (c == '\n') {
        out << "\\n";
    } else if (c == '\t') {
        out << "\\t";
    } else if (c == '\\') {
        out << "\\\\";
    } else if (in_string && c == '\"') {
        out << "\\\"";
    } else if (!in_string && c == '\'') {
        out << "\\'";
    } else if (c >= 32 && c != 127) {
        out << c;
    } else {
        out << "\\x";
        if (c < 16) out << "0";
        out << std::hex << static_cast<unsigned>(c);
    }
}

static void display_char_literal(std::ostream & out, unsigned c) {
    out << "'";
    std::string s;
    push_unicode_scalar(s, c);
    for (unsigned i = 0; i < s.size(); i++) {
        display_char_literal_utf8(out, s[i], false);
    }
    out << "'";
}

static void display_string_literal(std::ostream & out, std::string const & s) {
    out << "\"";
    for (unsigned i = 0; i < s.size(); i++) {
        display_char_literal_utf8(out, s[i], true);
    }
    out << "\"";
}

format pp_string_literal(std::string const & s) {
    std::ostringstream out;
    display_string_literal(out, s);
    return format(out.str());
}

format pp_char_literal(unsigned c) {
    std::ostringstream out;
    display_char_literal(out, c);
    return format(out.str());
}

expr mk_string_literal(std::string const & v) {
    return mk_lit(literal(v.c_str()));
}

bool is_string_literal(expr const & e) {
    return is_lit(e) && lit_value(e).kind() == literal_kind::String;
}

void initialize_string() {
    g_nat             = new expr(mk_const(get_nat_name()));
    g_char            = new expr(mk_const(get_char_name()));
    g_char_mk         = new expr(mk_const(get_char_mk_name()));
    g_char_of_nat     = new expr(mk_const(get_char_of_nat_name()));
    g_string          = new expr(mk_const(get_string_name()));
    g_empty           = new expr(mk_const(get_string_empty_name()));
    g_str             = new expr(mk_const(get_string_str_name()));
    g_fin_mk          = new expr(mk_const(get_fin_mk_name()));
}

optional<expr> expand_string_literal(expr const & e) {
    if (!is_string_literal(e)) return none_expr();
    return some_expr(from_string_core(lit_value(e).get_string().to_std_string()));
}

void finalize_string() {
    delete g_nat;
    delete g_str;
    delete g_empty;
    delete g_string;
    delete g_char_of_nat;
    delete g_char;
    delete g_char_mk;
    delete g_fin_mk;
}

expr from_string_core(std::string const & s) {
    buffer<unsigned> tmp;
    utf8_decode(s, tmp);
    expr r = *g_empty;
    for (unsigned i = 0; i < tmp.size(); i++) {
        expr n = to_nat_expr(mpz(tmp[i]));
        expr c = mk_app(*g_char_of_nat, n);
        r = mk_app(*g_str, r, c);
    }
    return r;
}

expr from_string(std::string const & s) {
    return mk_string_literal(s);
}

optional<unsigned> to_char_core(expr const & e) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (fn == *g_char_mk && args.size() == 2) {
        /* TODO(Leo): FIX, we are now using uint32 instead of nat */
        if (auto n = to_num(args[0])) {
            return optional<unsigned>(n->get_unsigned_int());
        } else {
            return optional<unsigned>();
        }
    } else if (fn == *g_char_of_nat && args.size() == 1) {
        if (auto n = to_num(args[0])) {
            return optional<unsigned>(n->get_unsigned_int());
        } else {
            return optional<unsigned>();
        }
    } else {
        return optional<unsigned>();
    }
}

bool is_char_value_core(expr const & e) {
    return static_cast<bool>(to_char_core(e));
}

optional<unsigned> to_char(abstract_type_context & ctx, expr const & e) {
    if (auto v = to_char_core(e)) {
        if (ctx.is_def_eq(ctx.infer(e), mk_char_type()))
            return v;
    }
    return optional<unsigned>();
}

bool is_char_value(abstract_type_context & ctx, expr const & e) {
    if (!is_char_value_core(e))
        return false;
    expr type = ctx.infer(e);
    if (has_expr_metavar(type))
        return false;
    return ctx.is_def_eq(type, mk_char_type());
}

static bool append_char(expr const & e, std::string & r) {
    if (auto c = to_char_core(e)) {
        push_unicode_scalar(r, *c);
        return true;
    } else {
        return false;
    }
}

bool to_string_core(expr const & e, std::string & r) {
    if (e == *g_empty) {
        return true;
    } else if (is_string_literal(e)) {
        r = lit_value(e).get_string().to_std_string();
        return true;
    } else {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (fn == *g_str && args.size() == 2) {
            return to_string_core(args[0], r) && append_char(args[1], r);
        } else {
            return false;
        }
    }
}

optional<std::string> to_string(expr const & e) {
    if (is_string_literal(e)) {
        return optional<std::string>(std::string(lit_value(e).get_string().to_std_string()));
    } else {
        std::string tmp;
        if (to_string_core(e, tmp)) {
            return optional<std::string>(tmp);
        } else {
            return optional<std::string>();
        }
    }
}

bool is_string_value(expr const & e) {
    /* TODO(Leo): optimize if needed */
    return static_cast<bool>(to_string(e));
}
}
