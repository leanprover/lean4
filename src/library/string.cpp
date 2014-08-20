/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <algorithm>
#include "kernel/type_checker.h"
#include "library/kernel_serializer.h"
#include "library/string.h"

namespace lean {
static name g_string_macro("string_macro");
static std::string g_string_opcode("Str");

static expr g_bool(Const(name("bool")));
static expr g_ff(Const(name("ff")));
static expr g_tt(Const(name("tt")));
static expr g_char(Const(name("string", "char")));
static expr g_ascii(Const(name("string", "ascii")));
static expr g_string(Const(name("string", "string")));
static expr g_empty(Const(name("string", "empty")));
static expr g_str(Const(name("string", "str")));

expr from_string_core(unsigned i, std::string const & s);

/** \brief The string macro is a compact way of encoding strings inside Lean expressions. */
class string_macro : public macro_definition_cell {
    std::string m_value;
public:
    string_macro(std::string const & v):m_value(v) {}
    virtual bool lt(macro_definition_cell const & d) const {
        return m_value < static_cast<string_macro const &>(d).m_value;
    }
    virtual name get_name() const { return g_string_macro; }
    virtual expr get_type(expr const &, expr const *, extension_context &) const {
        return g_string;
    }
    virtual optional<expr> expand(expr const &, extension_context &) const {
        return some_expr(from_string_core(0, m_value));
    }
    virtual unsigned trust_level() const { return 0; }
    virtual bool operator==(macro_definition_cell const & other) const {
        string_macro const * other_ptr = dynamic_cast<string_macro const *>(&other);
        return other_ptr && m_value == other_ptr->m_value;
    }
    virtual void display(std::ostream & out) const {
        out << "\"";
        for (unsigned i = 0; i < m_value.size(); i++) {
            char c = m_value[i];
            if (c == '\n')
                out << "\\n";
            else if (c == '\t')
                out << "\\t";
            else if (c == '\r')
                out << "\\r";
            else if (c == 0)
                out << "\\0";
            else if (c == '\"')
                out << "\\\"";
            else
                out << c;
        }
        out << "\"";
    }
    virtual format pp(formatter const &) const {
        std::ostringstream out;
        display(out);
        return format(out.str());
    }
    virtual bool is_atomic_pp(bool, bool) const { return true; }
    virtual unsigned hash() const { return std::hash<std::string>()(m_value); }
    virtual void write(serializer & s) const { s << g_string_opcode << m_value; }
    std::string const & get_value() const { return m_value; }
};

expr mk_string_macro(std::string const & v) {
    return mk_macro(macro_definition(new string_macro(v)));
}

bool is_string_macro(expr const & e) {
    return is_macro(e) && dynamic_cast<string_macro const *>(macro_def(e).raw()) != nullptr;
}

string_macro const & to_string_macro(expr const & e) {
    lean_assert(is_string_macro(e));
    return *static_cast<string_macro const *>(macro_def(e).raw());
}

static register_macro_deserializer_fn
string_macro_des_fn(g_string_opcode,
                    [](deserializer & d, unsigned num, expr const *) {
                         if (num != 0)
                             throw corrupted_stream_exception();
                         std::string v = d.read_string();
                         return mk_string_macro(v);
                    });

bool has_string_decls(environment const & env) {
    try {
        type_checker tc(env);
        return
            tc.infer(g_ff).first    == g_bool &&
            tc.infer(g_tt).first    == g_bool &&
            tc.infer(g_ascii).first == g_bool >> (g_bool >> (g_bool >> (g_bool >> (g_bool >> (g_bool >> (g_bool >> (g_bool >> g_char))))))) &&
            tc.infer(g_empty).first == g_string &&
            tc.infer(g_str).first   == g_char >> (g_string >> g_string);
    } catch (...) {
        return false;
    }
}

expr from_char(unsigned char c) {
    buffer<expr> bits;
    while (c != 0) {
        if (c % 2 == 1)
            bits.push_back(g_tt);
        else
            bits.push_back(g_ff);
        c /= 2;
    }
    while (bits.size() < 8)
        bits.push_back(g_ff);
    return mk_rev_app(g_ascii, bits.size(), bits.data());
}

expr from_string_core(unsigned i, std::string const & s) {
    if (i == s.size())
        return g_empty;
    else
        return mk_app(g_str, from_char(s[i]), from_string_core(i+1, s));
}

expr from_string(std::string const & s) {
    return mk_string_macro(s);
}

bool to_char_core(expr const & e, buffer<char> & tmp) {
    buffer<expr> args;
    if (get_app_rev_args(e, args) == g_ascii && args.size() == 8) {
        unsigned v = 0;
        for (unsigned i = 0; i < args.size(); i++) {
            v *= 2;
            if (args[i] == g_tt)
                v++;
            else if (args[i] != g_ff)
                return false;
        }
        tmp.push_back(v);
        return true;
    } else {
        return false;
    }
}

bool to_string_core(expr const & e, buffer<char> & tmp) {
    if (e == g_empty) {
        return true;
    } else {
        buffer<expr> args;
        return
            get_app_args(e, args) == g_str &&
            args.size() == 2 &&
            to_char_core(args[0], tmp) &&
            to_string_core(args[1], tmp);
    }
}

optional<std::string> to_string(expr const & e) {
    if (is_string_macro(e)) {
        return optional<std::string>(to_string_macro(e).get_value());
    } else {
        buffer<char> tmp;
        if (to_string_core(e, tmp)) {
            std::string r;
            unsigned i = tmp.size();
            while (i > 0) {
                --i;
                r += tmp[i];
            }
            return optional<std::string>(r);
        } else {
            return optional<std::string>();
        }
    }
}
}
