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
#include "library/constants.h"

namespace lean {
static name * g_string_macro         = nullptr;
static std::string * g_string_opcode = nullptr;
static expr * g_bool                 = nullptr;
static expr * g_ff                   = nullptr;
static expr * g_tt                   = nullptr;
static expr * g_char                 = nullptr;
static expr * g_ascii                = nullptr;
static expr * g_string               = nullptr;
static expr * g_empty                = nullptr;
static expr * g_str                  = nullptr;

expr from_string_core(unsigned i, std::string const & s);

/** \brief The string macro is a compact way of encoding strings inside Lean expressions. */
class string_macro : public macro_definition_cell {
    std::string m_value;
public:
    string_macro(std::string const & v):m_value(v) {}
    virtual bool lt(macro_definition_cell const & d) const {
        return m_value < static_cast<string_macro const &>(d).m_value;
    }
    virtual name get_name() const { return *g_string_macro; }
    virtual pair<expr, constraint_seq> check_type(expr const &, extension_context &, bool) const {
        return mk_pair(*g_string, constraint_seq());
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
    virtual void write(serializer & s) const { s << *g_string_opcode << m_value; }
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

void initialize_string() {
    g_string_macro  = new name("string_macro");
    g_string_opcode = new std::string("Str");
    g_bool          = new expr(Const(get_bool_name()));
    g_ff            = new expr(Const(get_bool_ff_name()));
    g_tt            = new expr(Const(get_bool_tt_name()));
    g_char          = new expr(Const(get_char_name()));
    g_ascii         = new expr(Const(get_char_mk_name()));
    g_string        = new expr(Const(get_string_name()));
    g_empty         = new expr(Const(get_string_empty_name()));
    g_str           = new expr(Const(get_string_str_name()));
    register_macro_deserializer(*g_string_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    std::string v = d.read_string();
                                    return mk_string_macro(v);
                                });
}

void finalize_string() {
    delete g_str;
    delete g_empty;
    delete g_string;
    delete g_ascii;
    delete g_char;
    delete g_tt;
    delete g_ff;
    delete g_bool;
    delete g_string_opcode;
    delete g_string_macro;
}

bool has_string_decls(environment const & env) {
    try {
        type_checker tc(env);
        return
            tc.infer(*g_ff).first    == *g_bool &&
            tc.infer(*g_tt).first    == *g_bool &&
            tc.infer(*g_ascii).first == *g_bool >> (*g_bool >> (*g_bool >> (*g_bool >> (*g_bool >> (*g_bool >> (*g_bool >> (*g_bool >> *g_char))))))) &&
            tc.infer(*g_empty).first == *g_string &&
            tc.infer(*g_str).first   == *g_char >> (*g_string >> *g_string);
    } catch (exception &) {
        return false;
    }
}

expr from_char(unsigned char c) {
    buffer<expr> bits;
    while (c != 0) {
        if (c % 2 == 1)
            bits.push_back(*g_tt);
        else
            bits.push_back(*g_ff);
        c /= 2;
    }
    while (bits.size() < 8)
        bits.push_back(*g_ff);
    return mk_rev_app(*g_ascii, bits.size(), bits.data());
}

expr from_string_core(unsigned i, std::string const & s) {
    if (i == s.size())
        return *g_empty;
    else
        return mk_app(*g_str, from_char(s[i]), from_string_core(i+1, s));
}

expr from_string(std::string const & s) {
    return mk_string_macro(s);
}

bool to_char_core(expr const & e, buffer<char> & tmp) {
    buffer<expr> args;
    if (get_app_rev_args(e, args) == *g_ascii && args.size() == 8) {
        unsigned v = 0;
        for (unsigned i = 0; i < args.size(); i++) {
            v *= 2;
            if (args[i] == *g_tt)
                v++;
            else if (args[i] != *g_ff)
                return false;
        }
        tmp.push_back(v);
        return true;
    } else {
        return false;
    }
}

bool to_string_core(expr const & e, buffer<char> & tmp) {
    if (e == *g_empty) {
        return true;
    } else {
        buffer<expr> args;
        return
            get_app_args(e, args) == *g_str &&
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
