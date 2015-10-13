/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/kernel_serializer.h"

namespace lean {
static name * g_prenum_name = nullptr;
static std::string * g_prenum_opcode = nullptr;
[[ noreturn ]] static void throw_ex() { throw exception("unexpected occurrence of 'pre-numeral' expression"); }

class prenum_macro_definition_cell : public macro_definition_cell {
    mpz m_value;
public:
    prenum_macro_definition_cell(mpz const & v):m_value(v) {}
    mpz const & get_value() const { return m_value; }
    virtual name get_name() const { return *g_prenum_name; }
    virtual format pp(formatter const &) const { return format(m_value); }
    virtual void display(std::ostream & out) const { out << m_value; }
    virtual pair<expr, constraint_seq> check_type(expr const &, extension_context &, bool) const { throw_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_ex(); }
    virtual void write(serializer & s) const {
        s.write_string(*g_prenum_opcode);
        s << m_value;
    }
    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<prenum_macro_definition_cell const *>(&other)) {
            return m_value == other_ptr->m_value;
        } else {
            return false;
        }
    }
    virtual unsigned hash() const {
        return ::lean::hash(m_value.hash(), g_prenum_name->hash());
    }
};

expr mk_prenum(mpz const & v) {
    return mk_macro(macro_definition(new prenum_macro_definition_cell(v)), 0, nullptr);
}

bool is_prenum(expr const & e) {
    return is_macro(e) && dynamic_cast<prenum_macro_definition_cell const*>(macro_def(e).raw()) != nullptr;
}

mpz const & prenum_value(expr const & e) {
    lean_assert(is_prenum(e));
    return static_cast<prenum_macro_definition_cell const *>(macro_def(e).raw())->get_value();
}

void initialize_prenum() {
    g_prenum_name   = new name("prenum");
    g_prenum_opcode = new std::string("Prenum");
    register_macro_deserializer(*g_prenum_opcode,
                                [](deserializer & d, unsigned, expr const *) {
                                    mpz v;
                                    d >> v;
                                    return mk_prenum(v);
                                });
}

void finalize_prenum() {
    delete g_prenum_name;
    delete g_prenum_opcode;
}
}
