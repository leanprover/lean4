/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/context.h"
#include "library/kernel_serializer.h"

namespace lean {
LEAN_THREAD_PTR(context, g_context);
static name * g_ref_value = nullptr;
static std::string * g_ref_value_opcode = nullptr;

class ref_definition_cell : public macro_definition_cell {
    name m_name;
    void check_macro(expr const & m) const {
        lean_assert(is_macro(m));
        if (macro_num_args(m) != 0)
            throw exception("invalid ref expression");
    }
public:
    ref_definition_cell(name const & n):m_name(n) {}
    name get_ref_name() const { return m_name; }

    virtual name get_name() const { return *g_ref_value; }

    virtual pair<expr, constraint_seq> check_type(expr const & m, extension_context &, bool) const {
        lean_assert(g_context);
        check_macro(m);
        return mk_pair(g_context->get_type(m_name), constraint_seq());
    }

    virtual optional<expr> expand(expr const & m, extension_context &) const {
        lean_assert(g_context);
        check_macro(m);
        return g_context->get_value(m_name);
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_ref_value_opcode);
        s << m_name;
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        return
            dynamic_cast<ref_definition_cell const *>(&other) != nullptr &&
            m_name == static_cast<ref_definition_cell const&>(other).m_name;
    }

    virtual unsigned hash() const { return m_name.hash(); }
};

expr mk_ref(name const & n) {
    return mk_macro(macro_definition(new ref_definition_cell(n)), 0, nullptr);
}

bool is_ref(expr const & e) {
    return is_macro(e) && dynamic_cast<ref_definition_cell const *>(macro_def(e).raw());
}

name get_ref_name(expr const & e) {
    lean_assert(is_ref(e));
    return static_cast<ref_definition_cell const *>(macro_def(e).raw())->get_ref_name();
}

scope_context::scope_context(context & ctx) {
    m_old_context = g_context;
    g_context     = &ctx;
}

scope_context::~scope_context() {
    g_context     = m_old_context;
}

void initialize_context() {
    g_ref_value        = new name("refv");
    g_ref_value_opcode = new std::string("RefV");
    register_macro_deserializer(*g_ref_value_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0) throw corrupted_stream_exception();
                                    name n;
                                    d >> n;
                                    return mk_ref(n);
                                });
}

void finalize_context() {
    delete g_ref_value;
    delete g_ref_value_opcode;
}
}
