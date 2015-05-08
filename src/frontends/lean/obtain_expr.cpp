/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/kernel_serializer.h"
#include "frontends/lean/obtain_expr.h"

namespace lean {
unsigned obtain_struct::size() const {
    if (m_leaf) return 1;
    unsigned r = 0;
    for (auto const & o : m_children) r += o.size();
    return r;
}

obtain_struct read_obtain_struct(deserializer & d);
inline serializer & operator<<(serializer & s, obtain_struct const & o) { o.write(s); return s; }
inline deserializer & operator>>(deserializer & d, obtain_struct & o) {
    o = read_obtain_struct(d);
    return d;
}

void obtain_struct::write(serializer & s) const {
    s << m_leaf;
    if (!m_leaf)
        write_list(s, m_children);
}

obtain_struct read_obtain_struct(deserializer & d) {
    bool leaf = d.read_bool();
    if (leaf)
        return obtain_struct();
    return obtain_struct(read_list<obtain_struct>(d));
}

static name * g_obtain_name = nullptr;
static std::string * g_obtain_opcode = nullptr;

[[ noreturn ]] static void throw_ex() { throw exception("unexpected occurrence of 'obtain' expression"); }

class obtain_macro_cell : public macro_definition_cell {
    obtain_struct m_struct;
public:
    obtain_macro_cell(obtain_struct const & s):m_struct(s) {}
    virtual name get_name() const { return *g_obtain_name; }
    virtual pair<expr, constraint_seq> check_type(expr const &, extension_context &, bool) const { throw_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_ex(); }
    virtual void write(serializer & s) const {
        s << *g_obtain_opcode << m_struct;
    }
    obtain_struct const & get_struct() const { return m_struct; }
};

static bool validate(obtain_struct const & s, expr const & decls_goal) {
    unsigned sz = s.size();
    expr it = decls_goal;
    for (unsigned i = 0; i < sz; i++) {
        if (!is_lambda(it))
            return false;
        it = binding_body(it);
    }
    return true;
}

static expr mk_obtain_expr_core(obtain_struct const & s, expr const & from, expr const & decls_goal) {
    lean_assert(validate(s, decls_goal));
    macro_definition def(new obtain_macro_cell(s));
    expr args[2] = {from, decls_goal};
    return mk_macro(def, 2, args);
}

expr mk_obtain_expr(obtain_struct const & s, buffer<expr> const & decls, expr const & from, expr const & goal) {
    lean_assert(s.size() == decls.size());
    lean_assert(std::all_of(decls.begin(), decls.end(), is_local));
    return mk_obtain_expr_core(s, from, Fun(decls, goal));
}

bool is_obtain_expr(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_obtain_name;
}

void decompose_obtain(expr const & e, obtain_struct & s, expr & from, expr & decls_goal) {
    lean_assert(is_obtain_expr(e));
    s = static_cast<obtain_macro_cell const*>(macro_def(e).raw())->get_struct();
    from = macro_arg(e, 0);
    decls_goal = macro_arg(e, 1);
}

void initialize_obtain_expr() {
    g_obtain_name   = new name("obtain");
    g_obtain_opcode = new std::string("Obtain");
    register_macro_deserializer(*g_obtain_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    obtain_struct s;
                                    d >> s;
                                    if (!validate(s, args[1]))
                                        throw corrupted_stream_exception();
                                    return mk_obtain_expr_core(s, args[0], args[1]);
                                });
}

void finalize_obtain_expr() {
    delete g_obtain_opcode;
    delete g_obtain_name;
}
};
