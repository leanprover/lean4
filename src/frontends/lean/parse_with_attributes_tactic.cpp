/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/constants.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/tactic/expr_to_tactic.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/decl_attributes.h"

namespace lean {
static name * g_name             = nullptr;
static std::string * g_opcode    = nullptr;

// Auxiliary macro for wrapping decl_attributes object as an expression
class attributes_macro_cell : public macro_definition_cell {
    decl_attributes m_decl;
public:
    attributes_macro_cell(decl_attributes const & decl):m_decl(decl) {}
    virtual name get_name() const { return *g_name; }
    virtual void write(serializer & s) const { s << *g_opcode; m_decl.write(s); }
    virtual pair<expr, constraint_seq> check_type(expr const &, extension_context &, bool) const {
        return mk_pair(mk_constant(get_tactic_expr_name()), constraint_seq());
    }
    virtual optional<expr> expand(expr const &, extension_context &) const {
        return some_expr(mk_constant(get_tactic_expr_builtin_name()));
    }
    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto o = dynamic_cast<attributes_macro_cell const *>(&other))
            return m_decl == o->m_decl;
        return false;
    }
    decl_attributes const & get_attrs() const { return m_decl; }
};

expr mk_attributes_expr(decl_attributes const & d) {
    macro_definition def(new attributes_macro_cell(d));
    return mk_macro(def);
}

bool is_attributes_expr(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_name;
}

decl_attributes const & get_attributes_expr_attributes(expr const & e) {
    lean_assert(is_attributes_expr(e));
    return static_cast<attributes_macro_cell const*>(macro_def(e).raw())->get_attrs();
}

static expr * g_with_attributes_tac = nullptr;

expr mk_with_attributes_tactic_expr(decl_attributes const & a, buffer<name> const & cs, expr const & t) {
    return mk_app(*g_with_attributes_tac, mk_attributes_expr(a), ids_to_tactic_expr(cs), t);
}

tactic with_attributes(decl_attributes const & d, list<name> const & cs, tactic const & t) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            environment new_env = env;
            for (name const & c : cs)
                new_env = d.apply(new_env, ios, c, get_namespace(new_env));
            return t(new_env, ios, s);
        });
}

expr parse_with_attributes_tactic(parser & p) {
    buffer<name> cs;
    bool persistent   = false;
    bool abbrev       = false;
    decl_attributes attributes(abbrev, persistent);
    name c            = p.check_constant_next("invalid 'with_attributes' tactical, constant expected");
    cs.push_back(c);
    while (p.curr_is_identifier()) {
        cs.push_back(p.check_constant_next("invalid 'with_attributes' tactical, constant expected"));
    }
    attributes.parse(p);
    expr t = p.parse_tactic(get_max_prec());
    return mk_with_attributes_tactic_expr(attributes, cs, t);
}

void initialize_with_attributes_tactic() {
    g_name     = new name("attributes");
    g_opcode   = new std::string("ATTRS");
    register_macro_deserializer(*g_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num > 0)
                                        throw corrupted_stream_exception();
                                    decl_attributes attrs;
                                    attrs.read(d);
                                    return mk_attributes_expr(attrs);
                                });

    name with_attributes_tac_name{"tactic", "with_attributes_tac"};
    g_with_attributes_tac = new expr(Const(with_attributes_tac_name));
    register_tac(with_attributes_tac_name,
                 [=](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const * p) {
                     buffer<expr> args;
                     get_app_args(e, args);
                     if (args.size() != 3)
                         throw expr_to_tactic_exception(e, "invalid 'with_attributes' tactical, it must have two arguments");
                     check_tactic_expr(args[0], "invalid 'with_attributes' tactical, invalid argument");
                     expr attrs = get_tactic_expr_expr(args[0]);
                     if (!is_attributes_expr(attrs))
                         throw expr_to_tactic_exception(args[0], "invalid 'with_attributes' tactical, invalid argument");
                     buffer<name> cs;
                     get_tactic_id_list_elements(args[1], cs, "invalid 'with_attributes' tactical, invalid argument");
                     tactic t  = expr_to_tactic(tc, fn, args[2], p);
                     return with_attributes(get_attributes_expr_attributes(attrs), to_list(cs), t);
                 });
}

void finalize_with_attributes_tactic() {
    delete g_name;
    delete g_opcode;
    delete g_with_attributes_tac;
}
}
