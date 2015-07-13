/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/type_checker.h"
#include "library/kernel_serializer.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
static name * g_options_name             = nullptr;
static std::string * g_options_opcode    = nullptr;

[[ noreturn ]] static void throw_ex() { throw exception("unexpected occurrence of 'options' expression"); }

// Auxiliary macro for wrapping a options object as an expression
class options_macro_cell : public macro_definition_cell {
    options m_info;
public:
    options_macro_cell(options const & info):m_info(info) {}
    virtual name get_name() const { return *g_options_name; }
    virtual void write(serializer & s) const {
        s << *g_options_opcode << m_info;
    }
    virtual pair<expr, constraint_seq> check_type(expr const &, extension_context &, bool) const { throw_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_ex(); }
    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto o = dynamic_cast<options_macro_cell const *>(&other))
            return m_info == o->m_info;
        return false;
    }
    options const & get_info() const { return m_info; }
};

expr mk_options_expr(options const & loc) {
    macro_definition def(new options_macro_cell(loc));
    return mk_macro(def);
}

bool is_options_expr(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_options_name;
}

options const & get_options_expr_options(expr const & e) {
    lean_assert(is_options_expr(e));
    return static_cast<options_macro_cell const*>(macro_def(e).raw())->get_info();
}

static expr * g_with_options_tac = nullptr;

expr mk_with_options_tactic_expr(options const & o, expr const & t) {
    return mk_app(*g_with_options_tac, mk_options_expr(o), t);
}

tactic with_options(options const & o, tactic const & t) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            options c = ios.get_options();
            io_state new_ios(ios, join(c, o));
            return t(env, new_ios, s);
        });
}

void initialize_with_options_tactic() {
    g_options_name     = new name("options");
    g_options_opcode   = new std::string("OPTM");
    register_macro_deserializer(*g_options_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num > 0)
                                        throw corrupted_stream_exception();
                                    options info;
                                    d >> info;
                                    return mk_options_expr(info);
                                });

    name with_options_tac_name{"tactic", "with_options_tac"};
    g_with_options_tac = new expr(Const(with_options_tac_name));
    register_tac(with_options_tac_name,
                 [=](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const * p) {
                     buffer<expr> args;
                     get_app_args(e, args);
                     if (args.size() != 2)
                         throw expr_to_tactic_exception(e, "invalid 'with_options' tactical, it must have two arguments");
                     check_tactic_expr(args[0], "invalid 'with_options' tactical, invalid argument");
                     expr opts = get_tactic_expr_expr(args[0]);
                     if (!is_options_expr(opts))
                         throw expr_to_tactic_exception(args[0], "invalid 'with_options' tactical, invalid argument");
                     tactic t  = expr_to_tactic(tc, fn, args[1], p);
                     return with_options(get_options_expr_options(opts), t);
                 });
}

void finalize_with_options_tactic() {
    delete g_options_name;
    delete g_options_opcode;
    delete g_with_options_tac;
}
}
