/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/lbool.h"
#include "kernel/converter.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"
#include "kernel/type_checker.h"
#include "kernel/default_converter.h"

namespace lean {
/**
   \brief Predicate for deciding whether \c d is an opaque definition or not.

   Here is the basic idea:

   1) Each definition has an opaque flag. This flag cannot be modified after a definition is added to the environment.
   The opaque flag affects the convertability check. The idea is to minimize the number of delta-reduction steps.
   We also believe it increases the modularity of Lean developments by minimizing the dependency on how things are defined.
   We should view non-opaque definitions as "inline definitions" used in programming languages such as C++.

   2) To be able to prove theorems about an opaque definition, we treat an opaque definition D in a module M as
   transparent when we are type checking another definition/theorem D' also in M. This rule only applies if
   D is not a theorem, nor pred(D) is true. To implement this feature, this class has a field
   m_module_idx that is not none when this rule should be applied.
*/
bool is_opaque(declaration const & d, optional<module_idx> const & mod_idx) {
    lean_assert(d.is_definition());
    if (d.is_theorem()) return true;                               // theorems are always opaque
    if (!d.is_opaque()) return false;                              // d is a transparent definition
    if (mod_idx && d.get_module_idx() == *mod_idx) return false;   // the opaque definitions in mod_idx are considered transparent
    return true;                                                   // d is opaque
}

static optional<module_idx> * g_opt_main_module_idx = nullptr;

optional<declaration> is_delta(environment const & env, expr const & e) {
    expr const & f = get_app_fn(e);
    if (is_constant(f)) {
        if (auto d = env.find(const_name(f)))
            if (d->is_definition() && !is_opaque(*d, *g_opt_main_module_idx))
                return d;
    }
    return none_declaration();
}

static no_delayed_justification * g_no_delayed_jst = nullptr;

pair<bool, constraint_seq> converter::is_def_eq(expr const & t, expr const & s, type_checker & c) {
    return is_def_eq(t, s, c, *g_no_delayed_jst);
}

name converter::mk_fresh_name(type_checker & tc) { return tc.mk_fresh_name(); }

pair<expr, constraint_seq> converter::infer_type(type_checker & tc, expr const & e) { return tc.infer_type(e); }

extension_context & converter::get_extension(type_checker & tc) { return tc.get_extension(); }


/** \brief Do nothing converter */
struct dummy_converter : public converter {
    virtual pair<expr, constraint_seq> whnf(expr const & e, type_checker &) {
        return mk_pair(e, constraint_seq());
    }
    virtual pair<bool, constraint_seq> is_def_eq(expr const &, expr const &, type_checker &, delayed_justification &) {
        return mk_pair(true, constraint_seq());
    }
    virtual optional<module_idx> get_module_idx() const { return optional<module_idx>(); }
    virtual bool is_opaque(declaration const &) const { return false; }
};

std::unique_ptr<converter> mk_dummy_converter() {
    return std::unique_ptr<converter>(new dummy_converter());
}

void initialize_converter() {
    g_opt_main_module_idx = new optional<module_idx>(g_main_module_idx);
    g_no_delayed_jst      = new no_delayed_justification();
}

void finalize_converter() {
    delete g_opt_main_module_idx;
    delete g_no_delayed_jst;
}
}
