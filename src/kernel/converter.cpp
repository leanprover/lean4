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
// Temporary hack for ignoring opaque annotations in the kernel
LEAN_THREAD_VALUE(unsigned, g_everything_transparent, false);

transparent_scope::transparent_scope():m_old_value(g_everything_transparent) {
    g_everything_transparent = true;
}
transparent_scope::~transparent_scope() {
    g_everything_transparent = m_old_value;
}

/**
   \brief Predicate for deciding whether \c d is an opaque definition or not.

   Here is the basic idea:

   1) Each definition has an opaque flag. This flag cannot be modified after a definition is added to the environment.
   The opaque flag affects the convertability check. The idea is to minimize the number of delta-reduction steps.
   We also believe it increases the modularity of Lean developments by minimizing the dependency on how things are defined.
   We should view non-opaque definitions as "inline definitions" used in programming languages such as C++.

   2) Whenever type checking an expression, the user can provide a predicate that is true for for additional definitions that
   should be considered opaque. Note that, if \c t type checks when using predicate P, then t also type checks
   (modulo resource constraints) without it. Again, the purpose of the predicate is to mimimize the number
   of delta-reduction steps.

   3) To be able to prove theorems about an opaque definition, we treat an opaque definition D in a module M as
   transparent when we are type checking another definition/theorem D' also in M. This rule only applies if
   D is not a theorem, nor pred(D) is true. To implement this feature, this class has a field
   m_module_idx that is not none when this rule should be applied.
*/
bool is_opaque(declaration const & d, extra_opaque_pred const & pred, optional<module_idx> const & mod_idx) {
    lean_assert(d.is_definition());
    if (g_everything_transparent) return false; // temporary hack
    if (d.is_theorem()) return true;                               // theorems are always opaque
    if (pred(d.get_name())) return true;                           // extra_opaque predicate overrides opaque flag
    if (!d.is_opaque()) return false;                              // d is a transparent definition
    if (mod_idx && d.get_module_idx() == *mod_idx) return false;   // the opaque definitions in mod_idx are considered transparent
    return true;                                                   // d is opaque
}

extra_opaque_pred g_always_false([](name const &) { return false; });
extra_opaque_pred const & no_extra_opaque() {
    return g_always_false;
}

/** \brief Auxiliary method for \c is_delta */
static optional<declaration> is_delta_core(environment const & env, expr const & e, extra_opaque_pred const & pred,
                                           optional<module_idx> const & mod_idx) {
    if (is_constant(e)) {
        if (auto d = env.find(const_name(e)))
            if (d->is_definition() && !is_opaque(*d, pred, mod_idx))
                return d;
    }
    return none_declaration();
}

/**
   \brief Return some definition \c d iff \c e is a target for delta-reduction, and the given definition is the one
   to be expanded.
*/
optional<declaration> is_delta(environment const & env, expr const & e,
                               extra_opaque_pred const & pred, optional<module_idx> const & mod_idx) {
    return is_delta_core(env, get_app_fn(e), pred, mod_idx);
}

static optional<module_idx> * g_opt_main_module_idx = nullptr;
optional<declaration> is_delta(environment const & env, expr const & e, extra_opaque_pred const & pred) {
    return is_delta(env, e, pred, *g_opt_main_module_idx);
}

optional<declaration> is_delta(environment const & env, expr const & e) {
    return is_delta(env, e, g_always_false);
}


static no_delayed_justification * g_no_delayed_jst = nullptr;
pair<bool, constraint_seq> converter::is_def_eq(expr const & t, expr const & s, type_checker & c) {
    return is_def_eq(t, s, c, *g_no_delayed_jst);
}

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

name converter::mk_fresh_name(type_checker & tc) { return tc.mk_fresh_name(); }
pair<expr, constraint_seq> converter::infer_type(type_checker & tc, expr const & e) { return tc.infer_type(e); }
extension_context & converter::get_extension(type_checker & tc) { return tc.get_extension(); }

std::unique_ptr<converter> mk_default_converter(environment const & env, optional<module_idx> mod_idx,
                                                bool memoize, extra_opaque_pred const & pred) {
    return std::unique_ptr<converter>(new default_converter(env, mod_idx, memoize, pred));
}
std::unique_ptr<converter> mk_default_converter(environment const & env, optional<module_idx> mod_idx,
                                                bool memoize) {
    return mk_default_converter(env, mod_idx, memoize, g_always_false);
}
std::unique_ptr<converter> mk_default_converter(environment const & env, bool unfold_opaque_main, bool memoize,
                                                extra_opaque_pred const & pred) {
    if (unfold_opaque_main)
        return mk_default_converter(env, optional<module_idx>(0), memoize, pred);
    else
        return mk_default_converter(env, optional<module_idx>(), memoize, pred);
}
std::unique_ptr<converter> mk_default_converter(environment const & env, bool unfold_opaque_main, bool memoize) {
    return mk_default_converter(env, unfold_opaque_main, memoize, g_always_false);
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
