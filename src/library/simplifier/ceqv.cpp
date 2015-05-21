/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "library/util.h"
#include "library/relation_manager.h"
#include "library/occurs.h"

namespace lean {
bool is_equivalence(environment const & env, expr const & e, expr & rel, expr & lhs, expr & rhs) {
    buffer<expr> args;
    rel = get_app_args(e, args);
    if (!is_constant(rel) || !is_equivalence(env, const_name(rel)))
        return false;
    relation_info const * rel_info = get_relation_info(env, const_name(rel));
    if (!rel_info || rel_info->get_lhs_pos() >= args.size() || rel_info->get_rhs_pos() >= args.size())
        return false;
    lhs = args[rel_info->get_lhs_pos()];
    rhs = args[rel_info->get_rhs_pos()];
    return true;
}

bool is_equivalence(environment const & env, expr const & e, expr & lhs, expr & rhs) {
    expr rel;
    return is_equivalence(env, e, rel, lhs, rhs);
}

bool is_ceqv(environment const & env, name_generator && ngen, expr e) {
    if (has_expr_metavar(e))
        return false;
    name_set to_find;
    // Define a procedure for removing arguments from to_find.
    auto visitor_fn = [&](expr const & e, unsigned) {
        if (is_local(e)) {
            to_find.erase(mlocal_name(e));
            return false;
        } else if (is_metavar(e)) {
            return false;
        } else {
            return true;
        }
    };
    bool is_std = is_standard(env);
    type_checker tc(env, ngen.mk_child());
    buffer<expr> hypotheses; // arguments that are propositions
    while (is_pi(e)) {
        if (!to_find.empty()) {
            // Support for dependent types.
            // We may find the instantiation for the previous arguments
            // by matching the type.
            for_each(binding_domain(e), visitor_fn);
        }
        expr local = mk_local(ngen.next(), binding_domain(e));
        if (binding_info(e).is_inst_implicit()) {
            // If the argument can be instantiated by type class resolution, then
            // we don't need to find it in the lhs
        } else if (is_std && tc.is_prop(binding_domain(e)).first) {
            // If the argument is a proposition, we store it in hypotheses.
            // We check whether the lhs occurs in hypotheses or not.
            hypotheses.push_back(binding_domain(e));
        } else {
            to_find.insert(mlocal_name(local));
        }
        e = instantiate(binding_body(e), local);
    }
    expr lhs, rhs;
    if (!is_equivalence(env, e, lhs, rhs))
        return false;
    // traverse lhs, and remove found variables from to_find
    for_each(lhs, visitor_fn);
    if (!to_find.empty())
        return false;
    // basic looping ceq detection: the left-hand-side should not occur in the right-hand-side,
    // nor it should occur in any of the hypothesis
    if (occurs(lhs, rhs))
        return false;
    if (std::any_of(hypotheses.begin(), hypotheses.end(), [&](expr const & h) { return occurs(lhs, h); }))
        return false;
    return true;
}

static bool is_permutation(expr const & lhs, expr const & rhs, unsigned offset, buffer<optional<unsigned>> & p) {
    if (lhs.kind() != rhs.kind())
        return false;
    switch (lhs.kind()) {
    case expr_kind::Constant: case expr_kind::Sort:
    case expr_kind::Meta: case expr_kind::Local:
        return lhs == rhs;
    case expr_kind::Var:
        if (var_idx(lhs) < offset) {
            return lhs == rhs; // locally bound variable
        } else if (var_idx(lhs) - offset < p.size()) {
            if (p[var_idx(lhs) - offset]) {
                return *(p[var_idx(lhs) - offset]) == var_idx(rhs);
            } else {
                p[var_idx(lhs) - offset] = var_idx(rhs);
                return true;
            }
        } else {
            return lhs == rhs; // free variable
        }
    case expr_kind::Lambda: case expr_kind::Pi:
        return
            is_permutation(binding_domain(lhs), binding_domain(rhs), offset, p) &&
            is_permutation(binding_body(lhs), binding_body(rhs), offset+1, p);
    case expr_kind::App:
        return
            is_permutation(app_fn(lhs), app_fn(rhs), offset, p) &&
            is_permutation(app_arg(lhs), app_arg(rhs), offset, p);
    case expr_kind::Macro:
        if (macro_def(lhs) != macro_def(rhs) ||
            macro_num_args(lhs) != macro_num_args(rhs))
            return false;
        for (unsigned i = 0; i < macro_num_args(lhs); i++) {
            if (!is_permutation(macro_arg(lhs, i), macro_arg(rhs, i), offset, p))
                return false;
        }
        return true;
    }
    lean_unreachable();
}

bool is_permutation_ceqv(environment const & env, expr e) {
    unsigned num_args = 0;
    while (is_pi(e)) {
        e = binding_domain(e);
        num_args++;
    }
    expr lhs, rhs;
    if (is_equivalence(env, e, lhs, rhs)) {
        buffer<optional<unsigned>> permutation;
        permutation.resize(num_args);
        return is_permutation(lhs, rhs, 0, permutation);
    } else {
        return false;
    }
}
}
