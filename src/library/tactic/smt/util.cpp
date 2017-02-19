/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/annotation.h"
#include "library/util.h"
#include "library/replace_visitor.h"
#include "library/vm/vm.h"
#include "library/tactic/smt/congruence_closure.h"

namespace lean {
static name * g_cc_proof_name = nullptr;
static macro_definition * g_cc_proof_macro = nullptr;

class cc_proof_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_cc_proof_name; }

    virtual expr check_type(expr const & e, abstract_type_context & ctx, bool) const {
        return mk_eq(ctx, macro_arg(e, 0), macro_arg(e, 1));
    }

    virtual optional<expr> expand(expr const &, abstract_type_context &) const {
        /* This is a temporary/delayed proof step. */
        lean_unreachable();
    }

    virtual void write(serializer &) const {
        /* This is a temporary/delayed proof step. */
        lean_unreachable();
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        cc_proof_macro_cell const * other_ptr = dynamic_cast<cc_proof_macro_cell const *>(&other);
        return other_ptr;
    }

    virtual unsigned hash() const { return 23; }
};

/* Delayed (congruence closure procedure) proof.
   This proof is a placeholder for the real one that is computed only if needed. */
expr mk_delayed_cc_eq_proof(expr const & e1, expr const & e2) {
    expr args[2] = {e1, e2};
    return mk_macro(*g_cc_proof_macro, 2, args);
}

bool is_delayed_cc_eq_proof(expr const & e) {
    return is_macro(e) && dynamic_cast<cc_proof_macro_cell const *>(macro_def(e).raw());
}

static name * g_theory_proof = nullptr;

expr mark_cc_theory_proof(expr const & pr) {
    return mk_annotation(*g_theory_proof, pr);
}

bool is_cc_theory_proof(expr const & e) {
    return is_annotation(e, *g_theory_proof);
}

expr get_cc_theory_proof_arg(expr const & pr) {
    lean_assert(is_cc_theory_proof(pr));
    return get_annotation_arg(pr);
}

class expand_delayed_cc_proofs_fn : public replace_visitor {
    congruence_closure const & m_cc;

    expr visit_macro(expr const & e) {
        if (is_delayed_cc_eq_proof(e)) {
            expr const & lhs = macro_arg(e, 0);
            expr const & rhs = macro_arg(e, 1);
            return *m_cc.get_eq_proof(lhs, rhs);
        } else {
            return replace_visitor::visit_macro(e);
        }
    }

public:
    expand_delayed_cc_proofs_fn(congruence_closure const & cc):m_cc(cc) {}
};

expr expand_delayed_cc_proofs(congruence_closure const & cc, expr const & e) {
    return expand_delayed_cc_proofs_fn(cc)(e);
}

void initialize_smt_util() {
    g_cc_proof_name   = new name("cc_proof");
    g_cc_proof_macro  = new macro_definition(new cc_proof_macro_cell());
    g_theory_proof    = new name("th_proof");
    register_annotation(*g_theory_proof);
}

void finalize_smt_util() {
    delete g_cc_proof_macro;
    delete g_cc_proof_name;
    delete g_theory_proof;
}
}
