/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/unifier.h"
#include "library/reducible.h"
#include "library/metavar_closure.h"
#include "frontends/lean/util.h"
#include "frontends/lean/info_manager.h"
namespace lean {
/** \brief Create a "choice" constraint that postpone the
    solving the constraints <tt>(cs union (m =?= e))</tt>.
*/
constraint mk_proof_qed_cnstr(environment const & env, expr const & m, expr const & e,
                              constraint_seq const & cs, unifier_config const & cfg,
                              info_manager * im, bool relax) {
    justification j         = mk_failed_to_synthesize_jst(env, m);
    auto choice_fn = [=](expr const & meta, expr const & meta_type, substitution const & s,
                         name_generator const & _ngen) {
        name_generator ngen(_ngen);
        type_checker_ptr tc(mk_type_checker(env, ngen.mk_child(), relax));
        pair<expr, constraint_seq> tcs = tc->infer(e);
        expr e_type                    = tcs.first;
        justification new_j            = mk_type_mismatch_jst(e, e_type, meta_type);
        pair<bool, constraint_seq> dcs = tc->is_def_eq(e_type, meta_type, new_j);
        if (!dcs.first)
            throw unifier_exception(new_j, s);
        constraint_seq new_cs          = cs + tcs.second + dcs.second;
        buffer<constraint> cs_buffer;
        new_cs.linearize(cs_buffer);

        metavar_closure cls(meta);
        cls.add(meta_type);
        cls.mk_constraints(s, j, relax, cs_buffer);
        cs_buffer.push_back(mk_eq_cnstr(meta, e, j, relax));

        unifier_config new_cfg(cfg);
        new_cfg.m_discard    = false;
        unify_result_seq seq = unify(env, cs_buffer.size(), cs_buffer.data(), ngen, substitution(), new_cfg);
        auto p = seq.pull();
        lean_assert(p);
        substitution new_s     = p->first.first;
        constraints  postponed = map(p->first.second,
                                     [&](constraint const & c) {
                                         // we erase internal justifications
                                         return update_justification(c, j);
                                     });
        if (im)
            im->instantiate(new_s);
        constraints r = cls.mk_constraints(new_s, j, relax);
        return append(r, postponed);
    };
    bool owner = false;
    return mk_choice_cnstr(m, choice_fn, to_delay_factor(cnstr_group::Epilogue), owner, j, relax);
}
}
