/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/user_recursors.h"
#include "library/blast/revert.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"

namespace lean {
namespace blast {
static unsigned g_ext_id = 0;
struct recursor_branch_extension : public branch_extension {
    hypothesis_priority_queue m_rec_queue;
    recursor_branch_extension() {}
    recursor_branch_extension(recursor_branch_extension const & b):m_rec_queue(b.m_rec_queue) {}
    virtual ~recursor_branch_extension() {}
    virtual branch_extension * clone() { return new recursor_branch_extension(*this); }
};

void initialize_recursor_action() {
    g_ext_id = register_branch_extension(new recursor_branch_extension());
}

void finalize_recursor_action() {
}

static recursor_branch_extension & get_extension() {
    return static_cast<recursor_branch_extension&>(curr_state().get_extension(g_ext_id));
}

optional<name> is_recursor_action_target(hypothesis_idx hidx) {
    state & s = curr_state();
    hypothesis const & h = s.get_hypothesis_decl(hidx);
    expr const & type = h.get_type();
    if (!is_app(type) && !is_constant(type))
        return optional<name>();
    if (is_relation_app(type))
        return optional<name>(); // we don't apply recursors to equivalence relations: =, ~, <->, etc.
    if (!h.is_assumption() && !is_prop(type))
        return optional<name>(); // we only consider assumptions or propositions
    if (get_type_context().is_class(type)) {
        // we don't eliminate type classes instances
        // TODO(Leo): we may revise that in the future... some type classes instances may be worth eliminating (e.g., decidable).
        return optional<name>();
    }
    // TODO(Leo): more restrictions?
    // TODO(Leo): consider user-provided hints
    expr const & I    = get_app_fn(type);
    if (!is_constant(I))
        return optional<name>();
    if (inductive::is_inductive_decl(env(), const_name(I)))
        return optional<name>(name(inductive::get_elim_name(const_name(I)))); // it is builtin recursive datatype
    list<name> Rs = get_recursors_for(env(), const_name(I));
    if (!Rs)
        return optional<name>();
    else
        return optional<name>(head(Rs)); // type has user-defined recursors
}

unsigned get_num_minor_premises(name const & R) {
    return get_recursor_info(env(), R).get_num_minors();
}

bool is_recursive_recursor(name const & R) {
    return get_recursor_info(env(), R).is_recursive();
}

struct recursor_proof_step_cell : public proof_step_cell {
    bool       m_dep;
    branch     m_branch;      // branch for backtracking
    expr       m_proof;       // recursor-application (the position where the goal-proofs are marked by the local constants).
    list<expr> m_goals;       // type of each subgoal/branch encoded as a local constant
    list<expr> m_goal_proofs; // proofs generated so far
    optional<unsigned> m_split_idx;

    recursor_proof_step_cell(bool dep, branch const & b, expr const & pr, list<expr> const & goals, list<expr> const & goal_proofs,
                             optional<unsigned> const & split_idx):
        m_dep(dep), m_branch(b), m_proof(pr), m_goals(goals), m_goal_proofs(goal_proofs),
        m_split_idx(split_idx) {
    }

    virtual ~recursor_proof_step_cell() {}

    virtual action_result resolve(expr const & pr) const override {
        state & s = curr_state();
        s.set_branch(m_branch);
        if (!m_dep) {
            // It is not a dependent elimination, so if pr did not use new hypothesis,
            // we don't need to investigate other branches.
            // This is also a form of non-chronological backtracking.
            expr const & goal    = head(m_goals);
            unsigned arity       = get_arity(mlocal_type(goal));
            expr it              = pr;
            bool skip            = true;
            for (unsigned i = 0; i < arity; i++) {
                if (!is_lambda(it)) {
                    skip = false;
                    break;
                }
                it = binding_body(it);
                if (!closed(it)) {
                    skip = false;
                    break;
                }
            }
            if (skip) {
                lean_assert(closed(it));
                if (m_split_idx) {
                    lean_trace_search(tout() << "backjumping split #" << *m_split_idx << "\n";);
                }
                return action_result::solved(it);
            }
        }
        list<expr> new_goals = tail(m_goals);
        list<expr> new_prs   = cons(pr, m_goal_proofs);
        if (empty(new_goals)) {
            buffer<expr> proof_args;
            expr const & rec = get_app_args(m_proof, proof_args);
            // update proof_args that are goals with their proofs
            unsigned i = proof_args.size();
            while (i > 0) {
                --i;
                if (is_fresh_local(proof_args[i])) {
                    lean_assert(new_prs);
                    proof_args[i] = head(new_prs);
                    new_prs       = tail(new_prs);
                }
            }
            expr result = mk_app(rec, proof_args);
            if (m_split_idx)
                lean_trace_search(tout() << "solved split #" << *m_split_idx << "\n";);
            return action_result::solved(result);
        } else {
            s.pop_proof_step();
            s.push_proof_step(new recursor_proof_step_cell(m_dep, m_branch, m_proof, new_goals, new_prs, m_split_idx));
            s.set_target(mlocal_type(head(new_goals)));
            lean_assert(m_split_idx);
            lean_trace_search(tout() << "next of split #" << *m_split_idx << "\n";);
            return action_result::new_branch();
        }
    }
};

action_result recursor_action(hypothesis_idx hidx, name const & R) {
    state & s = curr_state();
    hypothesis const & h = s.get_hypothesis_decl(hidx);
    expr const & type    = h.get_type();
    lean_assert(is_constant(get_app_fn(type)));

    recursor_info rec_info = get_recursor_info(env(), R);

    if (!rec_info.has_dep_elim() && s.target_depends_on(hidx)) {
        // recursor does does not support dependent elimination, but conclusion
        // depends on major premise
        return action_result::failed();
    }

    buffer<expr> type_args;
    get_app_args(type, type_args);
    buffer<optional<expr>> params;
    for (optional<unsigned> const & pos : rec_info.get_params_pos()) {
        if (!pos) {
            params.push_back(none_expr());
        } else if (*pos >= type_args.size()) {
            return action_result::failed(); // major premise type is ill-formed
        } else {
            params.push_back(some_expr(type_args[*pos]));
        }
    }

    buffer<expr> indices;
    list<unsigned> const & idx_pos = rec_info.get_indices_pos();
    for (unsigned pos : idx_pos) {
        if (pos >= type_args.size()) {
            return action_result::failed(); // major premise type is ill-formed");
        }
        expr const & idx = type_args[pos];
        if (!is_href(idx)) {
            return action_result::failed(); // argument of major premise type is not a href
        }
        for (unsigned i = 0; i < type_args.size(); i++) {
            if (i != pos && is_local(type_args[i]) && mlocal_name(type_args[i]) == mlocal_name(idx)) {
                return action_result::failed(); // argument of major premise is an index, but it occurs more than once
            }
            if (i > pos && // occurs after idx
                std::find(idx_pos.begin(), idx_pos.end(), i) != idx_pos.end() && // it is also an index
                is_href(type_args[i]) && // if it is not an index, it will fail anyway.
                s.hidx_depends_on(href_index(idx), href_index(type_args[i]))) {
                // argument of major premise type is an index, but its type depends on another index
                return action_result::failed();
            }
        }
        indices.push_back(idx);
    }

    scope_curr_state save_state;
    hypothesis_idx_buffer_set to_revert;
    s.collect_direct_forward_deps(hidx, to_revert);
    for (auto i : indices)
        s.collect_direct_forward_deps(href_index(i), to_revert);
    if (!indices.empty()) {
        // If the set of indices is not empty, then we must remove hidx from to_revert,
        // since it depends on the indices.
        to_revert.erase(hidx);
    }
    revert(to_revert);

    expr target       = s.get_target();
    auto target_level = get_type_context().get_level_core(target);
    if (!target_level) return action_result::failed(); // failed to extract universe level of target

    buffer<level> rec_lvls;
    expr const & I = get_app_fn(type);
    buffer<level> I_lvls;
    to_buffer(const_levels(I), I_lvls);
    bool found_target_lvl = false;
    for (unsigned idx : rec_info.get_universe_pos()) {
        if (idx == recursor_info::get_motive_univ_idx()) {
            rec_lvls.push_back(*target_level);
            found_target_lvl = true;
        } else {
            if (idx >= I_lvls.size())
                return action_result::failed(); // ill-formed recursor
            rec_lvls.push_back(I_lvls[idx]);
        }
    }

    if (!found_target_lvl && !is_zero(*target_level)) {
        // recursor can only eliminate into Prop
        return action_result::failed();
    }
    expr rec    = mk_constant(rec_info.get_name(), to_list(rec_lvls));

    for (optional<expr> const & p : params) {
        if (p) {
            rec = mk_app(rec, *p);
        } else {
            // try type class resolution to synthesize argument
            expr rec_type = relaxed_whnf(infer_type(rec));
            if (!is_pi(rec_type))
                return action_result::failed(); // ill-formed recursor
            expr arg_type = binding_domain(rec_type);
            if (auto inst = mk_class_instance(arg_type)) {
                rec = mk_app(rec, *inst);
            } else {
                return action_result::failed(); // failed to generate instance
            }
        }
    }

    expr motive = target;
    if (rec_info.has_dep_elim())
        motive  = s.mk_lambda(h.get_self(), motive);
    motive = s.mk_lambda(indices, motive);
    rec      = mk_app(rec, motive);

    expr rec_type          = relaxed_whnf(infer_type(rec));
    unsigned curr_pos      = params.size() + 1 /* motive */;
    unsigned first_idx_pos = rec_info.get_first_index_pos();
    bool consumed_major    = false;
    buffer<expr> new_goals;

    while (is_pi(rec_type) && curr_pos < rec_info.get_num_args()) {
        if (first_idx_pos == curr_pos) {
            for (expr const & idx : indices) {
                rec      = mk_app(rec, idx);
                rec_type = relaxed_whnf(instantiate(binding_body(rec_type), idx));
                if (!is_pi(rec_type))
                    return action_result::failed(); // ill-formed type
                curr_pos++;
            }
            rec      = mk_app(rec, h.get_self());
            rec_type = relaxed_whnf(instantiate(binding_body(rec_type), h.get_self()));
            consumed_major = true;
            curr_pos++;
        } else {
            expr new_type  = binding_domain(rec_type);
            expr rec_arg;
            if (binding_info(rec_type).is_inst_implicit()) {
                auto inst = mk_class_instance(new_type);
                if (!inst) return action_result::failed(); // type class resolution failed
                rec_arg   = *inst;
            } else {
                rec_arg = mk_fresh_local(new_type); // placeholder
                new_goals.push_back(rec_arg);
            }
            rec       = mk_app(rec, rec_arg);
            rec_type  = relaxed_whnf(instantiate(binding_body(rec_type), rec_arg));
            curr_pos++;
        }
    }

    if (curr_pos != rec_info.get_num_args() || !consumed_major)
        return action_result::failed(); // ill-formed recursor

    save_state.commit();
    optional<unsigned> split_idx;
    if (new_goals.size() > 1) {
        split_idx = mk_split_idx();
    }
    lean_trace_search(
        tout() << "recursor ";
        if (split_idx)
            tout () << "(split #" << *split_idx << ") ";
        tout() << R << " " << h << "\n";);
    if (new_goals.empty()) {
        return action_result::solved(rec);
    }
    s.del_hypothesis(hidx);
    s.push_proof_step(new recursor_proof_step_cell(rec_info.has_dep_elim(), s.get_branch(), rec, to_list(new_goals), list<expr>(), split_idx));
    s.set_target(mlocal_type(new_goals[0]));
    return action_result::new_branch();
}

action_result recursor_action(hypothesis_idx hidx) {
    state & s = curr_state();
    hypothesis const & h = s.get_hypothesis_decl(hidx);
    expr const & type = h.get_type();
    expr const & I    = get_app_fn(type);
    if (!is_constant(I))
        return action_result::failed();
    list<name> Rs = get_recursors_for(env(), const_name(I));
    for (auto R : Rs) {
        auto r = recursor_action(hidx, R);
        if (!failed(r))
            return r;
    }
    return action_result::failed();
}

action_result recursor_preprocess_action(hypothesis_idx hidx) {
    if (!get_config().m_recursor)
        return action_result::failed();
    if (optional<name> R = is_recursor_action_target(hidx)) {
        unsigned num_minor = get_num_minor_premises(*R);
        if (num_minor == 1) {
            action_result r = recursor_action(hidx, *R);
            if (!failed(r)) {
                // if (!preprocess) display_action("recursor");
                return r;
            }
        } else {
            // If the hypothesis recursor has more than 1 minor premise, we
            // put it in a priority queue.
            // TODO(Leo): refine

            // TODO(Leo): the following weight computation is too simple...
            double w = 1.0 / (static_cast<double>(hidx) + 1.0);
            if (!is_recursive_recursor(*R)) {
                // TODO(Leo): we need a better strategy for handling recursive recursors...
                w += static_cast<double>(num_minor);
                recursor_branch_extension & ext = get_extension();
                ext.m_rec_queue.insert(w, hidx);
                return action_result::new_branch();
            }
        }
    }
    return action_result::failed();
}

action_result recursor_action() {
    if (!get_config().m_recursor)
        return action_result::failed();
    recursor_branch_extension & ext = get_extension();
    while (true) {
        if (ext.m_rec_queue.empty())
            return action_result::failed();
        unsigned hidx             = ext.m_rec_queue.erase_min();
        hypothesis const & h_decl = curr_state().get_hypothesis_decl(hidx);
        if (h_decl.is_dead())
            continue;
        if (optional<name> R = is_recursor_action_target(hidx)) {
            Try(recursor_action(hidx, *R));
        }
    }
}
}}
