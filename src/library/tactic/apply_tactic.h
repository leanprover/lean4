/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic_state.h"
namespace lean {
/*
inductive new_goals
| non_dep_first | non_dep_only | all
*/
enum class new_goals_kind { NonDepFirst, NonDepOnly, All };
/*
structure apply_cfg :=
(md            := semireducible)
(approx        := tt)
(new_goals     := new_goals.non_dep_first)
(instances     := tt)
(auto_param    := tt)
(opt_param     := tt)
(unify         := tt)
*/
struct apply_cfg {
    transparency_mode m_mode{transparency_mode::Semireducible};
    bool              m_approx{true};
    new_goals_kind    m_new_goals{new_goals_kind::NonDepFirst};
    bool              m_instances{true};
    bool              m_auto_param{true};
    bool              m_opt_param{true};
    bool              m_unify{true};
    apply_cfg() {}
    apply_cfg(vm_obj const & cfg);
};
optional<tactic_state> apply(type_context_old & ctx, expr const & e, apply_cfg const & cfg, tactic_state const & s);
/* For backward compatibility */
optional<tactic_state> apply(type_context_old & ctx, bool all, bool use_instances, expr const & e, tactic_state const & s);

/* Helper functions */
bool synth_instances(type_context_old & ctx, buffer<expr> const & metas, buffer<bool> const & is_instance,
                     tactic_state const & s, vm_obj * out_error_obj, char const * tac_name);
void collect_new_goals(type_context_old & ctx, new_goals_kind k, buffer<expr> const & metas, buffer<expr> & new_goals);

void initialize_apply_tactic();
void finalize_apply_tactic();
}
