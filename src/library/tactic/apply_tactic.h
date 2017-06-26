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
*/
struct apply_cfg {
    transparency_mode m_mode{transparency_mode::Semireducible};
    bool              m_approx{true};
    new_goals_kind    m_new_goals{new_goals_kind::NonDepFirst};
    bool              m_instances{true};
    bool              m_auto_param{true};
    bool              m_opt_param{true};
    apply_cfg() {}
    apply_cfg(vm_obj const & cfg);
};
optional<tactic_state> apply(type_context & ctx, expr const & e, apply_cfg const & cfg, tactic_state const & s);
/* For backward compatibility */
optional<tactic_state> apply(type_context & ctx, bool all, bool use_instances, expr const & e, tactic_state const & s);
void initialize_apply_tactic();
void finalize_apply_tactic();
}
