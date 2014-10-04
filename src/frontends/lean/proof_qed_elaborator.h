/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/unifier.h"
#include "frontends/lean/info_manager.h"

namespace lean {
/** \brief Create a "choice" constraint that postpone the
    solving the constraints <tt>(cs union (m =?= e))</tt>.

    \remark A proof-qed block may instantiate meta-variables in the
    info_manager. Thus, we provide the info_manager to make sure
    this assignments are reflected on it.
*/
constraint mk_proof_qed_cnstr(environment const & env, expr const & m, expr const & e,
                              constraint_seq const & cs, unifier_config const & cfg,
                              info_manager * im, bool relax);
}
