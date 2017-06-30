/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/apply_tactic.h"
namespace lean {
/*
structure rewrite_cfg extends apply_cfg :=
(md            := reducible)
(symm          := ff)
(occs          := occurrences.all)
*/
struct rewrite_cfg : public apply_cfg {
    bool              m_symm{false};
    occurrences       m_occs;
    rewrite_cfg() { m_mode = transparency_mode::Reducible; }
    rewrite_cfg(vm_obj const & cfg);
};

void initialize_rewrite_tactic();
void finalize_rewrite_tactic();
}
