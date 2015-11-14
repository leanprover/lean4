/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/hypothesis.h"
namespace lean {
namespace blast {
/** \brief If the given hypothesis is of the form (H : t = x) or (H : x = s), then
    eliminate x (and H). Return true if success. */
bool subst_action(hypothesis_idx hidx);
}}
