/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/hypothesis.h"

namespace lean {
namespace blast {
/** \brief Revert the given hypotheses and their dependencies.
    Return the total number of hypotheses reverted. */
unsigned revert(buffer<hypothesis_idx> & hidxs);
unsigned revert(hypothesis_idx_buffer_set & hidxs);
}}
