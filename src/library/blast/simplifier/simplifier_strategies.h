/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/strategy.h"

namespace lean {
namespace blast {
strategy mk_simplify_target_strategy();
strategy mk_simplify_all_strategy();
strategy mk_simplify_using_hypotheses_strategy();
}}
