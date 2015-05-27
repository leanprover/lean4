/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
class parser;
expr parse_rewrite_tactic(parser & p);
expr parse_krewrite_tactic(parser & p);
expr parse_xrewrite_tactic(parser & p);
expr parse_esimp_tactic(parser & p);
expr parse_unfold_tactic(parser & p);
expr parse_fold_tactic(parser & p);
}
