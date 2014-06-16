/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/parser.h"

namespace lean {
tactic parse_skip_tactic(parser &) {
    // TODO(Leo): this is just for testing
    return tactic();
}

tactic_cmd_table get_builtin_tactic_cmds() {
    tactic_cmd_table t;
    t.insert("skip", tactic_cmd_info("skip", "dummy tactic", parse_skip_tactic));
    return t;
}
}
