/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/exception.h"
#include "util/sstream.h"
#include "library/tactic/proof_builder.h"

namespace lean {
expr find(proof_map const & m, name const & n) {
    expr * r = const_cast<proof_map&>(m).splay_find(n);
    if (r)
        return *r;
    throw exception(sstream() << "proof for goal '" << n << "' not found");
}
}
