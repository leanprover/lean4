/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/sexpr_fn.h"

namespace lean {

sexpr append(sexpr const & l1, sexpr const & l2) {
    lean_assert(is_list(l1));
    if (is_nil(l1))
        return l2;
    else
        return sexpr(head(l1), append(tail(l1), l2));
}

sexpr reverse_it(sexpr const & a, sexpr const & l) {
    if (is_nil(l))
        return a;
    else
        return reverse_it(sexpr(head(l), a), tail(l));
}

sexpr reverse(sexpr const & l) {
    return reverse_it(nil(), l);
}

}
