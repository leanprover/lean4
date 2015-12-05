/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/util.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {
bool is_not(expr const & e, expr & a) {
    return ::lean::is_not(env(), e, a);
}
bool is_not(expr const & e) {
    expr not_e;
    return is_not(e, not_e);
}
bool is_false(expr const & e) {
    return ::lean::is_false(env(), e);
}
}}
