/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/lbool.h"
namespace lean {
std::ostream & operator<<(std::ostream & out, lbool b) {
    switch (b) {
    case l_false: return out << "l_false";
    case l_true:  return out << "l_true";
    default:      return out << "l_undef";
    }
}
}
