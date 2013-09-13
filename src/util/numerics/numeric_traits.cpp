/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include <cfenv>
#include <cmath>
#include "util/numerics/numeric_traits.h"

namespace lean {

void set_processor_rounding(bool plus_inf) {
    if (plus_inf)
        std::fesetround(FE_UPWARD);
    else
        std::fesetround(FE_DOWNWARD);
}
};
