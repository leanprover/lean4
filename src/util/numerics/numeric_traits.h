/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#pragma once

namespace lean {
/**
   \brief Template specializations define traits for native and lean
   numeric types.
*/
template<typename T>
class numeric_traits {
};

void set_processor_rounding(bool plus_inf);
}
