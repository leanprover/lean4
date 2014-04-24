/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
namespace lean {
/**
   \brief lifted Booleans
*/
enum lbool { l_false = -1, l_undef, l_true };
inline lbool operator~(lbool lb) { return static_cast<lbool>(-static_cast<int>(lb)); }
inline lbool to_lbool(bool b) { return static_cast<lbool>(static_cast<int>(b)*2-1); }
std::ostream & operator<<(std::ostream & out, lbool b);
}
