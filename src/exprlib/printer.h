/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include "expr.h"
#include "context.h"

namespace lean {
std::ostream & operator<<(std::ostream & out, context const & ctx);
std::ostream & operator<<(std::ostream & out, expr const & e);
std::ostream & operator<<(std::ostream & out, std::pair<expr const &, context const &> const & p);
class environment;
std::ostream & operator<<(std::ostream & out, environment const & env);
}
