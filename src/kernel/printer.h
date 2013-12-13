/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <utility>
#include "kernel/expr.h"
#include "kernel/context.h"

namespace lean {
class ro_environment;
std::ostream & operator<<(std::ostream & out, context const & ctx);
std::ostream & operator<<(std::ostream & out, expr const & e);
std::ostream & operator<<(std::ostream & out, std::pair<expr const &, context const &> const & p);
class object;
std::ostream & operator<<(std::ostream & out, object const & obj);
std::ostream & operator<<(std::ostream & out, ro_environment const & env);
}
void print(lean::expr const & a);
void print(lean::expr const & a, lean::context const & c);
void print(lean::context const & c);
void print(lean::ro_environment const & e);
