/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "kernel/environment.h"
#include "checker/text_import.h"

namespace lean {

format compose_many(std::initializer_list<format> const & fmts);

format simple_pp(name const & n);
format simple_pp(environment const & env, expr const & e, lowlevel_notations const & notations);

}
