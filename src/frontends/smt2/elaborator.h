/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/type_context.h"

namespace lean {
namespace smt2 {

name mk_user_name(std::string const & s);
expr elaborate_constant(std::string const & symbol);
expr elaborate_app(type_context & tctx, buffer<expr> & args);

void initialize_elaborator();
void finalize_elaborator();

}}
