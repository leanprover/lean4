/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Leonardo de Moura, Sebastian Ullrich
*/
#pragma once
#include <string>
#include <vector>
#include "kernel/environment.h"
#include "util/sexpr/options.h"
#include "frontends/lean/json.h"

namespace lean {

std::vector<json> get_completions(std::string const & pattern, environment const & env, options const & o);

}
