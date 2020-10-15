/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <utility>
#include <limits>
#include <lean/mpz.h>
#include "util/pair.h"
#include "util/name_map.h"
#include "util/name_set.h"
#include "util/options.h"
#include "util/format.h"
#include "kernel/environment.h"
#include "library/abstract_type_context.h"
#include "frontends/lean/token_table.h"

namespace lean {
formatter_factory mk_pretty_formatter_factory();
void initialize_pp();
void finalize_pp();
}
