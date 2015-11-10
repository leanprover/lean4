/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"

namespace lean {
namespace blast {
unsigned get_blast_max_depth(options const & o);
unsigned get_blast_init_depth(options const & o);
unsigned get_blast_inc_depth(options const & o);
void initialize_options();
void finalize_options();
}}
