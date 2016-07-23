/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include <string>
#include <utility>
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/io_state_stream.h"

namespace lean {
namespace smt2 {

bool parse_commands(environment & env, io_state & ios, char const * fname);

void initialize_parser();
void finalize_parser();

}}
