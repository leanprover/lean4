/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "frontends/smt2/init_module.h"
#include "frontends/smt2/scanner.h"
#include "frontends/smt2/elaborator.h"
#include "frontends/smt2/parser.h"

namespace lean {

void initialize_frontend_smt2_module() {
    smt2::initialize_scanner();
    smt2::initialize_elaborator();
    smt2::initialize_parser();
}

void finalize_frontend_smt2_module() {
    smt2::finalize_parser();
    smt2::finalize_elaborator();
    smt2::finalize_scanner();
}

}
