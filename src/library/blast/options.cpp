/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"

#ifndef LEAN_DEFAULT_BLAST_MAX_DEPTH
#define LEAN_DEFAULT_BLAST_MAX_DEPTH 128
#endif
#ifndef LEAN_DEFAULT_BLAST_INIT_DEPTH
#define LEAN_DEFAULT_BLAST_INIT_DEPTH 1
#endif
#ifndef LEAN_DEFAULT_BLAST_INC_DEPTH
#define LEAN_DEFAULT_BLAST_INC_DEPTH 5
#endif

namespace lean {
namespace blast {
/* Options */
static name * g_blast_max_depth    = nullptr;
static name * g_blast_init_depth   = nullptr;
static name * g_blast_inc_depth    = nullptr;

unsigned get_blast_max_depth(options const & o) {
    return o.get_unsigned(*g_blast_max_depth, LEAN_DEFAULT_BLAST_MAX_DEPTH);
}
unsigned get_blast_init_depth(options const & o) {
    return o.get_unsigned(*g_blast_init_depth, LEAN_DEFAULT_BLAST_INIT_DEPTH);
}
unsigned get_blast_inc_depth(options const & o) {
    return o.get_unsigned(*g_blast_inc_depth, LEAN_DEFAULT_BLAST_INC_DEPTH);
}

void initialize_options() {
    g_blast_max_depth  = new name{"blast", "max_depth"};
    g_blast_init_depth = new name{"blast", "init_depth"};
    g_blast_inc_depth  = new name{"blast", "inc_depth"};

    register_unsigned_option(*blast::g_blast_max_depth, LEAN_DEFAULT_BLAST_MAX_DEPTH,
                             "(blast) max search depth for blast");
    register_unsigned_option(*blast::g_blast_init_depth, LEAN_DEFAULT_BLAST_INIT_DEPTH,
                             "(blast) initial search depth for blast (remark: blast uses iteration deepening)");
    register_unsigned_option(*blast::g_blast_inc_depth, LEAN_DEFAULT_BLAST_INC_DEPTH,
                             "(blast) search depth increment for blast (remark: blast uses iteration deepening)");
}
void finalize_options() {
    delete g_blast_max_depth;
    delete g_blast_init_depth;
    delete g_blast_inc_depth;
}
}}
