/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/compiler/util.h"

namespace lean {
/* Convert expression to Low Level Normal Form (LLNF). This is the last normal form
   before converting to the IR. */
pair<environment, comp_decls> to_llnf(environment const & env, comp_decls const & ds, bool unboxed_data = false);

optional<pair<environment, comp_decl>> mk_boxed_version(environment env, name const & fn, unsigned arity);

bool is_llnf_apply(expr const & e);
bool is_llnf_closure(expr const & e);
bool is_llnf_cnstr(expr const & e, unsigned & cidx, unsigned & nusize, unsigned & ssz);
bool is_llnf_reuse(expr const & e, unsigned & cidx, unsigned & nusize, unsigned & ssz);
bool is_llnf_reset(expr const & e, unsigned & n);
bool is_llnf_proj(expr const & e, unsigned & idx);
bool is_llnf_sproj(expr const & e, unsigned & sz, unsigned & n, unsigned & offset);
bool is_llnf_uproj(expr const & e, unsigned & idx);
bool is_llnf_sset(expr const & e, unsigned & sz, unsigned & n, unsigned & offset);
bool is_llnf_uset(expr const & e, unsigned & n);
bool is_llnf_jmp(expr const & e);
bool is_llnf_unbox(expr const & e);
bool is_llnf_box(expr const & e, unsigned & n);
bool is_llnf_inc(expr const & e);
bool is_llnf_dec(expr const & e);

bool is_llnf_op(expr const & e);
inline bool is_llnf_cnstr(expr const & e) { unsigned d1, d2, d3; return is_llnf_cnstr(e, d1, d2, d3); }
inline bool is_llnf_reuse(expr const & e) { unsigned d1, d2, d3; return is_llnf_reuse(e, d1, d2, d3); }
inline bool is_llnf_reset(expr const & e) { unsigned i; return is_llnf_reset(e, i); }
inline bool is_llnf_proj(expr const & e) { unsigned d; return is_llnf_proj(e, d); }
inline bool is_llnf_sproj(expr const & e) { unsigned d1, d2, d3; return is_llnf_sproj(e, d1, d2, d3); }
inline bool is_llnf_uproj(expr const & e) { unsigned d; return is_llnf_uproj(e, d); }
inline bool is_llnf_sset(expr const & e) { unsigned d1, d2, d3; return is_llnf_sset(e, d1, d2, d3); }
inline bool is_llnf_uset(expr const & e) { unsigned d; return is_llnf_uset(e, d); }
inline bool is_llnf_box(expr const & e) { unsigned n; return is_llnf_box(e, n); }

expr get_constant_ll_type(environment const & env, name const & c);
unsigned get_llnf_arity(environment const & env, name const & c);

void initialize_llnf();
void finalize_llnf();
}
