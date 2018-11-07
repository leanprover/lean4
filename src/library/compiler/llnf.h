/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/* Convert expression to Low Level Normal Form (LLNF). This is the last normal form
   before converting to the IR. */
expr to_llnf(environment const & env, expr const & e, bool unboxed_data = false);

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

inline bool is_llnf_cnstr(expr const & e) { unsigned d1, d2, d3; return is_llnf_cnstr(e, d1, d2, d3); }
inline bool is_llnf_reuse(expr const & e) { unsigned d1, d2, d3; return is_llnf_reuse(e, d1, d2, d3); }
inline bool is_llnf_reset(expr const & e) { unsigned i; return is_llnf_reset(e, i); }
inline bool is_llnf_proj(expr const & e) { unsigned d; return is_llnf_proj(e, d); }
inline bool is_llnf_sproj(expr const & e) { unsigned d1, d2, d3; return is_llnf_sproj(e, d1, d2, d3); }
inline bool is_llnf_uproj(expr const & e) { unsigned d; return is_llnf_uproj(e, d); }
inline bool is_llnf_sset(expr const & e) { unsigned d1, d2, d3; return is_llnf_sset(e, d1, d2, d3); }
inline bool is_llnf_uset(expr const & e) { unsigned d; return is_llnf_uset(e, d); }

void initialize_llnf();
void finalize_llnf();
}
