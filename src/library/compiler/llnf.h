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

bool is_llnf_cnstr(expr const & e, unsigned & cidx, unsigned & ssz);
bool is_llnf_reuse(expr const & e, unsigned & cidx, unsigned & ssz);
bool is_llnf_reset(expr const & e, unsigned & n);
bool is_llnf_proj(expr const & e, unsigned & idx);

inline bool is_llnf_cnstr(expr const & e) { unsigned d1, d2; return is_llnf_cnstr(e, d1, d2); }
inline bool is_llnf_reuse(expr const & e) { unsigned d1, d2; return is_llnf_reuse(e, d1, d2); }
inline bool is_llnf_reset(expr const & e) { unsigned i; return is_llnf_reset(e, i); }
inline bool is_llnf_proj(expr const & e) { unsigned d; return is_llnf_proj(e, d); }

void initialize_llnf();
void finalize_llnf();
}
