/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/simp_lemmas.h"

namespace lean {
environment add_eqn_lemma(environment const & env, name const & eqn_lemma);
bool has_eqn_lemmas(environment const & env, name const & cname);
void get_eqn_lemmas_for(environment const & env, name const & cname, bool refl_only, buffer<simp_lemma> & result);
void initialize_eqn_lemmas();
void finalize_eqn_lemmas();
}
