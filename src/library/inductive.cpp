/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/environment.h"
#include "library/inductive.h"

namespace lean {

bool is_inductive(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

list<name> get_intro_rule_names(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

optional<name> is_intro_rule_name(environment const & env, name const & ir_name) {
    throw exception("TODO(dhs): implement");
}

/* For basic inductive types, we can prove this lemma using <ind_name>.no_confusion.

   For non-basic inductive types, we first create a function <ind_name>.cidx that maps
   each element of \e ind_type to a natural number depending only on its constructor.
   We then prove the lemma <tt>forall c1 c2, cidx c1 != cidx c2 -> c1 != c2</tt> and
   use it to prove the desired theorem.
*/
expr prove_intro_rules_disjoint(environment const & env, name const & ir_name1, name const & ir_name2) {
    throw exception("TODO(dhs): implement");
}

unsigned get_inductive_num_params(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

void initialize_library_inductive() {}
void finalize_library_inductive() {}

}
