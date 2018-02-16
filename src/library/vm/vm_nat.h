/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <limits>
#include "library/vm/vm.h"

namespace lean {
unsigned to_unsigned(vm_obj const & o);
optional<unsigned> try_to_unsigned(vm_obj const & o);
unsigned force_to_unsigned(vm_obj const & o, unsigned def = std::numeric_limits<unsigned>::max());
size_t force_to_size_t(vm_obj const & o, size_t def = std::numeric_limits<size_t>::max());

/* Auxiliary function for converting vm_obj representing numerals into mpz.
   This function is useful for writing new primitives.
   It avoids unnecessary mpz object allocation by using thread local storage.
   The result is a reference. The reference may be invalidated if `vm_nat_to_mpz1` is invoked again.
   We can avoid copying the reference to mpz object by using `vm_nat_to_mpz2`. */
mpz const & vm_nat_to_mpz1(vm_obj const & o);
/* See \c vm_nat_to_mpz1 */
mpz const & vm_nat_to_mpz2(vm_obj const & o);

void initialize_vm_nat();
void finalize_vm_nat();
}
