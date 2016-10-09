/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/simp_lemmas.h"
#include "library/vm/vm.h"
namespace lean {
simp_lemmas const & to_simp_lemmas(vm_obj const & o);
vm_obj to_obj(simp_lemmas const & s);
void initialize_simp_lemmas_tactics();
void finalize_simp_lemmas_tactics();
}
