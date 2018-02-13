/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/abstract_context_cache.h"
#include "library/compiler/procedure.h"
namespace lean {

/* \brief Remove constructor/projection/cases_on applications of trivial structures.

   We say a structure is trivial if it has only constructor and
   the constructor has only one relevant field.
   In this case, we use a simple optimization where we represent elements of this inductive
   datatype as the only relevant element. */
void erase_trivial_structures(environment const & env, abstract_context_cache & cache, buffer<procedure> & procs);

/** \brief Replaces cases_on, projections and constructor applications with _cases.idx, _proj.idx and _cnstr.idx
    It also removes irrelevant fields from constructors.
    \remark nat.cases_on, nat.succ and nat.zero are ignored. */
void simp_inductive(environment const & env, abstract_context_cache & cache, buffer<procedure> & procs);

/** \brief Return non-none idx iff \c e is of the form _cnstr.idx */
optional<unsigned> is_internal_cnstr(expr const & e);
/** \brief Return non-none idx iff \c e is of the form _proj.idx */
optional<unsigned> is_internal_proj(expr const & e);
/** \brief Return non-none n iff \c e is of the form _cases.n */
optional<unsigned> is_internal_cases(expr const & e);

/** \brief Return true iff 'e' is an internal cases, a nat.cases_on,
    or a VM builtin cases. That is, it returns true for constants
    that produce branching during code generation. */
bool is_vm_supported_cases(environment const & env, expr const & e);

/** \brief Return the number of minor premises for a vm supported cases construct. */
unsigned get_vm_supported_cases_num_minors(environment const & env, expr const & fn);

void initialize_simp_inductive();
void finalize_simp_inductive();
}
