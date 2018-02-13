/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/abstract_context_cache.h"

namespace lean {
/** \brief Eta-expand constructor/projection applications, I.rec and I.cases_on applications,
    the minor premises of I.rec and I.cases_on applications, I.no_confusion applications,
    quotient type constructor and lift applications, and subtype.elt_of applications. */
expr eta_expand(environment const & env, abstract_context_cache & cache, expr const & e);
}
