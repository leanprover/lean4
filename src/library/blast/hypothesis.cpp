/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/hypothesis.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {
bool hypothesis::depends_on(expr const & h) const { return m_deps.contains(href_index(h)); }
bool hypothesis::is_assumption() const { return !m_value || is_local_non_href(*m_value); }
}}
