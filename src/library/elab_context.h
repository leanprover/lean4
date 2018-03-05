/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_generator.h"
#include "kernel/environment.h"
#include "library/abstract_context_cache.h"
#include "library/metavar_context.h"

namespace lean {
/*
  The elaboration context contains the main data used to elaborate a Lean expression.
  This context is shared between different \c type_context objects.
  A \c type_context object is used to infer types; solve unification/matching constraints;
  perform type class resolution; and reduce terms. Each \c type_context object may
  use a different \c local_context (i.e., hypotheses).

  When we create a \c type_context object we just need to provide this \c elab_context
  object and a \c local_context.

  In the tactic framework, we define a subclass called \c tactic_context.
  It contains additional information such as the set of goals. The \c tactic_context
  is the preferred way to write tactics in C++.

  In the past, the \c type_context object would contain the information stored here.
  This decision created several problems when we needed to create multiple \c type_context
  objects with different local contexts and/or for solving different unification/matching
  constraints. The main benefits of the new design are:
  - Multiple \c type_context objects may share the same \c elab_context.
  - Faster \c type_context creation.
  - It allows us to provide a clean Lean API for using type_context objects directly.
*/
class elab_context {
protected:
    environment              m_env;
    metavar_context          m_mctx;
    name_generator           m_ngen;
    context_cacheless        m_dummy_cache;
    abstract_context_cache * m_cache;

    friend class type_context;     // TODO(Leo): delete after we have a cleaner API here
    friend class type_context_old; // TODO(Leo): delete after refactoring
public:
    elab_context(environment const & env, metavar_context const & mctx, name_generator const & ngen, abstract_context_cache * cache);
    elab_context(environment const & env, metavar_context const & mctx, name_generator const & ngen, options const & opts);
    elab_context(elab_context const &) = delete;
    elab_context(elab_context &&) = delete;
    ~elab_context() {}

    elab_context const & operator=(elab_context const &) = delete;
    elab_context const & operator=(elab_context &&) = delete;

    environment const & env() const { return m_env; }
    metavar_context & mctx() { return m_mctx; }
    abstract_context_cache & cache() { return *m_cache; }
    name next_name() { return m_ngen.next(); }
};
}
