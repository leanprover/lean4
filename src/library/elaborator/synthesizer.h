/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "util/lazy_list.h"
#include "kernel/environment.h"
#include "kernel/context.h"
#include "library/elaborator/elaborator_exception.h"

namespace lean {
/**
   \brief A synthesizer generates a sequence of expressions of a given type.
*/
class synthesizer {
public:
    virtual ~synthesizer() {}

    /**
       \brief Return a sequence of expressions
       of type \c type in the given environment and context.
    */
    virtual lazy_list<expr> operator()(environment const & env, context const & ctx, expr const & type) = 0;
};
}
