/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
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

    /** \brief The synthesizer produces a "result" object that can generates the sequence of possible solutions. */
    class result {
    public:
        virtual ~result() {}
        /** \brief Return the next possible solution. An elaborator_exception is throw in case of failure. */
        virtual expr next() = 0;
        /** \brief Interrupt the computation for the next solution. */
        virtual void interrupt() = 0;
    };

    /**
       \brief Return an object for computing a sequence of expressions
       of type \c type in the given environment and context.
    */
    virtual std::unique_ptr<result> operator()(environment const & env, context const & ctx, expr const & type) = 0;
};
}
