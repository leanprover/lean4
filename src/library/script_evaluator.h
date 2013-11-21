/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"

namespace lean {
class environment;
class io_state;
/**
   \brief Abstract base class for script code evaluators.
   These evaluators are used to execute user-supplied code embedded in frontend files (.e.g., .lean, .smt2, etc).
   In the current implementation we only have one implementation of this class based on the Lua programming language. So, the main purpose of this class is to organize the dependencies between modules.
*/
class script_evaluator {
public:
    virtual ~script_evaluator() {}
    virtual void dostring(char const * str) = 0;
    virtual void dostring(char const * str, environment & env, io_state & st) = 0;
};

/**
   \brief Base class for exceptions producing when evaluating scripts.
*/
class script_exception : public exception {
public:
    enum class source { String, File, Unknown };
    virtual source get_source() const = 0;
    virtual char const * get_filename() const = 0;
    virtual unsigned get_line() const = 0;
    virtual char const * get_msg() const noexcept = 0;
    virtual char const * what() const noexcept;
};
}
