/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"

namespace lean {
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
