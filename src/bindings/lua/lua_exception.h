/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/exception.h"

namespace lean {
/**
   \brief Exception for wrapping errors produced by the Lua engine.
*/
class lua_exception : public exception {
public:
    enum class source { String, File, Unknown };
private:
    source      m_source;
    std::string m_file;   // if source == File, then this field contains the filename that triggered the error.
    unsigned    m_line;   // line number
public:
    lua_exception(char const * lua_error);
    source get_source() const { return m_source; }
    char const * get_filename() const;
    unsigned get_line() const;
    /** \brief Return error message without position information */
    char const * msg() const noexcept;
    virtual char const * what() const noexcept;
};
}
