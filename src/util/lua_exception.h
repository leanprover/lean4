/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/exception.h"
#include "util/script_exception.h"

namespace lean {
/**
   \brief Exception for wrapping errors produced by the Lua engine.
*/
class lua_exception : public script_exception {
private:
    source      m_source;
    std::string m_file;   // if source == File, then this field contains the filename that triggered the error.
    unsigned    m_line;   // line number
public:
    lua_exception(char const * lua_error);
    virtual ~lua_exception();
    virtual source get_source() const { return m_source; }
    virtual char const * get_filename() const;
    virtual unsigned get_line() const;
    /** \brief Return error message without position information */
    virtual char const * get_msg() const noexcept;
};
}
