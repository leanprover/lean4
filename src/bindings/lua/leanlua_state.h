/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include <string>
#include "util/exception.h"

namespace lean {
/**
   \brief Wrapper for lua_State objects which contains all Lean bindings.
*/
class leanlua_state {
    struct imp;
    std::shared_ptr<imp> m_ptr;
public:
    leanlua_state();
    ~leanlua_state();

    /**
       \brief Execute the file with the given name.
       This method throws an exception if an error occurs.
    */
    void dofile(char const * fname);
    /**
       \brief Execute the given string.
       This method throws an exception if an error occurs.
    */
    void dostring(char const * str);
};

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
