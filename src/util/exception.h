/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/lua.h"
#include <exception>
#include <string>
#include <memory>

namespace lean {
class sstream;
/** \brief Base class for all Lean exceptions */
class throwable : public std::exception {
protected:
    std::string m_msg;
    throwable() {}
public:
    throwable(char const * msg);
    throwable(std::string const & msg);
    throwable(sstream const & strm);
    virtual ~throwable() noexcept;
    virtual char const * what() const noexcept;
    virtual throwable * clone() const { return new throwable(m_msg); }
    virtual void rethrow() const { throw *this; }
};

/** \brief Base class for all Lean "logical" exceptions, that is, exceptions not related
    to resource constraints, and runtime errors */
class exception : public throwable {
protected:
    exception() {}
public:
    exception(char const * msg):throwable(msg) {}
    exception(std::string const & msg):throwable(msg) {}
    exception(sstream const & strm):throwable(strm) {}
    virtual throwable * clone() const { return new exception(m_msg); }
    virtual void rethrow() const { throw *this; }
};

/** \brief Exception produced by a Lean parser. */
class parser_exception : public exception {
protected:
    std::string m_fname;
    unsigned    m_line;
    unsigned    m_pos;
public:
    parser_exception(char const * msg, char const * fname, unsigned l, unsigned p);
    parser_exception(std::string const & msg, char const * fname, unsigned l, unsigned p);
    parser_exception(sstream const & strm, char const * fname, unsigned l, unsigned p);
    virtual ~parser_exception() noexcept;
    virtual char const * what() const noexcept;
    unsigned get_line() const { return m_line; }
    unsigned get_pos() const { return m_pos; }
    std::string const & get_file_name() const { return m_fname; }
    virtual throwable * clone() const { return new parser_exception(m_msg, m_fname.c_str(), m_line, m_pos); }
    virtual void rethrow() const { throw *this; }
    parser_exception update_line(unsigned line_delta) const { return parser_exception(m_msg, m_fname.c_str(), m_line + line_delta, m_pos); }
};

/** \brief Exception used to sign that a computation was interrupted */
class interrupted : public throwable {
public:
    interrupted() {}
    virtual ~interrupted() noexcept {}
    virtual char const * what() const noexcept { return "interrupted"; }
    virtual throwable * clone() const { return new interrupted(); }
    virtual void rethrow() const { throw *this; }
};

class stack_space_exception : public throwable {
    std::string m_component_name;
public:
    stack_space_exception(char const * component_name):m_component_name(component_name) {}
    virtual char const * what() const noexcept;
    virtual throwable * clone() const { return new stack_space_exception(m_component_name.c_str()); }
    virtual void rethrow() const { throw *this; }
};

class memory_exception : public throwable {
    std::string m_component_name;
public:
    memory_exception(char const * component_name):m_component_name(component_name) {}
    virtual char const * what() const noexcept;
    virtual throwable * clone() const { return new memory_exception(m_component_name.c_str()); }
    virtual void rethrow() const { throw *this; }
};

int push_exception(lua_State * L, throwable const & e);
throwable const & to_exception(lua_State * L, int i);
bool is_exception(lua_State * L, int i);
void open_exception(lua_State * L);
}
