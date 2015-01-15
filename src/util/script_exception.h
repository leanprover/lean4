/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <memory>
#include "util/exception.h"

namespace lean {
/**
   \brief Exception for wrapping errors produced by the Lua engine.
*/
class script_exception : public exception {
public:
    enum class source { String, File, Unknown };
protected:
    source      m_source;
    std::string m_file;   // if source == File, then this field contains the filename that triggered the error.
    unsigned    m_line;   // line number
    script_exception(source s, std::string f, unsigned l, std::string const & msg):exception(msg), m_source(s), m_file(f), m_line(l) {}
public:
    script_exception(char const * lua_error);
    virtual ~script_exception();
    virtual char const * what() const noexcept;
    virtual source get_source() const { return m_source; }
    virtual char const * get_file_name() const;
    virtual unsigned get_line() const;
    /** \brief Return error message without position information */
    virtual char const * get_msg() const noexcept;
    virtual throwable * clone() const { return new script_exception(m_source, m_file, m_line, m_msg); }
    virtual void rethrow() const { throw *this; }
};

/**
   \brief Lean exception occurred inside of a script
*/
class script_nested_exception : public script_exception {
    std::shared_ptr<throwable> m_exception;
    script_nested_exception(source s, std::string f, unsigned l, std::shared_ptr<throwable> const & ex);
public:
    script_nested_exception(bool file, std::string f, unsigned l, std::shared_ptr<throwable> const & ex):script_nested_exception(file ? source::File : source::String, f, l, ex) {}
    virtual ~script_nested_exception();
    virtual char const * what() const noexcept;
    virtual throwable * clone() const { return new script_nested_exception(m_source, m_file, m_line, m_exception); }
    virtual void rethrow() const { throw *this; }
    throwable const & get_exception() const { return *(m_exception.get()); }
};
}
