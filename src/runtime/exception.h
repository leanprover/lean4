/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
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
};

/** \brief Exception used to sign that a computation was interrupted */
class interrupted {
public:
    interrupted() {}
    virtual ~interrupted() noexcept {}
    virtual char const * what() const noexcept { return "interrupted"; }
};

class stack_space_exception : public throwable {
    std::string m_msg;
    stack_space_exception(std::string const & msg):m_msg(msg) {}
public:
    stack_space_exception(char const * component_name);
    virtual char const * what() const noexcept { return m_msg.c_str(); }
};

class memory_exception : public throwable {
    std::string m_msg;
    memory_exception(std::string const & msg):m_msg(msg) {}
public:
    memory_exception(char const * component_name);
    virtual char const * what() const noexcept { return m_msg.c_str(); }
};

class heartbeat_exception : public throwable {
public:
    heartbeat_exception() {}
    virtual char const * what() const noexcept;
};
}
