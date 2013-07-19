/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <exception>
#include <string>

namespace lean {

class exception : public std::exception {
    std::string m_msg;
public:
    exception(char const * msg);
    exception(std::string const & msg);
    exception(exception const & ex);
    virtual ~exception() noexcept;
    virtual char const * what() const noexcept;
};

}
