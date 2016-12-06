/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include <string>
#include <stdexcept>

namespace lean {

class dynamic_linking_exception : public std::runtime_error {
public:
    dynamic_linking_exception(std::string msg) : std::runtime_error(msg) {}
};

typedef void* dynamic_symbol;

class dynamic_library {
    std::string m_name;
    std::string m_path;
    void * m_handle;
public:
    dynamic_library(std::string library_path);
    ~dynamic_library();
    dynamic_symbol symbol(std::string name);
};

}
