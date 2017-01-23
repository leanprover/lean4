/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include <string>
#include "util/exception.h"

namespace lean {

class dynamic_linking_exception : public exception {
public:
    dynamic_linking_exception(std::string msg): exception(msg) {}
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
