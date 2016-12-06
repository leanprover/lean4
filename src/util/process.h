/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once

#include <iostream>
#include <string>
#include "util/buffer.h"

namespace lean  {

class process {
    std::string m_proc_name;
    buffer<std::string> m_args;
public:
    process(std::string exe_name);
    process & arg(std::string arg_str);
    void run();
};
}
