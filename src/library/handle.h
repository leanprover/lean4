/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author:  Leonardo de Moura & Jared Roesch
*/
#pragma once

#include <string>
#include <stdio.h>
#include "util/buffer.h"
#include "library/pipe.h"

namespace lean {

class handle_exception : exception {
public:
    handle_exception(std::string msg) : exception(msg) {}
};

class handle {
public:
    FILE * m_file;
    handle(FILE * file_desc):m_file(file_desc) {}

    void close();

    ~handle();

    void write(buffer<char> & data);
    void flush();

    bool is_stdin();
    bool is_stdout();
    bool is_stderr();
    bool is_closed();
};

typedef std::shared_ptr<handle> handle_ref;

}
