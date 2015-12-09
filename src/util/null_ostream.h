/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>

#define LEAN_NULL_AUX_BUFFER_SIZE 64

namespace lean {
class null_streambuf : public std::streambuf {
    char                m_buffer[LEAN_NULL_AUX_BUFFER_SIZE];
protected:
    virtual int overflow(int c) override;
};

class null_ostream : public std::ostream {
public:
    null_streambuf * rdbuf() const;
};
}
