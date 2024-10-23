/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include "util/null_ostream.h"
namespace lean {
/**
    \brief Wrapper for std::ostream.
    The idea is to be able to have an output stream that can be
    "reassigned".

    std::unique_ptr<output_channel> out;
    out = new stdout_channel();
    (*out) << "writing to standard output";
    out = new stderr_channel();
    (*out) << "writing to standard input";
    out = new file_output_channel("file.txt");
    (*out) << "writing to file";
*/
class output_channel {
public:
    virtual ~output_channel() {}
    virtual std::ostream & get_stream() = 0;
};
class stdout_channel : public output_channel {
public:
    virtual std::ostream & get_stream() { return std::cout; }
};
class stderr_channel : public output_channel {
public:
    virtual std::ostream & get_stream() { return std::cerr; }
};
class file_output_channel : public output_channel {
    std::ofstream m_out;
public:
    file_output_channel(char const * fname):m_out(fname) {}
    virtual ~file_output_channel() {}
    virtual std::ostream & get_stream() { return m_out; }
};
class string_output_channel : public output_channel {
    std::ostringstream m_out;
public:
    string_output_channel() {}
    virtual ~string_output_channel() {}
    virtual std::ostream & get_stream() { return m_out; }
    std::string str() const { return m_out.str(); }
};
class null_output_channel : public output_channel {
    null_streambuf m_buffer;
    std::ostream   m_out;
public:
    null_output_channel():m_out(&m_buffer) {}
    virtual ~null_output_channel() {}
    virtual std::ostream & get_stream() { return m_out; }
};
template<typename T>
output_channel & operator<<(output_channel & out, T const & v) {
    out.get_stream() << v;
    return out;
}
}
