/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
namespace lean {
/** \brief Helper class for creating an auxiliary lean file and locking it.
    We use this object to prevent a lean process from reading a .olean (.ilean/.clean)
    file while another one is writing. */
class file_lock {
    std::string m_fname;
    int m_fd;
public:
    file_lock(char const * fname, bool exclusive);
    file_lock(std::string const & fname, bool exclusive):file_lock(fname.c_str(), exclusive) {}
    ~file_lock();
};

class exclusive_file_lock : public file_lock {
public:
    exclusive_file_lock(char const * fname):file_lock(fname, true) {}
    exclusive_file_lock(std::string const & fname):file_lock(fname, true) {}
};

class shared_file_lock : public file_lock {
public:
    shared_file_lock(char const * fname):file_lock(fname, false) {}
    shared_file_lock(std::string const & fname):file_lock(fname, false) {}
};
}
