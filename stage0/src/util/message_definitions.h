/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <utility>
#include <string>
#include "runtime/int.h"
#include "util/name.h"

namespace lean {

typedef pair<unsigned, unsigned> pos_info; //!< Line and column information

struct pos_range {
    pos_info m_begin, m_end;
};

struct location {
    std::string m_file_name;
    pos_range m_range;
};

}
