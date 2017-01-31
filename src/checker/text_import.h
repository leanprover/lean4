/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <iostream>
#include <unordered_map>
#include <string>
#include "kernel/environment.h"

namespace lean {

enum class lowlevel_notation_kind {
    Prefix, Postfix, Infix,
};
struct lowlevel_notation_info {
    lowlevel_notation_kind m_kind;
    std::string m_token;
    unsigned m_prec;
};

using lowlevel_notations = std::unordered_map<name, lowlevel_notation_info, name_hash>;

void import_from_text(std::istream & in, environment & env, lowlevel_notations & notations);

}
