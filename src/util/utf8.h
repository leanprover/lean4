/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/optional.h"

namespace lean {
using uchar = unsigned char;

bool is_utf8_next(unsigned char c);
unsigned get_utf8_size(unsigned char c);
size_t utf8_strlen(char const * str);
optional<size_t> utf8_char_pos(char const * str, size_t char_idx);
char const * get_utf8_last_char(char const * str);
std::string utf8_trim(std::string const & s);
unsigned utf8_to_unicode(uchar const * begin, uchar const * end);
inline unsigned utf8_to_unicode(char const * begin, char const * end) {
    return utf8_to_unicode(reinterpret_cast<uchar const *>(begin),
                           reinterpret_cast<uchar const *>(end));
}
}
