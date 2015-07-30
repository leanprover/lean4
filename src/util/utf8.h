/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
namespace lean {
bool is_utf8_next(unsigned char c);
unsigned get_utf8_size(unsigned char c);
size_t utf8_strlen(char const * str);
}
