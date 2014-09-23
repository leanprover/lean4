/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
namespace lean {
/**
    \brief Return true iff \c c is a "safe" ASCII characters.
    It is a "keyboard" character.
*/
bool is_safe_ascii(char c);
/**
    \brief Return true iff the given string contains only "safe"
    ASCII character.
*/
bool is_safe_ascii(char const * str);

void initialize_ascii();
void finalize_ascii();
}
