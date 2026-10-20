/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <string>
#include "runtime/optional.h"
#include "lean/lean.h"

namespace lean {
LEAN_EXPORT unsigned get_utf8_size(unsigned char c);
/* Return the length of the string `str` encoded using UTF8.
   `str` may contain null characters. */
LEAN_EXPORT size_t utf8_strlen(char const * str, size_t sz);

/* If `c` is the first byte of an utf-8 encoded unicode scalar value,
   then return `some(n)` where `n` is the number of bytes needed to encode
   the unicode scalar value. Otherwise, return `none` */
LEAN_EXPORT optional<unsigned> get_utf8_first_byte_opt(unsigned char c);

/* "Read" next unicode character starting at position i in a string using UTF-8 encoding.
   Return the unicode character and update i. */
LEAN_EXPORT unsigned next_utf8(std::string const & str, size_t & i);
LEAN_EXPORT unsigned next_utf8(char const * str, size_t size, size_t & i);

/* Decode a UTF-8 encoded string `str` into unicode scalar values */
LEAN_EXPORT void utf8_decode(std::string const & str, std::vector<unsigned> & out);

/* Returns true if the given character is valid UTF-8 */
LEAN_EXPORT bool validate_utf8_one(uint8_t const * str, size_t size, size_t & pos);

/* Returns true if the provided string is valid UTF-8 */
LEAN_EXPORT bool validate_utf8(uint8_t const * str, size_t size, size_t & pos, size_t & i);

/* Push a unicode scalar value into a utf-8 encoded string */
LEAN_EXPORT void push_unicode_scalar(std::string & s, unsigned code);

/* Store unicode scalar value at `d`, `d` must point to memory with enough space to store `c`.
   Return the number of bytes consumed. */
LEAN_EXPORT unsigned push_unicode_scalar(char * d, unsigned code);
}
