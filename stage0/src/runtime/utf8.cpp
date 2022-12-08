/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstdlib>
#include <string>
#include "runtime/debug.h"
#include "runtime/optional.h"
#include "runtime/utf8.h"

namespace lean {
bool is_utf8_next(unsigned char c) { return (c & 0xC0) == 0x80; }

unsigned get_utf8_size(unsigned char c) {
    if ((c & 0x80) == 0)
        return 1;
    else if ((c & 0xE0) == 0xC0)
        return 2;
    else if ((c & 0xF0) == 0xE0)
        return 3;
    else if ((c & 0xF8) == 0xF0)
        return 4;
    else if ((c & 0xFC) == 0xF8)
        return 5;
    else if ((c & 0xFE) == 0xFC)
        return 6;
    else if (c == 0xFF)
        return 1;
    else
        return 1; /* invalid */
}

extern "C" LEAN_EXPORT size_t lean_utf8_strlen(char const * str) {
    size_t r = 0;
    while (*str != 0) {
        unsigned sz = get_utf8_size(*str);
        r++;
        str += sz;
    }
    return r;
}

size_t utf8_strlen(char const * str) {
    return lean_utf8_strlen(str);
}

extern "C" LEAN_EXPORT size_t lean_utf8_n_strlen(char const * str, size_t sz) {
    size_t r = 0;
    size_t i = 0;
    while (i < sz) {
        unsigned d = get_utf8_size(str[i]);
        r++;
        i += d;
    }
    return r;
}

size_t utf8_strlen(char const * str, size_t sz) {
    return lean_utf8_n_strlen(str, sz);
}

size_t utf8_strlen(std::string const & str) {
    return utf8_strlen(str.data(), str.size());
}

optional<size_t> utf8_char_pos(char const * str, size_t char_idx) {
    size_t r = 0;
    while (*str != 0) {
        if (char_idx == 0)
            return some<size_t>(r);
        char_idx--;
        unsigned sz = get_utf8_size(*str);
        r += sz;
        str += sz;
    }
    return optional<size_t>();
}

char const * get_utf8_last_char(char const * str) {
    char const * r;
    lean_assert(*str != 0);
    do {
        r = str;
        unsigned sz = get_utf8_size(*str);
        str += sz;
    } while (*str != 0);
    return r;
}

std::string utf8_trim(std::string const & s) {
    int start = -1, stop = -1;
    for (unsigned i = 0; i < s.size(); i += get_utf8_size(s[i])) {
        if (s[i] == ' ') {
            if (stop == -1)
                stop = i;
        } else {
            if (start == -1)
                start = i;
            stop = -1;
        }
    }
    if (stop == -1)
        stop = s.size();
    return s.substr(start, stop - start);
}

unsigned utf8_to_unicode(uchar const * begin, uchar const * end) {
    unsigned result = 0;
    if (begin == end)
        return result;
    auto it = begin;
    unsigned c = *it;
    ++it;
    if (c < 128)
        return c;
    unsigned mask     = (1u << 6) -1;
    unsigned hmask    = mask;
    unsigned shift    = 0;
    unsigned num_bits = 0;
    while ((c & 0xC0) == 0xC0) {
        c <<= 1;
        c &= 0xff;
        num_bits += 6;
        hmask >>= 1;
        shift++;
        result <<= 6;
        if (it == end)
            return 0;
        result |= *it & mask;
        ++it;
    }
    result |= ((c >> shift) & hmask) << num_bits;
    return result;
}

/*
Table 3-6. UTF-8 Bit Distribution
Scalar Value               | First Byte | Second Byte | Third Byte | Fourth Byte
00000000 0xxxxxxx          | 0xxxxxxx   |             |            |
00000yyy yyxxxxxx          | 110yyyyy   | 10xxxxxx    |            |
zzzzyyyy yyxxxxxx          | 1110zzzz   | 10yyyyyy    | 10xxxxxx   |
000uuuuu zzzzyyyy yyxxxxxx | 11110uuu   | 10uuzzzz    | 10yyyyyy   | 10xxxxxx
*/

optional<unsigned> get_utf8_first_byte_opt(unsigned char c) {
    if ((c & 0x80) == 0) {
        /* 0xxxxxxx */
        return optional<unsigned>(1);
    } else if ((c & 0xe0) == 0xc0) {
        /* 110yyyyy */
        return optional<unsigned>(2);
    } else if ((c & 0xf0) == 0xe0) {
        /* 1110zzzz */
        return optional<unsigned>(3);
    } else if ((c & 0xf8) == 0xf0) {
        /* 11110uuu */
        return optional<unsigned>(4);
    } else {
        return optional<unsigned>();
    }
}

unsigned next_utf8(char const * str, size_t size, size_t & i) {
    unsigned c = static_cast<unsigned char>(str[i]);
    /* zero continuation (0 to 127) */
    if ((c & 0x80) == 0) {
        i++;
        return c;
    }

    /* one continuation (128 to 2047) */
    if ((c & 0xe0) == 0xc0 && i + 1 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        unsigned r = ((c & 0x1f) << 6) | (c1 & 0x3f);
        if (r >= 128) {
            i += 2;
            return r;
        }
    }

    /* two continuations (2048 to 55295 and 57344 to 65535) */
    if ((c & 0xf0) == 0xe0 && i + 2 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        unsigned c2 = static_cast<unsigned char>(str[i+2]);
        unsigned r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
        if (r >= 2048 && (r < 55296 || r > 57343)) {
            i += 3;
            return r;
        }
    }

    /* three continuations (65536 to 1114111) */
    if ((c & 0xf8) == 0xf0 && i + 3 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i+1]);
        unsigned c2 = static_cast<unsigned char>(str[i+2]);
        unsigned c3 = static_cast<unsigned char>(str[i+3]);
        unsigned r  = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
        if (r >= 65536 && r <= 1114111) {
            i += 4;
            return r;
        }
    }

    /* invalid UTF-8 encoded string */
    i++;
    return c;
}


unsigned next_utf8(std::string const & str, size_t & i) {
    return next_utf8(str.data(), str.size(), i);
}

void utf8_decode(std::string const & str, std::vector<unsigned> & out) {
    size_t i = 0;
    while (i < str.size()) {
        out.push_back(next_utf8(str, i));
    }
}

#define TAG_CONT    static_cast<unsigned char>(0b10000000)
#define TAG_TWO_B   static_cast<unsigned char>(0b11000000)
#define TAG_THREE_B static_cast<unsigned char>(0b11100000)
#define TAG_FOUR_B  static_cast<unsigned char>(0b11110000)
#define MAX_ONE_B   0x80
#define MAX_TWO_B   0x800
#define MAX_THREE_B 0x10000

template<typename T>
class push_back_trait {};

template<> class push_back_trait<char*> {
public:
    static void push(char * & s, unsigned char c) { *s = c; ++s; }
};

template<> class push_back_trait<std::string> {
public:
    static void push(std::string & s, unsigned char c) { s.push_back(c); }
};

template<typename T>
unsigned push_unicode_scalar_core(T & d, unsigned code) {
    if (code < MAX_ONE_B) {
        push_back_trait<T>::push(d, static_cast<unsigned char>(code));
        return 1;
    } else if (code < MAX_TWO_B) {
        push_back_trait<T>::push(d, static_cast<unsigned char>(code >> 6 & 0x1F) | TAG_TWO_B);
        push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | TAG_CONT);
        return 2;
    } else if (code < MAX_THREE_B) {
        push_back_trait<T>::push(d, static_cast<unsigned char>(code >> 12 & 0x0F) | TAG_THREE_B);
        push_back_trait<T>::push(d, static_cast<unsigned char>(code >>  6 & 0x3F) | TAG_CONT);
        push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | TAG_CONT);
        return 3;
    } else {
        push_back_trait<T>::push(d, static_cast<unsigned char>(code >> 18 & 0x07) | TAG_FOUR_B);
        push_back_trait<T>::push(d, static_cast<unsigned char>(code >> 12 & 0x3F) | TAG_CONT);
        push_back_trait<T>::push(d, static_cast<unsigned char>(code >>  6 & 0x3F) | TAG_CONT);
        push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | TAG_CONT);
        return 4;
    }
}

unsigned push_unicode_scalar(char * d, unsigned code) {
    return push_unicode_scalar_core<char*>(d, code);
}

void push_unicode_scalar(std::string & s, unsigned code) {
    push_unicode_scalar_core(s, code);
}
}
