#include <lean/lean.h>

#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include "runtime/compact.h"
#include "runtime/object.h"
#include "runtime/utf8.h"

namespace lean {
namespace {
unsigned get_utf8_size_impl(unsigned char c) {
    if ((c & 0x80) == 0) return 1;
    if ((c & 0xE0) == 0xC0) return 2;
    if ((c & 0xF0) == 0xE0) return 3;
    if ((c & 0xF8) == 0xF0) return 4;
    return 1;
}

template <typename T>
class push_back_trait;

template <>
class push_back_trait<char *> {
public:
    static void push(char *& s, unsigned char c) {
        *s = static_cast<char>(c);
        ++s;
    }
};

template <>
class push_back_trait<std::string> {
public:
    static void push(std::string & s, unsigned char c) {
        s.push_back(static_cast<char>(c));
    }
};

template <typename T>
unsigned push_unicode_scalar_core(T & d, unsigned code) {
    constexpr unsigned char tag_cont = static_cast<unsigned char>(0b10000000);
    constexpr unsigned char tag_two_b = static_cast<unsigned char>(0b11000000);
    constexpr unsigned char tag_three_b = static_cast<unsigned char>(0b11100000);
    constexpr unsigned char tag_four_b = static_cast<unsigned char>(0b11110000);

    if (code < 0x80) {
        push_back_trait<T>::push(d, static_cast<unsigned char>(code));
        return 1;
    }
    if (code < 0x800) {
        push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 6) & 0x1F) | tag_two_b);
        push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | tag_cont);
        return 2;
    }
    if (code < 0x10000) {
        push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 12) & 0x0F) | tag_three_b);
        push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 6) & 0x3F) | tag_cont);
        push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | tag_cont);
        return 3;
    }

    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 18) & 0x07) | tag_four_b);
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 12) & 0x3F) | tag_cont);
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 6) & 0x3F) | tag_cont);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | tag_cont);
    return 4;
}
} // namespace

size_t utf8_strlen(char const * str) {
    size_t result = 0;
    while (*str != 0) {
        ++result;
        str += get_utf8_size_impl(static_cast<unsigned char>(*str));
    }
    return result;
}

size_t utf8_strlen(char const * str, size_t size) {
    size_t result = 0;
    size_t i = 0;
    while (i < size) {
        ++result;
        i += get_utf8_size_impl(static_cast<unsigned char>(str[i]));
    }
    return result;
}

size_t utf8_strlen(std::string const & str) {
    return utf8_strlen(str.data(), str.size());
}

optional<unsigned> get_utf8_first_byte_opt(unsigned char c) {
    if ((c & 0x80) == 0) return optional<unsigned>(1);
    if ((c & 0xE0) == 0xC0) return optional<unsigned>(2);
    if ((c & 0xF0) == 0xE0) return optional<unsigned>(3);
    if ((c & 0xF8) == 0xF0) return optional<unsigned>(4);
    return optional<unsigned>();
}

unsigned next_utf8(char const * str, size_t size, size_t & i) {
    unsigned c = static_cast<unsigned char>(str[i]);
    if ((c & 0x80) == 0) {
        ++i;
        return c;
    }
    if ((c & 0xE0) == 0xC0 && i + 1 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i + 1]);
        unsigned r = ((c & 0x1F) << 6) | (c1 & 0x3F);
        if (r >= 0x80) {
            i += 2;
            return r;
        }
    }
    if ((c & 0xF0) == 0xE0 && i + 2 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i + 1]);
        unsigned c2 = static_cast<unsigned char>(str[i + 2]);
        unsigned r = ((c & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
        if (r >= 0x800 && (r < 0xD800 || r > 0xDFFF)) {
            i += 3;
            return r;
        }
    }
    if ((c & 0xF8) == 0xF0 && i + 3 < size) {
        unsigned c1 = static_cast<unsigned char>(str[i + 1]);
        unsigned c2 = static_cast<unsigned char>(str[i + 2]);
        unsigned c3 = static_cast<unsigned char>(str[i + 3]);
        unsigned r = ((c & 0x07) << 18) | ((c1 & 0x3F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F);
        if (r >= 0x10000 && r <= 0x10FFFF) {
            i += 4;
            return r;
        }
    }
    ++i;
    return c;
}

unsigned next_utf8(std::string const & str, size_t & i) {
    return next_utf8(str.data(), str.size(), i);
}

void utf8_decode(std::string const & str, std::vector<unsigned> & out) {
    size_t i = 0;
    while (i < str.size()) out.push_back(next_utf8(str, i));
}

bool validate_utf8_one(uint8_t const * str, size_t size, size_t & pos) {
    size_t i = pos;
    unsigned c = str[i];
    if ((c & 0x80) == 0) {
        ++pos;
        return true;
    }
    if ((c & 0xE0) == 0xC0 && i + 1 < size) {
        unsigned c1 = str[i + 1];
        unsigned r = ((c & 0x1F) << 6) | (c1 & 0x3F);
        if ((c1 & 0xC0) == 0x80 && r >= 0x80) {
            pos += 2;
            return true;
        }
    }
    if ((c & 0xF0) == 0xE0 && i + 2 < size) {
        unsigned c1 = str[i + 1];
        unsigned c2 = str[i + 2];
        unsigned r = ((c & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
        if ((c1 & 0xC0) == 0x80 && (c2 & 0xC0) == 0x80 && r >= 0x800 && (r < 0xD800 || r > 0xDFFF)) {
            pos += 3;
            return true;
        }
    }
    if ((c & 0xF8) == 0xF0 && i + 3 < size) {
        unsigned c1 = str[i + 1];
        unsigned c2 = str[i + 2];
        unsigned c3 = str[i + 3];
        unsigned r = ((c & 0x07) << 18) | ((c1 & 0x3F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F);
        if ((c1 & 0xC0) == 0x80 && (c2 & 0xC0) == 0x80 && (c3 & 0xC0) == 0x80 && r >= 0x10000 && r <= 0x10FFFF) {
            pos += 4;
            return true;
        }
    }
    return false;
}

bool validate_utf8(uint8_t const * str, size_t size, size_t & pos, size_t & i) {
    pos = 0;
    i = 0;
    while (pos < size) {
        if (!validate_utf8_one(str, size, pos)) return false;
        ++i;
    }
    return true;
}

unsigned push_unicode_scalar(char * d, unsigned code) {
    return push_unicode_scalar_core<char *>(d, code);
}

void push_unicode_scalar(std::string & s, unsigned code) {
    push_unicode_scalar_core(s, code);
}
} // namespace

extern "C" void * mi_malloc_small(size_t size) noexcept {
    return std::malloc(size);
}

extern "C" size_t leanrt_test_mpz_object_size(void);
extern "C" size_t leanrt_test_mpz_value_offset(void);
extern "C" uint8_t leanrt_test_mpz_eq_cstr(lean_object * o, char const * value);
extern "C" uint8_t leanrt_test_int_eq_cstr(lean_object * o, char const * value);

extern "C" uint8_t leanrt_test_nat_eq_cstr(lean_object * o, char const * value) {
    lean_object * expected = lean_cstr_to_nat(value);
    bool eq;
    if (lean_is_scalar(o)) {
        eq = lean_is_scalar(expected) && lean_unbox(o) == lean_unbox(expected);
    } else if (lean_is_scalar(expected)) {
        eq = false;
    } else {
        eq = lean_nat_big_eq(o, expected);
    }
    if (!lean_is_scalar(expected)) {
        lean_dec(expected);
    }
    return eq ? 1 : 0;
}

extern "C" uint8_t leanrt_test_cpp_int_eq_cstr(lean_object * o, char const * value) {
    return leanrt_test_int_eq_cstr(o, value);
}

extern "C" size_t leanrt_test_cpp_mpz_object_size(void) {
    return sizeof(lean::mpz_object);
}

extern "C" size_t leanrt_test_cpp_mpz_value_offset(void) {
    return offsetof(lean::mpz_object, m_value);
}

extern "C" int leanrt_test_mpz_compactor_roundtrip(lean_object * o, char const * expected) {
    if (leanrt_test_mpz_object_size() != sizeof(lean::mpz_object) ||
        leanrt_test_mpz_value_offset() != offsetof(lean::mpz_object, m_value)) {
        return 0;
    }

    lean::object_compactor compactor;
    compactor(reinterpret_cast<lean::object *>(o));
    size_t size = compactor.size();
    void * data = std::malloc(size);
    if (data == nullptr) return -1;
    std::memcpy(data, compactor.data(), size);
    lean::compacted_region region(size, data, nullptr, false, [data]() { std::free(data); });
    auto * roundtrip = reinterpret_cast<lean_object *>(region.read());
    if (roundtrip == nullptr || lean_obj_tag(roundtrip) != LeanMPZ) {
        return -1;
    }

    return leanrt_test_mpz_eq_cstr(roundtrip, expected) ? 1 : -1;
}
