#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <vector>

#include "runtime/alloc.h"
#include "runtime/utf8.h"

namespace lean {
namespace {
unsigned get_utf8_size_impl(unsigned char c) {
  if ((c & 0x80) == 0) {
    return 1;
  } else if ((c & 0xE0) == 0xC0) {
    return 2;
  } else if ((c & 0xF0) == 0xE0) {
    return 3;
  } else if ((c & 0xF8) == 0xF0) {
    return 4;
  } else if ((c & 0xFC) == 0xF8) {
    return 5;
  } else if ((c & 0xFE) == 0xFC) {
    return 6;
  } else {
    return 1;
  }
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
  static void push(std::string& s, unsigned char c) {
    s.push_back(static_cast<char>(c));
  }
};

template <typename T>
unsigned push_unicode_scalar_core(T& d, unsigned code) {
  constexpr unsigned char tag_cont = static_cast<unsigned char>(0b10000000);
  constexpr unsigned char tag_two_b = static_cast<unsigned char>(0b11000000);
  constexpr unsigned char tag_three_b = static_cast<unsigned char>(0b11100000);
  constexpr unsigned char tag_four_b = static_cast<unsigned char>(0b11110000);

  if (code < 0x80) {
    push_back_trait<T>::push(d, static_cast<unsigned char>(code));
    return 1;
  } else if (code < 0x800) {
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 6) & 0x1F) | tag_two_b);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | tag_cont);
    return 2;
  } else if (code < 0x10000) {
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 12) & 0x0F) | tag_three_b);
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 6) & 0x3F) | tag_cont);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | tag_cont);
    return 3;
  } else {
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 18) & 0x07) | tag_four_b);
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 12) & 0x3F) | tag_cont);
    push_back_trait<T>::push(d, static_cast<unsigned char>((code >> 6) & 0x3F) | tag_cont);
    push_back_trait<T>::push(d, static_cast<unsigned char>(code & 0x3F) | tag_cont);
    return 4;
  }
}
} // namespace

size_t utf8_strlen(char const* str) {
  size_t result = 0;
  while (*str != 0) {
    ++result;
    str += get_utf8_size_impl(static_cast<unsigned char>(*str));
  }
  return result;
}

size_t utf8_strlen(char const* str, size_t size) {
  size_t result = 0;
  size_t i = 0;
  while (i < size) {
    ++result;
    i += get_utf8_size_impl(static_cast<unsigned char>(str[i]));
  }
  return result;
}

size_t utf8_strlen(std::string const& str) {
  return utf8_strlen(str.data(), str.size());
}

optional<unsigned> get_utf8_first_byte_opt(unsigned char c) {
  if ((c & 0x80) == 0) {
    return optional<unsigned>(1);
  } else if ((c & 0xE0) == 0xC0) {
    return optional<unsigned>(2);
  } else if ((c & 0xF0) == 0xE0) {
    return optional<unsigned>(3);
  } else if ((c & 0xF8) == 0xF0) {
    return optional<unsigned>(4);
  } else {
    return optional<unsigned>();
  }
}

unsigned next_utf8(char const* str, size_t size, size_t& i) {
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

unsigned next_utf8(std::string const& str, size_t& i) {
  return next_utf8(str.data(), str.size(), i);
}

void utf8_decode(std::string const& str, std::vector<unsigned>& out) {
  size_t i = 0;
  while (i < str.size()) {
    out.push_back(next_utf8(str, i));
  }
}

bool validate_utf8_one(uint8_t const* str, size_t size, size_t& pos) {
  unsigned c = str[pos];
  if ((c & 0x80) == 0) {
    ++pos;
  } else if ((c & 0xE0) == 0xC0) {
    if (pos + 1 >= size) return false;
    unsigned c1 = str[pos + 1];
    if ((c1 & 0xC0) != 0x80) return false;
    unsigned r = ((c & 0x1F) << 6) | (c1 & 0x3F);
    if (r < 0x80) return false;
    pos += 2;
  } else if ((c & 0xF0) == 0xE0) {
    if (pos + 2 >= size) return false;
    unsigned c1 = str[pos + 1];
    unsigned c2 = str[pos + 2];
    if ((c1 & 0xC0) != 0x80 || (c2 & 0xC0) != 0x80) return false;
    unsigned r = ((c & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
    if (r < 0x800 || (r >= 0xD800 && r <= 0xDFFF)) return false;
    pos += 3;
  } else if ((c & 0xF8) == 0xF0) {
    if (pos + 3 >= size) return false;
    unsigned c1 = str[pos + 1];
    unsigned c2 = str[pos + 2];
    unsigned c3 = str[pos + 3];
    if ((c1 & 0xC0) != 0x80 || (c2 & 0xC0) != 0x80 || (c3 & 0xC0) != 0x80) return false;
    unsigned r = ((c & 0x07) << 18) | ((c1 & 0x3F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F);
    if (r < 0x10000 || r > 0x10FFFF) return false;
    pos += 4;
  } else {
    return false;
  }
  return true;
}

bool validate_utf8(uint8_t const* str, size_t size, size_t& pos, size_t& i) {
  while (pos < size) {
    if (!validate_utf8_one(str, size, pos)) {
      return false;
    }
    ++i;
  }
  return true;
}

unsigned push_unicode_scalar(char* d, unsigned code) {
  return push_unicode_scalar_core<char*>(d, code);
}

void push_unicode_scalar(std::string& s, unsigned code) {
  push_unicode_scalar_core(s, code);
}
} // namespace lean

extern "C" void* mi_malloc_small(size_t size) {
  unsigned aligned = lean_align(static_cast<unsigned>(size), LEAN_OBJECT_SIZE_DELTA);
  void* mem = std::malloc(sizeof(size_t) + aligned);
  if (mem == nullptr) {
    return nullptr;
  }
  *static_cast<size_t*>(mem) = aligned;
  return static_cast<size_t*>(mem) + 1;
}

extern "C" void mi_free(void* ptr) {
  if (ptr == nullptr) {
    return;
  }
  std::free(static_cast<size_t*>(ptr) - 1);
}
