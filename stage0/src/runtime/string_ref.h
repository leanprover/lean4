/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "runtime/sstream.h"
#include "runtime/object_ref.h"
#include "runtime/list_ref.h"
namespace lean {
/* Wrapper for Lean string objects */
class string_ref : public object_ref {
public:
    explicit string_ref(char const * s):object_ref(mk_string(s)) {}
    explicit string_ref(std::string const & s):object_ref(mk_string(s)) {}
    explicit string_ref(sstream const & strm):string_ref(strm.str()) {}
    string_ref(string_ref const & other):object_ref(other) {}
    string_ref(string_ref && other):object_ref(std::move(other)) {}
    explicit string_ref(obj_arg o):object_ref(o) {}
    string_ref(b_obj_arg o, bool b):object_ref(o, b) {}
    string_ref & operator=(string_ref const & other) { object_ref::operator=(other); return *this; }
    string_ref & operator=(string_ref && other) { object_ref::operator=(std::move(other)); return *this; }
    /* Number of bytes used to store the string in UTF8.
       Remark: it does not include the null character added in the end to make it efficient to
       convert to C string. */
    size_t num_bytes() const { return string_size(raw()) - 1; }
    /* The length is the number of unicode scalars. It is <= num_bytes. */
    size_t length() const { return string_len(raw()); }
    char const * data() const { return string_cstr(raw()); }
    std::string to_std_string() const { return std::string(data(), num_bytes()); }
    friend bool operator==(string_ref const & s1, string_ref const & s2) { return string_eq(s1.raw(), s2.raw()); }
    friend bool operator!=(string_ref const & s1, string_ref const & s2) { return string_ne(s1.raw(), s2.raw()); }
    friend bool operator<(string_ref const & s1, string_ref const & s2) { return string_lt(s1.raw(), s2.raw()); }
    friend bool operator==(string_ref const & s1, char const * s2) { return string_eq(s1.raw(), s2); }
    friend bool operator!=(string_ref const & s1, char const * s2) { return !(s1 == s2); }
};
typedef list_ref<string_ref> string_refs;
};
