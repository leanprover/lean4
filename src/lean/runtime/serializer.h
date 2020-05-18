/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <iostream>
#include <string>
#include <sstream>
#include <functional>
#include <unordered_map>
#include <cstring>
#include "runtime/object.h"
#include "runtime/optional.h"

namespace lean {
class serializer {
    std::ostream & m_out;
    std::unordered_map<object*, unsigned, std::hash<object*>, std::equal_to<object*>> m_obj_table;
    void write_constructor(object * o);
    void write_closure(object * o);
    void write_thunk(object * o);
    void write_task(object * o);
    void write_array(object * o);
    void write_scalar_array(object * o);
    void write_string_object(object * o);
    void write_external(object * o);
public:
    serializer(std::ostream & out):m_out(out) {}
    ~serializer();
    void write_string(char const * str) { m_out.write(str, strlen(str) + 1); }
    void write_string(std::string const & str) { write_string(str.c_str()); }
    void write_unsigned_short(unsigned short i);
    void write_unsigned(unsigned i);
    void write_uint64(uint64 i);
    void write_size_t(size_t i);
    void write_int(int i);
    void write_char(char c) { m_out.put(c); }
    void write_bool(bool b) { m_out.put(b ? 1 : 0); }
    void write_double(double b);
    void write_mpz(mpz const & m);
    void write_object(object * o);
    void write_blob(std::string const &);
};

inline serializer & operator<<(serializer & s, char const * str) { s.write_string(str); return s; }
inline serializer & operator<<(serializer & s, std::string const & str) { s.write_string(str); return s; }
inline serializer & operator<<(serializer & s, unsigned i) { s.write_unsigned(i); return s; }
inline serializer & operator<<(serializer & s, uint64 i) { s.write_uint64(i); return s; }
inline serializer & operator<<(serializer & s, int i) { s.write_int(i); return s; }
inline serializer & operator<<(serializer & s, char c) { s.write_char(c); return s; }
inline serializer & operator<<(serializer & s, bool b) { s.write_bool(b); return s; }
inline serializer & operator<<(serializer & s, double b) { s.write_double(b); return s; }
inline serializer & operator<<(serializer & s, object * o) { s.write_object(o); return s; }

class deserializer {
    std::istream &        m_in;
    std::vector<object*>  m_objs;
    optional<std::string> m_fname;
    unsigned read_unsigned_ext();
    object * read_constructor();
    object * read_closure();
    object * read_thunk();
    object * read_task();
    object * read_array();
    object * read_scalar_array();
    object * read_string_object();
    object * read_external();
public:
    deserializer(std::istream & in):m_in(in) {}
    deserializer(std::istream & in, optional<std::string> const & fname):m_in(in), m_fname(fname) {}
    ~deserializer();
    std::string read_string();
    unsigned read_unsigned() {
        unsigned r = static_cast<unsigned>(m_in.get());
        return r < 255 ? r : read_unsigned_ext();
    }
    uint64 read_uint64();
    size_t read_size_t();
    int read_int() { return read_unsigned(); }
    char read_char() { return m_in.get(); }
    bool read_bool() { return m_in.get() != 0; }
    unsigned short read_unsigned_short();
    double read_double();
    mpz read_mpz();
    std::string read_blob();
    object * read_object();
    optional<std::string> get_fname() const { return m_fname; }
};

inline deserializer & operator>>(deserializer & d, std::string & str) { str = d.read_string(); return d; }
inline deserializer & operator>>(deserializer & d, unsigned & i) { i = d.read_unsigned(); return d; }
inline deserializer & operator>>(deserializer & d, uint64 & i) { i = d.read_uint64(); return d; }
inline deserializer & operator>>(deserializer & d, int & i) { i = d.read_int(); return d; }
inline deserializer & operator>>(deserializer & d, char & c) { c = d.read_char(); return d; }
inline deserializer & operator>>(deserializer & d, bool & b) { b = d.read_bool(); return d; }
inline deserializer & operator>>(deserializer & d, double & b) { b = d.read_double(); return d; }

class corrupted_stream_exception : public exception {
public:
    corrupted_stream_exception();
};

void initialize_serializer();
void finalize_serializer();

template<typename T>
serializer & write_optional(serializer & s, optional<T> const & a) {
    if (a)
        s << true << *a;
    else
        s << false;
    return s;
}

template<typename T>
optional<T> read_optional(deserializer & d) {
    if (d.read_bool()) {
        T r;
        d >> r;
        return optional<T>(r);
    } else {
        return optional<T>();
    }
}

template<typename T>
serializer & operator<<(serializer & s, optional<T> const & a) {
    return write_optional<T>(s, a);
}

template<typename T>
deserializer & operator>>(deserializer & d, optional<T> & a) {
    a = read_optional<T>(d);
    return d;
}

inline serializer & operator<<(serializer & s, mpz const & n) { s.write_mpz(n); return s; }
inline deserializer & operator>>(deserializer & d, mpz & n) { n = d.read_mpz(); return d; }
}
