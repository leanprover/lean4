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
#include <cstring>
#include "util/extensible_object.h"
#include "util/list.h"
#include "util/buffer.h"
#include "util/int64.h"
#include "util/optional.h"
#include "util/pair.h"

namespace lean {
/**
   \brief Low-tech serializer.
   The actual functionality is implemented using extensions.
*/
class serializer_core {
    std::ostream & m_out;
public:
    serializer_core(std::ostream & out):m_out(out) {}
    void write_string(char const * str) { m_out.write(str, strlen(str) + 1); }
    void write_string(std::string const & str) { write_string(str.c_str()); }
    void write_unsigned(unsigned i);
    void write_uint64(uint64 i);
    void write_int(int i);
    void write_char(char c) { m_out.put(c); }
    void write_bool(bool b) { m_out.put(b ? 1 : 0); }
    void write_double(double b);
    void write_blob(std::string const &);
};

typedef extensible_object<serializer_core> serializer;

inline serializer & operator<<(serializer & s, char const * str) { s.write_string(str); return s; }
inline serializer & operator<<(serializer & s, std::string const & str) { s.write_string(str); return s; }
inline serializer & operator<<(serializer & s, unsigned i) { s.write_unsigned(i); return s; }
inline serializer & operator<<(serializer & s, uint64 i) { s.write_uint64(i); return s; }
inline serializer & operator<<(serializer & s, int i) { s.write_int(i); return s; }
inline serializer & operator<<(serializer & s, char c) { s.write_char(c); return s; }
inline serializer & operator<<(serializer & s, bool b) { s.write_bool(b); return s; }
inline serializer & operator<<(serializer & s, double b) { s.write_double(b); return s; }
template<typename T1, typename T2>
inline serializer & operator<<(serializer & s, pair<T1, T2> const & p) { s << p.first << p.second; return s; }

/**
   \brief Low-tech serializer.
   The actual functionality is implemented using extensions.
*/
class deserializer_core {
    std::istream &        m_in;
    optional<std::string> m_fname;
    unsigned read_unsigned_ext();
public:
    deserializer_core(std::istream & in):m_in(in) {}
    deserializer_core(std::istream & in, optional<std::string> const & fname):m_in(in), m_fname(fname) {}
    std::string read_string();
    unsigned read_unsigned() {
        unsigned r = static_cast<unsigned>(m_in.get());
        return r < 255 ? r : read_unsigned_ext();
    }
    uint64 read_uint64();
    int read_int() { return read_unsigned(); }
    char read_char() { return m_in.get(); }
    bool read_bool() { return m_in.get() != 0; }
    double read_double();
    std::string read_blob();
    optional<std::string> get_fname() const { return m_fname; }
};

typedef extensible_object<deserializer_core> deserializer;

inline deserializer & operator>>(deserializer & d, std::string & str) { str = d.read_string(); return d; }
inline deserializer & operator>>(deserializer & d, unsigned & i) { i = d.read_unsigned(); return d; }
inline deserializer & operator>>(deserializer & d, uint64 & i) { i = d.read_uint64(); return d; }
inline deserializer & operator>>(deserializer & d, int & i) { i = d.read_int(); return d; }
inline deserializer & operator>>(deserializer & d, char & c) { c = d.read_char(); return d; }
inline deserializer & operator>>(deserializer & d, bool & b) { b = d.read_bool(); return d; }
inline deserializer & operator>>(deserializer & d, double & b) { b = d.read_double(); return d; }
template<typename T1, typename T2>
inline deserializer & operator>>(deserializer & d, pair<T1, T2> & p) { d >> p.first >> p.second; return d; }


class corrupted_stream_exception : public exception {
public:
    corrupted_stream_exception();
};

void initialize_serializer();
void finalize_serializer();

template<typename T>
serializer & write_list(serializer & s, list<T> const & ls) {
    s << length(ls);
    for (auto const & e : ls)
        s << e;
    return s;
}

template<typename T, typename R>
list<T> read_list(deserializer & d, R && t_reader) {
    unsigned num = d.read_unsigned();
    buffer<T> ls;
    for (unsigned i = 0; i < num; i++)
        ls.push_back(t_reader(d));
    return to_list(ls.begin(), ls.end());
}

template<typename T>
list<T> read_list(deserializer & d) {
    return read_list<T>(d, [](deserializer & d) { T r; d >> r; return r; });
}

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
}
