/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include <limits>
#include <stdio.h>
#include <utility>
#include <ios>
#include "runtime/exception.h"
#include "runtime/serializer.h"
#include "runtime/object.h"
#include "runtime/mpz.h"

namespace lean {
void initialize_serializer() {
}

void finalize_serializer() {
}

serializer::~serializer() {
    for (std::pair<object*, unsigned> const & it : m_obj_table) {
        dec_ref(it.first);
    }
}

void serializer::write_unsigned_short(unsigned short i) {
    static_assert(sizeof(i) == 2, "unexpected unsigned short size");
    m_out.put((i >> 8) & 0xff);
    m_out.put(i & 0xff);
}

void serializer::write_unsigned(unsigned i) {
    static_assert(sizeof(i) == 4, "unexpected unsigned size");
    if (i < 255) {
        m_out.put(i & 0xff);
    } else {
        m_out.put(-1);
        m_out.put((i >> 24) & 0xff);
        m_out.put((i >> 16) & 0xff);
        m_out.put((i >> 8) & 0xff);
        m_out.put(i & 0xff);
    }
}

void serializer::write_uint64(uint64 i) {
    static_assert(sizeof(i) == 8, "unexpected uint64 size");
    write_unsigned((i >> 32) & 0xffffffff);
    write_unsigned(i & 0xffffffff);
}

void serializer::write_size_t(size_t i) {
    if (sizeof(i) == 8) {
        write_uint64(static_cast<uint64>(i));
    } else {
        lean_assert(sizeof(i) == 4);
        write_unsigned(static_cast<unsigned>(i));
    }
}

void serializer::write_int(int i) {
    static_assert(sizeof(i) == 4, "unexpected int size");
    write_unsigned(i);
}

void serializer::write_blob(std::string const & s) {
    write_unsigned(s.size());
    m_out.write(&s[0], s.size());
}

void serializer::write_constructor(object * o) {
    lean_assert(is_cnstr(o));
    unsigned num_objs  = cnstr_num_objs(o);
    unsigned obj_size  = lean_object_byte_size(o);
    unsigned main_size = sizeof(lean_ctor_object) + sizeof(lean_object*)*num_objs;
    lean_assert(obj_size >= main_size);
    unsigned scalar_sz = obj_size - main_size;
    write_unsigned_short(cnstr_tag(o));
    write_unsigned_short(num_objs);
    write_unsigned_short(scalar_sz);
    object ** it  = cnstr_obj_cptr(o);
    object ** end = it + num_objs;
    for (; it != end; ++it)
        write_object(*it);
    unsigned char * sit  = cnstr_scalar_cptr(o);
    unsigned char * send = sit + scalar_sz;
    for (; sit != send; ++sit)
        m_out.put(*sit);
}

void serializer::write_closure(object *) { // NOLINT
    /* TODO(Leo): we need a table from function pointer to unique name id.

       For serializing bytecode, we will need to retrieve the unique name id too.
       The trick of storing the bytecode index as the first argument of an "eval"
       C function is not going to work. It seems we will to store the index as
       a tagged pointer and handle it at `apply`.
    */
    throw exception("serializer for closures has not been implemented yet");
}

void serializer::write_thunk(object * o) {
    object * r = thunk_get(o);
    write_object(r);
}

void serializer::write_task(object * o) {
    object * r = task_get(o);
    write_object(r);
}

void serializer::write_array(object * o) {
    lean_assert(is_array(o));
    size_t sz    = sarray_size(o);
    write_size_t(sz);
    object ** it  = array_cptr(o);
    object ** end = it + sz;
    for (; it != end; ++it)
        write_object(*it);
}

void serializer::write_scalar_array(object * o) {
    lean_assert(is_sarray(o));
    unsigned esz = sarray_elem_size(o);
    size_t sz    = sarray_size(o);
    write_unsigned(esz);
    write_size_t(sz);
    size_t num_bytes = sz*esz;
    uint8 const * it  = sarray_cptr(o);
    uint8 const * end = it + num_bytes;
    for (; it != end; ++it)
        m_out.put(*it);
}

void serializer::write_string_object(object * o) {
    size_t sz  = string_size(o);
    size_t len = string_len(o);
    write_size_t(sz);
    write_size_t(len);
    char const * it  = string_cstr(o);
    char const * end = it + sz;
    for (; it != end; ++it)
        m_out.put(*it);
}

void serializer::write_mpz(mpz const & n) {
    std::ostringstream out;
    out << n;
    write_string(out.str());
}

void serializer::write_external(object *) { // NOLINT
    /* TODO(Leo): we need support for registering serializers/deserializers
       for external objects.
    */
    throw exception("serializer for external objects has not been implemented yet");
}

void serializer::write_object(object * o) {
    if (is_scalar(o)) {
        m_out.put(0);
        write_unsigned(unbox(o));
    } else {
        auto it = m_obj_table.find(o);
        if (it != m_obj_table.end()) {
            m_out.put(1);
            write_unsigned(it->second);
        } else {
            uint8 k = lean_ptr_tag(o);
            m_out.put(static_cast<unsigned>(k) + 2);
            switch (k) {
            case LeanClosure:      write_closure(o); break;
            case LeanTask:         write_task(o); break;
            case LeanThunk:        write_thunk(o); break;
            case LeanArray:        write_array(o); break;
            case LeanScalarArray:  write_scalar_array(o); break;
            case LeanString:       write_string_object(o); break;
            case LeanMPZ:          write_mpz(mpz_value(o)); break;
            case LeanExternal:     write_external(o); break;
            case LeanReserved:     lean_unreachable(); break;
            default:               write_constructor(o); break;
            }
            inc_ref(o);
            m_obj_table.insert(std::make_pair(o, m_obj_table.size()));
        }
    }
}

corrupted_stream_exception::corrupted_stream_exception():
    exception("corrupted binary file") {}

void serializer::write_double(double d) {
    std::ostringstream out;
    // TODO(Leo): the following code may miss precision.
    // We should use std::ios::hexfloat, but it is not supported by
    // g++ yet.
    out.flags (std::ios::scientific);
    out.precision(std::numeric_limits<double>::digits10 + 1);
    out << std::hex << d;
    write_string(out.str());
}

deserializer::~deserializer() {
    for (object * o : m_objs)
        dec_ref(o);
}

std::string deserializer::read_string() {
    std::string r;
    while (true) {
        char c = m_in.get();
        if (c == 0)
            break;
        if (m_in.eof())
            throw corrupted_stream_exception();
        r += c;
    }
    return r;
}

unsigned deserializer::read_unsigned_ext() {
    unsigned r;
    static_assert(sizeof(r) == 4, "unexpected unsigned size");
    r  = static_cast<unsigned>(m_in.get()) << 24;
    r |= static_cast<unsigned>(m_in.get()) << 16;
    r |= static_cast<unsigned>(m_in.get()) << 8;
    r |= static_cast<unsigned>(m_in.get());
    return r;
}

unsigned short deserializer::read_unsigned_short() {
    unsigned short r;
    static_assert(sizeof(r) == 2, "unexpected unsigned short size");
    r  = static_cast<unsigned short>(m_in.get()) << 8;
    r |= static_cast<unsigned short>(m_in.get());
    return r;
}

uint64 deserializer::read_uint64() {
    uint64 r;
    static_assert(sizeof(r) == 8, "unexpected uint64 size");
    r  = static_cast<uint64>(read_unsigned()) << 32;
    r |= static_cast<uint64>(read_unsigned());
    return r;
}

size_t deserializer::read_size_t() {
    if (sizeof(size_t) == 8) {
        return static_cast<size_t>(read_uint64());
    } else {
        lean_assert(sizeof(size_t) == 4);
        return static_cast<size_t>(read_unsigned());
    }
}

double deserializer::read_double() {
    // TODO(Leo): use std::hexfloat as soon as it is supported by g++
    std::istringstream in(read_string());
    double r;
    in >> r;
    return r;
}

mpz deserializer::read_mpz() {
    return mpz(read_string().c_str());
}

std::string deserializer::read_blob() {
    unsigned sz = read_unsigned();
    std::string s(sz, '\0');
    m_in.read(&s[0], sz);
    return s;
}

object * deserializer::read_constructor() {
    unsigned tag       = read_unsigned_short();
    unsigned num_objs  = read_unsigned_short();
    unsigned scalar_sz = read_unsigned_short();
    object * r = alloc_cnstr(tag, num_objs, scalar_sz);
    for (unsigned i = 0; i < num_objs; i++) {
        object * o = read_object();
        inc(o);
        cnstr_set(r, i, o);
    }
    unsigned char * it  = cnstr_scalar_cptr(r);
    unsigned char * end = it + scalar_sz;
    for (; it != end; ++it)
        *it = m_in.get();
    return r;
}

object * deserializer::read_closure() {
    throw exception("serializer for closures has not been implemented yet");
}

object * deserializer::read_thunk() {
    object * v = read_object();
    inc(v);
    return thunk_pure(v);
}

object * deserializer::read_task() {
    object * v = read_object();
    inc(v);
    return task_pure(v);
}

object * deserializer::read_array() {
    size_t sz     = read_size_t();
    object * r    = alloc_array(sz, sz);
    object ** it  = array_cptr(r);
    object ** end = it + sz;
    for (; it != end; ++it) {
        object * o = read_object();
        inc(o);
        *it = o;
    }
    return r;
}

object * deserializer::read_scalar_array() {
    unsigned esz   = read_unsigned();
    size_t sz      = read_size_t();
    object * r     = alloc_sarray(esz, sz, sz);
    uint8 * it     = sarray_cptr(r);
    uint8 * end    = it + sz*esz;
    for (; it != end; ++it)
        *it = m_in.get();
    return r;
}

object * deserializer::read_string_object() {
    size_t sz            = read_size_t();
    size_t len           = read_size_t();
    object * r           = alloc_string(sz, sz, len);
    unsigned char * it   = const_cast<unsigned char*>(reinterpret_cast<unsigned char const *>(string_cstr(r)));
    unsigned char * end  = it + sz;
    for (; it != end; ++it)
        *it = m_in.get();
    return r;
}

object * deserializer::read_external() {
    throw exception("serializer for external objects has not been implemented yet");
}

object * deserializer::read_object() {
    unsigned c = m_in.get();
    if (c == 0) {
        return box(read_unsigned());
    } else if (c == 1) {
        unsigned i = read_unsigned();
        if (i >= m_objs.size())
            throw corrupted_stream_exception();
        return m_objs[i];
    } else {
        object * r;
        switch (c - 2) {
        case LeanClosure:      r = read_closure(); break;
        case LeanThunk:        r = read_thunk(); break;
        case LeanTask:         r = read_task(); break;
        case LeanArray:        r = read_array(); break;
        case LeanScalarArray:  r = read_scalar_array(); break;
        case LeanString:       r = read_string_object(); break;
        case LeanMPZ:          r = alloc_mpz(read_mpz()); break;
        case LeanExternal:     r = read_external(); break;
        case LeanReserved:     throw corrupted_stream_exception();
        default:
            if (c - 2 < LeanMaxCtorTag)
                r = read_constructor();
            else
                throw corrupted_stream_exception();
            break;
        }
        m_objs.push_back(r);
        return r;
    }
}
}
