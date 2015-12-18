/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/io_state.h"
namespace lean {
class parser;
class decl_attributes {
public:
    struct entry {
        std::string    m_attr;
        list<unsigned> m_params;
        entry() {}
        entry(char const * attr):m_attr(attr) {}
        entry(char const * attr, unsigned p):m_attr(attr), m_params(to_list(p)) {}
        entry(char const * attr, list<unsigned> const & ps):m_attr(attr), m_params(ps) {}
        bool operator==(entry const & e) const { return m_attr == e.m_attr && m_params == e.m_params; }
        bool operator!=(entry const & e) const { return !operator==(e); }
    };
private:
    bool               m_is_abbrev; // if true only abbreviation attributes are allowed
    bool               m_persistent;
    bool               m_parsing_only;
    list<entry>        m_entries;
    optional<unsigned> m_prio;
public:
    decl_attributes(bool is_abbrev = false, bool persistent = true);
    void parse(parser & p);
    environment apply(environment env, io_state const & ios, name const & d, name const & ns) const;
    bool is_parsing_only() const { return m_parsing_only; }
    void write(serializer & s) const;
    void read(deserializer & d);
    friend bool operator==(decl_attributes const & d1, decl_attributes const & d2);
};
bool operator==(decl_attributes const & d1, decl_attributes const & d2);
}
