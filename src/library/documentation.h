/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
namespace lean {
class doc_entry {
    optional<name> m_decl_name;
    std::string    m_doc;
public:
    doc_entry(std::string const & doc):m_doc(doc) {}
    doc_entry(name const & decl_name, std::string const & doc):m_decl_name(decl_name), m_doc(doc) {}
    optional<name> const & get_decl_name() const { return m_decl_name; }
    std::string const & get_doc() const { return m_doc; }
};
environment add_module_doc_string(environment const & env, std::string doc);
environment add_doc_string(environment const & env, name const & n, std::string);
optional<std::string> get_doc_string(environment const & env, name const & n);
void get_module_doc_strings(environment const & env, buffer<doc_entry> & result);
void initialize_documentation();
void finalize_documentation();
}
