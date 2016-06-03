/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"

namespace lean {
/** Structure for storing the contents of an 'export' command. */
struct export_decl {
    name                   m_ns;
    name                   m_as;
    list<name>             m_metacls;
    bool                   m_decls;
    bool                   m_had_explicit;
    list<pair<name, name>> m_renames;
    list<name>             m_except_names;

    export_decl() {}
    export_decl(name const & ns, name const & as, buffer<name> const & metacls,
                 bool decls, bool had_explicit, buffer<pair<name, name>> const & renames,
                 buffer<name> const & except_names):
        m_ns(ns), m_as(as), m_metacls(to_list(metacls)), m_decls(decls), m_had_explicit(had_explicit),
        m_renames(to_list(renames)), m_except_names(to_list(except_names)) {}
};

/** \brief We store export commands to allow us to replay them whenever the namespace is opened. */
environment add_export_decl(environment const & env, export_decl const & entry);
list<export_decl> get_export_decls(environment const & env);

name const & get_export_decl_class_name();

void initialize_export_decl();
void finalize_export_decl();
}
