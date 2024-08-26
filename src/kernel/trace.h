/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <string>
#include "library/elab_environment.h"
#include "util/options.h"
#include "util/message_definitions.h"

namespace lean {
void register_trace_class(name const & n, name const & decl_name = {});
void register_trace_class_alias(name const & n, name const & alias);
bool is_trace_enabled();
bool is_trace_class_enabled(name const & n);

#define lean_is_trace_enabled(CName) (::lean::is_trace_enabled() && ::lean::is_trace_class_enabled(CName))

class scope_trace_env {
    unsigned                 m_enable_sz;
    unsigned                 m_disable_sz;
    elab_environment const * m_old_env;
    options     const *      m_old_opts;
    void init(elab_environment * env, options * opts);
public:
    scope_trace_env(elab_environment const & env, options const & opts);
    ~scope_trace_env();
};

struct tclass { name m_cls; tclass(name const & c):m_cls(c) {} };

struct tout {
    sstream m_out;
    ~tout();
};

template <typename T>
tout & operator<<(tout const & out, T const & t) {
    tout & out_mut = const_cast<tout &>(out);
    out_mut.m_out << t;
    return out_mut;
}

std::ostream & operator<<(std::ostream & ios, tclass const &);

#define lean_trace(CName, CODE) {               \
if (lean_is_trace_enabled(CName)) {             \
    tout() << tclass(CName); CODE               \
}}

std::string trace_pp_expr(expr const & e);

void initialize_trace();
void finalize_trace();
}
