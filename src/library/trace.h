/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/io_state_stream.h"

namespace lean {
void register_trace_class(name const & n);
void register_trace_class_alias(name const & n, name const & alias);
bool is_trace_enabled();
bool is_trace_class_enabled(name const & n);

class scope_trace_env {
    unsigned            m_sz;
    environment const * m_old_env;
    io_state    const * m_old_ios;
public:
    scope_trace_env(environment const & env, io_state const & ios);
    ~scope_trace_env();
};

class scope_trace_inc_depth {
    bool m_active{false};
public:
    ~scope_trace_inc_depth();
    void activate();
};

/* Temporarily set an option if it is not already set in the trace environment. */
class scope_trace_init_bool_option {
    io_state const * m_old_ios;
    io_state         m_tmp_ios;
public:
    scope_trace_init_bool_option(name const & n, bool v);
    ~scope_trace_init_bool_option();
};

#define lean_trace_inc_depth(CName)                             \
scope_trace_inc_depth trace_inc_depth_helper ## __LINE__;       \
if (is_trace_enabled() && is_trace_class_enabled(name(CName)))  \
    trace_inc_depth_helper ## __LINE__.activate();

struct tdepth {};
struct tclass { name m_cls; tclass(name const & c):m_cls(c) {} };

io_state_stream tout();
io_state_stream const & operator<<(io_state_stream const & ios, tdepth const &);
io_state_stream const & operator<<(io_state_stream const & ios, tclass const &);

#define lean_is_trace_enabled(CName) (::lean::is_trace_enabled() && ::lean::is_trace_class_enabled(CName))

#define lean_trace_plain(CName, CODE) {         \
if (lean_is_trace_enabled(CName)) {             \
    CODE                                        \
}}

#define lean_trace(CName, CODE) {               \
if (lean_is_trace_enabled(CName)) {             \
    tout() << tclass(CName); CODE               \
}}

#define lean_trace_d(CName, CODE) {               \
if (lean_is_trace_enabled(CName)) {               \
    tout() << tdepth() << tclass(CName); CODE     \
}}

void initialize_trace();
void finalize_trace();
}
