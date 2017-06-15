/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <string>
#include "library/io_state_stream.h"

namespace lean {
void register_trace_class(name const & n);
void register_trace_class_alias(name const & n, name const & alias);
bool is_trace_enabled();
bool is_trace_class_enabled(name const & n);

#define lean_is_trace_enabled(CName) (::lean::is_trace_enabled() && ::lean::is_trace_class_enabled(CName))

class scope_trace_env {
    unsigned                m_enable_sz;
    unsigned                m_disable_sz;
    environment const *     m_old_env;
    options     const *     m_old_opts;
    abstract_type_context * m_old_ctx;
    void init(environment * env, options * opts, abstract_type_context * ctx);
public:
    scope_trace_env(environment const & env, options const & opts, abstract_type_context & ctx);
    scope_trace_env(environment const & env, abstract_type_context & ctx);
    scope_trace_env(options const & opts);
    ~scope_trace_env();
};

class scope_traces_as_messages {
    std::string                            m_stream_name;
    pos_info                               m_pos;
    std::unique_ptr<io_state>              m_redirected_ios;
    std::unique_ptr<scope_global_ios>      m_scoped_ios;
    std::shared_ptr<string_output_channel> m_buffer;

public:
    scope_traces_as_messages(std::string const & stream_name, pos_info const & pos);
    scope_traces_as_messages(pos_info_provider const * provider, expr const & ref);
    ~scope_traces_as_messages();
    bool enabled() const { return static_cast<bool>(m_scoped_ios); }
};

class scope_traces_as_string {
    std::unique_ptr<io_state>              m_redirected_ios;
    std::unique_ptr<scope_global_ios>      m_scoped_ios;
    std::shared_ptr<string_output_channel> m_buffer;
public:
    scope_traces_as_string();
    ~scope_traces_as_string();
    std::string get_string() const { return m_buffer->str(); }
};

class scope_trace_inc_depth {
    bool m_active{false};
public:
    ~scope_trace_inc_depth();
    void activate();
};

#define LEAN_MERGE_(a, b)  a##b
#define LEAN_LABEL_(a) LEAN_MERGE_(unique_name_, a)
#define LEAN_UNIQUE_NAME LEAN_LABEL_(__LINE__)

#define lean_trace_inc_depth(CName)                                     \
scope_trace_inc_depth LEAN_UNIQUE_NAME;                                 \
if (::lean::is_trace_enabled() && ::lean::is_trace_class_enabled(name(CName))) \
    LEAN_UNIQUE_NAME.activate();

/* Temporarily set an option if it is not already set in the trace environment. */
class scope_trace_init_bool_option {
    bool                      m_initialized{false};
    options                   m_opts;
    options *                 m_old_opts;
public:
    ~scope_trace_init_bool_option();
    void init(name const & opt, bool val);
};

#define lean_trace_init_bool(CName, Opt, Val)           \
    scope_trace_init_bool_option LEAN_UNIQUE_NAME;      \
if (lean_is_trace_enabled(CName)) {                     \
    LEAN_UNIQUE_NAME.init(Opt, Val);                    \
}

/* Helper object for temporarily silencing trace messages */
class scope_trace_silent {
    bool m_old_value;
public:
    scope_trace_silent(bool flag);
    ~scope_trace_silent();
};

struct tdepth {};
struct tclass { name m_cls; tclass(name const & c):m_cls(c) {} };

io_state_stream tout();
io_state_stream const & operator<<(io_state_stream const & ios, tdepth const &);
io_state_stream const & operator<<(io_state_stream const & ios, tclass const &);

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
