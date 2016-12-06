/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/output_channel.h"
#include "util/sexpr/options.h"
#include "kernel/expr.h"

namespace lean {
/**
   \brief State provided to internal lean procedures that need to:
   1- Access user defined options
   2- Produce verbosity messages
   3- Output results
   4- Produce formatted output
*/
class io_state {
    options                         m_options;
    formatter_factory               m_formatter_factory;
    std::shared_ptr<output_channel> m_regular_channel;
    std::shared_ptr<output_channel> m_diagnostic_channel;
public:
    io_state();
    io_state(formatter_factory const & fmtf);
    io_state(options const & opts, formatter_factory const & fmtf);
    io_state(io_state const & ios, std::shared_ptr<output_channel> const & r, std::shared_ptr<output_channel> const & d);
    io_state(io_state const & ios, options const & o);
    ~io_state();

    options const & get_options() const { return m_options; }
    formatter_factory const & get_formatter_factory() const { return m_formatter_factory; }
    std::shared_ptr<output_channel> const & get_regular_channel_ptr() const { return m_regular_channel; }
    std::shared_ptr<output_channel> const & get_diagnostic_channel_ptr() const { return m_diagnostic_channel; }
    output_channel & get_regular_channel() const { return *m_regular_channel; }
    output_channel & get_diagnostic_channel() const { return *m_diagnostic_channel; }
    std::ostream & get_regular_stream() const { return m_regular_channel->get_stream(); }
    std::ostream & get_diagnostic_stream() const { return m_diagnostic_channel->get_stream(); }

    void set_regular_channel(std::shared_ptr<output_channel> const & out);
    void set_diagnostic_channel(std::shared_ptr<output_channel> const & out);
    void set_options(options const & opts);
    void set_formatter_factory(formatter_factory const & f);
    template<typename T> void set_option(name const & n, T const & v) {
        set_options(get_options().update(n, v));
    }
};

/** \brief Return a dummy io_state that is meant to be used in contexts that require an io_state, but it is not really used */
io_state const & get_dummy_ios();

/** \brief Return reference to thread local io_state object. */
io_state const & get_global_ios();

/** \brief Formatted exceptions where the format object must be eagerly constructed.
    This is slightly different from ext_exception where the format object is built on demand. */
class formatted_exception : public exception {
protected:
    optional<expr> m_expr;
    format         m_fmt;
    formatted_exception(optional<expr> const & e, format const & fmt):m_expr(e), m_fmt(fmt) {}
public:
    explicit formatted_exception(format const & fmt):m_fmt(fmt) {}
    formatted_exception(expr const & e, format const & fmt):m_expr(e), m_fmt(fmt) {}
    virtual ~formatted_exception() noexcept {}
    virtual char const * what() const noexcept;
    virtual throwable * clone() const { return new formatted_exception(m_expr, m_fmt); }
    virtual void rethrow() const { throw *this; }
    virtual optional<expr> get_main_expr() const { return m_expr; }
    virtual format pp() const { return m_fmt; }
};

struct scope_global_ios {
    io_state * m_old_ios;
public:
    scope_global_ios(io_state const & ios);
    ~scope_global_ios();
};

options const & get_options_from_ios(io_state const & ios);

void initialize_io_state();
void finalize_io_state();
}
