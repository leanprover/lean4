/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include "kernel/pos_info_provider.h"
#include "util/sexpr/options.h"
#include "library/io_state.h"

namespace lean {
/** \brief Auxiliary object for "inserting" delimiters for flycheck */
class flycheck_scope {
    std::ostream &  m_out;
    bool            m_flycheck;
public:
    flycheck_scope(std::ostream & out, options const & o, char const * kind);
    flycheck_scope(io_state const & ios, char const * kind):
        flycheck_scope(ios.get_regular_stream(), ios.get_options(), kind) {}
    ~flycheck_scope();
    bool enabled() const { return m_flycheck; }
};

/** Redirects the diagnostic output stream of the global ios as a flycheck information. */
class flycheck_output_scope {
    char const *                           m_stream_name;
    pos_info                               m_pos;
    std::ostream &                         m_out;
    io_state                               m_redirected_ios;
    std::unique_ptr<scope_global_ios>      m_scoped_ios;
    std::shared_ptr<string_output_channel> m_buffer;
public:
    flycheck_output_scope(io_state const & ios, char const * stream_name, pos_info const & pos);
    flycheck_output_scope(char const * stream_name, pos_info const & pos) :
        flycheck_output_scope(get_global_ios(), stream_name, pos) {}
    flycheck_output_scope(pos_info_provider const * provider, expr const & ref);
    ~flycheck_output_scope();
    bool enabled() const { return static_cast<bool>(m_scoped_ios); }
};

struct flycheck_error : public flycheck_scope {
    flycheck_error(std::ostream & out, options const & o):flycheck_scope(out, o, "ERROR") {}
    flycheck_error(io_state const & ios):flycheck_scope(ios, "ERROR") {}
};

struct flycheck_warning : public flycheck_scope {
    flycheck_warning(std::ostream & out, options const & o):flycheck_scope(out, o, "WARNING") {}
    flycheck_warning(io_state const & ios):flycheck_scope(ios, "WARNING") {}
};

struct flycheck_information : public flycheck_scope {
    flycheck_information(std::ostream & out, options const & o):flycheck_scope(out, o, "INFORMATION") {}
    flycheck_information(io_state const & ios):flycheck_scope(ios, "INFORMATION") {}
};
}
