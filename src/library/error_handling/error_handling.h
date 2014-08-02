/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/exception.h"
#include "kernel/pos_info_provider.h"
#include "library/io_state_stream.h"

namespace lean {
/** \brief Auxiliary object for "inserting" delimiters for flycheck */
class flycheck_scope {
    io_state_stream const & m_ios;
    bool                    m_flycheck;
public:
    flycheck_scope(io_state_stream const & ios, char const * kind);
    ~flycheck_scope();
};

struct flycheck_error : public flycheck_scope {
    flycheck_error(io_state_stream const & ios):flycheck_scope(ios, "ERROR") {}
};

struct flycheck_warning : public flycheck_scope {
    flycheck_warning(io_state_stream const & ios):flycheck_scope(ios, "WARNING") {}
};

class flyinfo_scope {
    io_state_stream const & m_ios;
    bool                    m_flyinfo;
public:
    flyinfo_scope(io_state_stream const & ios);
    ~flyinfo_scope();
};

/**
   \brief Display position information associated with \c e (IF avaiable).
   If it is not available, it just displays "error:"
*/
void display_error_pos(io_state_stream const & ios, pos_info_provider const * p, expr const & e);
/** \brief Display position information + "error:" */
void display_error_pos(io_state_stream const & ios, char const * strm_name, unsigned line, unsigned pos);
/** \brief Similar to #display_error_pos, but displays a "warning:" */
void display_warning_pos(io_state_stream const & ios, char const * strm_name, unsigned line, unsigned pos);
/**
   \brief Display exception in the regular stream of \c ios, using the configuration options and formatter from \c ios.
   Exceptions that contain expressions use the given \c pos_info_provider (if available) to retrieve line number information.
*/
void display_error(io_state_stream const & ios, pos_info_provider const * p, exception const & ex);
}
