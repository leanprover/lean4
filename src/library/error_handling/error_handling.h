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
void display_pos(std::ostream & out, options const & o, char const * strm_name, unsigned line, unsigned pos);
void display_pos(std::ostream & out, char const * strm_name, unsigned line, unsigned pos);
void display_pos(io_state_stream const & ios, char const * strm_name, unsigned line, unsigned pos);
/**
   \brief Display position information associated with \c e (IF avaiable).
   If it is not available, it just displays "error:"
*/
void display_error_pos(io_state_stream const & ios, pos_info_provider const * p, expr const & e);
/** \brief Display position information + "error:" */
void display_error_pos(io_state_stream const & ios, char const * strm_name, unsigned line, unsigned pos);
/** \brief Similar to #display_error_pos, but displays a "warning:" */
void display_warning_pos(io_state_stream const & ios, char const * strm_name, unsigned line, unsigned pos);
void display_information_pos(io_state_stream const & ios, char const * strm_name, unsigned line, unsigned pos);
/**
   \brief Display exception in the regular stream of \c ios, using the configuration options and formatter from \c ios.
   Exceptions that contain expressions use the given \c pos_info_provider (if available) to retrieve line number information.
*/
void display_error(io_state_stream const & ios, pos_info_provider const * p, throwable const & ex);
}
