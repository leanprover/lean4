/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/name_set.h"
#include "kernel/ext_exception.h"
#include "kernel/for_each_fn.h"
#include "library/io_state_stream.h"
#include "library/unifier.h"
#include "library/parser_nested_exception.h"
#include "library/flycheck.h"
#include "library/pp_options.h"
#include "library/error_handling.h"

namespace lean {
void display_pos(std::ostream & out, options const & o, char const * strm_name, unsigned line, unsigned pos) {
    out << strm_name << ":";
    if (o.get_bool("flycheck", false)) {
        // generate valid line and column for flycheck mode
        if (line == static_cast<unsigned>(-1))
            line = 1;
        if (pos == static_cast<unsigned>(-1))
            pos = 0;
    }
    if (line != static_cast<unsigned>(-1))
        out << line << ":";
    if (pos != static_cast<unsigned>(-1))
        out << pos << ":";
}

void display_pos(std::ostream & out, char const * strm_name, unsigned line, unsigned pos) {
    display_pos(out, options(), strm_name, line, pos);
}

void display_pos(io_state_stream const & ios, char const * strm_name, unsigned line, unsigned pos) {
    display_pos(ios.get_stream(), ios.get_options(), strm_name, line, pos);
}

void display_error_pos(std::ostream & out, options const & o, char const * strm_name, unsigned line, unsigned pos) {
    display_pos(out, o, strm_name, line, pos);
    out << " error:";
}

void display_error_pos(io_state_stream const & ios, char const * strm_name, unsigned line, unsigned pos) {
    display_error_pos(ios.get_stream(), ios.get_options(), strm_name, line, pos);
}

void display_warning_pos(std::ostream & out, options const & o, char const * strm_name, unsigned line, unsigned pos) {
    display_pos(out, o, strm_name, line, pos);
    out << " warning:";
}

void display_warning_pos(io_state_stream const & ios, char const * strm_name, unsigned line, unsigned pos) {
    display_warning_pos(ios.get_stream(), ios.get_options(), strm_name, line, pos);
}

void display_information_pos(std::ostream & out, options const & o, char const * strm_name, unsigned line, unsigned pos) {
    display_pos(out, o, strm_name, line, pos);
    out << " information:";
}

void display_information_pos(io_state_stream const & ios, char const * strm_name, unsigned line, unsigned pos) {
    display_information_pos(ios.get_stream(), ios.get_options(), strm_name, line, pos);
}

void display_error_pos(std::ostream & out, options const & o, pos_info_provider const * p, expr const & e) {
    if (p) {
        auto pos = p->get_pos_info_or_some(e);
        display_error_pos(out, o, p->get_file_name(), pos.first, pos.second);
    } else {
        out << "error:";
    }
}

void display_error_pos(io_state_stream const & ios, pos_info_provider const * p, expr const & e) {
    display_error_pos(ios.get_stream(), ios.get_options(), p, e);
}

void display_error_pos(io_state_stream const & ios, pos_info_provider const * p, optional<expr> const & e) {
    if (e) {
        display_error_pos(ios, p, *e);
    } else if (p) {
        auto pos = p->get_some_pos();
        display_error_pos(ios, p->get_file_name(), pos.first, pos.second);
    } else {
        ios << "error:";
    }
}

void display_error(io_state_stream const & ios, pos_info_provider const * p, throwable const & ex);

static void display_error(io_state_stream const & ios, pos_info_provider const * p, ext_exception const & ex) {
    display_error_pos(ios, p, ex.get_main_expr());
    ios << " " << ex << endl;
}

static void display_error(io_state_stream const & ios, pos_info_provider const * p, unifier_exception const & ex) {
    formatter fmt = ios.get_formatter();
    options opts  = ios.get_options();
    auto j = ex.get_justification();
    display_error_pos(ios, p, j.get_main_expr());
    ios << " " << mk_pair(j.pp(fmt, p, ex.get_substitution()), opts) << endl;
}

void display_error(io_state_stream const & ios, pos_info_provider const * p, throwable const & ex) {
    flycheck_error err(ios.get_stream(), ios.get_options());
    if (auto k_ex = dynamic_cast<ext_exception const *>(&ex)) {
        display_error(ios, p, *k_ex);
    } else if (auto e_ex = dynamic_cast<unifier_exception const *>(&ex)) {
        display_error(ios, p, *e_ex);
    } else if (p) {
        display_error_pos(ios, p->get_file_name(), p->get_some_pos().first, p->get_some_pos().second);
        ios << " " << ex.what() << endl;
    } else {
        ios << "error: " << ex.what() << endl;
    }
}
}
