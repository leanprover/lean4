/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/script_exception.h"
#include "util/name_set.h"
#include "kernel/kernel_exception.h"
#include "kernel/for_each_fn.h"
#include "library/io_state_stream.h"
// #include "library/elaborator/elaborator_justification.h"
// #include "library/elaborator/elaborator_exception.h"
#include "library/parser_nested_exception.h"
// #include "library/unsolved_metavar_exception.h"

namespace lean {
void display_error_pos(io_state const & ios, char const * strm_name, unsigned line, unsigned pos) {
    regular(ios) << strm_name << ":" << line << ":";
    if (pos != static_cast<unsigned>(-1))
        regular(ios) << pos << ":";
    regular(ios) << " error:";
}

void display_error_pos(io_state const & ios, pos_info_provider const * p, expr const & e) {
    if (p) {
        auto pos = p->get_pos_info(e);
        display_error_pos(ios, p->get_file_name(), pos.first, pos.second);
    } else {
        regular(ios) << "error:";
    }
}

void display_error_pos(io_state const & ios, pos_info_provider const * p, optional<expr> const & e) {
    if (e) {
        display_error_pos(ios, p, *e);
    } else if (p) {
        auto pos = p->get_some_pos();
        display_error_pos(ios, p->get_file_name(), pos.first, pos.second);
    } else {
        regular(ios) << "error:";
    }
}

void display_error(io_state const & ios, pos_info_provider const * p, exception const & ex);

static void display_error(io_state const & ios, pos_info_provider const * p, kernel_exception const & ex) {
    display_error_pos(ios, p, ex.get_main_expr());
    regular(ios) << " " << ex << endl;
}

// static void display_error(io_state const & ios, pos_info_provider const * p, elaborator_exception const & ex) {
//     formatter fmt = ios.get_formatter();
//     options opts  = ios.get_options();
//     auto j = ex.get_justification();
//     j = remove_detail(j);
//     regular(ios) << mk_pair(j.pp(fmt, opts, p, true), opts) << endl;
// }

// struct delta_pos_info_provider : public pos_info_provider {
//     unsigned m_delta;
//     std::string m_file_name;
//     pos_info_provider const & m_provider;
//     delta_pos_info_provider(unsigned d, char const * fname, pos_info_provider const & p):m_delta(d), m_file_name(fname), m_provider(p) {}
//     virtual std::pair<unsigned, unsigned> get_pos_info(expr const & e) const {
//         auto r = m_provider.get_pos_info(e);
//         return mk_pair(r.first + m_delta, r.second);
//     }
//     virtual char const * get_file_name() const { return m_file_name.c_str(); }
//     virtual std::pair<unsigned, unsigned> get_some_pos() const {
//         auto r = m_provider.get_some_pos();
//         return mk_pair(r.first + m_delta, r.second);
//     }
// };


static void display_error(io_state const & ios, pos_info_provider const * p, script_exception const & ex) {
    if (p) {
        char const * msg = ex.get_msg();
        char const * space = msg && *msg == ' ' ? "" : " ";
        switch (ex.get_source()) {
        case script_exception::source::String:
            display_error_pos(ios, p->get_file_name(), ex.get_line() + p->get_some_pos().first - 1, static_cast<unsigned>(-1));
            regular(ios) << " executing script," << space << msg << endl;
            break;
        case script_exception::source::File:
            display_error_pos(ios, p->get_file_name(), p->get_some_pos().first, p->get_some_pos().second);
            regular(ios) << " executing external script (" << ex.get_file_name() << ":" << ex.get_line() << ")," << space << msg << endl;
            break;
        case script_exception::source::Unknown:
            display_error_pos(ios, p->get_file_name(), p->get_some_pos().first, p->get_some_pos().second);
            regular(ios) << " executing script, exact error position is not available, " << ex.what() << endl;
            break;
        }
    } else {
        regular(ios) << ex.what() << endl;
    }
}

static void display_error(io_state const & ios, pos_info_provider const * p, script_nested_exception const & ex) {
    switch (ex.get_source()) {
    case script_exception::source::String:
        if (p) {
            display_error_pos(ios, p->get_file_name(), ex.get_line() + p->get_some_pos().first - 1, static_cast<unsigned>(-1));
            regular(ios) << " executing script" << endl;
        }
        display_error(ios, nullptr, ex.get_exception());
        break;
    case script_exception::source::File:
        if (p) {
            display_error_pos(ios, p->get_file_name(), p->get_some_pos().first, p->get_some_pos().second);
            regular(ios) << " executing external script (" << ex.get_file_name() << ":" << ex.get_line() << ")" << endl;
        } else {
            display_error_pos(ios, ex.get_file_name(), ex.get_line(), -1);
            regular(ios) << " executing script" << endl;
        }
        display_error(ios, nullptr, ex.get_exception());
        break;
    case script_exception::source::Unknown:
        display_error(ios, nullptr, ex.get_exception());
        break;
    }
}

// static void display_error(io_state const & ios, pos_info_provider const *, parser_nested_exception const & ex) {
//     display_error(ios, &(ex.get_provider()), ex.get_exception());
// }

// static void display_error(io_state const & ios, pos_info_provider const *, parser_exception const & ex) {
//     regular(ios) << ex.what() << endl;
// }

// static void display_error(io_state const & ios, pos_info_provider const * p, unsolved_metavar_exception const & ex) {
//     display_error_pos(ios, p, ex.get_expr());
//     formatter fmt = ios.get_formatter();
//     options opts  = ios.get_options();
//     unsigned indent = get_pp_indent(opts);
//     format r = nest(indent, compose(line(), fmt(ex.get_expr(), opts)));
//     regular(ios) << " " << ex.what() << mk_pair(r, opts) << endl;
//     if (p) {
//         name_set already_displayed;
//         for_each(ex.get_expr(), [&](expr const & e, unsigned) -> bool {
//                 if (is_metavar(e)) {
//                     name const & m = metavar_name(e);
//                     if (already_displayed.find(m) == already_displayed.end()) {
//                         already_displayed.insert(m);
//                         for (unsigned i = 0; i < indent; i++) regular(ios) << " ";
//                         display_error_pos(ios, p, e);
//                         regular(ios) << " unsolved metavar " << m << endl;
//                     }
//                 }
//                 return true;
//             });
//     }
// }

void display_error(io_state const & ios, pos_info_provider const * p, exception const & ex) {
    if (auto k_ex = dynamic_cast<kernel_exception const *>(&ex)) {
        display_error(ios, p, *k_ex);
    // } else if (auto e_ex = dynamic_cast<elaborator_exception const *>(&ex)) {
    //     display_error(ios, p, *e_ex);
    // } else if (auto m_ex = dynamic_cast<unsolved_metavar_exception const *>(&ex)) {
    //     display_error(ios, p, *m_ex);
    } else if (auto ls_ex = dynamic_cast<script_nested_exception const *>(&ex)) {
        display_error(ios, p, *ls_ex);
    } else if (auto s_ex = dynamic_cast<script_exception const *>(&ex)) {
        display_error(ios, p, *s_ex);
    // } else if (auto n_ex = dynamic_cast<parser_nested_exception const *>(&ex)) {
    //     display_error(ios, p, *n_ex);
    // } else if (auto n_ex = dynamic_cast<parser_exception const *>(&ex)) {
    //     display_error(ios, p, *n_ex);
    } else if (p) {
        display_error_pos(ios, p->get_file_name(), p->get_some_pos().first, p->get_some_pos().second);
        regular(ios) << " " << ex.what() << endl;
    } else {
        regular(ios) << "error: " << ex.what() << endl;
    }
}
}

