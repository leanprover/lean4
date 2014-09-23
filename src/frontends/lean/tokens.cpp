/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name.h"

namespace lean {
static name * g_period       = nullptr;
static name * g_colon        = nullptr;
static name * g_lparen       = nullptr;
static name * g_rparen       = nullptr;
static name * g_llevel_curly = nullptr;
static name * g_lcurly       = nullptr;
static name * g_rcurly       = nullptr;
static name * g_ldcurly      = nullptr;
static name * g_rdcurly      = nullptr;
static name * g_lbracket     = nullptr;
static name * g_rbracket     = nullptr;
static name * g_bar          = nullptr;
static name * g_comma        = nullptr;
static name * g_add          = nullptr;
static name * g_max          = nullptr;
static name * g_imax         = nullptr;
static name * g_cup          = nullptr;
static name * g_import       = nullptr;
static name * g_show         = nullptr;
static name * g_have         = nullptr;
static name * g_assume       = nullptr;
static name * g_take         = nullptr;
static name * g_fun          = nullptr;
static name * g_ellipsis     = nullptr;
static name * g_raw          = nullptr;
static name * g_true         = nullptr;
static name * g_false        = nullptr;
static name * g_options      = nullptr;
static name * g_arrow        = nullptr;
static name * g_declarations = nullptr;
static name * g_decls        = nullptr;
static name * g_hiding       = nullptr;
static name * g_exposing     = nullptr;
static name * g_renaming     = nullptr;
static name * g_as           = nullptr;
static name * g_on           = nullptr;
static name * g_off          = nullptr;
static name * g_none         = nullptr;

void initialize_tokens() {
    g_period       = new name(".");
    g_colon        = new name(":");
    g_lparen       = new name("(");
    g_rparen       = new name(")");
    g_llevel_curly = new name(".{");
    g_lcurly       = new name("{");
    g_rcurly       = new name("}");
    g_ldcurly      = new name("⦃");
    g_rdcurly      = new name("⦄");
    g_lbracket     = new name("[");
    g_rbracket     = new name("]");
    g_bar          = new name("|");
    g_comma        = new name(",");
    g_add          = new name("+");
    g_max          = new name("max");
    g_imax         = new name("imax");
    g_cup          = new name("\u2294");
    g_import       = new name("import");
    g_show         = new name("show");
    g_have         = new name("have");
    g_assume       = new name("assume");
    g_take         = new name("take");
    g_fun          = new name("fun");
    g_ellipsis     = new name("...");
    g_raw          = new name("raw");
    g_true         = new name("true");
    g_false        = new name("false");
    g_options      = new name("options");
    g_arrow        = new name("->");
    g_declarations = new name("declarations");
    g_decls        = new name("decls");
    g_hiding       = new name("hiding");
    g_exposing     = new name("exposing");
    g_renaming     = new name("renaming");
    g_as           = new name("as");
    g_on           = new name("[on]");
    g_off          = new name("[off]");
    g_none         = new name("[none]");
}

void finalize_tokens() {
    delete g_raw;
    delete g_true;
    delete g_false;
    delete g_options;
    delete g_arrow;
    delete g_declarations;
    delete g_decls;
    delete g_hiding;
    delete g_exposing;
    delete g_renaming;
    delete g_as;
    delete g_on;
    delete g_off;
    delete g_none;
    delete g_ellipsis;
    delete g_fun;
    delete g_take;
    delete g_assume;
    delete g_have;
    delete g_show;
    delete g_import;
    delete g_cup;
    delete g_imax;
    delete g_max;
    delete g_add;
    delete g_comma;
    delete g_bar;
    delete g_rbracket;
    delete g_lbracket;
    delete g_rdcurly;
    delete g_ldcurly;
    delete g_lcurly;
    delete g_rcurly;
    delete g_llevel_curly;
    delete g_rparen;
    delete g_lparen;
    delete g_colon;
    delete g_period;
}

name const & get_period_tk() { return *g_period; }
name const & get_colon_tk() { return *g_colon; }
name const & get_lparen_tk() { return *g_lparen; }
name const & get_rparen_tk() { return *g_rparen; }
name const & get_llevel_curly_tk() { return *g_llevel_curly; }
name const & get_lcurly_tk() { return *g_lcurly; }
name const & get_rcurly_tk() { return *g_rcurly; }
name const & get_ldcurly_tk() { return *g_ldcurly; }
name const & get_rdcurly_tk() { return *g_rdcurly; }
name const & get_lbracket_tk() { return *g_lbracket; }
name const & get_rbracket_tk() { return *g_rbracket; }
name const & get_bar_tk() { return *g_bar; }
name const & get_comma_tk() { return *g_comma; }
name const & get_add_tk() { return *g_add; }
name const & get_max_tk() { return *g_max; }
name const & get_imax_tk() { return *g_imax; }
name const & get_cup_tk() { return *g_cup; }
name const & get_import_tk() { return *g_import; }
name const & get_show_tk() { return *g_show; }
name const & get_have_tk() { return *g_have; }
name const & get_assume_tk() { return *g_assume; }
name const & get_take_tk() { return *g_take; }
name const & get_fun_tk() { return *g_fun; }
name const & get_ellipsis_tk() { return *g_ellipsis; }
name const & get_raw_tk() { return *g_raw; }
name const & get_true_tk() { return *g_true; }
name const & get_false_tk() { return *g_false; }
name const & get_options_tk() { return *g_options; }
name const & get_arrow_tk() { return *g_arrow; }
name const & get_declarations_tk() { return *g_declarations; }
name const & get_decls_tk() { return *g_decls; }
name const & get_hiding_tk() { return *g_hiding; }
name const & get_exposing_tk() { return *g_exposing; }
name const & get_renaming_tk() { return *g_renaming; }
name const & get_as_tk() { return *g_as; }
name const & get_on_tk() { return *g_on; }
name const & get_off_tk() { return *g_off; }
name const & get_none_tk() { return *g_none; }
}
