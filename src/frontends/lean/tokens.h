/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name.h"

namespace lean {
void initialize_tokens();
void finalize_tokens();
name const & get_period_tk();
name const & get_colon_tk();
name const & get_lparen_tk();
name const & get_rparen_tk();
name const & get_llevel_curly_tk();
name const & get_lcurly_tk();
name const & get_rcurly_tk();
name const & get_ldcurly_tk();
name const & get_rdcurly_tk();
name const & get_lbracket_tk();
name const & get_rbracket_tk();
name const & get_bar_tk();
name const & get_comma_tk();
name const & get_add_tk();
name const & get_max_tk();
name const & get_imax_tk();
name const & get_cup_tk();
name const & get_import_tk();
name const & get_show_tk();
name const & get_have_tk();
name const & get_assume_tk();
name const & get_take_tk();
name const & get_fun_tk();
name const & get_ellipsis_tk();
name const & get_raw_tk();
name const & get_true_tk();
name const & get_false_tk();
name const & get_options_tk();
name const & get_arrow_tk();
name const & get_declarations_tk();
name const & get_decls_tk();
name const & get_hiding_tk();
name const & get_exposing_tk();
name const & get_renaming_tk();
name const & get_as_tk();
name const & get_on_tk();
name const & get_off_tk();
name const & get_none_tk();
}
