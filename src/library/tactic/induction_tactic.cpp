/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic induction_tactic(name const & H, optional<name> const & rec, list<name> const & ids) {
    // TODO(Leo)
    name rec1 = "unknown";
    if (rec) rec1 = *rec;
    std::cout << "induction: " << H << " " << rec1 << " " << ids << "\n";
    return id_tactic();
}

void initialize_induction_tactic() {
    register_tac(name{"tactic", "induction"},
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     name H = tactic_expr_to_id(app_arg(app_fn(e)), "invalid 'induction' tactic, argument must be an identifier");
                     buffer<name> ids;
                     get_tactic_id_list_elements(app_arg(e), ids, "invalid 'induction' tactic, list of identifiers expected");
                     return induction_tactic(H, optional<name>(), to_list(ids.begin(), ids.end()));
                 });
    register_tac(name{"tactic", "induction_using"},
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     name H = tactic_expr_to_id(app_arg(app_fn(app_fn(e))), "invalid 'induction' tactic, argument must be an identifier");
                     check_tactic_expr(app_arg(app_fn(e)), "invalid 'induction' tactic, invalid argument");
                     expr rec = get_tactic_expr_expr(app_arg(app_fn(e)));
                     if (!is_constant(rec))
                         throw expr_to_tactic_exception(app_arg(app_fn(e)), "invalid 'induction' tactic, constant expected");
                     buffer<name> ids;
                     get_tactic_id_list_elements(app_arg(e), ids, "invalid 'induction' tactic, list of identifiers expected");
                     return induction_tactic(H, optional<name>(const_name(rec)), to_list(ids.begin(), ids.end()));
                 });
}
void finalize_induction_tactic() {
}
}
