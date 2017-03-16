/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include "library/vm/vm_parser.h"
#include <string>
#include <iostream>
#include <vector>
#include <library/num.h>
#include <library/quote.h>
#include "frontends/lean/parser.h"
#include "library/trace.h"
#include "library/type_context.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/elaborator.h"
#include "library/tactic/elaborate.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_pos_info.h"
#include "library/vm/interaction_state.h"
#include "util/task_queue.h"

namespace lean {

struct lean_parser_state {
    parser * m_p;
};

template struct interaction_monad<lean_parser_state>;
typedef interaction_monad<lean_parser_state> lean_parser;

#define TRY try {
#define CATCH } catch (break_at_pos_exception const & ex) { throw; }\
                catch (exception const & ex) { return lean_parser::mk_exception(ex, s); }

vm_obj run_parser(parser & p, expr const & spec) {
    type_context ctx(p.env(), p.get_options());
    return lean_parser::get_result_value(lean_parser::evaluator(ctx, p.get_options())(spec, lean_parser_state {&p}));
}

vm_obj vm_parser_state_cur_pos(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    return to_obj(s.m_p->pos());
}

vm_obj vm_parser_ident(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    TRY;
        name ident = s.m_p->check_id_next("identifier expected");
        return lean_parser::mk_success(to_obj(ident), s);
    CATCH;
}

vm_obj vm_parser_tk(vm_obj const & vm_tk, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    TRY;
        name tk = to_string(vm_tk);
        if (!s.m_p->curr_is_token(tk))
            throw parser_error(sstream() << "'" << tk << "' expected", s.m_p->pos());
        s.m_p->next();
        return lean_parser::mk_success(s);
    CATCH;
}

vm_obj vm_parser_qexpr(vm_obj const & vm_rbp, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    TRY;
        auto rbp = to_unsigned(vm_rbp);
        parser::quote_scope scope(*s.m_p, true);
        expr e = s.m_p->parse_expr(rbp);
        return lean_parser::mk_success(to_obj(e), s);
    CATCH;
}

void initialize_vm_parser() {
    DECLARE_VM_BUILTIN(name({"lean", "parser_state", "cur_pos"}), vm_parser_state_cur_pos);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "ident"}),         vm_parser_ident);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "tk"}),            vm_parser_tk);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "qexpr"}),         vm_parser_qexpr);
}

void finalize_vm_parser() {
}

}
