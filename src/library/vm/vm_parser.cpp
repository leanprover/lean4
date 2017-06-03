/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include "library/vm/vm_parser.h"
#include <string>
#include <iostream>
#include <vector>
#include "library/constants.h"
#include "library/explicit.h"
#include "library/num.h"
#include "library/quote.h"
#include "library/trace.h"
#include "library/vm/interaction_state_imp.h"
#include "library/tactic/elaborate.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_pos_info.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/parser.h"
#include "util/utf8.h"

namespace lean {

struct lean_parser_state {
    parser * m_p;
};

bool is_ts_safe(lean_parser_state const &) { return false; }
template struct interaction_monad<lean_parser_state>;
typedef interaction_monad<lean_parser_state> lean_parser;

#define TRY try {
#define CATCH } catch (break_at_pos_exception const & ex) { throw; }\
                catch (exception const & ex) { return lean_parser::mk_exception(ex, s); }

vm_obj run_parser(parser & p, expr const & spec) {
    type_context ctx(p.env(), p.get_options());
    return lean_parser::get_result_value(lean_parser::evaluator(ctx, p.get_options())(spec, lean_parser_state {&p}));
}

expr parse_interactive_param(parser & p, expr const & param_ty) {
    lean_assert(is_app_of(param_ty, get_interactive_parse_name()));
    buffer<expr> param_args;
    get_app_args(param_ty, param_args);
    // alpha, has_reflect alpha, parser alpha
    lean_assert(param_args.size() == 3);
    if (!closed(param_args[2])) {
        throw elaborator_exception(param_args[2], "error running user-defined parser: must be closed expression");
    }
    try {
        vm_obj vm_parsed = run_parser(p, param_args[2]);
        type_context ctx(p.env());
        name n("_reflect");
        lean_parser::evaluator eval(ctx, p.get_options());
        auto env = eval.compile(n, param_args[1]);
        vm_state S(env, p.get_options());
        auto vm_res = S.invoke(n, vm_parsed);
        expr r = to_expr(vm_res);
        if (is_app_of(r, get_expr_subst_name())) {
            return r; // HACK
        } else {
            return mk_as_is(r);
        }
    } catch (exception & ex) {
        if (!p.has_error_recovery()) throw;
        p.mk_message(ERROR).set_exception(ex).report();
        return p.mk_sorry(p.pos(), true);
    }
}

vm_obj vm_parser_state_env(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    return to_obj(s.m_p->env());
}

vm_obj vm_parser_state_options(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    return to_obj(s.m_p->get_options());
}

vm_obj vm_parser_state_cur_pos(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    return to_obj(s.m_p->pos());
}

vm_obj vm_parser_ident(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    TRY;
        auto _ = s.m_p->no_error_recovery_scope();
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

vm_obj vm_parser_pexpr(vm_obj const & vm_rbp, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    TRY;
        auto rbp = to_unsigned(vm_rbp);
        if (auto e = s.m_p->maybe_parse_expr(rbp)) {
            return lean_parser::mk_success(to_obj(*e), s);
        } else {
            throw parser_error(sstream() << "expression expected", s.m_p->pos());
        }
    CATCH;
}

vm_obj vm_parser_qexpr(vm_obj const & vm_rbp, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    TRY;
        auto rbp = to_unsigned(vm_rbp);
        parser::quote_scope scope(*s.m_p, true);
        if (auto e = s.m_p->maybe_parse_expr(rbp)) {
            return lean_parser::mk_success(to_obj(*e), s);
        } else {
            throw parser_error(sstream() << "expression expected", s.m_p->pos());
        }
    CATCH;
}

vm_obj vm_parser_skip_info(vm_obj const &, vm_obj const & vm_p, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    return s.m_p->without_break_at_pos<vm_obj>([&]() {
        return invoke(vm_p, o);
    });
}

vm_obj vm_parser_set_goal_info_pos(vm_obj const &, vm_obj const & vm_p, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    auto pos = s.m_p->pos();
    try {
        return invoke(vm_p, o);
    } catch (break_at_pos_exception & ex) {
        ex.report_goal_pos(pos);
        throw;
    }
}

vm_obj vm_parser_with_input(vm_obj const &, vm_obj const & vm_p, vm_obj const & vm_input, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    std::string input = to_string(vm_input);
    std::istringstream strm(input);
    vm_obj vm_state; pos_info pos;
    auto _ = s.m_p->no_error_recovery_scope();
    TRY;
        std::tie(vm_state, pos) = s.m_p->with_input<vm_obj>(strm, [&]() {
            return invoke(vm_p, o);
        });
    CATCH;

    if (lean_parser::is_result_exception(vm_state)) {
        return vm_state;
    }
    auto vm_res = lean_parser::get_result_value(vm_state);

    // figure out remaining string from end position
    pos_info pos2 = {1, 0};
    unsigned spos = 0;
    while (pos2 < pos) {
        lean_assert(spos < input.size());
        if (input[spos] == '\n') {
            pos2.first++;
            pos2.second = 0;
        } else {
            pos2.second++;
        }
        spos += get_utf8_size(input[spos]);
    }

    vm_res = mk_vm_pair(vm_res, to_obj(input.substr(spos)));
    return lean_parser::mk_result(vm_res, lean_parser::get_result_state(vm_state));
}

void initialize_vm_parser() {
    DECLARE_VM_BUILTIN(name({"lean", "parser_state", "env"}),         vm_parser_state_env);
    DECLARE_VM_BUILTIN(name({"lean", "parser_state", "options"}),     vm_parser_state_options);
    DECLARE_VM_BUILTIN(name({"lean", "parser_state", "cur_pos"}),     vm_parser_state_cur_pos);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "ident"}),             vm_parser_ident);
    DECLARE_VM_BUILTIN(get_lean_parser_tk_name(),                     vm_parser_tk);
    DECLARE_VM_BUILTIN(get_lean_parser_pexpr_name(),                  vm_parser_pexpr);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "qexpr"}),             vm_parser_qexpr);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "skip_info"}),         vm_parser_skip_info);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "set_goal_info_pos"}), vm_parser_set_goal_info_pos);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "with_input"}),        vm_parser_with_input);
}

void finalize_vm_parser() {
}

}
