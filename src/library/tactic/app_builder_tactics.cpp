/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/vm/vm.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_option.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/app_builder_tactics.h"

namespace lean {
vm_obj tactic_mk_app_core(vm_obj const & c, vm_obj const & as, vm_obj const & tmode, vm_obj const & _s) {
    tactic_state const & s = to_tactic_state(_s);
    try {
        metavar_context mctx   = s.mctx();
        type_context ctx       = mk_type_context_for(s, mctx, to_transparency_mode(tmode));
        buffer<expr> args;
        to_buffer_expr(as, args);
        expr r                 = mk_app(ctx, to_name(c), args.size(), args.data());
        return mk_tactic_success(to_obj(r), s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_mk_mapp_core(vm_obj const & c, vm_obj const & as, vm_obj const & tmode, vm_obj const & _s) {
    tactic_state const & s = to_tactic_state(_s);
    try {
        metavar_context mctx   = s.mctx();
        type_context ctx       = mk_type_context_for(s, mctx, to_transparency_mode(tmode));
        buffer<bool> mask;
        buffer<expr> args;
        vm_obj it = as;
        while (!is_nil(it)) {
            vm_obj opt = head(it);
            if (is_none(opt)) {
                mask.push_back(false);
            } else {
                mask.push_back(true);
                args.push_back(to_expr(get_some_value(opt)));
            }
            it = tail(it);
        }
        expr r = mk_app(ctx, to_name(c), mask.size(), mask.data(), args.data());
        return mk_tactic_success(to_obj(r), s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

void initialize_app_builder_tactics() {
    DECLARE_VM_BUILTIN(name({"tactic", "mk_app_core"}),   tactic_mk_app_core);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_mapp_core"}),  tactic_mk_mapp_core);
}

void finalize_app_builder_tactics() {
}
}
