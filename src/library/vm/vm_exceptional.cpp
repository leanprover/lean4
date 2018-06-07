/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/kernel_exception.h"
#include "library/trace.h"
#include "library/vm/vm_exceptional.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_format.h"

namespace lean {
struct vm_throwable : public vm_external {
    std::exception_ptr m_val;
    vm_throwable(std::exception_ptr const & ex):m_val(ex) {}
    virtual ~vm_throwable() {}
    virtual void dealloc() override { delete this; }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_throwable(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new vm_throwable(m_val); }
};

std::exception_ptr const & to_throwable(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_throwable*>(to_external(o)));
    return static_cast<vm_throwable*>(to_external(o))->m_val;
}

vm_obj to_obj(std::exception_ptr const & ex) {
    return mk_vm_external(new vm_throwable(ex));
}

/** Implement two different signatures:
    1) throwable -> options -> format
    2) throwable -> unit -> format */
vm_obj throwable_to_format(vm_obj const & _ex, vm_obj const & _opts) {
    std::exception_ptr const & ex = to_throwable(_ex);
    if (!ex)
        return to_obj(format("null-exception"));

    try {
        std::rethrow_exception(ex);
    } catch (ext_exception & ex) {
        if (is_simple(_opts)) {
            io_state_stream ios = tout();
            formatter fmt = ios.get_formatter();
            return to_obj(ex.pp(fmt));
        } else {
            options opts = to_options(_opts);
            scope_trace_env scope1(opts);
            io_state_stream ios = tout();
            formatter fmt = ios.get_formatter();
            return to_obj(ex.pp(fmt));
        }
    } catch (formatted_exception & ex) {
        return to_obj(ex.pp());
    } catch (std::exception & ex) {
        return to_obj(format(ex.what()));
    } catch (...) {
        return to_obj(format("unknown-exception"));
    }
}

static unsigned g_throwable_to_format_fun_idx = -1;

unsigned get_throwable_to_format_fun_idx() {
    return g_throwable_to_format_fun_idx;
}

vm_obj mk_vm_exceptional_success(vm_obj const & a) {
    return mk_vm_constructor(0, a);
}

vm_obj mk_vm_exceptional_exception(std::exception_ptr const & ex) {
    vm_obj _ex = to_obj(ex);
    return mk_vm_constructor(1, mk_vm_closure(g_throwable_to_format_fun_idx, 1, &_ex));
}

void initialize_vm_exceptional() {
    DECLARE_VM_BUILTIN("_throwable_to_format", throwable_to_format);
}

void finalize_vm_exceptional() {
}

void initialize_vm_exceptional_builtin_idxs() {
    g_throwable_to_format_fun_idx = *get_vm_builtin_idx(name("_throwable_to_format"));
}
}
