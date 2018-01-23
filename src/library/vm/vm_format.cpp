/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/sexpr/format.h"
#include "library/trace.h"
#include "library/parray.h"
#include "kernel/scope_pos_info_provider.h"
#include "library/vm/vm.h"
#include "library/vm/vm_array.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_options.h"

namespace lean {
struct vm_format : public vm_external {
    format m_val;
    vm_format(format const & v):m_val(v) {}
    virtual ~vm_format() {}
    virtual void dealloc() override { this->~vm_format(); get_vm_allocator().deallocate(sizeof(vm_format), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_format(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_format))) vm_format(m_val); }
};

bool is_format(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_format*>(to_external(o));
}

format const & to_format(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_format*>(to_external(o)));
    return static_cast<vm_format*>(to_external(o))->m_val;
}

vm_obj to_obj(format const & n) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_format))) vm_format(n));
}

vm_obj format_line() {
    return to_obj(line());
}

vm_obj format_space() {
    return to_obj(space());
}

vm_obj format_nil() {
    return to_obj(format());
}

vm_obj format_compose(vm_obj const & fmt1, vm_obj const & fmt2) {
    return to_obj(compose(to_format(fmt1), to_format(fmt2)));
}

vm_obj format_nest(vm_obj const & i, vm_obj const & fmt) {
    return to_obj(nest(to_unsigned(i), to_format(fmt)));
}

vm_obj format_highlight(vm_obj const & fmt, vm_obj const & c) {
    return to_obj(highlight(to_format(fmt), static_cast<format::format_color>(cidx(c))));
}

vm_obj format_group(vm_obj const & fmt) {
    return to_obj(group(to_format(fmt)));
}

vm_obj format_of_string(vm_obj const & s) {
    return to_obj(format(to_string(s)));
}

vm_obj format_of_nat(vm_obj const & n) {
    if (is_simple(n))
        return to_obj(format(cidx(n)));
    else
        return to_obj(format(to_mpz(n).to_string()));
}

vm_obj format_flatten(vm_obj const & fmt) {
    return to_obj(flatten(to_format(fmt)));
}

vm_obj format_to_string(vm_obj const & fmt, vm_obj const & opts) {
    std::ostringstream out;
    out << mk_pair(to_format(fmt), to_options(opts));
    return to_obj(out.str());
}

/* TODO(jroesch): unify with IO */
static vm_obj mk_buffer(parray<vm_obj> const & a) {
    return mk_vm_pair(mk_vm_nat(a.size()), to_obj(a));
}

vm_obj format_to_buffer(vm_obj const & fmt, vm_obj const & opts) {
    std::ostringstream out;
    out << mk_pair(to_format(fmt), to_options(opts));

    // TODO(jroesch): make this more performant?
    auto fmt_string = out.str();
    parray<vm_obj> buffer;

    for (auto c : out.str()) {
        buffer.push_back(mk_vm_simple(c));
    }

    return mk_buffer(buffer);
}

vm_obj format_print_using(vm_obj const & fmt, vm_obj const & opts, vm_obj const & /* state */) {
    get_global_ios().get_regular_stream() << mk_pair(to_format(fmt), to_options(opts));
    return mk_io_result(mk_vm_unit());
}

vm_obj format_of_options(vm_obj const & opts) {
    return to_obj(pp(to_options(opts)));
}

vm_obj format_is_nil(vm_obj const & fmt) {
    return mk_vm_bool(to_format(fmt).is_nil_fmt());
}

vm_obj trace_fmt(vm_obj const &, vm_obj const & fmt, vm_obj const & fn) {
    tout() << to_format(fmt) << "\n";
    return invoke(fn, mk_vm_unit());
}

vm_obj scope_trace(vm_obj const &, vm_obj const & line, vm_obj const & col, vm_obj const & fn) {
    pos_info_provider * pip = get_pos_info_provider();
    if (pip) {
        scope_traces_as_messages traces_as_messages(pip->get_file_name(), pos_info(force_to_unsigned(line), force_to_unsigned(col)));
        return invoke(fn, mk_vm_unit());
    } else {
        return invoke(fn, mk_vm_unit());
    }
}

struct vm_format_thunk : public vm_external {
    std::function<format()> m_val;
    vm_format_thunk(std::function<format()> const & fn):m_val(fn) {}
    virtual ~vm_format_thunk() {}
    virtual void dealloc() override { this->~vm_format_thunk(); get_vm_allocator().deallocate(sizeof(vm_format_thunk), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_format_thunk(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_format_thunk))) vm_format_thunk(m_val); }
};

std::function<format()> const & to_format_thunk(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_format_thunk*>(to_external(o)));
    return static_cast<vm_format_thunk*>(to_external(o))->m_val;
}

vm_obj to_obj(std::function<format()> const & fn) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_format_thunk))) vm_format_thunk(fn));
}

static unsigned g_apply_format_thunk_idx = -1;

vm_obj mk_vm_format_thunk(std::function<format()> const & fn) {
    vm_obj t = to_obj(fn);
    return mk_vm_closure(g_apply_format_thunk_idx, 1, &t);
}

vm_obj apply_format_thunk(vm_obj const & t, vm_obj const & /* u */) {
    format f = to_format_thunk(t)();
    return to_obj(f);
}

void initialize_vm_format() {
    DECLARE_VM_BUILTIN(name({"format", "line"}),             format_line);
    DECLARE_VM_BUILTIN(name({"format", "space"}),            format_space);
    DECLARE_VM_BUILTIN(name({"format", "nil"}),              format_nil);
    DECLARE_VM_BUILTIN(name({"format", "compose"}),          format_compose);
    DECLARE_VM_BUILTIN(name({"format", "nest"}),             format_nest);
    DECLARE_VM_BUILTIN(name({"format", "highlight"}),        format_highlight);
    DECLARE_VM_BUILTIN(name({"format", "group"}),            format_group);
    DECLARE_VM_BUILTIN(name({"format", "of_string"}),        format_of_string);
    DECLARE_VM_BUILTIN(name({"format", "of_nat"}),           format_of_nat);
    DECLARE_VM_BUILTIN(name({"format", "flatten"}),          format_flatten);
    DECLARE_VM_BUILTIN(name({"format", "to_string"}),        format_to_string);
    DECLARE_VM_BUILTIN(name({"format", "to_buffer"}),        format_to_buffer);
    DECLARE_VM_BUILTIN(name({"format", "print_using"}),      format_print_using);
    DECLARE_VM_BUILTIN(name({"format", "of_options"}),       format_of_options);
    DECLARE_VM_BUILTIN(name({"format", "is_nil"}),           format_is_nil);
    DECLARE_VM_BUILTIN(name("trace_fmt"),                    trace_fmt);
    DECLARE_VM_BUILTIN(name("scope_trace"),                  scope_trace);
    DECLARE_VM_BUILTIN("_apply_format_thunk", apply_format_thunk);
}

void finalize_vm_format() {
}

void initialize_vm_format_builtin_idxs() {
    g_apply_format_thunk_idx = *get_vm_builtin_idx(name("_apply_format_thunk"));
}
}
