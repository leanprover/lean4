/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "library/io_state.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {
vm_obj mk_io_result(vm_obj const & r) {
    return mk_vm_constructor(0, 1, &r);
}

vm_obj mk_io_failure(vm_obj const & e) {
    return mk_vm_constructor(1, 1, &e);
}

vm_obj mk_io_failure(std::string const & s) {
    return mk_io_failure(mk_vm_constructor(0, to_obj(s)));
}

static vm_obj io_put_str(vm_obj const & str, vm_obj const &) {
    get_global_ios().get_regular_stream() << to_string(str);
    return mk_io_result(mk_vm_unit());
}

static vm_obj io_get_line(vm_obj const &) {
    if (get_global_ios().get_options().get_bool("server"))
        throw exception("get_line: cannot read from stdin in server mode");
    std::string str;
    std::getline(std::cin, str);
    return mk_io_result(to_obj(str));
}

/*
structure io.terminal (m : Type → Type → Type) :=
(put_str     : string → m io.error unit)
(get_line    : m io.error string)
*/
static vm_obj mk_terminal() {
    vm_obj fields[2] = {
        mk_native_closure(io_put_str),
        mk_native_closure(io_get_line)
    };
    return mk_vm_constructor(0, 2, fields);
}

static vm_obj mk_not_implemented_yet() {
    return mk_io_failure("not implemented yet");
}

static vm_obj fs_mk_file_handle(vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const &) {
    return mk_not_implemented_yet();
}

static vm_obj fs_file_size(vm_obj const &, vm_obj const &) {
    return mk_not_implemented_yet();
}

static vm_obj fs_is_eof(vm_obj const &, vm_obj const &) {
    return mk_not_implemented_yet();
}

static vm_obj fs_look_ahead(vm_obj const &, vm_obj const &) {
    return mk_not_implemented_yet();
}

static vm_obj fs_flush(vm_obj const &, vm_obj const &) {
    return mk_not_implemented_yet();
}

static vm_obj fs_close(vm_obj const &, vm_obj const &) {
    return mk_not_implemented_yet();
}

static vm_obj fs_read(vm_obj const &, vm_obj const &, vm_obj const &) {
    return mk_not_implemented_yet();
}

static vm_obj fs_write(vm_obj const &, vm_obj const &, vm_obj const &) {
    return mk_not_implemented_yet();
}

static vm_obj fs_get_line(vm_obj const &, vm_obj const &) {
    return mk_not_implemented_yet();
}

/*
(handle         : Type)
(mk_file_handle : string → io.mode → bool → m io.error handle)
(file_size      : handle → m io.error nat)
(is_eof         : handle → m io.error bool)
(look_ahead     : handle → m io.error char)
(flush          : handle → m io.error unit)
(close          : handle → m io.error unit)
(read           : handle → nat → m io.error char_buffer)
(write          : handle → char_buffer → m io.error unit)
(get_line       : handle → m io.error char_buffer)
*/
static vm_obj mk_fs() {
    vm_obj fields[9] = {
        mk_native_closure(fs_mk_file_handle),
        mk_native_closure(fs_file_size),
        mk_native_closure(fs_is_eof),
        mk_native_closure(fs_look_ahead),
        mk_native_closure(fs_flush),
        mk_native_closure(fs_close),
        mk_native_closure(fs_read),
        mk_native_closure(fs_write),
        mk_native_closure(fs_get_line)
    };
    return mk_vm_constructor(0, 9, fields);
}

static vm_obj io_return(vm_obj const &, vm_obj const &, vm_obj const & a, vm_obj const &) {
    return mk_io_result(a);
}

static vm_obj io_bind(vm_obj const & /* e */, vm_obj const & /* α */, vm_obj const & /* β */, vm_obj const & a, vm_obj const & b, vm_obj const &) {
    vm_obj r = invoke(a, mk_vm_unit());
    if (cidx(r) == 0) {
        vm_obj v = cfield(r, 0);
        return invoke(b, v, mk_vm_unit());
    } else {
        return r;
    }
}

static vm_obj io_catch(vm_obj const &, vm_obj const &, vm_obj const &, vm_obj const & a, vm_obj const & b, vm_obj const &) {
    vm_obj r = invoke(a, mk_vm_unit());
    if (cidx(r) == 1) {
        vm_obj e = cfield(r, 0);
        return invoke(b, e, mk_vm_unit());
    } else {
        return r;
    }
}

static vm_obj io_fail(vm_obj const &, vm_obj const &, vm_obj const & e, vm_obj const &) {
    return mk_io_failure(e);
}

static vm_obj io_m(vm_obj const &, vm_obj const &) {
    return mk_vm_simple(0);
}

/*
structure io.interface :=
(m        : Type → Type → Type)
(return   : ∀ e α, α → m e α)
(bind     : ∀ e α β, m e α → (α → m e β) → m e β)
(catch    : ∀ e₁ e₂ α, m e₁ α → (e₁ → m e₂ α) → m e₂ α)
(fail     : ∀ e α, e → m e α)
(term     : io.terminal m)
(fs       : io.file_system m)
*/
vm_obj mk_io_interface() {
    vm_obj fields[7] = {
        mk_native_closure(io_m), /* TODO(Leo): delete after we improve code generator */
        mk_native_closure(io_return),
        mk_native_closure(io_bind),
        mk_native_closure(io_catch),
        mk_native_closure(io_fail),
        mk_terminal(),
        mk_fs()
    };
    return mk_vm_constructor(0, 7, fields);
}

optional<vm_obj> is_io_result(vm_obj const & o) {
    if (cidx(o) == 0)
        return some(cfield(o, 0));
    else
        return optional<vm_obj>();
}

optional<vm_obj> is_io_error(vm_obj const & o) {
    if (cidx(o) == 1)
        return some(cfield(o, 0));
    else
        return optional<vm_obj>();
}

/*
inductive io.error
| other     : string → io.error
| sys       : nat → io.error
| primitive : io.error_kind → io.error
*/
std::string io_error_to_string(vm_obj const & o) {
    if (cidx(o) == 0) {
        return to_string(cfield(o, 0));
    } else if (cidx(o) == 1) {
        return (sstream() << "system error #" << to_unsigned(cfield(o, 0))).str();
    } else {
        /*
          inductive io.error_kind
          | not_found | permission_denied | connection_refused
          | connection_reset | connection_aborted | not_connected
          | addr_in_use | addr_not_available | broken_pipe
          | already_exists | would_block | invalid_input
          | invalid_data | timeout | write_zero | interrupted
          | unexpected_eof
        */
        /* TODO(Leo): return string describing the errors above */
        return (sstream() << "primitive error #" << to_unsigned(cfield(o, 0))).str();
    }
}

void initialize_vm_io() {
}

void finalize_vm_io() {
}
}
