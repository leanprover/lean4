/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <cstdio>
#include <iostream>
#include "util/sstream.h"
#include "library/io_state.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_array.h"
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

vm_obj mk_io_failure(sstream const & s) {
    return mk_io_failure(mk_vm_constructor(0, to_obj(s.str())));
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

struct handle {
    FILE * m_handle;
    handle(FILE * h):m_handle(h) {}
    ~handle() { if (m_handle && m_handle != stdin && m_handle != stderr && m_handle != stdout) fclose(m_handle); }
};

typedef std::shared_ptr<handle> handle_ref;

struct vm_handle : public vm_external {
    handle_ref m_handle;
    vm_handle(handle_ref const & h):m_handle(h) {}
    virtual ~vm_handle() {}
    virtual void dealloc() override { this->~vm_handle(); get_vm_allocator().deallocate(sizeof(vm_handle), this); }
    virtual vm_external * clone(vm_clone_fn const &) override { throw exception("handle objects cannot be cloned"); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { throw exception("handle objects cannot be cloned"); }
};

bool is_handle(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_handle*>(to_external(o));
}

handle_ref const & to_handle(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_handle*>(to_external(o)));
    return static_cast<vm_handle*>(to_external(o))->m_handle;
}

vm_obj to_obj(handle_ref const & h) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_handle))) vm_handle(h));
}

/*
inductive io.mode
| read | write | read_write | append
*/
char const * to_c_io_mode(vm_obj const & mode, vm_obj const & bin) {
    bool is_bin = to_bool(bin);
    switch (cidx(mode)) {
    case 0: return is_bin ? "rb" : "r";
    case 1: return is_bin ? "wb" : "w";
    case 2: return is_bin ? "r+b" : "r+";
    case 3: return is_bin ? "ab" : "a";
    }
    lean_vm_check(false);
    lean_unreachable();
}

/* (mk_file_handle : string → io.mode → bool → m io.error handle) */
static vm_obj fs_mk_file_handle(vm_obj const & fname, vm_obj const & m, vm_obj const & bin, vm_obj const &) {
    FILE * h = fopen(to_string(fname).c_str(), to_c_io_mode(m, bin));
    if (h != nullptr)
        return mk_io_result(to_obj(std::make_shared<handle>(h)));
    else
        return mk_io_failure(sstream() << "failed to open file '" << to_string(fname) << "'");
}

static vm_obj mk_handle_has_been_closed_error() {
    return mk_io_failure("invalid io action, handle has been closed");
}

static bool has_been_closed(handle_ref const & href) {
    return href->m_handle == nullptr;
}

static vm_obj fs_is_eof(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);
    if (has_been_closed(href)) return mk_handle_has_been_closed_error();
    bool r = feof(href->m_handle) != 0;
    return mk_io_result(mk_vm_bool(r));
}

static vm_obj fs_flush(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);
    if (has_been_closed(href)) return mk_handle_has_been_closed_error();
    if (fflush(href->m_handle) == 0) {
        return mk_io_result(mk_vm_unit());
    } else {
        clearerr(href->m_handle);
        return mk_io_failure("flush failed");
    }
}

static vm_obj fs_close(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);
    if (has_been_closed(href)) return mk_handle_has_been_closed_error();
    if (href->m_handle == stdin)
        return mk_io_failure("close failed, stdin cannot be closed");
    if (href->m_handle == stdout)
        return mk_io_failure("close failed, stdout cannot be closed");
    if (href->m_handle == stderr)
        return mk_io_failure("close failed, stderr cannot be closed");
    if (fclose(href->m_handle) == 0) {
        href->m_handle = nullptr;
        return mk_io_result(mk_vm_unit());
    } else {
        clearerr(href->m_handle);
        return mk_io_failure("close failed");
    }
}

static vm_obj mk_buffer(parray<vm_obj> const & a) {
    return mk_vm_pair(mk_vm_nat(a.size()), to_obj(a));
}

static vm_obj fs_read(vm_obj const & h, vm_obj const & n, vm_obj const &) {
    handle_ref const & href = to_handle(h);
    if (has_been_closed(href)) return mk_handle_has_been_closed_error();
    buffer<char> tmp;
    unsigned num = force_to_unsigned(n); /* TODO(Leo): handle size_t */
    tmp.resize(num, 0);
    size_t sz = fread(tmp.data(), 1, num, href->m_handle);
    if (ferror(href->m_handle)) {
        clearerr(href->m_handle);
        return mk_io_failure("read failed");
    }
    parray<vm_obj> r;
    for (size_t i = 0; i < sz; i++) {
        r.push_back(mk_vm_simple(static_cast<unsigned char>(tmp[i])));
    }
    return mk_io_result(mk_buffer(r));
}

static vm_obj fs_write(vm_obj const & h, vm_obj const & b, vm_obj const &) {
    handle_ref const & href = to_handle(h);
    if (has_been_closed(href)) return mk_handle_has_been_closed_error();
    buffer<char> tmp;
    parray<vm_obj> const & a = to_array(cfield(b, 1));
    unsigned sz = a.size();
    for (unsigned i = 0; i < sz; i++) {
        tmp.push_back(static_cast<unsigned char>(cidx(a[i])));
    }
    if (fwrite(tmp.data(), 1, sz, href->m_handle) != sz) {
        clearerr(href->m_handle);
        return mk_io_failure("write failed");
    }
    return mk_io_result(mk_vm_unit());
}

static vm_obj fs_get_line(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);
    if (has_been_closed(href)) return mk_handle_has_been_closed_error();
    parray<vm_obj> r;
    while (true) {
        int c = fgetc(href->m_handle);
        if (ferror(href->m_handle)) {
            clearerr(href->m_handle);
            return mk_io_failure("get_line failed");
        }
        if (c == EOF)
            break;
        r.push_back(mk_vm_simple(static_cast<unsigned char>(static_cast<char>(c))));
        if (c == '\n')
            break;
    }
    return mk_io_result(mk_buffer(r));
}

static vm_obj fs_read_file(vm_obj const & fname, vm_obj const & bin, vm_obj const &) {
    FILE * h = fopen(to_string(fname).c_str(), to_bool(bin) ? "rb" : "r");
    if (h == nullptr)
        return mk_io_failure(sstream() << "read_file '" << to_string(fname) << "' failed");
#define BUFFER_SIZE 1024
    buffer<char, BUFFER_SIZE> tmp;
    tmp.resize(BUFFER_SIZE);
    parray<vm_obj> r;
    while (true) {
        unsigned sz = fread(tmp.data(), 1, BUFFER_SIZE, h);
        for (unsigned i = 0; i < sz; i++) {
            r.push_back(mk_vm_simple(static_cast<unsigned char>(tmp[i])));
        }
        if (sz < BUFFER_SIZE) {
            if (ferror(h)) {
                clearerr(h);
                fclose(h);
                return mk_io_failure(sstream() << "read_file '" << to_string(fname) << "' failed");
            }
            fclose(h);
            return mk_io_result(mk_buffer(r));
        }
    }
}

static vm_obj fs_stdin(vm_obj const &) {
    return mk_io_result(to_obj(std::make_shared<handle>(stdin)));
}

static vm_obj fs_stdout(vm_obj const &) {
    return mk_io_result(to_obj(std::make_shared<handle>(stdout)));
}

static vm_obj fs_stderr(vm_obj const &) {
    return mk_io_result(to_obj(std::make_shared<handle>(stderr)));
}

/*
(handle         : Type)
(read_file      : string → bool → m io.error char_buffer)
(mk_file_handle : string → io.mode → bool → m io.error handle)
(is_eof         : handle → m io.error bool)
(flush          : handle → m io.error unit)
(close          : handle → m io.error unit)
(read           : handle → nat → m io.error char_buffer)
(write          : handle → char_buffer → m io.error unit)
(get_line       : handle → m io.error char_buffer)
(stdin          : m io.error handle)
(stdout         : m io.error handle)
(stderr         : m io.error handle)
*/
static vm_obj mk_fs() {
    vm_obj fields[11] = {
        mk_native_closure(fs_read_file),
        mk_native_closure(fs_mk_file_handle),
        mk_native_closure(fs_is_eof),
        mk_native_closure(fs_flush),
        mk_native_closure(fs_close),
        mk_native_closure(fs_read),
        mk_native_closure(fs_write),
        mk_native_closure(fs_get_line),
        mk_native_closure(fs_stdin),
        mk_native_closure(fs_stdout),
        mk_native_closure(fs_stderr)
    };
    return mk_vm_constructor(0, 11, fields);
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

static vm_obj io_monad(vm_obj const &, vm_obj const &) {
    return get_vm_state().invoke(get_unsafe_monad_from_pure_bind_name(),
                                 {mk_vm_simple(0), mk_native_closure(io_return), mk_native_closure(io_bind)});
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
(monad    : Π e, monad (m e))
(catch    : ∀ e₁ e₂ α, m e₁ α → (e₁ → m e₂ α) → m e₂ α)
(fail     : ∀ e α, e → m e α)
(term     : io.terminal m)
(fs       : io.file_system m)
*/
vm_obj mk_io_interface() {
    vm_obj fields[6] = {
        mk_native_closure(io_m), /* TODO(Leo): delete after we improve code generator */
        mk_native_closure(io_monad),
        mk_native_closure(io_catch),
        mk_native_closure(io_fail),
        mk_terminal(),
        mk_fs()
    };
    return mk_vm_constructor(0, 6, fields);
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
*/
std::string io_error_to_string(vm_obj const & o) {
    if (cidx(o) == 0) {
        return to_string(cfield(o, 0));
    } else if (cidx(o) == 1) {
        return (sstream() << "system error #" << to_unsigned(cfield(o, 0))).str();
    }
    lean_vm_check(false);
    lean_unreachable();
}

void initialize_vm_io() {
}

void finalize_vm_io() {
}
}
