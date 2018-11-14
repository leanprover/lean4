/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <vector>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#ifdef _MSC_VER
#include <direct.h>
#define getcwd _getcwd
#define PATH_MAX _MAX_PATH
#else
#include <unistd.h>
#endif
#ifdef __linux__
#include <linux/limits.h>
#endif
#include <util/unit.h>
#include "runtime/sstream.h"
#include "library/handle.h"
#include "library/io_state.h"
#include "library/constants.h"
#include "library/process.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_io.h"

namespace lean {
static vm_obj const REAL_WORLD = mk_vm_simple(0);

vm_obj mk_io_result(vm_obj const & r) {
    return mk_vm_constructor(0, r, REAL_WORLD);
}

vm_obj get_io_result(vm_obj const & r) {
    return cfield(r, 0);
}

vm_obj run_io(vm_obj const & act) {
    auto r = invoke(act, REAL_WORLD);
    return cfield(r, 0);
}

vm_obj mk_ioe_result(vm_obj const & r) {
    return mk_io_result(mk_vm_constructor(1, r));
}

vm_obj mk_ioe_failure(vm_obj const & e) {
    return mk_io_result(mk_vm_constructor(0, e));
}

vm_obj mk_ioe_failure(std::string const & s) {
    return mk_ioe_failure(to_obj(s));
}

vm_obj mk_ioe_failure(sstream const & s) {
    return mk_ioe_failure(s.str());
}

static vm_obj io_put_str(vm_obj const & str, vm_obj const &) {
    if ((get_global_ios().get_regular_stream() << to_string(str)).bad())
        return mk_ioe_failure("io.put_str failed");
    else
        return mk_ioe_result(mk_vm_unit());
}

static vm_obj io_get_line(vm_obj const &) {
    if (get_global_ios().get_options().get_bool("server"))
        return mk_ioe_failure("io.get_line: cannot read from stdin in server mode");
    std::string str;
    std::getline(std::cin, str);
    if (std::cin.bad())
        return mk_ioe_failure("io.get_line failed");
    else
        return mk_ioe_result(to_obj(str));
}

struct vm_handle : public vm_external {
    handle_ref m_handle;
    vm_handle(handle_ref const & h):m_handle(h) {}
    vm_handle(handle_ref && h):m_handle(std::move(h)) {}
    virtual ~vm_handle() {}
    virtual void dealloc() override { delete this; }
    virtual vm_external * clone(vm_clone_fn const &) override { return new vm_handle(m_handle); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { lean_unreachable(); }
};

static handle_ref const & to_handle(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_handle*>(to_external(o)));
    return static_cast<vm_handle*>(to_external(o))->m_handle;
}

static vm_obj to_obj(handle_ref && h) {
    return mk_vm_external(new vm_handle(std::move(h)));
}

/*
struct vm_child : public vm_external {
    std::shared_ptr<child> m_child;
    vm_child(std::shared_ptr<child> && h):m_child(std::move(h)) {}
    vm_child(std::shared_ptr<child> const & h):m_child(h) {}
    virtual ~vm_child() {}
    virtual void dealloc() override { delete this; }
    virtual vm_external * clone(vm_clone_fn const &) override { return new vm_child(m_child); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { lean_unreachable(); }
};

std::shared_ptr<child> const & to_child(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_child*>(to_external(o)));
    return static_cast<vm_child*>(to_external(o))->m_child;
}

static vm_obj to_obj(std::shared_ptr<child> && h) {
    return mk_vm_external(new vm_child(std::move(h)));
}
*/

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

/* (mk_file_handle : string → io.mode → bool → ioe handle) */
static vm_obj fs_mk_file_handle(vm_obj const & fname, vm_obj const & m, vm_obj const & bin, vm_obj const &) {
    FILE * h = fopen(to_string(fname).c_str(), to_c_io_mode(m, bin));
    if (h != nullptr)
        return mk_ioe_result(to_obj(std::make_shared<handle>(h)));
    else
        return mk_ioe_failure(sstream() << "failed to open file '" << to_string(fname) << "'");
}

static vm_obj mk_handle_has_been_closed_error() {
    return mk_ioe_failure("invalid io action, handle has been closed");
}

static vm_obj fs_is_eof(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);
    if (href->is_closed()) return mk_handle_has_been_closed_error();
    bool r = feof(href->m_file) != 0;
    return mk_ioe_result(mk_vm_bool(r));
}

static vm_obj fs_flush(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);

    if (href->is_closed()) {
        return mk_handle_has_been_closed_error();
    }

    try {
        href->flush();
        return mk_ioe_result(mk_vm_unit());
    } catch (handle_exception e) {
        return mk_ioe_failure("flush failed");
    }
}

static vm_obj fs_close(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);

    if (href->is_closed()) {
        return mk_handle_has_been_closed_error();
    }

    if (href->is_stdin())
        return mk_ioe_failure("close failed, stdin cannot be closed");
    if (href->is_stdout())
        return mk_ioe_failure("close failed, stdout cannot be closed");
    if (href->is_stderr())
        return mk_ioe_failure("close failed, stderr cannot be closed");

    try {
        href->close();
        return mk_ioe_result(mk_vm_unit());
    } catch (handle_exception e) {
        return mk_ioe_failure("close failed");
    }
}

static vm_obj fs_read(vm_obj const & h, vm_obj const & n, vm_obj const &) {
    handle_ref const & href = to_handle(h);
    if (href->is_closed()) return mk_handle_has_been_closed_error();
    buffer<char> tmp;
    unsigned num = force_to_unsigned(n); /* TODO(Leo): handle size_t */
    tmp.resize(num, 0);
    size_t sz = fread(tmp.data(), 1, num, href->m_file);
    if (ferror(href->m_file)) {
        clearerr(href->m_file);
        return mk_ioe_failure("read failed");
    }
    return mk_ioe_result(to_obj(std::string(tmp.data(), sz)));
}

static vm_obj fs_write(vm_obj const & h, vm_obj const & b, vm_obj const &) {
    handle_ref const & href = to_handle(h);

    if (href->is_closed()) {
        return mk_handle_has_been_closed_error();
    }

    try {
        href->write(to_string(b));
        return mk_ioe_result(mk_vm_unit());
    } catch (handle_exception e) {
        return mk_ioe_failure("write failed");
    }
}

static vm_obj fs_get_line(vm_obj const & h, vm_obj const &) {
    handle_ref const & href = to_handle(h);

    if (href->is_closed()) {
        return mk_handle_has_been_closed_error();
    }

    std::string r;
    while (true) {
        int c = fgetc(href->m_file);
        if (ferror(href->m_file)) {
            clearerr(href->m_file);
            return mk_ioe_failure("get_line failed");
        }
        if (c == EOF)
            break;
        r.push_back(static_cast<char>(c));
        if (c == '\n')
            break;
    }
    return mk_ioe_result(to_obj(r));
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
stdio to_stdio(vm_obj const & o) {
    switch (cidx(o)) {
    case 0:
        return stdio::PIPED;
    case 1:
        return stdio::INHERIT;
    case 2:
        return stdio::NUL;
    default:
        lean_unreachable()
    }
}

static vm_obj io_process_wait(vm_obj const & ch, vm_obj const &) {
    return mk_io_result(mk_vm_nat(to_child(ch)->wait()));
}
*/

/*
static vm_obj io_get_env(vm_obj const & k, vm_obj const &) {
    if (auto v = getenv(to_string(k).c_str())) {
        return mk_io_result(mk_vm_some(to_obj(std::string(v))));
    } else {
        return mk_io_result(mk_vm_none());
    }
}

static vm_obj io_get_cwd(vm_obj const &) {
    char buffer[PATH_MAX];
    auto cwd = getcwd(buffer, sizeof(buffer));
    if (cwd) {
        return mk_io_result(to_obj(std::string(cwd)));
    } else {
        return mk_ioe_failure("get_cwd failed");
    }
}

static vm_obj io_set_cwd(vm_obj const & cwd, vm_obj const &) {
    if (chdir(to_string(cwd).c_str()) == 0) {
        return mk_io_result(mk_vm_unit());
    } else {
        return mk_ioe_failure("set_cwd failed");
    }
}
*/

static std::vector<std::string> * g_cmdline_args = nullptr;

static vm_obj to_list(buffer<vm_obj> const & ls) {
    vm_obj obj = mk_vm_simple(0);
    for (unsigned i = ls.size(); i > 0; i--)
        obj = mk_vm_constructor(1, ls[i - 1], obj);
    return obj;
}

static vm_obj io_cmdline_args() {
    buffer<vm_obj> objs;
    for (auto & s : *g_cmdline_args) objs.push_back(to_obj(s));
    return to_list(objs);
}

void set_io_cmdline_args(std::vector<std::string> const & args) {
    *g_cmdline_args = args;
}

optional<vm_obj> is_ioe_result(vm_obj const & o) {
    auto r = cfield(o, 0);
    if (cidx(o) == 0)
        return some(cfield(o, 0));
    else
        return optional<vm_obj>();
}

optional<vm_obj> is_ioe_error(vm_obj const & o) {
    auto r = cfield(o, 0);
    if (cidx(o) == 1)
        return some(cfield(o, 0));
    else
        return optional<vm_obj>();
}

/*
MK_THREAD_LOCAL_GET_DEF(vm_obj, get_rand_gen);

vm_obj io_set_rand_gen(vm_obj const & g, vm_obj const &) {
    get_rand_gen() = g;
    return mk_io_result(mk_vm_unit());
}

vm_obj io_rand(vm_obj const & lo, vm_obj const & hi, vm_obj const &) {
    vm_obj & gen = get_rand_gen();
    if (is_simple(gen)) {
        if (optional<unsigned> lo1 = try_to_unsigned(lo)) {
            if (optional<unsigned> hi1 = try_to_unsigned(hi)) {
                unsigned r = 0;
                if (*lo1 < *hi1) {
                    r = *lo1 + (std::rand() % (*hi1 - *lo1)); // NOLINT
                }
                return mk_io_result(mk_vm_nat(r));
            }
        }
        mpz const & lo1 = vm_nat_to_mpz1(lo);
        mpz const & hi1 = vm_nat_to_mpz2(hi);
        mpz r(0);
        if (lo1 < hi1) {
            r = lo1 + (mpz(std::rand()) % (hi1 - lo1)); // NOLINT
        }
        return mk_io_result(mk_vm_nat(r));
    } else {
        return mk_ioe_failure("not implemented yet, io_rand_nat primitive has been deleted");
    }
}
*/

void initialize_vm_io() {
    DECLARE_VM_BUILTIN(name({"io", "prim", "put_str"}), io_put_str);
    DECLARE_VM_BUILTIN(name({"io", "prim", "get_line"}), io_get_line);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "mk"}), fs_mk_file_handle);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "is_eof"}), fs_is_eof);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "flush"}), fs_flush);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "close"}), fs_close);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "read"}), fs_read);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "write"}), fs_write);
    DECLARE_VM_BUILTIN(name({"io", "prim", "handle", "get_line"}), fs_get_line);
    DECLARE_VM_BUILTIN(name({"io", "stdin"}), fs_stdin);
    DECLARE_VM_BUILTIN(name({"io", "stdout"}), fs_stdout);
    DECLARE_VM_BUILTIN(name({"io", "stderr"}), fs_stderr);
    DECLARE_VM_BUILTIN(name({"io", "cmdline_args"}), io_cmdline_args);
    g_cmdline_args = new std::vector<std::string>();
}

void finalize_vm_io() {
    delete g_cmdline_args;
}
}
