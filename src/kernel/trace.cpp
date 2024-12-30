/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include "util/io.h"
#include "util/option_declarations.h"
#include "library/elab_environment.h"
#include "kernel/local_ctx.h"
#include "kernel/trace.h"

namespace lean {
static name_set *            g_trace_classes = nullptr;
static name_map<name_set>  * g_trace_aliases = nullptr;
MK_THREAD_LOCAL_GET_DEF(std::vector<name>, get_enabled_trace_classes);
MK_THREAD_LOCAL_GET_DEF(std::vector<name>, get_disabled_trace_classes);
LEAN_THREAD_PTR(elab_environment,      g_env);
LEAN_THREAD_PTR(options,               g_opts);

void register_trace_class(name const & n, name const & decl_name) {
    register_option(name("trace") + n, decl_name, data_value_kind::Bool, "false",
                    "(trace) enable/disable tracing for the given module and submodules");
    g_trace_classes->insert(n);
}

void register_trace_class_alias(name const & n, name const & alias) {
    name_set new_s;
    if (auto s = g_trace_aliases->find(n))
        new_s = *s;
    new_s.insert(alias);
    g_trace_aliases->insert(n, new_s);
}

bool is_trace_enabled() {
    return !get_enabled_trace_classes().empty();
}

static void update_class(std::vector<name> & cs, name const & c) {
    if (std::find(cs.begin(), cs.end(), c) == cs.end()) {
        cs.push_back(c);
    }
}

static void enable_trace_class(name const & c) {
    update_class(get_enabled_trace_classes(), c);
}

static void disable_trace_class(name const & c) {
    update_class(get_disabled_trace_classes(), c);
}

static bool is_trace_class_set_core(std::vector<name> const & cs, name const & n) {
    for (name const & p : cs) {
        if (is_prefix_of(p, n)) {
            return true;
        }
    }
    return false;
}

static bool is_trace_class_set(std::vector<name> const & cs, name const & n) {
    if (is_trace_class_set_core(cs, n))
        return true;
    auto it = n;
    while (true) {
        if (auto s = g_trace_aliases->find(it)) {
            bool found = false;
            s->for_each([&](name const & alias) {
                    if (!found && is_trace_class_set_core(cs, alias))
                        found = true;
                });
            if (found)
                return true;
        }
        if (it.is_atomic())
            return false;
        it = it.get_prefix();
    }
}

bool is_trace_class_enabled(name const & n) {
    if (!is_trace_enabled())
        return false;
    if (is_trace_class_set(get_disabled_trace_classes(), n))
        return false; // it was explicitly disabled
    return is_trace_class_set(get_enabled_trace_classes(), n);
}


void scope_trace_env::init(elab_environment * env, options * opts) {
    m_enable_sz  = get_enabled_trace_classes().size();
    m_disable_sz = get_disabled_trace_classes().size();
    m_old_env    = g_env;
    m_old_opts   = g_opts;
    g_env        = env;
    name trace("trace");
    if (opts && g_opts != opts) {
        opts->for_each([&](name const & n) {
                if (is_prefix_of(trace, n)) {
                    name cls        = n.replace_prefix(trace, name());
                    if (opts->get_bool(n, false))
                        enable_trace_class(cls);
                    else
                        disable_trace_class(cls);
                }
            });
    }
    g_opts = opts;
}

scope_trace_env::scope_trace_env(elab_environment const & env, options const & o) {
    init(const_cast<elab_environment*>(&env), const_cast<options*>(&o));
}

scope_trace_env::~scope_trace_env() {
    g_env  = const_cast<elab_environment*>(m_old_env);
    g_opts = const_cast<options*>(m_old_opts);
    get_enabled_trace_classes().resize(m_enable_sz);
    get_disabled_trace_classes().resize(m_disable_sz);
}

extern "C" obj_res lean_io_eprint(obj_arg s, obj_arg w);
static void io_eprint(obj_arg s) {
    object * r = lean_io_eprint(s, lean_io_mk_world());
    if (!lean_io_result_is_ok(r))
        lean_io_result_show_error(r);
    lean_dec(r);
}

tout::~tout() {
    io_eprint(mk_string(m_out.str()));
}

std::ostream & operator<<(std::ostream & ios, tclass const & c) {
    ios << "[" << c.m_cls << "] ";
    return ios;
}

void initialize_trace() {
    g_trace_classes = new name_set();
    g_trace_aliases = new name_map<name_set>();

    register_trace_class(name{"debug"});
}

void finalize_trace() {
    delete g_trace_classes;
    delete g_trace_aliases;
}

/*
@[export lean_mk_metavar_ctx]
def mkMetavarContext : Unit → MetavarContext := fun _ => {}
*/
extern "C" lean_object* lean_mk_metavar_ctx(lean_object*);

/*
@[export lean_pp_expr]
def ppExprLegacy (env : Environment) (mctx : MetavarContext) (lctx : LocalContext) (opts : Options) (e : Expr) : IO Format :=
*/
extern "C" object * lean_pp_expr(object * env, object * mctx, object * lctx, object * opts, object * e, object * w);

/*
@[export lean_format_pretty]
def pretty (f : Format) (w : Nat := defWidth) (indent : Nat := 0) (column := 0) : String :=
*/
extern "C" object * lean_format_pretty(object * f, object * w, object * i, object * c);

std::string pp_expr(elab_environment const & env, options const & opts, local_ctx const & lctx, expr const & e) {
    options o = opts;
    // o = o.update(name{"pp", "proofs"}, true); --
    object_ref fmt = get_io_result<object_ref>(lean_pp_expr(env.to_obj_arg(), lean_mk_metavar_ctx(lean_box(0)), lctx.to_obj_arg(), o.to_obj_arg(),
                                                            e.to_obj_arg(), io_mk_world()));
    string_ref str(lean_format_pretty(fmt.to_obj_arg(), lean_unsigned_to_nat(80), lean_unsigned_to_nat(0), lean_unsigned_to_nat(0)));
    return str.to_std_string();
}

std::string pp_expr(elab_environment const & env, options const & opts, expr const & e) {
    local_ctx lctx;
    return pp_expr(env, opts, lctx, e);
}

std::string trace_pp_expr(expr const & e) {
    return pp_expr(*g_env, *g_opts, e);
}
}
