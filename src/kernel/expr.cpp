/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include <vector>
#include <sstream>
#include <string>
#include <algorithm>
#include <limits>
#include "util/list_fn.h"
#include "util/hash.h"
#include "util/buffer.h"
#include "util/object_serializer.h"
#include "util/lru_cache.h"
#include "util/memory_pool.h"
#include "kernel/expr.h"
#include "kernel/expr_eq_fn.h"
#include "kernel/free_vars.h"

#ifndef LEAN_INITIAL_EXPR_CACHE_CAPACITY
#define LEAN_INITIAL_EXPR_CACHE_CAPACITY 1024*16
#endif

namespace lean {
static expr g_dummy(mk_var(0));
expr::expr():expr(g_dummy) {}

unsigned hash_levels(levels const & ls) {
    unsigned r = 23;
    for (auto const & l : ls)
        r = hash(hash(l), r);
    return r;
}

MK_THREAD_LOCAL_GET(unsigned, get_hash_alloc_counter, 0)

expr_cell::expr_cell(expr_kind k, unsigned h, bool has_expr_mv, bool has_univ_mv, bool has_local, bool has_param_univ):
    m_flags(0),
    m_kind(static_cast<unsigned>(k)),
    m_has_expr_mv(has_expr_mv),
    m_has_univ_mv(has_univ_mv),
    m_has_local(has_local),
    m_has_param_univ(has_param_univ),
    m_hash(h),
    m_tag(nulltag),
    m_rc(0) {
    // m_hash_alloc does not need to be a unique identifier.
    // We want diverse hash codes because given expr_cell * c1 and expr_cell * c2,
    // if c1 != c2, then there is high probability c1->m_hash_alloc != c2->m_hash_alloc.
    // Remark: using pointer address as a hash code is not a good idea.
    //    - each execution run will behave differently.
    //    - the hash is not diverse enough
    m_hash_alloc = get_hash_alloc_counter();
    get_hash_alloc_counter()++;
}

void expr_cell::dec_ref(expr & e, buffer<expr_cell*> & todelete) {
    if (e.m_ptr) {
        expr_cell * c = e.steal_ptr();
        lean_assert(!(e.m_ptr));
        if (c->dec_ref_core())
            todelete.push_back(c);
    }
}

optional<bool> expr_cell::is_arrow() const {
    // it is stored in bits 0-1
    unsigned r = (m_flags & (1+2));
    if (r == 0) {
        return optional<bool>();
    } else if (r == 1) {
        return optional<bool>(true);
    } else {
        lean_assert(r == 2);
        return optional<bool>(false);
    }
}

void expr_cell::set_is_arrow(bool flag) {
    unsigned mask = flag ? 1 : 2;
    m_flags |= mask;
    lean_assert(is_arrow() && *is_arrow() == flag);
}

void expr_cell::set_tag(tag t) {
    m_tag = t;
}

bool is_meta(expr const & e) {
    return is_metavar(get_app_fn(e));
}

// Expr variables
typedef memory_pool<sizeof(expr_var)> var_allocator;
MK_THREAD_LOCAL_GET_DEF(var_allocator, get_var_allocator);
expr_var::expr_var(unsigned idx):
    expr_cell(expr_kind::Var, idx, false, false, false, false),
    m_vidx(idx) {
    if (idx == std::numeric_limits<unsigned>::max())
        throw exception("invalid free variable index, de Bruijn index is too big");
}
void expr_var::dealloc() {
    this->~expr_var();
    get_var_allocator().recyle(this);
}

// Expr constants
typedef memory_pool<sizeof(expr_const)> const_allocator;
MK_THREAD_LOCAL_GET_DEF(const_allocator, get_const_allocator);
expr_const::expr_const(name const & n, levels const & ls):
    expr_cell(expr_kind::Constant, ::lean::hash(n.hash(), hash_levels(ls)), false, has_meta(ls), false, has_param(ls)),
    m_name(n),
    m_levels(ls) {
}
void expr_const::dealloc() {
    this->~expr_const();
    get_const_allocator().recyle(this);
}

// Expr metavariables and local variables
typedef memory_pool<sizeof(expr_mlocal)> mlocal_allocator;
MK_THREAD_LOCAL_GET_DEF(mlocal_allocator, get_mlocal_allocator);
expr_mlocal::expr_mlocal(bool is_meta, name const & n, expr const & t):
    expr_composite(is_meta ? expr_kind::Meta : expr_kind::Local, n.hash(), is_meta || t.has_expr_metavar(), t.has_univ_metavar(),
                   !is_meta || t.has_local(), t.has_param_univ(),
                   1, get_free_var_range(t)),
    m_name(n),
    m_type(t) {}
void expr_mlocal::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_type, todelete);
    this->~expr_mlocal();
    get_mlocal_allocator().recyle(this);
}

typedef memory_pool<sizeof(expr_local)> local_allocator;
MK_THREAD_LOCAL_GET_DEF(local_allocator, get_local_allocator);
expr_local::expr_local(name const & n, name const & pp_name, expr const & t, binder_info const & bi):
    expr_mlocal(false, n, t),
    m_pp_name(pp_name),
    m_bi(bi) {}
void expr_local::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_type, todelete);
    this->~expr_local();
    get_local_allocator().recyle(this);
}

// Composite expressions
expr_composite::expr_composite(expr_kind k, unsigned h, bool has_expr_mv, bool has_univ_mv,
                               bool has_local, bool has_param_univ, unsigned d, unsigned fv_range):
    expr_cell(k, h, has_expr_mv, has_univ_mv, has_local, has_param_univ),
    m_depth(d),
    m_free_var_range(fv_range) {}

// Expr applications
typedef memory_pool<sizeof(expr_app)> app_allocator;
MK_THREAD_LOCAL_GET_DEF(app_allocator, get_app_allocator);
expr_app::expr_app(expr const & fn, expr const & arg):
    expr_composite(expr_kind::App, ::lean::hash(fn.hash(), arg.hash()),
                   fn.has_expr_metavar() || arg.has_expr_metavar(),
                   fn.has_univ_metavar() || arg.has_univ_metavar(),
                   fn.has_local()        || arg.has_local(),
                   fn.has_param_univ()   || arg.has_param_univ(),
                   std::max(get_depth(fn), get_depth(arg)) + 1,
                   std::max(get_free_var_range(fn), get_free_var_range(arg))),
    m_fn(fn), m_arg(arg) {
    m_hash = ::lean::hash(m_hash, m_depth);
}
void expr_app::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_fn, todelete);
    dec_ref(m_arg, todelete);
    this->~expr_app();
    get_app_allocator().recyle(this);
}

static unsigned dec(unsigned k) { return k == 0 ? 0 : k - 1; }

bool operator==(binder_info const & i1, binder_info const & i2) {
    return
        i1.is_implicit() == i2.is_implicit() &&
        i1.is_cast() == i2.is_cast() &&
        i1.is_contextual() == i2.is_contextual() &&
        i1.is_strict_implicit() == i2.is_strict_implicit();
}

// Expr binders (Lambda, Pi)
typedef memory_pool<sizeof(expr_binding)> binding_allocator;
MK_THREAD_LOCAL_GET_DEF(binding_allocator, get_binding_allocator);
expr_binding::expr_binding(expr_kind k, name const & n, expr const & t, expr const & b, binder_info const & i):
    expr_composite(k, ::lean::hash(t.hash(), b.hash()),
                   t.has_expr_metavar()   || b.has_expr_metavar(),
                   t.has_univ_metavar()   || b.has_univ_metavar(),
                   t.has_local()          || b.has_local(),
                   t.has_param_univ()     || b.has_param_univ(),
                   std::max(get_depth(t), get_depth(b)) + 1,
                   std::max(get_free_var_range(t), dec(get_free_var_range(b)))),
    m_binder(n, t, i),
    m_body(b) {
    m_hash = ::lean::hash(m_hash, m_depth);
    lean_assert(k == expr_kind::Lambda || k == expr_kind::Pi);
}
void expr_binding::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_body, todelete);
    dec_ref(m_binder.m_type, todelete);
    this->~expr_binding();
    get_binding_allocator().recyle(this);
}

// Expr Sort
typedef memory_pool<sizeof(expr_sort)> sort_allocator;
MK_THREAD_LOCAL_GET_DEF(sort_allocator, get_sort_allocator);
expr_sort::expr_sort(level const & l):
    expr_cell(expr_kind::Sort, ::lean::hash(l), false, has_meta(l), false, has_param(l)),
    m_level(l) {
}
expr_sort::~expr_sort() {}
void expr_sort::dealloc() {
    this->~expr_sort();
    get_sort_allocator().recyle(this);
}

// Macro definition
bool macro_definition_cell::lt(macro_definition_cell const &) const { return false; }
bool macro_definition_cell::operator==(macro_definition_cell const & other) const { return typeid(*this) == typeid(other); }
unsigned macro_definition_cell::trust_level() const { return 0; }

format macro_definition_cell::pp(formatter const &) const { return format(get_name()); }
void macro_definition_cell::display(std::ostream & out) const { out << get_name(); }
bool macro_definition_cell::is_atomic_pp(bool, bool) const { return true; }
unsigned macro_definition_cell::hash() const { return get_name().hash(); }

macro_definition::macro_definition(macro_definition_cell * ptr):m_ptr(ptr) { lean_assert(m_ptr); m_ptr->inc_ref(); }
macro_definition::macro_definition(macro_definition const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
macro_definition::macro_definition(macro_definition && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
macro_definition::~macro_definition() { if (m_ptr) m_ptr->dec_ref(); }
macro_definition & macro_definition::operator=(macro_definition const & s) { LEAN_COPY_REF(s); }
macro_definition & macro_definition::operator=(macro_definition && s) { LEAN_MOVE_REF(s); }
bool macro_definition::operator<(macro_definition const & other) const {
    if (get_name() == other.get_name())
        return m_ptr->lt(*other.m_ptr);
    else
        return get_name() < other.get_name();
}

static unsigned max_depth(unsigned num, expr const * args) {
    unsigned r = 0;
    for (unsigned i = 0; i < num; i++) {
        unsigned d = get_depth(args[i]);
        if (d > r)
            r = d;
    }
    return r;
}

static unsigned get_free_var_range(unsigned num, expr const * args) {
    unsigned r = 0;
    for (unsigned i = 0; i < num; i++) {
        unsigned d = get_free_var_range(args[i]);
        if (d > r)
            r = d;
    }
    return r;
}

expr_macro::expr_macro(macro_definition const & m, unsigned num, expr const * args):
    expr_composite(expr_kind::Macro,
                   lean::hash(num, [&](unsigned i) { return args[i].hash(); }, m.hash()),
                   std::any_of(args, args+num, [](expr const & e) { return e.has_expr_metavar(); }),
                   std::any_of(args, args+num, [](expr const & e) { return e.has_univ_metavar(); }),
                   std::any_of(args, args+num, [](expr const & e) { return e.has_local(); }),
                   std::any_of(args, args+num, [](expr const & e) { return e.has_param_univ(); }),
                   max_depth(num, args) + 1,
                   get_free_var_range(num, args)),
    m_definition(m),
    m_num_args(num) {
    m_args = new expr[num];
    for (unsigned i = 0; i < m_num_args; i++)
        m_args[i] = args[i];
}
void expr_macro::dealloc(buffer<expr_cell*> & todelete) {
    for (unsigned i = 0; i < m_num_args; i++) dec_ref(m_args[i], todelete);
    delete(this);
}
expr_macro::~expr_macro() {
    delete[] m_args;
}

// =======================================
// Constructors

#ifdef LEAN_CACHE_EXPRS
typedef lru_cache<expr, expr_hash, is_bi_equal_proc> expr_cache;
MK_THREAD_LOCAL_GET(bool, get_expr_cache_enabled, true)
MK_THREAD_LOCAL_GET(expr_cache, get_expr_cache, LEAN_INITIAL_EXPR_CACHE_CAPACITY);
bool enable_expr_caching(bool f) {
    bool r = get_expr_cache_enabled();
    get_expr_cache_enabled() = f;
    return r;
}
inline expr cache(expr const & e) {
    if (get_expr_cache_enabled()) {
        if (auto r = get_expr_cache().insert(e))
            return *r;
    }
    return e;
}
#else
inline expr cache(expr && e) { return e; }
bool enable_expr_caching(bool) { return true; } // NOLINT
#endif

expr mk_var(unsigned idx) { return cache(expr(new (get_var_allocator().allocate()) expr_var(idx))); }
expr mk_constant(name const & n, levels const & ls) { return cache(expr(new (get_const_allocator().allocate()) expr_const(n, ls))); }
expr mk_macro(macro_definition const & m, unsigned num, expr const * args) { return cache(expr(new expr_macro(m, num, args))); }
expr mk_metavar(name const & n, expr const & t) { return cache(expr(new (get_mlocal_allocator().allocate()) expr_mlocal(true, n, t))); }
expr mk_local(name const & n, name const & pp_n, expr const & t, binder_info const & bi) {
    return cache(expr(new (get_local_allocator().allocate()) expr_local(n, pp_n, t, bi)));
}
expr mk_app(expr const & f, expr const & a) {
    return cache(expr(new (get_app_allocator().allocate()) expr_app(f, a)));
}
expr mk_binding(expr_kind k, name const & n, expr const & t, expr const & e, binder_info const & i) {
    return cache(expr(new (get_binding_allocator().allocate()) expr_binding(k, n, t, e, i)));
}
expr mk_sort(level const & l) { return cache(expr(new (get_sort_allocator().allocate()) expr_sort(l))); }
// =======================================

typedef buffer<expr_cell*> del_buffer;
MK_THREAD_LOCAL_GET_DEF(del_buffer, get_dealloc_buffer)

void expr_cell::dealloc() {
    try {
        del_buffer & todo = get_dealloc_buffer();
        todo.push_back(this);
        while (!todo.empty()) {
            expr_cell * it = todo.back();
            todo.pop_back();
            lean_assert(it->get_rc() == 0);
            switch (it->kind()) {
            case expr_kind::Var:        static_cast<expr_var*>(it)->dealloc(); break;
            case expr_kind::Macro:      static_cast<expr_macro*>(it)->dealloc(todo); break;
            case expr_kind::Meta:       static_cast<expr_mlocal*>(it)->dealloc(todo); break;
            case expr_kind::Local:      static_cast<expr_local*>(it)->dealloc(todo); break;
            case expr_kind::Constant:   static_cast<expr_const*>(it)->dealloc(); break;
            case expr_kind::Sort:       static_cast<expr_sort*>(it)->dealloc(); break;
            case expr_kind::App:        static_cast<expr_app*>(it)->dealloc(todo); break;
            case expr_kind::Lambda:
            case expr_kind::Pi:         static_cast<expr_binding*>(it)->dealloc(todo); break;
            }
        }
    } catch (std::bad_alloc&) {
        // We need this catch, because push_back may fail when expanding the buffer.
        // In this case, we avoid the crash, and "accept" the memory leak.
    }
}

// Auxiliary constructors
expr mk_app(expr const & f, unsigned num_args, expr const * args) {
    expr r = f;
    for (unsigned i = 0; i < num_args; i++)
        r = mk_app(r, args[i]);
    return r;
}

expr mk_app(unsigned num_args, expr const * args) {
    lean_assert(num_args >= 2);
    return mk_app(mk_app(args[0], args[1]), num_args - 2, args+2);
}

expr mk_rev_app(expr const & f, unsigned num_args, expr const * args) {
    expr r = f;
    unsigned i = num_args;
    while (i > 0) {
        --i;
        r = mk_app(r, args[i]);
    }
    return r;
}

expr mk_rev_app(unsigned num_args, expr const * args) {
    lean_assert(num_args >= 2);
    return mk_rev_app(mk_app(args[num_args-1], args[num_args-2]), num_args-2, args);
}

expr mk_app_vars(expr const & f, unsigned n) {
    expr r = f;
    while (n > 0) {
        --n;
        r = mk_app(r, Var(n));
    }
    return r;
}

expr const & get_app_args(expr const & e, buffer<expr> & args) {
    unsigned sz = args.size();
    expr const * it = &e;
    while (is_app(*it)) {
        args.push_back(app_arg(*it));
        it = &(app_fn(*it));
    }
    std::reverse(args.begin() + sz, args.end());
    return *it;
}

void flat_app(expr const & e, buffer<expr> & args) {
    unsigned i = args.size();
    args.push_back(expr());
    expr const & f = get_app_args(e, args);
    args[i] = f;
}

expr const & get_app_rev_args(expr const & e, buffer<expr> & args) {
    expr const * it = &e;
    while (is_app(*it)) {
        args.push_back(app_arg(*it));
        it = &(app_fn(*it));
    }
    return *it;
}

expr const & get_app_fn(expr const & e) {
    expr const * it = &e;
    while (is_app(*it)) {
        it = &(app_fn(*it));
    }
    return *it;
}

unsigned get_app_num_args(expr const & e) {
    expr const * it = &e;
    unsigned n = 0;
    while (is_app(*it)) {
        it = &(app_fn(*it));
        n++;
    }
    return n;
}

static name const & get_default_var_name() {
    static name r("a");
    return r;
}
static name const & g_default_var_name = get_default_var_name(); // force it to be initialized

bool is_default_var_name(name const & n) { return n == get_default_var_name(); }
expr mk_arrow(expr const & t, expr const & e) { return mk_pi(get_default_var_name(), t, e); }

expr mk_pi(unsigned sz, expr const * domain, expr const & range) {
    expr r = range;
    unsigned i = sz;
    while (i > 0) {
        --i;
        r = mk_pi(name(g_default_var_name, i), domain[i], r);
    }
    return r;
}

expr mk_Bool() {
    static optional<expr> Bool;
    if (!Bool) Bool = mk_sort(mk_level_zero());
    return *Bool;
}

expr mk_Type() {
    static optional<expr> Type;
    if (!Type) Type = mk_sort(mk_level_one());
    return *Type;
}

expr Bool = mk_Bool();
expr Type = mk_Type();

unsigned get_depth(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:  case expr_kind::Constant: case expr_kind::Sort:
    case expr_kind::Meta: case expr_kind::Local:
        return 1;
    case expr_kind::Lambda: case expr_kind::Pi:  case expr_kind::Macro:
    case expr_kind::App:
        return static_cast<expr_composite*>(e.raw())->m_depth;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool operator==(expr const & a, expr const & b) { return expr_eq_fn()(a, b); }
bool is_bi_equal(expr const & a, expr const & b) { return expr_eq_fn(true)(a, b); }

expr copy_tag(expr const & e, expr && new_e) {
    tag t = e.get_tag();
    if (t != nulltag)
        new_e.set_tag(t);
    return new_e;
}

expr update_app(expr const & e, expr const & new_fn, expr const & new_arg) {
    if (!is_eqp(app_fn(e), new_fn) || !is_eqp(app_arg(e), new_arg))
        return copy_tag(e, mk_app(new_fn, new_arg));
    else
        return e;
}

expr update_rev_app(expr const & e, unsigned num, expr const * new_args) {
    expr const * it = &e;
    for (unsigned i = 0; i < num - 1; i++) {
        if (!is_app(*it) || !is_eqp(app_arg(*it), new_args[i]))
            return copy_tag(e, mk_rev_app(num, new_args));
        it = &app_fn(*it);
    }
    if (!is_eqp(*it, new_args[num - 1]))
        return copy_tag(e, mk_rev_app(num, new_args));
    return e;
}

expr update_binding(expr const & e, expr const & new_domain, expr const & new_body) {
    if (!is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body))
        return copy_tag(e, mk_binding(e.kind(), binding_name(e), new_domain, new_body, binding_info(e)));
    else
        return e;
}

expr update_binding(expr const & e, expr const & new_domain, expr const & new_body, binder_info const & bi) {
    if (!is_eqp(binding_domain(e), new_domain) || !is_eqp(binding_body(e), new_body) || bi != binding_info(e))
        return copy_tag(e, mk_binding(e.kind(), binding_name(e), new_domain, new_body, bi));
    else
        return e;
}

expr update_mlocal(expr const & e, expr const & new_type) {
    if (is_eqp(mlocal_type(e), new_type))
        return e;
    else if (is_metavar(e))
        return copy_tag(e, mk_metavar(mlocal_name(e), new_type));
    else
        return copy_tag(e, mk_local(mlocal_name(e), local_pp_name(e), new_type, local_info(e)));
}

expr update_local(expr const & e, expr const & new_type, binder_info const & bi) {
    if (is_eqp(mlocal_type(e), new_type) && local_info(e) == bi)
        return e;
    else
        return copy_tag(e, mk_local(mlocal_name(e), local_pp_name(e), new_type, bi));
}

expr update_sort(expr const & e, level const & new_level) {
    if (!is_eqp(sort_level(e), new_level))
        return copy_tag(e, mk_sort(new_level));
    else
        return e;
}

expr update_constant(expr const & e, levels const & new_levels) {
    if (!is_eqp(const_levels(e), new_levels))
        return copy_tag(e, mk_constant(const_name(e), new_levels));
    else
        return e;
}

expr update_macro(expr const & e, unsigned num, expr const * args) {
    if (num == macro_num_args(e)) {
        unsigned i = 0;
        for (i = 0; i < num; i++) {
            if (!is_eqp(macro_arg(e, i), args[i]))
                break;
        }
        if (i == num)
            return e;
    }
    return copy_tag(e, mk_macro(to_macro(e)->m_definition, num, args));
}

bool is_atomic(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Constant: case expr_kind::Sort:
    case expr_kind::Var:
        return true;
    case expr_kind::Macro:
        return to_macro(e)->get_num_args() == 0;
    case expr_kind::App:      case expr_kind::Meta:
    case expr_kind::Local:    case expr_kind::Lambda:
    case expr_kind::Pi:
        return false;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool is_arrow(expr const & t) {
    optional<bool> r = t.raw()->is_arrow();
    if (r) {
        return *r;
    } else {
        bool res = is_pi(t) && !has_free_var(binding_body(t), 0);
        t.raw()->set_is_arrow(res);
        return res;
    }
}

static name g_let("let");
std::string const & get_let_macro_opcode() {
    static std::string g_let_macro_opcode("let");
    return g_let_macro_opcode;
}

/**
   \brief We use a macro to mark expressions that denote "let"-expressions.
   This marks have no real semantic meaning, but are used by Lean's pretty printer.
*/
class let_macro_definition_cell : public macro_definition_cell {
    static void check_macro(expr const & m) {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception("invalid 'let' macro");
    }
public:
    virtual name get_name() const { return g_let; }
    virtual expr get_type(expr const & m, expr const * arg_types, extension_context &) const {
        check_macro(m);
        return arg_types[0];
    }
    virtual optional<expr> expand(expr const & m, extension_context &) const {
        check_macro(m);
        return some_expr(macro_arg(m, 0));
    }
    virtual void write(serializer & s) const { s.write_string(get_let_macro_opcode()); }
};

static macro_definition g_let_macro_definition(new let_macro_definition_cell());
expr mk_let_macro(expr const & e) { return mk_macro(g_let_macro_definition, 1, &e); }
bool is_let_macro(expr const & e) { return is_macro(e) && macro_def(e) == g_let_macro_definition; }
expr let_macro_arg(expr const & e) { lean_assert(is_let_macro(e)); return macro_arg(e, 0); }

static bool has_free_var_in_domain(expr const & b, unsigned vidx) {
    if (is_pi(b)) {
        return has_free_var(binding_domain(b), vidx) || has_free_var_in_domain(binding_body(b), vidx+1);
    } else {
        return false;
    }
}

expr infer_implicit(expr const & t, unsigned num_params, bool strict) {
    if (num_params == 0) {
        return t;
    } else if (is_pi(t)) {
        expr new_body = infer_implicit(binding_body(t), num_params-1, strict);
        if (binding_info(t).is_implicit() || binding_info(t).is_strict_implicit()) {
            // argument is already marked as implicit
            return update_binding(t, binding_domain(t), new_body);
        } else if ((strict  && has_free_var_in_domain(new_body, 0)) ||
                   (!strict && has_free_var(new_body, 0))) {
            return update_binding(t, binding_domain(t), new_body, mk_implicit_binder_info());
        } else {
            return update_binding(t, binding_domain(t), new_body);
        }
    } else {
        return t;
    }
}

expr infer_implicit(expr const & t, bool strict) {
    return infer_implicit(t, std::numeric_limits<unsigned>::max(), strict);
}
}
