/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include <vector>
#include <sstream>
#include <string>
#include <algorithm>
#include "util/hash.h"
#include "util/buffer.h"
#include "util/object_serializer.h"
#include "kernel/expr.h"
// #include "kernel/free_vars.h"
// #include "kernel/expr_eq.h"
// #include "kernel/metavar.h"
// #include "kernel/max_sharing.h"

namespace lean {
#if 0
static expr g_dummy(mk_var(0));
expr::expr():expr(g_dummy) {}

// Local context entries
local_entry::local_entry(unsigned s, unsigned n):m_kind(local_entry_kind::Lift), m_s(s), m_n(n) {}
local_entry::local_entry(unsigned s, expr const & v):m_kind(local_entry_kind::Inst), m_s(s), m_v(v) {}
local_entry::~local_entry() {}
bool local_entry::operator==(local_entry const & e) const {
    if (m_kind != e.m_kind || m_s != e.m_s)
        return false;
    if (is_inst())
        return m_v == e.m_v;
    else
        return m_n == e.m_n;
}

unsigned hash_args(unsigned size, expr const * args) {
    return hash(size, [&args](unsigned i){ return args[i].hash(); });
}

expr_cell::expr_cell(expr_kind k, unsigned h, bool has_mv):
    m_kind(static_cast<unsigned>(k)),
    m_flags(has_mv ? 4 : 0),
    m_hash(h),
    m_rc(0) {
    // m_hash_alloc does not need to be a unique identifier.
    // We want diverse hash codes such that given expr_cell * c1 and expr_cell * c2,
    // if c1 != c2, then there is high probability c1->m_hash_alloc != c2->m_hash_alloc.
    // Remark: using pointer address as a hash code is not a good idea.
    //    - each execution run will behave differently.
    //    - the hash is not diverse enough
    static LEAN_THREAD_LOCAL unsigned g_hash_alloc_counter = 0;
    m_hash_alloc = g_hash_alloc_counter;
    g_hash_alloc_counter++;
}

void expr_cell::dec_ref(expr & e, buffer<expr_cell*> & todelete) {
    if (e.m_ptr) {
        expr_cell * c = e.steal_ptr();
        lean_assert(!(e.m_ptr));
        if (c->dec_ref_core())
            todelete.push_back(c);
    }
}

void expr_cell::dec_ref(optional<expr> & c, buffer<expr_cell*> & todelete) {
    if (c)
        dec_ref(*c, todelete);
}

optional<bool> expr_cell::is_arrow() const {
    // it is stored in bits 3-4
    unsigned r = (m_flags & (8+16)) >> 3;
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
    unsigned mask = flag ? 8 : 16;
    m_flags |= mask;
    lean_assert(is_arrow() && *is_arrow() == flag);
}

// Expr variables
expr_var::expr_var(unsigned idx):
    expr_cell(expr_kind::Var, idx, false),
    m_vidx(idx) {}

// Expr constants
expr_const::expr_const(name const & n, optional<expr> const & t):
    expr_cell(expr_kind::Constant, n.hash(), t && t->has_metavar()),
    m_name(n),
    m_type(t) {}
void expr_const::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_type, todelete);
    delete(this);
}

// Expr heterogeneous equality
expr_heq::expr_heq(expr const & lhs, expr const & rhs):
    expr_cell(expr_kind::HEq, ::lean::hash(lhs.hash(), rhs.hash()), lhs.has_metavar() || rhs.has_metavar()),
    m_lhs(lhs), m_rhs(rhs), m_depth(std::max(get_depth(lhs), get_depth(rhs))+1) {
}
void expr_heq::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_lhs, todelete);
    dec_ref(m_rhs, todelete);
    delete(this);
}

// Expr dependent pairs
expr_dep_pair::expr_dep_pair(expr const & f, expr const & s, expr const & t):
    expr_cell(expr_kind::Pair, ::lean::hash(f.hash(), s.hash()), f.has_metavar() || s.has_metavar() || t.has_metavar()),
    m_first(f), m_second(s), m_type(t), m_depth(std::max(get_depth(f), get_depth(s))+1) {
}
void expr_dep_pair::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_first,  todelete);
    dec_ref(m_second, todelete);
    dec_ref(m_type,   todelete);
    delete(this);
}

// Expr pair projection
expr_proj::expr_proj(bool f, expr const & e):
    expr_cell(expr_kind::Proj, ::lean::hash(17, e.hash()), e.has_metavar()),
    m_first(f), m_depth(get_depth(e)+1), m_expr(e) {}
void expr_proj::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_expr, todelete);
    delete(this);
}

// Expr applications
expr_app::expr_app(unsigned num_args, bool has_mv):
    expr_cell(expr_kind::App, 0, has_mv),
    m_num_args(num_args) {
}
void expr_app::dealloc(buffer<expr_cell*> & todelete) {
    unsigned i = m_num_args;
    while (i > 0) {
        --i;
        dec_ref(m_args[i], todelete);
    }
    delete[] reinterpret_cast<char*>(this);
}
expr mk_app(unsigned n, expr const * as) {
    lean_assert(n > 1);
    unsigned new_n;
    unsigned n0 = 0;
    expr const & arg0 = as[0];
    bool has_mv = std::any_of(as, as + n, [](expr const & c) { return c.has_metavar(); });
    // Remark: we represent ((app a b) c) as (app a b c)
    if (is_app(arg0)) {
        n0    = num_args(arg0);
        new_n = n + n0 - 1;
    } else {
        new_n = n;
    }
    char * mem   = new char[sizeof(expr_app) + new_n*sizeof(expr)];
    expr r(new (mem) expr_app(new_n, has_mv));
    expr * m_args = to_app(r)->m_args;
    unsigned i = 0;
    unsigned j = 0;
    unsigned depth = 0;
    if (new_n != n) {
        for (; i < n0; ++i) {
            new (m_args+i) expr(arg(arg0, i));
            depth = std::max(depth, get_depth(m_args[i]));
        }
        j++;
    }
    for (; i < new_n; ++i, ++j) {
        lean_assert(j < n);
        new (m_args+i) expr(as[j]);
        depth = std::max(depth, get_depth(m_args[i]));
    }
    to_app(r)->m_hash  = hash_args(new_n, m_args);
    to_app(r)->m_depth = depth + 1;
    return r;
}

// Expr abstractions (and subclasses: Lambda, Pi and Sigma)
expr_abstraction::expr_abstraction(expr_kind k, name const & n, expr const & t, expr const & b):
    expr_cell(k, ::lean::hash(t.hash(), b.hash()), t.has_metavar() || b.has_metavar()),
    m_name(n),
    m_domain(t),
    m_body(b) {
    m_depth = 1 + std::max(get_depth(m_domain), get_depth(m_body));
}
void expr_abstraction::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_body, todelete);
    dec_ref(m_domain, todelete);
    delete(this);
}

expr_lambda::expr_lambda(name const & n, expr const & t, expr const & e):expr_abstraction(expr_kind::Lambda, n, t, e) {}

expr_pi::expr_pi(name const & n, expr const & t, expr const & e):expr_abstraction(expr_kind::Pi, n, t, e) {}

expr_sigma::expr_sigma(name const & n, expr const & t, expr const & e):expr_abstraction(expr_kind::Sigma, n, t, e) {}

// Expr Type
expr_type::expr_type(level const & l):
    expr_cell(expr_kind::Type, l.hash(), false),
    m_level(l) {
}
expr_type::~expr_type() {}

// Expr Let
expr_let::expr_let(name const & n, optional<expr> const & t, expr const & v, expr const & b):
    expr_cell(expr_kind::Let, ::lean::hash(v.hash(), b.hash()), v.has_metavar() || b.has_metavar() || (t && t->has_metavar())),
    m_name(n),
    m_type(t),
    m_value(v),
    m_body(b) {
    unsigned depth = std::max(get_depth(m_value), get_depth(m_body));
    if (m_type)
        depth = std::max(depth, get_depth(*m_type));
    m_depth = 1 + depth;
}
void expr_let::dealloc(buffer<expr_cell*> & todelete) {
    dec_ref(m_body, todelete);
    dec_ref(m_value, todelete);
    dec_ref(m_type, todelete);
    delete(this);
}
expr_let::~expr_let() {}

// Expr Semantic attachment
name value::get_unicode_name() const { return get_name(); }
optional<expr> value::normalize(unsigned, expr const *) const { return none_expr(); }
void value::display(std::ostream & out) const { out << get_name(); }
bool value::operator==(value const & other) const { return typeid(*this) == typeid(other); }
bool value::operator<(value const & other) const {
    if (get_name() == other.get_name())
        return lt(other);
    else
        return get_name() < other.get_name();
}
format value::pp() const { return format(get_name()); }
format value::pp(bool unicode, bool) const { return unicode ? format(get_unicode_name()) : pp(); }
unsigned value::hash() const { return get_name().hash(); }
int value::push_lua(lua_State *) const { return 0; } // NOLINT
expr_value::expr_value(value & v):
    expr_cell(expr_kind::Value, v.hash(), false),
    m_val(v) {
    m_val.inc_ref();
}
expr_value::~expr_value() {
    m_val.dec_ref();
}
typedef std::unordered_map<std::string, value::reader> value_readers;
static std::unique_ptr<value_readers> g_value_readers;
value_readers & get_value_readers() {
    if (!g_value_readers)
        g_value_readers.reset(new value_readers());
    return *(g_value_readers.get());
}

void value::register_deserializer(std::string const & k, value::reader rd) {
    value_readers & readers = get_value_readers();
    lean_assert(readers.find(k) == readers.end());
    readers[k] = rd;
}
static expr read_value(deserializer & d) {
    auto k  = d.read_string();
    value_readers & readers = get_value_readers();
    auto it = readers.find(k);
    lean_assert(it != readers.end());
    return it->second(d);
}

// Expr Metavariable
expr_metavar::expr_metavar(name const & n, local_context const & lctx):
    expr_cell(expr_kind::MetaVar, n.hash(), true),
    m_name(n), m_lctx(lctx) {}
expr_metavar::~expr_metavar() {}

void expr_cell::dealloc() {
    try {
        buffer<expr_cell*> todo;
        todo.push_back(this);
        while (!todo.empty()) {
            expr_cell * it = todo.back();
            todo.pop_back();
            lean_assert(it->get_rc() == 0);
            switch (it->kind()) {
            case expr_kind::Var:        delete static_cast<expr_var*>(it); break;
            case expr_kind::Value:      delete static_cast<expr_value*>(it); break;
            case expr_kind::MetaVar:    delete static_cast<expr_metavar*>(it); break;
            case expr_kind::Type:       delete static_cast<expr_type*>(it); break;
            case expr_kind::Constant:   static_cast<expr_const*>(it)->dealloc(todo); break;
            case expr_kind::Pair:       static_cast<expr_dep_pair*>(it)->dealloc(todo); break;
            case expr_kind::Proj:       static_cast<expr_proj*>(it)->dealloc(todo); break;
            case expr_kind::App:        static_cast<expr_app*>(it)->dealloc(todo); break;
            case expr_kind::Lambda:     static_cast<expr_lambda*>(it)->dealloc(todo); break;
            case expr_kind::Pi:         static_cast<expr_pi*>(it)->dealloc(todo); break;
            case expr_kind::Sigma:      static_cast<expr_sigma*>(it)->dealloc(todo); break;
            case expr_kind::HEq:        static_cast<expr_heq*>(it)->dealloc(todo); break;
            case expr_kind::Let:        static_cast<expr_let*>(it)->dealloc(todo); break;
            }
        }
    } catch (std::bad_alloc&) {
        // We need this catch, because push_back may fail when expanding the buffer.
        // In this case, we avoid the crash, and "accept" the memory leak.
    }
}

expr mk_type() {
    static LEAN_THREAD_LOCAL expr r = mk_type(level());
    return r;
}

bool operator==(expr const & a, expr const & b) {
    return expr_eq_fn<>()(a, b);
}

bool is_arrow(expr const & t) {
    optional<bool> r = t.raw()->is_arrow();
    if (r) {
        return *r;
    } else {
        bool res = is_pi(t) && !has_free_var(abst_body(t), 0);
        t.raw()->set_is_arrow(res);
        return res;
    }
}

bool is_cartesian(expr const & t) {
    return is_sigma(t) && !has_free_var(abst_body(t), 0);
}

unsigned get_depth(expr const & e) {
    switch (e.kind()) {
    case expr_kind::Var:   case expr_kind::Constant:  case expr_kind::Type:
    case expr_kind::Value: case expr_kind::MetaVar:
        return 1;
    case expr_kind::HEq:
        return to_heq(e)->m_depth;
    case expr_kind::Pair:
        return to_pair(e)->m_depth;
    case expr_kind::Proj:
        return to_proj(e)->m_depth;
    case expr_kind::App:
        return to_app(e)->m_depth;
    case expr_kind::Pi: case expr_kind::Lambda: case expr_kind::Sigma:
        return to_abstraction(e)->m_depth;
    case expr_kind::Let:
        return to_let(e)->m_depth;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

expr copy(expr const & a) {
    switch (a.kind()) {
    case expr_kind::Var:      return mk_var(var_idx(a));
    case expr_kind::Constant: return mk_constant(const_name(a), const_type(a));
    case expr_kind::Type:     return mk_type(ty_level(a));
    case expr_kind::Value:    return mk_value(static_cast<expr_value*>(a.raw())->m_val);
    case expr_kind::Pair:     return mk_pair(pair_first(a), pair_second(a), pair_type(a));
    case expr_kind::Proj:     return mk_proj(proj_first(a), proj_arg(a));
    case expr_kind::App:      return mk_app(num_args(a), begin_args(a));
    case expr_kind::Lambda:   return mk_lambda(abst_name(a), abst_domain(a), abst_body(a));
    case expr_kind::Pi:       return mk_pi(abst_name(a), abst_domain(a), abst_body(a));
    case expr_kind::Sigma:    return mk_sigma(abst_name(a), abst_domain(a), abst_body(a));
    case expr_kind::Let:      return mk_let(let_name(a), let_type(a), let_value(a), let_body(a));
    case expr_kind::HEq:      return mk_heq(heq_lhs(a), heq_rhs(a));
    case expr_kind::MetaVar:  return mk_metavar(metavar_name(a), metavar_lctx(a));
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

serializer & operator<<(serializer & s, local_context const & lctx) {
    s << length(lctx);
    for (auto const & e : lctx) {
        if (e.is_lift()) {
            s << true << e.s() << e.n();
        } else {
            s << false << e.s() << e.v();
        }
    }
    return s;
}

local_context read_local_context(deserializer & d) {
    unsigned num = d.read_unsigned();
    buffer<local_entry> entries;
    for (unsigned i = 0; i < num; i++) {
        if (d.read_bool()) {
            unsigned s, n;
            d >> s >> n;
            entries.push_back(mk_lift(s, n));
        } else {
            unsigned s; expr v;
            d >> s >> v;
            entries.push_back(mk_inst(s, v));
        }
    }
    return to_list(entries.begin(), entries.end());
}

// To save space, we pack the number of arguments in small applications in the kind byte.
// The extra kinds start at g_first_app_size_kind. This value should be bigger than the
// real kinds. Moreover g_first_app_size_kind + g_small_app_num_args should fit in a byte.
constexpr char g_first_app_size_kind = 32;
constexpr char g_small_app_num_args  = 32;
constexpr bool is_small(expr_kind k) { return 0 <= static_cast<char>(k) && static_cast<char>(k) < g_first_app_size_kind; }
static_assert(is_small(expr_kind::Var) && is_small(expr_kind::Constant) && is_small(expr_kind::Value) && is_small(expr_kind::App) &&
              is_small(expr_kind::Pair) && is_small(expr_kind::Proj) &&
              is_small(expr_kind::Lambda) && is_small(expr_kind::Pi) && is_small(expr_kind::Sigma) && is_small(expr_kind::Type) &&
              is_small(expr_kind::Let) && is_small(expr_kind::HEq) && is_small(expr_kind::MetaVar), "expr_kind is too big");

class expr_serializer : public object_serializer<expr, expr_hash_alloc, expr_eqp> {
    typedef object_serializer<expr, expr_hash_alloc, expr_eqp> super;
    max_sharing_fn m_max_sharing_fn;

    void write_core(optional<expr> const & a) {
        serializer & s = get_owner();
        if (a) {
            s << true;
            write_core(*a);
        } else {
            s << false;
        }
    }

    void write_core(expr const & a) {
        auto k = a.kind();
        char kc;
        if (k == expr_kind::App && num_args(a) < g_small_app_num_args) {
            kc = static_cast<char>(g_first_app_size_kind + num_args(a));
        } else {
            kc = static_cast<char>(k);
        }
        super::write_core(a, kc, [&]() {
                serializer & s = get_owner();
                if (kc >= static_cast<char>(g_first_app_size_kind)) {
                    // compressed application
                    for (unsigned i = 0; i < num_args(a); i++)
                        write_core(arg(a, i));
                    return;
                }
                switch (k) {
                case expr_kind::Var:       s << var_idx(a); break;
                case expr_kind::Constant:  s << const_name(a); write_core(const_type(a)); break;
                case expr_kind::Type:      s << ty_level(a); break;
                case expr_kind::Value:     to_value(a).write(s); break;
                case expr_kind::Pair:      write_core(pair_first(a)); write_core(pair_second(a)); write_core(pair_type(a)); break;
                case expr_kind::Proj:      s << proj_first(a); write_core(proj_arg(a)); break;
                case expr_kind::HEq:       write_core(heq_lhs(a)); write_core(heq_rhs(a)); break;
                case expr_kind::App:
                    s << num_args(a);
                    for (unsigned i = 0; i < num_args(a); i++)
                        write_core(arg(a, i));
                    break;
                case expr_kind::Lambda:
                case expr_kind::Pi:
                case expr_kind::Sigma:     s << abst_name(a); write_core(abst_domain(a)); write_core(abst_body(a)); break;
                case expr_kind::Let:       s << let_name(a); write_core(let_type(a)); write_core(let_value(a)); write_core(let_body(a)); break;
                case expr_kind::MetaVar:   s << metavar_name(a) << metavar_lctx(a); break;
                }
            });
    }
public:
    void write(expr const & a) {
        write_core(m_max_sharing_fn(a));
    }
};

class expr_deserializer : public object_deserializer<expr> {
    typedef object_deserializer<expr> super;
public:
    optional<expr> read_opt() {
        deserializer & d = get_owner();
        if (d.read_bool()) {
            return some_expr(read());
        } else {
            return none_expr();
        }
    }

    expr read() {
        return super::read_core([&](char c) {
                deserializer & d = get_owner();
                if (c >= g_first_app_size_kind) {
                    // compressed application
                    unsigned num = c - g_first_app_size_kind;
                    buffer<expr> args;
                    for (unsigned i = 0; i < num; i++)
                        args.push_back(read());
                    return mk_app(args);
                }
                auto k = static_cast<expr_kind>(c);
                switch (k) {
                case expr_kind::Var:
                    return mk_var(d.read_unsigned());
                case expr_kind::Constant: {
                    auto n = read_name(d);
                    return mk_constant(n, read_opt());
                }
                case expr_kind::Type:
                    return mk_type(read_level(d));
                    break;
                case expr_kind::Value:
                    return read_value(d);
                case expr_kind::Pair: {
                    expr f = read();
                    expr s = read();
                    return mk_pair(f, s, read());
                }
                case expr_kind::HEq: {
                    expr lhs = read();
                    return mk_heq(lhs, read());
                }
                case expr_kind::Proj: {
                    bool f = d.read_bool();
                    return mk_proj(f, read());
                }
                case expr_kind::App: {
                    buffer<expr> args;
                    unsigned num = d.read_unsigned();
                    for (unsigned i = 0; i < num; i++)
                        args.push_back(read());
                    return mk_app(args);
                }
                case expr_kind::Lambda: {
                    name n = read_name(d);
                    expr d = read();
                    return mk_lambda(n, d, read());
                }
                case expr_kind::Pi: {
                    name n = read_name(d);
                    expr d = read();
                    return mk_pi(n, d, read());
                }
                case expr_kind::Sigma: {
                    name n = read_name(d);
                    expr d = read();
                    return mk_sigma(n, d, read());
                }
                case expr_kind::Let: {
                    name n = read_name(d);
                    optional<expr> t = read_opt();
                    expr v = read();
                    return mk_let(n, t, v, read());
                }
                case expr_kind::MetaVar: {
                    name n = read_name(d);
                    return mk_metavar(n, read_local_context(d));
                }}
                throw_corrupted_file(); // LCOV_EXCL_LINE
            });
    }
};

struct expr_sd {
    unsigned m_s_extid;
    unsigned m_d_extid;
    expr_sd() {
        m_s_extid = serializer::register_extension([](){ return std::unique_ptr<serializer::extension>(new expr_serializer()); });
        m_d_extid = deserializer::register_extension([](){ return std::unique_ptr<deserializer::extension>(new expr_deserializer()); });
    }
};
static expr_sd g_expr_sd;

serializer & operator<<(serializer & s, expr const & n) {
    s.get_extension<expr_serializer>(g_expr_sd.m_s_extid).write(n);
    return s;
}

expr read_expr(deserializer & d) {
    return d.get_extension<expr_deserializer>(g_expr_sd.m_d_extid).read();
}
#endif
}
