/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <utility>
#include "util/escaped.h"
#include "kernel/environment.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "library/formatter.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/print.h"

namespace lean {
bool is_used_name(expr const & t, name const & n) {
    bool found = false;
    for_each(t, [&](expr const & e, unsigned) {
            if (found) return false; // already found
            if ((is_constant(e) && const_name(e).get_root() == n)  // t has a constant starting with n
                || (is_fvar(e) && fvar_name(e) == n)) {
                found = true;
                return false; // found it
            }
            return true; // continue search
        });
    return found;
}

name pick_unused_name(expr const & t, name const & s) {
    name r = s;
    unsigned i = 1;
    while (is_used_name(t, r)) {
        r = name(s).append_after(i);
        i++;
    }
    return r;
}

bool is_numerical_name(name n) {
    while (!n.is_atomic())
        n = n.get_prefix();
    return n.is_numeral();
}

static name * g_M   = nullptr;
static name * g_x   = nullptr;

void initialize_print() {
    g_M = new name("M");
    mark_persistent(g_M->raw());
    g_x = new name("x");
    mark_persistent(g_x->raw());
}

void finalize_print() {
    delete g_M;
    delete g_x;
}

static name cleanup_name(name const & n) {
    if (is_numerical_name(n))
        return *g_x;
    else
        return n;
}

pair<expr, expr> binding_body_fresh(expr const & b, bool /* preserve_type */) {
    lean_assert(is_binding(b));
    name n = cleanup_name(binding_name(b));
    n = pick_unused_name(binding_body(b), n);
    expr c = mk_fvar(n); // HACK
    return mk_pair(instantiate(binding_body(b), c), c);
}

pair<expr, expr> let_body_fresh(expr const & b, bool /* preserve_type */) {
    lean_assert(is_let(b));
    name n = cleanup_name(let_name(b));
    n = pick_unused_name(let_body(b), n);
    expr c = mk_fvar(n); // HACK
    return mk_pair(instantiate(let_body(b), c), c);
}

name fix_name(name const & a) {
    if (a.is_atomic()) {
        if (a.is_numeral())
            return *g_M;
        else
            return a;
    } else {
        name p = fix_name(a.get_prefix());
        if (p == a.get_prefix())
            return a;
        else if (a.is_numeral())
            return name(p, a.get_numeral());
        else
            return name(p, a.get_string());
    }
}

/**
   \brief Very basic printer for expressions.
   It is mainly used when debugging code.
*/
struct print_expr_fn {
    std::ostream & m_out;

    std::ostream & out() { return m_out; }

    static bool is_atomic(expr const & a) {
        if (::lean::is_atomic(a)) return true;
        if (is_proj(a)) return is_atomic(proj_expr(a));
        return false;
    }

    void print_child(expr const & a) {
        if (is_atomic(a)) {
            print(a);
        } else {
            out() << "("; print(a); out() << ")";
        }
    }

    void print_sort(expr const & a) {
        if (is_zero(sort_level(a))) {
            out() << "Prop";
        } else if (is_one(sort_level(a))) {
            out() << "Type";
        } else if (is_succ(sort_level(a))) {
            out() << "Type.{" << succ_of(sort_level(a)) << "}";
        } else {
            out() << "Sort.{" << sort_level(a) << "}";
        }
    }

    void print_app(expr const & e) {
        expr const & f = app_fn(e);
        if (is_app(f))
            print(f);
        else
            print_child(f);
        out() << " ";
        print_child(app_arg(e));
    }

    static bool is_arrow(expr const & t) {
        return lean::is_arrow(t) && binding_info(t) == binder_info::Default;
    }

    void print_arrow_body(expr const & a) {
        if (is_atomic(a) || is_arrow(a))
            return print(a);
        else
            return print_child(a);
    }

    void print_binding(char const * bname, expr e, bool is_lambda) {
        expr_kind k = e.kind();
        out() << bname;
        while (e.kind() == k && !is_arrow(e)) {
            out() << " ";
            auto p = binding_body_fresh(e);
            expr const & n = p.second;
            binder_info bi = binding_info(e);
            if (is_implicit(bi))
                out() << "{";
            else if (is_inst_implicit(bi))
                out() << "[";
            else if (is_strict_implicit(bi))
                out() << "{{";
            else
                out() << "(";
            out() << n << " : ";
            print(binding_domain(e));
            if (is_implicit(bi))
                out() << "}";
            else if (is_inst_implicit(bi))
                out() << "]";
            else if (is_strict_implicit(bi))
                out() << "}}";
            else
                out() << ")";
            e = p.first;
        }
        if (is_lambda) out() << " => ";
        else out() << ", ";
        print(e);
    }

    void print_let(expr const & e) {
        auto p = let_body_fresh(e);
        out() << "let " << p.second << " : ";
        print(let_type(e));
        out() << " := ";
        print(let_value(e));
        out() << "; ";
        print(p.first);
    }

    void print_const(expr const & a) {
        levels const & ls = const_levels(a);
        out() << const_name(a);
        if (!is_nil(ls)) {
            out() << ".{";
            bool first = true;
            for (auto l : ls) {
                if (first) first = false; else out() << ", ";
                out() << l;
            }
            out() << "}";
        }
    }

    void print_mdata(expr const & a) {
        out() << "[mdata ";
        auto k = mdata_data(a);
        while (!empty(k)) {
            out() << head(k).fst() << ":";
            auto const & v = head(k).snd();
            switch (v.kind()) {
                case data_value_kind::Bool: out() << v.get_bool(); break;
                case data_value_kind::Name: out() << v.get_name(); break;
                case data_value_kind::Nat: out() << v.get_nat(); break;
                case data_value_kind::String: out() << escaped(v.get_string().data()); break;
            }
            out() << " ";
            k = tail(k);
        }
        print(mdata_expr(a));
        out() << "]";
    }

    void print(expr const & a) {
        switch (a.kind()) {
        case expr_kind::MVar:
            out() << "?" << fix_name(mvar_name(a));
            break;
        case expr_kind::FVar:
            out() << fvar_name(a);
            break;
        case expr_kind::MData:
            print_mdata(a);
            break;
        case expr_kind::Proj:
            print_child(proj_expr(a));
            out() << "." << proj_idx(a).to_mpz() + 1;
            break;
        case expr_kind::BVar:
            out() << "#" << bvar_idx(a);
            break;
        case expr_kind::Const:
            print_const(a);
            break;
        case expr_kind::App:
            print_app(a);
            break;
        case expr_kind::Let:
            print_let(a);
            break;
        case expr_kind::Lambda:
            print_binding("fun", a, true);
            break;
        case expr_kind::Pi:
            if (!is_arrow(a)) {
                print_binding("forall", a, false);
            } else {
                print_child(binding_domain(a));
                out() << " -> ";
                print_arrow_body(lower_loose_bvars(binding_body(a), 1));
            }
            break;
        case expr_kind::Sort:
            print_sort(a);
            break;
        case expr_kind::Lit:
            switch (lit_value(a).kind()) {
            case literal_kind::Nat: out() << lit_value(a).get_nat().to_mpz(); break;
            case literal_kind::String: {
                std::string val(lit_value(a).get_string().to_std_string());
                out() << "\"" << escaped(val.c_str()) << "\""; break; // HACK Lean string as C string
            }}
            break;
        }
    }

    print_expr_fn(std::ostream & out):m_out(out) {}

    void operator()(expr const & e) {
        print(e);
    }
};

void init_default_print_fn() {
    set_print_fn([](std::ostream & out, expr const & e) {
            print_expr_fn pr(out);
            pr(e);
        });
}

extern "C" LEAN_EXPORT object * lean_expr_dbg_to_string(b_obj_arg e) {
    std::ostringstream out;
    out << expr(e, true);
    return mk_string(out.str());
}
}
