/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_set>
#include <vector>
#include <utility>
#include <functional>
#include "util/thread.h"
#include "util/map.h"
#include "util/sstream.h"
#include "util/exception.h"
#include "kernel/environment.h"
#include "library/expr_pair.h"
#include "library/io_state.h"
#include "library/all/all.h"
#include "frontends/lean/operator_info.h"
#include "frontends/lean/coercion.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/notation.h"
#include "frontends/lean/pp.h"

namespace lean {
static std::vector<bool> g_empty_vector;
/**
   \brief Environment extension object for the Lean default frontend.
*/
struct lean_extension : public environment::extension {
    typedef std::pair<std::vector<bool>, name> implicit_info;
    // Remark: only named objects are stored in the dictionary.
    typedef std::unordered_map<name, operator_info, name_hash, name_eq> operator_table;
    typedef std::unordered_map<name, implicit_info, name_hash, name_eq> implicit_table;
    typedef std::unordered_map<expr, list<operator_info>, expr_hash, std::equal_to<expr>> expr_to_operators;
    typedef std::unordered_map<expr_pair, expr, expr_pair_hash, expr_pair_eq> coercion_map;
    typedef std::unordered_map<expr, list<expr_pair>, expr_hash, std::equal_to<expr>> expr_to_coercions;
    typedef std::unordered_set<expr, expr_hash, std::equal_to<expr>> coercion_set;

    operator_table        m_nud; // nud table for Pratt's parser
    operator_table        m_led; // led table for Pratt's parser
    expr_to_operators     m_expr_to_operators; // map denotations to operators (this is used for pretty printing)
    implicit_table        m_implicit_table; // track the number of implicit arguments for a symbol.
    coercion_map          m_coercion_map; // mapping from (given_type, expected_type) -> coercion
    coercion_set          m_coercion_set; // Set of coercions
    expr_to_coercions     m_type_coercions; // mapping type -> list (to-type, function)

    lean_extension const * get_parent() const {
        return environment::extension::get_parent<lean_extension>();
    }

    /** \brief Return the nud operator for the given symbol. */
    operator_info find_nud(name const & n) const {
        auto it = m_nud.find(n);
        if (it != m_nud.end())
            return it->second;
        lean_extension const * parent = get_parent();
        if (parent)
            return parent->find_nud(n);
        else
            return operator_info();
    }

    /** \brief Return the led operator for the given symbol. */
    operator_info find_led(name const & n) const {
        auto it = m_led.find(n);
        if (it != m_led.end())
            return it->second;
        lean_extension const * parent = get_parent();
        if (parent)
            return parent->find_led(n);
        else
            return operator_info();
    }

    /**
        \brief Return true if the given operator is defined in this
        frontend object (parent frontends are ignored).
    */
    bool defined_here(operator_info const & n, bool led) const {
        if (led)
            return m_led.find(n.get_op_name()) != m_led.end();
        else
            return m_nud.find(n.get_op_name()) != m_nud.end();
    }

    /** \brief Return the led/nud operator for the given symbol. */
    operator_info find_op(name const & n, bool led) const {
        return led ? find_led(n) : find_nud(n);
    }

    /** \brief Insert a new led/nud operator. */
    void insert_op(operator_info const & op, bool led) {
        if (led)
            insert(m_led, op.get_op_name(), op);
        else
            insert(m_nud, op.get_op_name(), op);
    }

    /** \brief Find the operator that is used as notation for the given expression. */
    operator_info find_op_for(expr const & e, bool unicode) const {
        auto it = m_expr_to_operators.find(e);
        if (it != m_expr_to_operators.end()) {
            auto l = it->second;
            for (auto op : l) {
                if (unicode || op.is_safe_ascii())
                    return op;
            }
        }
        lean_extension const * parent = get_parent();
        if (parent)
            return parent->find_op_for(e, unicode);
        else
            return operator_info();
    }

    /** \brief Remove all internal denotations that are associated with the given operator symbol (aka notation) */
    void remove_bindings(operator_info const & op) {
        lean_extension const * parent = get_parent();
        for (expr const & d : op.get_denotations()) {
            if (parent && parent->find_op_for(d, true)) {
                // parent has an association for d... we must hide it.
                insert(m_expr_to_operators, d, list<operator_info>(operator_info()));
            } else {
                m_expr_to_operators.erase(d);
            }
        }
    }


    /** \brief Add a new entry d -> op in the mapping m_expr_to_operators */
    void insert_expr_to_operator_entry(expr const & d, operator_info const & op) {
        list<operator_info> & l = m_expr_to_operators[d];
        l = cons(op, l);
    }

    /** \brief Register the new operator in the tables for parsing and pretty printing. */
    void register_new_op(operator_info new_op, expr const & d, bool led) {
        new_op.add_expr(d);
        insert_op(new_op, led);
        insert_expr_to_operator_entry(d, new_op);
    }

    /**
        \brief Two operator (aka notation) denotations are compatible
        iff after ignoring all implicit arguments in the prefix and
        explicit arguments in the suffix, the remaining implicit arguments
        occur in the same positions.

        Let us denote implicit arguments with a '_' and explicit with a '*'.
        Then a denotation can be associated with a pattern containing one or more
        '_' and '*'.
        Two denotations are compatible, if we have the same pattern after
        removed the '_' from the prefix and '*' from the suffix.

        Here is an example of compatible denotations
                 f : Int -> Int -> Int              Pattern   * *
                 g : Pi {A : Type}, A -> A -> A     Pattern   _ * *
                 h : Pi {A B : Type}, A -> B -> A   Pattern   _ _ * *
            They are compatible, because after we remove the _ from the prefix, and * from the suffix,
            all of them reduce to the empty sequence

        Here is another example of compatible denotations:
                 f : Pi {A : Type} (a : A) {B : Type} (b : B), A    Pattern _ * _ *
                 g : Pi (i : Int) {T : Type} (x : T), T             Pattern * _ *
            They are compatible, because after we remove the _ from the prefix, and * from the suffix,
            we get the same sequence:  * _

        The following two are not compatible
                 f : Pi {A : Type} (a : A) {B : Type} (b : B), A    Pattern _ * _ *
                 g : Pi {A B : Type} (a : A) (b : B), A             Pattern _ _ * *

        Remark: we remove the explicit suffix at mark_implicit_arguments.
    */
    bool compatible_denotation(expr const & d1, expr const & d2) {
        auto imp1 = get_implicit_arguments(d1);
        auto imp2 = get_implicit_arguments(d2);
        auto it1  = std::find(imp1.begin(), imp1.end(), false);
        auto it2  = std::find(imp2.begin(), imp2.end(), false);
        for (; it1 != imp1.end() && it2 != imp2.end() && *it1 == *it2; ++it1, ++it2) {}
        return it1 == imp1.end() && it2 == imp2.end();
    }

    /**
        \brief Return true iff the existing denotations (aka
        overloads) for an operator op are compatible with the new
        denotation d.

        The compatibility is only an issue if implicit arguments are
        used. If one of the denotations has implicit arguments, then
        all of them should have implicit arguments, and the implicit
        arguments should occur in the same positions.
    */
    bool compatible_denotations(operator_info const & op, expr const & d) {
        return std::all_of(op.get_denotations().begin(), op.get_denotations().end(), [&](expr const & prev_d) { return compatible_denotation(prev_d, d); });
    }

    /**
        \brief Add a new operator and save information as object.

        If the new operator does not conflict with existing operators,
        then we just register it.
        If it conflicts, there are two options:
        1) It is an overload (we just add the internal name \c n as
        new option.
        2) It is a real conflict, and report the issue in the
        diagnostic channel, and override the existing operator (aka notation).
    */
    void add_op(operator_info new_op, expr const & d, bool led, environment & env, io_state & st) {
        name const & opn = new_op.get_op_name();
        operator_info old_op = find_op(opn, led);
        if (!old_op) {
            register_new_op(new_op, d, led);
        } else if (old_op == new_op) {
            if (compatible_denotations(old_op, d)) {
                // overload
                if (defined_here(old_op, led)) {
                    old_op.add_expr(d);
                    insert_expr_to_operator_entry(d, old_op);
                } else {
                    // we must copy the operator because it was defined in
                    // a parent frontend.
                    new_op = old_op.copy();
                    register_new_op(new_op, d, led);
                }
            } else {
                diagnostic(st) << "The denotation(s) for the existing notation:\n  " << old_op
                               << "\nhave been replaced with the new denotation:\n  " << d
                               << "\nbecause they conflict on how implicit arguments are used.\n";
                remove_bindings(old_op);
                register_new_op(new_op, d, led);
            }
        } else {
            diagnostic(st) << "Notation has been redefined, the existing notation:\n  " << old_op
                           << "\nhas been replaced with:\n  " << new_op << "\nbecause they conflict with each other.\n";
            remove_bindings(old_op);
            register_new_op(new_op, d, led);
        }
        env.add_neutral_object(new notation_declaration(new_op, d));
    }

    expr mk_explicit_definition_body(expr type, name const & n, unsigned i, unsigned sz) {
        if (i == sz) {
            buffer<expr> args;
            args.push_back(mk_constant(n));
            unsigned j = sz;
            while (j > 0) { --j; args.push_back(mk_var(j)); }
            return mk_app(args);
        } else {
            lean_assert(is_pi(type));
            return mk_lambda(abst_name(type), abst_domain(type), mk_explicit_definition_body(abst_body(type), n, i+1, sz));
        }
    }

    void mark_implicit_arguments(name const & n, unsigned sz, bool const * implicit, environment & env) {
        if (env.has_children())
            throw exception(sstream() << "failed to mark implicit arguments, frontend object is read-only");
        object const & obj = env.get_object(n);
        if (obj.kind() != object_kind::Definition && obj.kind() != object_kind::Postulate && obj.kind() != object_kind::Builtin)
            throw exception(sstream() << "failed to mark implicit arguments, the object '" << n << "' is not a definition or postulate");
        if (has_implicit_arguments(n))
            throw exception(sstream() << "the object '" << n << "' already has implicit argument information associated with it");
        name explicit_version(n, "explicit");
        if (env.find_object(explicit_version))
            throw exception(sstream() << "failed to mark implicit arguments for '" << n << "', the frontend already has an object named '" << explicit_version << "'");
        expr const & type = obj.get_type();
        unsigned num_args = 0;
        expr it = type;
        while (is_pi(it)) { num_args++; it = abst_body(it); }
        if (sz > num_args)
            throw exception(sstream() << "failed to mark implicit arguments for '" << n << "', object has only " << num_args << " arguments, but trying to mark " << sz << " arguments");
        // remove explicit suffix
        while (sz > 0 && !implicit[sz - 1]) sz--;
        if (sz == 0)
            throw exception(sstream() << "failed to mark implicit arguments for '" << n << "', all arguments are explicit");
        std::vector<bool> v(implicit, implicit+sz);
        m_implicit_table[n] = mk_pair(v, explicit_version);
        expr body = mk_explicit_definition_body(type, n, 0, num_args);
        if (obj.is_axiom() || obj.is_theorem()) {
            env.add_theorem(explicit_version, type, body);
        } else {
            env.add_definition(explicit_version, type, body);
        }
    }

    bool has_implicit_arguments(name const & n) const {
        if (m_implicit_table.find(n) != m_implicit_table.end())
            return true;
        lean_extension const * parent = get_parent();
        if (parent)
            return parent->has_implicit_arguments(n);
        else
            return false;
    }

    std::vector<bool> const & get_implicit_arguments(name const & n) const {
        auto it = m_implicit_table.find(n);
        if (it != m_implicit_table.end())
            return it->second.first;
        lean_extension const * parent = get_parent();
        if (parent)
            return parent->get_implicit_arguments(n);
        else
            return g_empty_vector;
    }

    std::vector<bool> const & get_implicit_arguments(expr const & n) const {
        if (is_constant(n))
            return get_implicit_arguments(const_name(n));
        else
            return g_empty_vector;
    }

    name const & get_explicit_version(name const & n) const {
        auto it = m_implicit_table.find(n);
        if (it != m_implicit_table.end())
            return it->second.second;
        lean_extension const * parent = get_parent();
        if (parent)
            return parent->get_explicit_version(n);
        else
            return name::anonymous();
    }

    bool is_explicit(name const & n) const {
        return !n.is_atomic() && get_explicit_version(n.get_prefix()) == n;
    }

    void add_coercion(expr const & f, environment & env) {
        expr type      = env.infer_type(f);
        expr norm_type = env.normalize(type);
        if (!is_arrow(norm_type))
            throw exception("invalid coercion declaration, a coercion must have an arrow type (i.e., a non-dependent functional type)");
        expr from      = abst_domain(norm_type);
        expr to        = abst_body(norm_type);
        if (from == to)
            throw exception("invalid coercion declaration, 'from' and 'to' types are the same");
        if (get_coercion(from, to))
            throw exception("invalid coercion declaration, frontend already has a coercion for the given types");
        m_coercion_map[expr_pair(from, to)] = f;
        m_coercion_set.insert(f);
        list<expr_pair> l = get_coercions(from);
        insert(m_type_coercions, from, cons(expr_pair(to, f), l));
        env.add_neutral_object(new coercion_declaration(f));
    }

    optional<expr> get_coercion(expr const & from_type, expr const & to_type) const {
        expr_pair p(from_type, to_type);
        auto it = m_coercion_map.find(p);
        if (it != m_coercion_map.end())
            return some_expr(it->second);
        lean_extension const * parent = get_parent();
        if (parent)
            return parent->get_coercion(from_type, to_type);
        else
            return none_expr();
    }

    list<expr_pair> get_coercions(expr const & from_type) const {
        auto r = m_type_coercions.find(from_type);
        if (r != m_type_coercions.end())
            return r->second;
        lean_extension const * parent = get_parent();
        if (parent)
            return parent->get_coercions(from_type);
        else
            return list<expr_pair>();
    }

    bool is_coercion(expr const & f) const {
        if (m_coercion_set.find(f) != m_coercion_set.end())
            return true;
        lean_extension const * parent = get_parent();
        return parent && parent->is_coercion(f);
    }
};

struct lean_extension_initializer {
    unsigned m_extid;
    lean_extension_initializer() {
        m_extid = environment::register_extension([](){ return std::unique_ptr<environment::extension>(new lean_extension()); });
    }
};

static lean_extension_initializer g_lean_extension_initializer;

static lean_extension const & to_ext(environment const & env) {
    return env.get_extension<lean_extension>(g_lean_extension_initializer.m_extid);
}

static lean_extension & to_ext(environment & env) {
    return env.get_extension<lean_extension>(g_lean_extension_initializer.m_extid);
}


bool is_explicit(environment const & env, name const & n) {
    return to_ext(env).is_explicit(n);
}

bool has_implicit_arguments(environment const & env, name const & n) {
    return to_ext(env).has_implicit_arguments(n);
}

name const & get_explicit_version(environment const & env, name const & n) {
    return to_ext(env).get_explicit_version(n);
}

std::vector<bool> const & get_implicit_arguments(environment const & env, name const & n) {
    return to_ext(env).get_implicit_arguments(n);
}

bool is_coercion(environment const & env, expr const & f) {
    return to_ext(env).is_coercion(f);
}

operator_info find_op_for(environment const & env, expr const & n, bool unicode) {
    operator_info r = to_ext(env).find_op_for(n, unicode);
    if (r || !is_constant(n)) {
        return r;
    } else {
        optional<object> obj = env.find_object(const_name(n));
        if (obj && obj->is_builtin() && obj->get_name() == const_name(n))
            return to_ext(env).find_op_for(obj->get_value(), unicode);
        else
            return r;
    }
}

frontend::frontend() {
    m_state.set_formatter(mk_pp_formatter(m_env));
    import_all(m_env);
    init_builtin_notation(*this);
}
frontend::frontend(environment const & env, io_state const & s):m_env(env), m_state(s) {
    import_all(m_env);
    init_builtin_notation(*this);
}

void frontend::add_infix(name const & opn, unsigned p, expr const & d)  {
    to_ext(m_env).add_op(infix(opn, p), d, true, m_env, m_state);
}
void frontend::add_infixl(name const & opn, unsigned p, expr const & d) {
    to_ext(m_env).add_op(infixl(opn, p), d, true, m_env, m_state);
}
void frontend::add_infixr(name const & opn, unsigned p, expr const & d) {
    to_ext(m_env).add_op(infixr(opn, p), d, true, m_env, m_state);
}
void frontend::add_prefix(name const & opn, unsigned p, expr const & d) {
    to_ext(m_env).add_op(prefix(opn, p), d, false, m_env, m_state);
}
void frontend::add_postfix(name const & opn, unsigned p, expr const & d) {
    to_ext(m_env).add_op(postfix(opn, p), d, true, m_env, m_state);
}
void frontend::add_mixfixl(unsigned sz, name const * opns, unsigned p, expr const & d) {
    to_ext(m_env).add_op(mixfixl(sz, opns, p), d, false, m_env, m_state);
}
void frontend::add_mixfixr(unsigned sz, name const * opns, unsigned p, expr const & d) {
    to_ext(m_env).add_op(mixfixr(sz, opns, p), d, true, m_env, m_state);
}
void frontend::add_mixfixc(unsigned sz, name const * opns, unsigned p, expr const & d) {
    to_ext(m_env).add_op(mixfixc(sz, opns, p), d, false, m_env, m_state);
}
void frontend::add_mixfixo(unsigned sz, name const * opns, unsigned p, expr const & d) {
    to_ext(m_env).add_op(mixfixo(sz, opns, p), d, true, m_env, m_state);
}
operator_info frontend::find_op_for(expr const & n, bool unicode) const {
    return ::lean::find_op_for(m_env, n, unicode);
}
operator_info frontend::find_nud(name const & n) const {
    return to_ext(m_env).find_nud(n);
}
operator_info frontend::find_led(name const & n) const {
    return to_ext(m_env).find_led(n);
}
void frontend::mark_implicit_arguments(name const & n, unsigned sz, bool const * implicit) {
    to_ext(m_env).mark_implicit_arguments(n, sz, implicit, m_env);
}
void frontend::mark_implicit_arguments(name const & n, unsigned prefix_sz) {
    buffer<bool> implicit; implicit.resize(prefix_sz, true);
    mark_implicit_arguments(n, implicit.size(), implicit.data());
}
void frontend::mark_implicit_arguments(expr const & n, unsigned prefix_sz) {
    if (is_constant(n)) {
        mark_implicit_arguments(const_name(n), prefix_sz);
    } else {
        lean_assert(is_value(n));
        mark_implicit_arguments(to_value(n).get_name(), prefix_sz);
    }
}
void frontend::mark_implicit_arguments(name const & n, std::initializer_list<bool> const & l) {
    mark_implicit_arguments(n, l.size(), l.begin());
}
void frontend::mark_implicit_arguments(expr const & n, std::initializer_list<bool> const & l) {
    if (is_constant(n)) {
        mark_implicit_arguments(const_name(n), l);
    } else {
        lean_assert(is_value(n));
        mark_implicit_arguments(to_value(n).get_name(), l);
    }
}
bool frontend::has_implicit_arguments(name const & n) const {
    return to_ext(m_env).has_implicit_arguments(n);
}
std::vector<bool> const & frontend::get_implicit_arguments(name const & n) const {
    return to_ext(m_env).get_implicit_arguments(n);
}
name const & frontend::get_explicit_version(name const & n) const {
    return to_ext(m_env).get_explicit_version(n);
}
bool frontend::is_explicit(name const & n) const {
    return to_ext(m_env).is_explicit(n);
}
void frontend::add_coercion(expr const & f) {
    to_ext(m_env).add_coercion(f, m_env);
}
optional<expr> frontend::get_coercion(expr const & from_type, expr const & to_type) const {
    return to_ext(m_env).get_coercion(from_type, to_type);
}
list<expr_pair> frontend::get_coercions(expr const & from_type) const {
    return to_ext(m_env).get_coercions(from_type);
}
bool frontend::is_coercion(expr const & f) const {
    return to_ext(m_env).is_coercion(f);
}
}
