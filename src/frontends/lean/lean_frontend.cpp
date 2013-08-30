/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <atomic>
#include "environment.h"
#include "toplevel.h"
#include "map.h"
#include "state.h"
#include "sstream.h"
#include "exception.h"
#include "lean_operator_info.h"
#include "lean_frontend.h"
#include "lean_notation.h"
#include "lean_pp.h"

namespace lean {
static std::vector<bool> g_empty_vector;
/** \brief Implementation of the Lean frontend */
struct frontend::imp {
    typedef std::pair<std::vector<bool>, name> implicit_info;
    // Remark: only named objects are stored in the dictionary.
    typedef std::unordered_map<name, operator_info, name_hash, name_eq> operator_table;
    typedef std::unordered_map<name, implicit_info, name_hash, name_eq> implicit_table;
    typedef std::unordered_map<expr, operator_info, expr_hash, std::equal_to<expr>> expr_to_operator;
    std::atomic<unsigned> m_num_children;
    std::shared_ptr<imp>  m_parent;
    environment           m_env;
    operator_table        m_nud; // nud table for Pratt's parser
    operator_table        m_led; // led table for Pratt's parser
    expr_to_operator      m_expr_to_operator; // map denotations to operators (this is used for pretty printing)
    implicit_table        m_implicit_table; // track the number of implicit arguments for a symbol.
    state                 m_state;

    bool has_children() const { return m_num_children > 0; }
    void inc_children() { m_num_children++; }
    void dec_children() { m_num_children--; }

    bool has_parent() const { return m_parent != nullptr; }

    /** \brief Return the nud operator for the given symbol. */
    operator_info find_nud(name const & n) const {
        auto it = m_nud.find(n);
        if (it != m_nud.end())
            return it->second;
        else if (has_parent())
            return m_parent->find_nud(n);
        else
            return operator_info();
    }

    /** \brief Return the led operator for the given symbol. */
    operator_info find_led(name const & n) const {
        auto it = m_led.find(n);
        if (it != m_led.end())
            return it->second;
        else if (has_parent())
            return m_parent->find_led(n);
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
    operator_info find_op_for(expr const & e) const {
        auto it = m_expr_to_operator.find(e);
        if (it != m_expr_to_operator.end())
            return it->second;
        else if (has_parent())
            return m_parent->find_op_for(e);
        else
            return operator_info();
    }

    /** \brief Remove all internal denotations that are associated with the given operator symbol (aka notation) */
    void remove_bindings(operator_info const & op) {
        for (expr const & d : op.get_denotations()) {
            if (has_parent() && m_parent->find_op_for(d)) {
                // parent has an association for d... we must hide it.
                insert(m_expr_to_operator, d, operator_info());
            } else {
                m_expr_to_operator.erase(d);
            }
        }
    }

    /** \brief Register the new operator in the tables for parsing and pretty printing. */
    void register_new_op(operator_info new_op, expr const & d, bool led) {
        new_op.add_expr(d);
        insert_op(new_op, led);
        insert(m_expr_to_operator, d, new_op);
    }

    /**
        \brief Two operator (aka notation) denotations are compatible
        iff one of the following holds:

        1) Both do not have implicit arguments

        2) Both have implicit arguments, and the implicit arguments
        occur in the same positions.

    */
    bool compatible_denotation(expr const & d1, expr const & d2) {
        return get_implicit_arguments(d1) == get_implicit_arguments(d2);
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
    void add_op(operator_info new_op, expr const & d, bool led) {
        name const & opn = new_op.get_op_name();
        operator_info old_op = find_op(opn, led);
        if (!old_op) {
            register_new_op(new_op, d, led);
        } else if (old_op == new_op) {
            if (compatible_denotations(old_op, d)) {
                // overload
                if (defined_here(old_op, led)) {
                    old_op.add_expr(d);
                } else {
                    // we must copy the operator because it was defined in
                    // a parent frontend.
                    new_op = old_op.copy();
                    register_new_op(new_op, d, led);
                }
            } else {
                diagnostic(m_state) << "The denotation(s) for the existing notation:\n  " << old_op << "\nhave been replaced with the new denotation:\n  " << d << "\nbecause they conflict on how implicit arguments are used.\n";
                remove_bindings(old_op);
                register_new_op(new_op, d, led);
            }
        } else {
            diagnostic(m_state) << "Notation has been redefined, the existing notation:\n  " << old_op << "\nhas been replaced with:\n  " << new_op << "\nbecause they conflict with each other.\n";
            remove_bindings(old_op);
            register_new_op(new_op, d, led);
        }
        m_env.add_neutral_object(new notation_declaration(new_op, d));
    }

    void add_infix(name const & opn, unsigned p, expr const & d)  { add_op(infix(opn, p), d, true); }
    void add_infixl(name const & opn, unsigned p, expr const & d) { add_op(infixl(opn, p), d, true); }
    void add_infixr(name const & opn, unsigned p, expr const & d) { add_op(infixr(opn, p), d, true); }
    void add_prefix(name const & opn, unsigned p, expr const & d) { add_op(prefix(opn, p), d, false); }
    void add_postfix(name const & opn, unsigned p, expr const & d) { add_op(postfix(opn, p), d, true); }
    void add_mixfixl(unsigned sz, name const * opns, unsigned p, expr const & d) { add_op(mixfixl(sz, opns, p), d, false); }
    void add_mixfixr(unsigned sz, name const * opns, unsigned p, expr const & d) { add_op(mixfixr(sz, opns, p), d, true);  }
    void add_mixfixc(unsigned sz, name const * opns, unsigned p, expr const & d) { add_op(mixfixc(sz, opns, p), d, false); }
    void add_mixfixo(unsigned sz, name const * opns, unsigned p, expr const & d) { add_op(mixfixo(sz, opns, p), d, true); }

    void mark_implicit_arguments(name const & n, unsigned sz, bool const * implicit) {
        if (has_children())
            throw exception(sstream() << "failed to mark implicit arguments, frontend object is read-only");
        object const & obj = m_env.get_object(n);
        if (obj.kind() != object_kind::Definition && obj.kind() != object_kind::Postulate)
            throw exception(sstream() << "failed to mark implicit arguments, the object '" << n << "' is not a definition or postulate");
        if (has_implicit_arguments(n))
            throw exception(sstream() << "the object '" << n << "' already has implicit argument information associated with it");
        name explicit_version(n, "explicit");
        if (m_env.find_object(explicit_version))
            throw exception(sstream() << "failed to mark implicit arguments for '" << n << "', the frontend already has an object named '" << explicit_version << "'");
        expr const & type = obj.get_type();
        unsigned num_args = 0;
        expr it = type;
        while (is_pi(it)) { num_args++; it = abst_body(it); }
        if (sz > num_args)
            throw exception(sstream() << "failed to mark implicit arguments for '" << n << "', object has only " << num_args << " arguments, but trying to mark " << sz << " arguments");
        std::vector<bool> v(implicit, implicit+sz);
        m_implicit_table[n] = mk_pair(v, explicit_version);
        if (obj.is_axiom() || obj.is_theorem()) {
            m_env.add_theorem(explicit_version, type, mk_constant(n));
        } else {
            m_env.add_definition(explicit_version, type, mk_constant(n));
        }
    }

    bool has_implicit_arguments(name const & n) {
        if (m_implicit_table.find(n) != m_implicit_table.end()) {
            return true;
        } else if (has_parent()) {
            return m_parent->has_implicit_arguments(n);
        } else {
            return false;
        }
    }

    std::vector<bool> const & get_implicit_arguments(name const & n) {
        auto it = m_implicit_table.find(n);
        if (it != m_implicit_table.end()) {
            return it->second.first;
        } else if (has_parent()) {
            return m_parent->get_implicit_arguments(n);
        } else {
            return g_empty_vector;
        }
    }

    std::vector<bool> const & get_implicit_arguments(expr const & n) {
        if (is_constant(n))
            return get_implicit_arguments(const_name(n));
        else
            return g_empty_vector;
    }

    name const & get_explicit_version(name const & n) {
        auto it = m_implicit_table.find(n);
        if (it != m_implicit_table.end()) {
            return it->second.second;
        } else if (has_parent()) {
            return m_parent->get_explicit_version(n);
        } else {
            return name::anonymous();
        }
    }

    void set_interrupt(bool flag) {
        m_env.set_interrupt(flag);
        m_state.set_interrupt(flag);
    }

    imp(frontend & fe):
        m_num_children(0) {
    }

    explicit imp(std::shared_ptr<imp> const & parent):
        m_num_children(0),
        m_parent(parent),
        m_env(m_parent->m_env.mk_child()),
        m_state(m_parent->m_state) {
        m_parent->inc_children();
    }

    ~imp() {
        if (m_parent)
            m_parent->dec_children();
    }
};

frontend::frontend():m_imp(new imp(*this)) {
    init_toplevel(m_imp->m_env);
    init_builtin_notation(*this);
    m_imp->m_state.set_formatter(mk_pp_formatter(*this));
}
frontend::frontend(imp * new_ptr):m_imp(new_ptr) {
    m_imp->m_state.set_formatter(mk_pp_formatter(*this));
}
frontend::frontend(std::shared_ptr<imp> const & ptr):m_imp(ptr) {}
frontend::~frontend() {}

frontend frontend::mk_child() const { return frontend(new imp(m_imp)); }
bool frontend::has_children() const { return m_imp->has_children(); }
bool frontend::has_parent() const { return m_imp->has_parent(); }
frontend frontend::parent() const { lean_assert(has_parent()); return frontend(m_imp->m_parent); }

environment const & frontend::get_environment() const { return m_imp->m_env; }

level frontend::add_uvar(name const & n, level const & l) { return m_imp->m_env.add_uvar(n, l); }
level frontend::add_uvar(name const & n) { return m_imp->m_env.add_uvar(n); }
level frontend::get_uvar(name const & n) const { return m_imp->m_env.get_uvar(n); }

void frontend::add_definition(name const & n, expr const & t, expr const & v, bool opaque) {
    return m_imp->m_env.add_definition(n, t, v, opaque);
}
void frontend::add_theorem(name const & n, expr const & t, expr const & v) { return m_imp->m_env.add_theorem(n, t, v); }
void frontend::add_definition(name const & n, expr const & v, bool opaque) { return m_imp->m_env.add_definition(n, v, opaque); }
void frontend::add_axiom(name const & n, expr const & t) { return m_imp->m_env.add_axiom(n, t); }
void frontend::add_var(name const & n, expr const & t) { return m_imp->m_env.add_var(n, t); }
object const & frontend::get_object(name const & n) const { return m_imp->m_env.get_object(n); }
object const & frontend::find_object(name const & n) const { return m_imp->m_env.find_object(n); }
bool frontend::has_object(name const & n) const { return m_imp->m_env.has_object(n); }
frontend::object_iterator frontend::begin_objects() const { return m_imp->m_env.begin_objects(); }
frontend::object_iterator frontend::end_objects() const { return m_imp->m_env.end_objects(); }
frontend::object_iterator frontend::begin_local_objects() const { return m_imp->m_env.begin_local_objects(); }
frontend::object_iterator frontend::end_local_objects() const { return m_imp->m_env.end_local_objects(); }

void frontend::add_infix(name const & opn, unsigned p, expr const & d)  { m_imp->add_infix(opn, p, d); }
void frontend::add_infixl(name const & opn, unsigned p, expr const & d)  { m_imp->add_infixl(opn, p, d); }
void frontend::add_infixr(name const & opn, unsigned p, expr const & d)  { m_imp->add_infixr(opn, p, d); }
void frontend::add_prefix(name const & opn, unsigned p, expr const & d)  { m_imp->add_prefix(opn, p, d); }
void frontend::add_postfix(name const & opn, unsigned p, expr const & d) { m_imp->add_postfix(opn, p, d); }
void frontend::add_mixfixl(unsigned sz, name const * opns, unsigned p, expr const & d) { m_imp->add_mixfixl(sz, opns, p, d); }
void frontend::add_mixfixr(unsigned sz, name const * opns, unsigned p, expr const & d) { m_imp->add_mixfixr(sz, opns, p, d); }
void frontend::add_mixfixc(unsigned sz, name const * opns, unsigned p, expr const & d) { m_imp->add_mixfixc(sz, opns, p, d); }
void frontend::add_mixfixo(unsigned sz, name const * opns, unsigned p, expr const & d) { m_imp->add_mixfixo(sz, opns, p, d); }
operator_info frontend::find_op_for(expr const & n) const { return m_imp->find_op_for(n); }
operator_info frontend::find_nud(name const & n) const { return m_imp->find_nud(n); }
operator_info frontend::find_led(name const & n) const { return m_imp->find_led(n); }

void frontend::mark_implicit_arguments(name const & n, unsigned sz, bool const * implicit) { m_imp->mark_implicit_arguments(n, sz, implicit); }
void frontend::mark_implicit_arguments(name const & n, std::initializer_list<bool> const & l) { mark_implicit_arguments(n, l.size(), l.begin()); }
bool frontend::has_implicit_arguments(name const & n) const { return m_imp->has_implicit_arguments(n); }
std::vector<bool> const & frontend::get_implicit_arguments(name const & n) const { return m_imp->get_implicit_arguments(n); }
name const & frontend::get_explicit_version(name const & n) const { return m_imp->get_explicit_version(n); }

state const & frontend::get_state() const { return m_imp->m_state; }
state & frontend::get_state_core() { return m_imp->m_state; }
void frontend::set_options(options const & opts) { return m_imp->m_state.set_options(opts); }
void frontend::set_regular_channel(std::shared_ptr<output_channel> const & out) { return m_imp->m_state.set_regular_channel(out); }
void frontend::set_diagnostic_channel(std::shared_ptr<output_channel> const & out) { return m_imp->m_state.set_diagnostic_channel(out); }

void frontend::set_interrupt(bool flag) { m_imp->set_interrupt(flag); }
}
