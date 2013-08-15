/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <atomic>
#include "map.h"
#include "frontend.h"
#include "environment.h"
#include "operator_info.h"

namespace lean {
/**
    \brief Create object for tracking notation/operator declarations.
    This object is mainly used for pretty printing.
*/
class notation_declaration : public anonymous_object {
    operator_info m_op;
    name          m_name;
public:
    notation_declaration(operator_info const & op, name const & n):m_op(op), m_name(n) {}
    virtual ~notation_declaration() {}
    static char const * g_keyword;
    virtual char const * keyword() const { return g_keyword; }
    virtual format pp(environment const &) const {
        // TODO
        return format();
    }
};
char const * notation_declaration::g_keyword = "Notation";

/** \brief Implementation of the Lean frontend */
struct frontend::imp {
    // Remark: only named objects are stored in the dictionary.
    typedef std::unordered_map<name, operator_info, name_hash, name_eq> operator_table;
    typedef std::unordered_map<name, unsigned, name_hash, name_eq> implicit_table;
    std::atomic<unsigned> m_num_children;
    std::shared_ptr<imp>  m_parent;
    environment           m_env;
    operator_table        m_nud; // nud table for Pratt's parser
    operator_table        m_led; // led table for Pratt's parser
    operator_table        m_name_to_operator; // map internal names to operators (this is used for pretty printing)
    implicit_table        m_implicit_table; // track the number of implicit arguments for a symbol.

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

    /** \brief Find the operator that is used as notation for the given internal symbol. */
    operator_info find_op_for(name const & n) const {
        auto it = m_name_to_operator.find(n);
        if (it != m_name_to_operator.end())
            return it->second;
        else if (has_parent())
            return m_parent->find_op_for(n);
        else
            return operator_info();
    }

    void diagnostic_msg(char const * msg) {
        // TODO
    }

    void report_op_redefined(operator_info const & old_op, operator_info const & new_op) {
        // TODO
    }

    /** \brief Remove all internal operators that are associated with the given operator symbol (aka notation) */
    void remove_bindings(operator_info const & op) {
        for (name const & n : op.get_internal_names()) {
            if (has_parent() && !is_nil(m_parent->find_op_for(n))) {
                // parent has a binding for n... we must hide it.
                insert(m_name_to_operator, n, operator_info());
            } else {
                m_name_to_operator.erase(n);
            }
        }
    }

    /** \brief Register the new operator in the tables for parsing and pretty printing. */
    void register_new_op(operator_info new_op, name const & n, bool led) {
        new_op.add_internal_name(n);
        insert_op(new_op, led);
        insert(m_name_to_operator, n, new_op);
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
    void add_op(operator_info new_op, name const & n, bool led) {
        name const & opn = new_op.get_op_name();
        operator_info old_op = find_op(opn, led);
        if (is_nil(old_op)) {
            register_new_op(new_op, n, led);
        } else if (old_op == new_op) {
            // overload
            if (defined_here(old_op, led)) {
                old_op.add_internal_name(n);
            } else {
                // we must copy the operator because it was defined in
                // a parent frontend.
                new_op = old_op.copy();
                register_new_op(new_op, n, led);
            }
        } else {
            report_op_redefined(old_op, new_op);
            remove_bindings(old_op);
            register_new_op(new_op, n, led);
        }
        m_env.add_anonymous_object(new notation_declaration(new_op, n));
    }

    imp():
        m_num_children(0) {
    }

    explicit imp(std::shared_ptr<imp> const & parent):
        m_num_children(0),
        m_parent(parent),
        m_env(m_parent->m_env.mk_child()) {
        m_parent->inc_children();
    }

    ~imp() {
        if (m_parent)
            m_parent->dec_children();
    }
};

frontend::frontend():
    m_imp(new imp()) {
}

frontend::frontend(imp * new_ptr):
    m_imp(new_ptr) {
}

frontend::frontend(std::shared_ptr<imp> const & ptr):
    m_imp(ptr) {
}

frontend::~frontend() {
}

frontend frontend::mk_child() const {
    return frontend(new imp(m_imp));
}

bool frontend::has_children() const {
    return m_imp->has_children();
}

bool frontend::has_parent() const {
    return m_imp->has_parent();
}

frontend frontend::parent() const {
    lean_assert(has_parent());
    return frontend(m_imp->m_parent);
}

environment const & frontend::env() const { return m_imp->m_env; }

level frontend::add_uvar(name const & n, level const & l) { return m_imp->m_env.add_uvar(n, l); }
level frontend::add_uvar(name const & n) { return m_imp->m_env.add_uvar(n); }
level frontend::get_uvar(name const & n) const { return m_imp->m_env.get_uvar(n); }
}

