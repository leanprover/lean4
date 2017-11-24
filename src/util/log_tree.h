/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <vector>
#include <functional>
#include <memory>
#include <string>
#include <limits>
#include "util/thread.h"
#include "util/int64.h"
#include "util/name_map.h"
#include "util/task.h"
#include "util/message_definitions.h"
#include "util/name_set.h"
#include "util/flet.h"

namespace lean {

struct log_entry_cell {
    virtual ~log_entry_cell() {}
};

using log_entry = std::shared_ptr<log_entry_cell const>;

class log_tree {
public:
    class node;
    struct event;
    using listener = std::function<void(std::vector<event> const &)>;

    enum class state { Created, Running, Cancelled, Finished };

    using detail_level = unsigned;
    constexpr static detail_level
        DefaultLevel = 100,
        ElaborationLevel = 200,
        CrossModuleLintLevel = 1000,
        MaxLevel = std::numeric_limits<detail_level>::max();

    struct node_cell {
        MK_LEAN_RC()
        void dealloc() { delete this; }

        name_map<node> m_children;
        name_set m_used_names;

        log_tree * m_tree = nullptr;
        bool m_detached = false;

        std::vector<log_entry> m_entries;

        location m_location;
        std::string m_description;
        gtask m_producer;
        detail_level m_detail_level = DefaultLevel;
        state m_state = state::Created;

        node_cell() : m_rc(0) {}
    };

    class node {
        friend class log_tree;

        node_cell * m_ptr;

        void detach_core(std::vector<event> & events) const;
        void notify(std::vector<event> const & events, unique_lock<mutex> & lock) const;
        node clone_core() const;

        unique_lock<mutex> lock() const { return unique_lock<mutex>(m_ptr->m_tree->m_mutex); }

        node(node_cell * ptr) : m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }

    public:
        node() : m_ptr(nullptr) {}
        node(node const & n) : node(n.m_ptr) {}
        node(node && n) : m_ptr(n.m_ptr) { n.m_ptr = nullptr; }
        ~node() { if (m_ptr) m_ptr->dec_ref(); }

        node & operator=(node const & n) { LEAN_COPY_REF(n); }
        node & operator=(node && n) { LEAN_MOVE_REF(n); }

        void clear_entries() const;

        void add(log_entry const & entry) const;

        std::vector<log_entry> get_entries() const;
        name_map<node> get_children() const;

        name_map<node> get_used_children() const;
        void remove_child(name const &) const;

        node mk_child(name n, std::string const & description, location const & loc,
                      detail_level lvl = DefaultLevel, bool overwrite = false);
        void reuse(name const & n) const;

        void finish() const;

        void set_producer(gtask const &);
        void set_state(state, bool ignore_illegal_transition = false);
        state get_state() const;
        detail_level get_detail_level() const { return m_ptr->m_detail_level; }
        location const & get_location() const { return m_ptr->m_location; }
        std::string const & get_description() const { return m_ptr->m_description; }
        name_set get_used_names() const;
        gtask get_producer() const;

        bool is_detached() const;

        gtask wait_for_finish() const;

        void for_each(std::function<bool(node const & n)> const &) const; // NOLINT
        bool has_entry_now(std::function<bool(log_entry const &)> const &) const; // NOLINT
        task<bool> has_entry(std::function<bool(log_entry const &)> const &) const; // NOLINT

        void print_to(std::ostream &, unsigned) const;
        void print() const;

        operator bool() const { return m_ptr != nullptr; }
    };

    struct event {
        enum { ProducerSet, EntryAdded, EntryRemoved, StateChanged } m_kind;
        node m_node;
        log_entry m_entry;
    };

private:
    mutex m_mutex;
    std::vector<listener> m_listeners;
    node m_root;

    void notify_core(std::vector<event> const & events);

public:
    log_tree();
    ~log_tree();

    node get_root() const { return m_root; }

    void print_to(std::ostream &) const;
    void print() const;

    void add_listener(listener const & l);

    void for_each(std::function<bool(node const & n)> const &) const; // NOLINT
};

bool has_logtree();
log_tree::node & logtree();
struct scope_log_tree_core : flet<log_tree::node *> {
    scope_log_tree_core(log_tree::node * lt);
};
class scope_log_tree {
    log_tree::node m_node;
    scope_log_tree_core m_scope;

public:
    scope_log_tree(log_tree::node const & lt);
    scope_log_tree();
    scope_log_tree(std::string const & desc);
    scope_log_tree(std::string const & desc, pos_range const & pos);
    ~scope_log_tree();

    log_tree::node & get() { return m_node; }
};

}
