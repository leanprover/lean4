/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "util/log_tree.h"
#include "util/task_builder.h"
#include <vector>
#include <string>
#include <algorithm>

namespace lean {

void log_tree::notify_core(std::vector<log_tree::event> const & events) {
    if (events.empty()) return;
    for (auto & l : m_listeners)
        l(events);
}

void log_tree::add_listener(log_tree::listener const & l) {
    unique_lock<mutex> lock(m_mutex);
    m_listeners.push_back(l);
}

log_tree::log_tree() {
    auto cell = new node_cell;
    cell->m_tree = this;
    m_root = node(cell);
}

log_tree::~log_tree() {
    std::vector<event> evs;
    m_root.detach_core(evs);
    m_root = node();
}

void log_tree::print_to(std::ostream & out) const {
    get_root().print_to(out, 0);
}

void log_tree::print() const {
    print_to(std::cerr);
}

void log_tree::node::for_each(std::function<bool(log_tree::node const &)> const & fn) const { // NOLINT
    if (fn(*this)) {
        get_children().for_each([&] (name const &, log_tree::node const & c) {
            c.for_each(fn);
        });
    }
};

void log_tree::for_each(std::function<bool(log_tree::node const &)> const & fn) const { // NOLINT
    m_root.for_each(fn);
};

void log_tree::node::detach_core(std::vector<log_tree::event> & events) const {
    if (m_ptr->m_detached) return;
    m_ptr->m_detached = true;
    m_ptr->m_children.for_each([&] (name const &, node const & c) { c.detach_core(events); });
    for (auto & e : m_ptr->m_entries) events.push_back({ event::EntryRemoved, m_ptr, e });
    if (m_ptr->m_producer) events.push_back({event::StateChanged, m_ptr, {}});
    m_ptr->m_producer = nullptr;
}

void log_tree::node::notify(std::vector<log_tree::event> const & events, unique_lock<mutex> & l) const {
    if (!m_ptr->m_detached) {
        l.unlock();
        m_ptr->m_tree->notify_core(events);
    }
}

log_tree::node log_tree::node::clone_core() const {
    auto copy = node(new node_cell);
    copy.m_ptr->m_children = m_ptr->m_children;
    m_ptr->m_children.clear();
    copy.m_ptr->m_tree = m_ptr->m_tree;
    copy.m_ptr->m_detached = m_ptr->m_detached;
    copy.m_ptr->m_entries = m_ptr->m_entries;
    return copy;
}

void log_tree::node::clear_entries() const {
    auto l = lock();

    std::vector<event> events;
    for (auto & e : m_ptr->m_entries) {
        events.push_back({event::EntryRemoved, *this, std::move(e)});
    }
    m_ptr->m_entries.clear();

    notify(events, l);
}

void log_tree::node::add(log_entry const & entry) const {
    auto l = lock();
    m_ptr->m_entries.push_back(entry);
    notify({{event::EntryAdded, *this, entry}}, l);
}

log_tree::node log_tree::node::mk_child(name n, std::string const & description, location const & loc,
                                        detail_level lvl, bool overwrite) {
    auto l = lock();
    std::vector<event> events;

    if (!overwrite && (n.is_anonymous() || m_ptr->m_used_names.contains(n))) {
        for (unsigned i = 0;; i++) {
            name n_(n, i);
            if (!m_ptr->m_used_names.contains(n_)) {
                n = n_;
                break;
            }
        }
    }
    m_ptr->m_used_names.insert(n);

    node child;
    if (auto existing = m_ptr->m_children.find(n)) {
        child = existing->clone_core();
        existing->detach_core(events);
    } else {
        child = node(new node_cell);
        child.m_ptr->m_tree = m_ptr->m_tree;
        child.m_ptr->m_detached = m_ptr->m_detached;
    }
    child.m_ptr->m_detail_level = std::max(m_ptr->m_detail_level, lvl);
    child.m_ptr->m_description = description.empty() ? m_ptr->m_description : description;
    child.m_ptr->m_location = loc;
    m_ptr->m_children.insert(n, child);

    notify(events, l);
    return child;
}

log_tree::state log_tree::node::get_state() const {
    auto l = lock();
    return m_ptr->m_state;
}

void log_tree::node::set_state(state s, bool ignore_illegal_trans) {
    auto l = lock();
    if (s >= m_ptr->m_state) {
        m_ptr->m_state = s;
        notify({{event::StateChanged, *this, {}}}, l);
    } else {
        lean_always_assert(ignore_illegal_trans);
    }
}

void log_tree::node::set_producer(gtask const & prod) {
    auto l = lock();
    if (m_ptr->m_detached) return;
    m_ptr->m_producer = prod;
    notify({{event::ProducerSet, *this, {}}}, l);
}

void log_tree::node::finish() const {
    auto l = lock();
    lean_always_assert(m_ptr->m_state < state::Finished);

    std::vector<event> events;
    m_ptr->m_producer.reset();
    m_ptr->m_state = state::Finished;

    buffer<pair<name, node>> to_delete;
    m_ptr->m_children.for_each([&] (name const & n, node const & c) {
        if (!m_ptr->m_used_names.contains(n))
            to_delete.emplace_back(n, c);
    });

    for (auto & c : to_delete) {
        m_ptr->m_children.erase(c.first);
        c.second.detach_core(events);
    }

    events.push_back({event::StateChanged, *this, {}});
    notify(events, l);
}

std::vector<log_entry> log_tree::node::get_entries() const {
    auto l = lock();
    return m_ptr->m_entries;
}

name_map<lean::log_tree::node> log_tree::node::get_children() const {
    auto l = lock();
    return m_ptr->m_children;
}

void log_tree::node::remove_child(name const & n) const {
    auto l = lock();
    if (auto c = m_ptr->m_children.find(n)) {
        m_ptr->m_children.erase(n);
        std::vector<event> events;
        c->detach_core(events);
        notify(events, l);
    }
}

name_map<log_tree::node> log_tree::node::get_used_children() const {
    auto l = lock();
    name_map<node> used_children;
    m_ptr->m_used_names.for_each([&] (name const & n) {
        if (auto c = m_ptr->m_children.find(n)) {
            used_children.insert(n, *c);
        }
    });
    return used_children;
}

void log_tree::node::reuse(name const & n) const {
    auto l = lock();
    m_ptr->m_used_names.insert(n);
}

name_set log_tree::node::get_used_names() const {
    auto l = lock();
    return m_ptr->m_used_names;
}

gtask log_tree::node::get_producer() const {
    auto l = lock();
    return m_ptr->m_producer;
}

bool log_tree::node::is_detached() const {
    auto l = lock();
    return m_ptr->m_detached;
}

void log_tree::node::print() const {
    print_to(std::cerr, 0);
}

void log_tree::node::print_to(std::ostream & out, unsigned indent) const {
    indent += 2;

    auto l = lock();
    auto begin = m_ptr->m_location.m_range.m_begin, end = m_ptr->m_location.m_range.m_end;
    out << m_ptr->m_location.m_file_name
        << ": " << begin.first << ":" << begin.second << " -- " << end.first << ":" << end.second << ": "
        << m_ptr->m_description << " ("
        << m_ptr->m_entries.size()
        << " entries, detail level = "
        << m_ptr->m_detail_level << ", producer = "
        << std::hex << reinterpret_cast<uintptr_t>(m_ptr->m_producer.get()) << std::dec
        << ")" << std::endl;

    if (auto prod = m_ptr->m_producer) {
        if (auto ex = prod->peek_exception()) {
            for (unsigned i = 0; i < indent; i++) out << ' ';
            out << "producer threw exception: ";
            try {
                std::rethrow_exception(ex);
            } catch (std::exception & ex) {
                out << ex.what();
            } catch (cancellation_exception) {
                out << "<cancelled>";
            } catch (...) {
                out << "<unknown exception>";
            }
            out << "\n";
        }
    }

    auto children = m_ptr->m_children;
    auto used_names = m_ptr->m_used_names;
    l.unlock();

    auto print_child = [&] (name const & n, log_tree::node const & c) {
        for (unsigned i = 0; i < indent; i++) out << ' ';
        out << n;
        if (!used_names.contains(n))
            out << " (unused)";
        out << ": ";
        c.print_to(out, indent);
    };

    name next = "_next";
    children.for_each([&] (name const & n, log_tree::node const & c) {
        if (n != next) print_child(n, c);
    });
    if (auto c = children.find(next)) {
        flet<unsigned> _(indent, indent - 2);
        print_child(next, *c);
    }
}

struct wait_for_finish_helper {
    std::vector<log_tree::node> m_unfinished_roots;

    void gather_unfinished(log_tree::node const & n) {
        n.for_each([&] (log_tree::node const & n1) {
            if (auto prod = n1.get_producer()) {
                m_unfinished_roots.push_back(n1);
                return false;
            } else {
                return true;
            }
        });
    }

    void get_deps(buffer<gtask> & deps) const {
        for (auto & root : m_unfinished_roots) {
            root.for_each([&] (log_tree::node const & n) {
                if (auto prod = n.get_producer()) deps.push_back(prod);
                return true;
            });
        }
    }

    bool is_finished() const { return m_unfinished_roots.empty(); }

    void check() {
        auto old_unfinished_roots = std::move(m_unfinished_roots);
        m_unfinished_roots.clear();
        for (auto & n : old_unfinished_roots) gather_unfinished(n);
    }
};

gtask log_tree::node::wait_for_finish() const {
    auto helper = std::make_shared<wait_for_finish_helper>();
    helper->gather_unfinished(*this);
    if (helper->is_finished()) return mk_pure_task(unit());
    return mk_dependency_task([helper] (buffer<gtask> & deps) {
        helper->check();
        helper->get_deps(deps);
    });
}

bool log_tree::node::has_entry_now(std::function<bool(log_entry const &)> const & fn) const { // NOLINT
    bool res = false;
    for_each([&] (node const & n) {
        if (res) return false;
        for (auto & e : n.get_entries()) {
            if (fn(e)) {
                res = true;
                break;
            }
        }
        return !res;
    });
    return res;
}

task<bool> log_tree::node::has_entry(std::function<bool(log_entry const &)> const & fn) const { // NOLINT
    auto finished = wait_for_finish();
    if (finished->peek_is_finished()) {
        return mk_pure_task<bool>(has_entry_now(fn));
    } else {
        auto t = *this;
        return task_builder<bool>([t, fn] { return t.has_entry_now(fn); }).depends_on(finished).build();
    }
}

LEAN_THREAD_PTR(log_tree::node, g_log_tree);
scope_log_tree_core::scope_log_tree_core(log_tree::node * lt) : flet<log_tree::node *>(g_log_tree, lt) {}

bool has_logtree() {
    return g_log_tree;
}

log_tree::node & logtree() {
    if (g_log_tree) {
        return *g_log_tree;
    } else {
        throw exception("no log tree in scope");
    }
}

scope_log_tree::scope_log_tree(log_tree::node const & lt) : m_node(lt), m_scope(m_node ? &m_node : nullptr) {
    if (m_node) m_node.clear_entries();
}

scope_log_tree::~scope_log_tree() {
    if (m_node) m_node.finish();
}

scope_log_tree::scope_log_tree(std::string const & desc, pos_range const & pos) :
        scope_log_tree(logtree().mk_child({}, desc, {logtree().get_location().m_file_name, pos})) {}

scope_log_tree::scope_log_tree(std::string const & desc) :
        scope_log_tree(logtree().mk_child({}, desc, logtree().get_location())) {}

scope_log_tree::scope_log_tree() : scope_log_tree(std::string()) {}

}
