/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <set>
#include "util/buffer.h"
#include "kernel/trace.h"

namespace lean {
void trace_cell::add_pos_info(format & r, expr const & e, pos_info_provider const * p) {
    if (!p || !e)
        return;
    format f = p->pp(e);
    if (!f)
        return;
    r += f;
    r += space();
}

format trace_cell::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool display_children) const {
    format r;
    add_pos_info(r, get_main_expr(), p);
    r += pp_header(fmt, opts);
    if (display_children) {
        buffer<trace_cell *> children;
        get_children(children);
        unsigned indent = get_pp_indent(opts);
        for (trace_cell * child : children) {
            r += nest(indent, compose(line(), child->pp(fmt, opts, p, display_children)));
        }
    }
    return r;
}

bool trace::has_children() const {
    buffer<trace_cell *> r;
    get_children(r);
    return !r.empty();
}

bool depends_on(trace const & t, trace const & d) {
    buffer<trace_cell *>   todo;
    std::set<trace_cell *> visited;
    buffer<trace_cell *>   children;
    todo.push_back(t.raw());
    while (!todo.empty()) {
        trace_cell * curr = todo.back();
        todo.pop_back();
        if (curr == d.raw()) {
            return true;
        } else {
            children.clear();
            curr->get_children(children);
            for (trace_cell * child : children) {
                if (child->is_shared()) {
                    if (visited.find(child) == visited.end()) {
                        visited.insert(child);
                        todo.push_back(child);
                    }
                } else {
                    todo.push_back(child);
                }
            }
        }
    }
    return false;
}
}
