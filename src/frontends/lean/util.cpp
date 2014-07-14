/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/scoped_ext.h"
#include "library/locals.h"
#include "frontends/lean/parser.h"

namespace lean {
void check_atomic(name const & n) {
    if (!n.is_atomic())
        throw exception(sstream() << "invalid declaration name '" << n << "', identifier must be atomic");
}

void check_in_section(parser const & p) {
    if (!in_section(p.env()))
        throw exception(sstream() << "invalid command, it must be used in a section");
}
static name g_root("_root_");
bool is_root_namespace(name const & n) {
    return n == g_root;
}
name remove_root_prefix(name const & n) {
    return n.replace_prefix(g_root, name());
}

// Sort local_names by order of occurrence in the section, and copy the associated parameters to section_ps
void sort_section_params(expr_struct_set const & locals, parser const & p, buffer<expr> & section_ps) {
    for (expr const & l : locals)
        section_ps.push_back(l);
    std::sort(section_ps.begin(), section_ps.end(), [&](expr const & p1, expr const & p2) {
            return p.get_local_index(mlocal_name(p1)) < p.get_local_index(mlocal_name(p2));
        });
}

// Return the levels in \c ls that are defined in the section
levels collect_section_levels(level_param_names const & ls, parser & p) {
    buffer<level> section_ls_buffer;
    for (name const & l : ls) {
        if (p.get_local_level_index(l))
            section_ls_buffer.push_back(mk_param_univ(l));
        else
            break;
    }
    return to_list(section_ls_buffer.begin(), section_ls_buffer.end());
}

// Collect local (section) constants occurring in type and value, sort them, and store in section_ps
void collect_section_locals(expr const & type, expr const & value, parser const & p, buffer<expr> & section_ps) {
    expr_struct_set ls;
    collect_locals(type, ls);
    collect_locals(value, ls);
    sort_section_params(ls, p, section_ps);
}

list<expr> locals_to_context(expr const & e, parser const & p) {
    expr_struct_set ls;
    collect_locals(e, ls);
    buffer<expr> locals;
    sort_section_params(ls, p, locals);
    std::reverse(locals.begin(), locals.end());
    return to_list(locals.begin(), locals.end());
}
}
