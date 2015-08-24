/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/name_set.h"
#include "util/name_map.h"
#include "util/list_fn.h"
#include "kernel/declaration.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/inductive/inductive.h"
#include "library/update_declaration.h"

namespace lean {
// Collect all universe global levels occurring in l into ls
static void collect_global_levels(level const & l, name_set & ls) {
    for_each(l, [&](level const & l) {
            if (is_global(l))
                ls.insert(global_id(l));
            return true;
        });
}

// Collect all universe global levels occurring in e into ls
static void collect_global_levels(expr const & e, name_set & ls) {
    for_each(e, [&](expr const & e, unsigned) {
            if (is_constant(e)) {
                for_each(const_levels(e), [&](level const & l) { collect_global_levels(l, ls); });
            } else if (is_sort(e)) {
                collect_global_levels(sort_level(e), ls);
            }
            return true;
        });
}

// Return a new ls s.t. there is no conflict between the names in ls and globals.
// Store the mapping between old and new names in param_name_map.
static level_param_names sanitize_level_params(level_param_names const & ls, name_set const & globals,
                                               name_map<name> & param_name_map) {
    buffer<name> new_params;
    for (name const & n : ls) {
        if (globals.contains(n)) {
            unsigned i = 1;
            name new_n = n.append_after(i);
            while (globals.contains(new_n)) {
                i++;
                name new_n = n.append_after(i);
            }
            param_name_map.insert(n, new_n);
            new_params.push_back(new_n);
        } else {
            new_params.push_back(n);
        }
    }
    if (param_name_map.empty())
        return ls;
    return to_list(new_params.begin(), new_params.end());
}

// Rename universe parameters occurring in l using the given mapping
static level rename_param_levels(level const & l, name_map<name> const & param_name_map) {
    return replace(l, [&](level const & l) {
            if (is_param(l)) {
                if (auto it = param_name_map.find(param_id(l))) {
                    return some_level(mk_param_univ(*it));
                }
            }
            return none_level();
        });
}

static levels rename_param_levels(levels const & ls, name_map<name> const & param_name_map) {
    return map(ls, [&](level const & l) { return rename_param_levels(l, param_name_map); });
}

// Rename universe parameters occurring in e using the given mapping
static expr rename_param_levels(expr const & e, name_map<name> const & param_name_map) {
    return replace(e, [&](expr const & e) {
            if (is_constant(e))
                return some_expr(update_constant(e, rename_param_levels(const_levels(e), param_name_map)));
            else if (is_sort(e))
                return some_expr(update_sort(e, rename_param_levels(sort_level(e), param_name_map)));
            else
                return none_expr();
        });
}

declaration sanitize_level_params(declaration const & d) {
    name_set globals;
    collect_global_levels(d.get_type(), globals);
    if (d.is_definition())
        collect_global_levels(d.get_value(), globals);
    if (globals.empty())
        return d;
    name_map<name> param_name_map;
    level_param_names new_ls = sanitize_level_params(d.get_univ_params(), globals, param_name_map);
    if (param_name_map.empty())
        return d;
    expr new_type = rename_param_levels(d.get_type(), param_name_map);
    if (d.is_constant_assumption()) {
        return update_declaration(d, new_ls, new_type);
    } else {
        expr new_value = rename_param_levels(d.get_value(), param_name_map);
        return update_declaration(d, new_ls, new_type, new_value);
    }
}

using inductive::inductive_decl;
using inductive::inductive_decl_name;
using inductive::inductive_decl_type;
using inductive::inductive_decl_intros;
using inductive::intro_rule;
using inductive::mk_intro_rule;
using inductive::intro_rule_name;
using inductive::intro_rule_type;

pair<level_param_names, list<inductive_decl>> sanitize_level_params(level_param_names const & ls, list<inductive_decl> const & decls) {
    name_set globals;
    for (auto const & d : decls) {
        collect_global_levels(inductive_decl_type(d), globals);
        for (auto const & r : inductive_decl_intros(d))
            collect_global_levels(intro_rule_type(r), globals);
    }
    if (globals.empty())
        return mk_pair(ls, decls);
    name_map<name> param_name_map;
    level_param_names new_ls = sanitize_level_params(ls, globals, param_name_map);
    if (param_name_map.empty())
        return mk_pair(ls, decls);
    buffer<inductive_decl> new_decls;
    for (auto const & d : decls) {
        expr new_type = rename_param_levels(inductive_decl_type(d), param_name_map);
        buffer<intro_rule> new_rules;
        for (auto const & r : inductive_decl_intros(d)) {
            expr new_type = rename_param_levels(intro_rule_type(r), param_name_map);
            new_rules.push_back(mk_intro_rule(intro_rule_name(r), new_type));
        }
        new_decls.push_back(inductive_decl(inductive_decl_name(d),
                                           new_type,
                                           to_list(new_rules.begin(), new_rules.end())));
    }
    return mk_pair(new_ls, to_list(new_decls.begin(), new_decls.end()));
}
}
