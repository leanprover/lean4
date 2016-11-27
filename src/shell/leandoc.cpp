/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "kernel/inductive/inductive.h"
#include "kernel/quotient/quotient.h"
#include "library/documentation.h"
#include "library/io_state.h"
#include "library/type_context.h"
#include "library/pp_options.h"
#include "library/protected.h"
#include "library/private.h"
#include "library/class.h"
#include "library/util.h"
#include "library/noncomputable.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/structure_cmd.h"

namespace lean {
static char const * get_decl_kind(environment const & env, name const & id) {
    declaration const & d = env.get(id);
    if (d.is_theorem()) return "Theorem";

    if (d.is_axiom() || d.is_constant_assumption()) {
        if (inductive::is_inductive_decl(env, id)) {
            if (is_structure(env, id) && is_class(env, id)) return "Class";
            if (is_structure(env, id) && !is_class(env, id))  return "Structure";
            if (is_class(env, id)) return "Inductive class";
            return "Inductive";
        }

        if (inductive::is_intro_rule(env, id)) return "Constructor";

        if (inductive::is_elim_rule(env, id)) return "Eliminator";

        if (is_quotient_decl(env, id)) return "Quotient type builtin";

        if (d.is_axiom()) return "Axiom";

        return "Constant";
    } else if (d.is_definition()) {
        if (is_instance(env, id)) return "Instance";
        if (is_class(env, id)) return "Class";
        return "Definition";
    }
    return "";
}

static name to_user_name(environment const & env, name const & n) {
    if (auto r = hidden_to_user_name(env, n))
        return *r;
    else
        return n;
}

static void add_string(format & r, char const * s) {
    r += format(s) + space();
}

static void print_constant(std::ostream & out, environment const & env, formatter const & fmt, char const * kind, declaration const & d) {
    options const & o = fmt.get_options();
    out << "```lean\n";
    format r;
    if (is_protected(env, d.get_name()))
        add_string(r, "protected");
    if (!d.is_trusted())
        add_string(r, "meta");
    if (d.is_definition() && is_marked_noncomputable(env, d.get_name()))
        add_string(r, "noncomputable");
    add_string(r, kind);
    name id = to_user_name(env, d.get_name());
    r += format(id);
    r += space() + colon() + space();
    r += nest(get_pp_indent(o), line() + fmt(d.get_type()));
    out << mk_pair(group(r), o);
    out << "\n";
    out << "```\n";
}

static void print_fields(std::ostream & out, environment const & env, formatter const & fmt, name const & S) {
    lean_assert(is_structure(env, S));
    options const & o = fmt.get_options();
    buffer<name> field_names;
    get_structure_fields(env, S, field_names);
    out << "```lean\n";
    for (name const & field_name : field_names) {
        declaration d = env.get(field_name);
        format r;
        r += format(d.get_name());
        r += space() + colon() + space();
        r += nest(get_pp_indent(o), line() + fmt(d.get_type()));
        out << mk_pair(group(r), fmt.get_options()) << "\n";
    }
    out << "```\n";
}

static void print_inductive(std::ostream & out, environment const & env, formatter const & fmt, name const & n) {
    options const & o = fmt.get_options();
    auto idecl = inductive::is_inductive_decl(env, n);
    lean_assert(idecl);
    out << "```lean\n";
    format r;
    if (is_structure(env, n)) {
        if (is_class(env, n))
            add_string(r, "class");
        else
            add_string(r, "structure");
    } else {
        if (is_class(env, n))
            add_string(r, "inductive class");
        else
            add_string(r, "inductive");
    }
    r += space() + format(n);
    r += space() + colon() + space();
    r += nest(get_pp_indent(o), line() + fmt(env.get(n).get_type()));
    out << mk_pair(group(r), o) << "\n";
    out << "```\n";
    if (is_structure(env, n)) {
        out << "**Fields:**\n";
        print_fields(out, env, fmt, n);
    } else {
        out << "**Constructors:**\n";
        buffer<name> constructors;
        get_intro_rule_names(env, n, constructors);
        out << "```lean\n";
        for (name const & c : constructors) {
            format r   = format(c);
            r += space() + colon() + space();
            r += nest(get_pp_indent(o), line() + fmt(env.get(c).get_type()));
            out << mk_pair(group(r), o) << "\n";
        }
        out << "```\n";
    }
}

static void print_id_info(std::ostream & out, environment const & env, formatter const & fmt, name const & id) {
    declaration const & d = env.get(id);
    if (d.is_theorem()) {
        print_constant(out, env, fmt, "theorem", d);
    } else if (d.is_axiom() || d.is_constant_assumption()) {
        if (inductive::is_inductive_decl(env, id)) {
            print_inductive(out, env, fmt, id);
        } else if (inductive::is_intro_rule(env, id)) {
            print_constant(out, env, fmt, "constructor", d);
                } else if (inductive::is_elim_rule(env, id)) {
            print_constant(out, env, fmt, "eliminator", d);
        } else if (is_quotient_decl(env, id)) {
            print_constant(out, env, fmt, "builtin-quotient-type-constant", d);
        } else if (d.is_axiom()) {
            print_constant(out, env, fmt, "axiom", d);
        } else {
            print_constant(out, env, fmt, "constant", d);
        }
    } else if (d.is_definition()) {
        if (is_instance(env, id))
            print_constant(out, env, fmt, "instance", d);
        else if (is_class(env, id))
            print_constant(out, env, fmt, "class", d);
        else
            print_constant(out, env, fmt, "def", d);
    }
}

static void gen_decl_doc(std::ostream & out, environment const & env, formatter const & fmt, name const & decl_name) {
    out << "<a name=\"" << decl_name << "\"></a>**" << get_decl_kind(env, decl_name) << "** " << decl_name << "\n";
    print_id_info(out, env, fmt, decl_name);
}

void gen_doc(environment const & env, options const & _opts, std::ostream & out) {
    type_context ctx(env);
    options opts     = _opts.update_if_undef(name{"pp", "width"}, 100);
    auto fmt_factory = lean::mk_pretty_formatter_factory();
    auto fmt         = fmt_factory(env, opts, ctx);
    buffer<doc_entry> entries;
    get_module_doc_strings(env, entries);
    for (doc_entry const & entry : entries) {
        if (auto decl_name = entry.get_decl_name()) {
            gen_decl_doc(out, env, fmt, *decl_name);
            out << "\n";
            out << entry.get_doc();
        } else {
            out << entry.get_doc();
        }
        out << "\n";
    }
}
}
