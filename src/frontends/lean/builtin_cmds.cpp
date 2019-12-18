/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include <vector>
#include "runtime/sstream.h"
#include "runtime/compact.h"
#include "util/timeit.h"
#include "util/option_declarations.h"
#include "kernel/replace_fn.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/trace.h"
#include "library/aliases.h"
#include "library/export_decl.h"
#include "library/protected.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/class.h"
#include "library/pp_options.h"
#include "library/aux_recursors.h"
#include "library/private.h"
#include "library/type_context.h"
#include "library/reducible.h"
#include "library/placeholder.h"
#include "library/compiler/compiler.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/inductive_cmds.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/print_cmd.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/typed_expr.h"
#include "library/compiler/ir_interpreter.h"
#include "library/time_task.h"

namespace lean {
environment section_cmd(parser & p) {
    name n;
    if (p.curr_is_identifier())
        n = p.check_atomic_id_next("invalid section, atomic identifier expected");
    p.push_local_scope();
    return push_scope(p.env(), p.ios(), scope_kind::Section, n);
}

// Execute open command
environment execute_open(environment env, io_state const & ios, export_decl const & edecl);

environment replay_export_decls_core(environment env, io_state const & ios, unsigned old_sz) {
    list<export_decl> new_export_decls = get_active_export_decls(env);
    unsigned new_sz = length(new_export_decls);
    lean_assert(new_sz >= old_sz);
    unsigned i = 0;
    for (export_decl const & d : new_export_decls) {
        if (i >= new_sz - old_sz)
            break;
        env = execute_open(env, ios, d);
        i++;
    }
    return env;
}

environment replay_export_decls_core(environment env, io_state const & ios) {
    return replay_export_decls_core(env, ios, 0);
}

environment execute_open(environment env, io_state const & ios, export_decl const & edecl) {
    unsigned fingerprint = 0;
    name const & ns = edecl.m_ns;
    fingerprint = hash(fingerprint, ns.hash());
    unsigned old_export_decls_sz = length(get_active_export_decls(env));
    env = activate_export_decls(env, ns);
    for (auto const & p : edecl.m_renames) {
        fingerprint = hash(hash(fingerprint, p.first.hash()), p.second.hash());
        env = add_expr_alias(env, p.first, p.second);
    }
    for (auto const & n : edecl.m_except_names) {
        fingerprint = hash(fingerprint, n.hash());
    }
    if (!edecl.m_had_explicit) {
        buffer<name> except_names;
        to_buffer(edecl.m_except_names, except_names);
        env = add_aliases(env, ns, edecl.m_as, except_names.size(), except_names.data());
    }
    return replay_export_decls_core(env, ios, old_export_decls_sz);
}

environment namespace_cmd(parser & p) {
    name n = p.check_decl_id_next("invalid namespace declaration, identifier expected");
    p.push_local_scope();
    unsigned old_export_decls_sz = length(get_active_export_decls(p.env()));
    environment env = push_scope(p.env(), p.ios(), scope_kind::Namespace, n);
    env = activate_export_decls(env, get_namespace(env));
    return replay_export_decls_core(env, p.ios(), old_export_decls_sz);
}

static environment redeclare_aliases(environment env, parser & p,
                                     local_level_decls old_level_decls,
                                     list<pair<name, expr>> old_entries) {
    environment const & old_env = p.env();
    if (!in_section(old_env))
        return env;
    list<pair<name, expr>> new_entries = p.get_local_entries();
    unsigned new_len = length(new_entries);
    unsigned old_len = length(old_entries);
    lean_assert(old_len >= new_len);
    name_set popped_locals;
    while (old_len > new_len) {
        pair<name, expr> entry = head(old_entries);
        if (is_local_p(entry.second))
            popped_locals.insert(local_name_p(entry.second));
        old_entries = tail(old_entries);
        old_len--;
    }
    name_set popped_levels;
    local_level_decls level_decls = p.get_local_level_decls();
    old_level_decls.for_each([&](name const & n, level const & l) {
            if (is_param(l) && !is_placeholder(l) && !level_decls.contains(n))
                popped_levels.insert(param_id(l));
        });
    return env;
}

environment end_scoped_cmd(parser & p) {
    local_level_decls level_decls  = p.get_local_level_decls();
    list<pair<name, expr>> entries = p.get_local_entries();
    if (!p.has_local_scopes()) {
        throw exception("invalid 'end', there is no open namespace/section");
    }
    p.pop_local_scope();
    if (p.curr_is_identifier()) {
        name n;
        n = p.check_id_next("invalid end of scope, identifier expected");
        environment env = pop_scope(p.env(), p.ios(), n);
        return redeclare_aliases(env, p, level_decls, entries);
    } else {
        environment env = pop_scope(p.env(), p.ios());
        return redeclare_aliases(env, p, level_decls, entries);
    }
}

/* Auxiliary class to setup private naming scope for transient commands such as #check/#reduce/#eval and run_cmd */
class transient_cmd_scope {
    environment            m_env;
    private_name_scope     m_prv_scope;
public:
    transient_cmd_scope(parser & p):
        m_env(p.env()),
        m_prv_scope(true, m_env) {
        p.set_env(m_env);
    }
};

environment check_cmd(parser & p) {
    expr e; names ls;
    transient_cmd_scope cmd_scope(p);
    std::tie(e, ls) = parse_local_expr(p, "_check");
    type_context_old tc(p.env());
    expr type = tc.infer(e);
    if (is_synthetic_sorry(e) && (is_synthetic_sorry(type) || is_metavar(type))) {
        // do not show useless type-checking results such as ?? : ?M_1
        return p.env();
    }
    auto out              = p.mk_message(p.cmd_pos(), p.pos(), INFORMATION);
    formatter fmt         = out.get_formatter();
    unsigned indent       = get_pp_indent(p.get_options());
    format e_fmt    = fmt(e);
    format type_fmt = fmt(type);
    format r = group(e_fmt + space() + format(":") + nest(indent, line() + type_fmt));
    out.set_caption("check result") << r;
    out.report();
    return p.env();
}

environment exit_cmd(parser & p) {
    (p.mk_message(p.cmd_pos(), WARNING) << "using 'exit' to interrupt Lean").report();
    throw interrupt_parser();
}

environment set_option_cmd(parser & p) {
    auto id_kind = parse_option_name(p, "invalid set option, identifier (i.e., option name) expected");
    name id       = id_kind.first;
    data_value_kind k = id_kind.second;
    if (k == data_value_kind::Bool) {
        if (p.curr_is_token_or_id(get_true_tk()))
            p.set_option(id, true);
        else if (p.curr_is_token_or_id(get_false_tk()))
            p.set_option(id, false);
        else
            throw parser_error("invalid Boolean option value, 'true' or 'false' expected", p.pos());
        p.next();
    } else if (k == data_value_kind::String) {
        if (!p.curr_is_string())
            throw parser_error("invalid option value, given option is not a string", p.pos());
        p.set_option(id, p.get_str_val().c_str());
        p.next();
    } else if (k == data_value_kind::Nat) {
        p.set_option(id, p.parse_small_nat());
    } else {
        throw parser_error("invalid option value, 'true', 'false', string, integer or decimal value expected", p.pos());
    }
    return p.env();
}

static void check_identifier(parser & p, environment const & env, name const & ns, name const & id) {
    name full_id = ns + id;
    if (!env.find(full_id))
        throw parser_error(sstream() << "invalid 'open' command, unknown declaration '" << full_id << "'", p.pos());
}

// open/export id (as id)? (id ...) (renaming id->id id->id) (hiding id ... id)
environment open_export_cmd(parser & p, bool open) {
    environment env = p.env();
    while (true) {
        auto pos   = p.pos();
        name ns    = p.check_id_next("invalid 'open/export' command, identifier expected");
        optional<name> real_ns = to_valid_namespace_name(env, ns);
        if (!real_ns)
            throw parser_error(sstream() << "invalid namespace name '" << ns << "'", pos);
        ns = *real_ns;
        name as;
        if (p.curr_is_token_or_id(get_as_tk())) {
            p.next();
            as = p.check_id_next("invalid 'open/export' command, identifier expected");
        }
        buffer<name> exception_names;
        buffer<pair<name, name>> renames;
        bool found_explicit = false;
        // Remark: we currently to not allow renaming and hiding of universe levels
        while (p.curr_is_token(get_lparen_tk())) {
            p.next();
            if (p.curr_is_token_or_id(get_renaming_tk())) {
                p.next();
                while (p.curr_is_identifier()) {
                    name from_id = p.get_name_val();
                    p.next();
                    p.check_token_next(get_arrow_tk(), "invalid 'open/export' command renaming, '->' expected");
                    name to_id = p.check_id_next("invalid 'open/export' command renaming, identifier expected");
                    check_identifier(p, env, ns, from_id);
                    exception_names.push_back(from_id);
                    renames.emplace_back(as+to_id, ns+from_id);
                }
            } else if (p.curr_is_token_or_id(get_hiding_tk())) {
                p.next();
                while (p.curr_is_identifier()) {
                    name id = p.get_name_val();
                    p.next();
                    check_identifier(p, env, ns, id);
                    exception_names.push_back(id);
                }
            } else if (p.curr_is_identifier()) {
                found_explicit = true;
                while (p.curr_is_identifier()) {
                    name id = p.get_name_val();
                    p.next();
                    check_identifier(p, env, ns, id);
                    renames.emplace_back(as+id, ns+id);
                }
            } else {
                throw parser_error("invalid 'open/export' command option, "
                                   "identifier, 'hiding' or 'renaming' expected", p.pos());
            }
            if (found_explicit && !exception_names.empty())
                throw parser_error("invalid 'open/export' command option, "
                                   "mixing explicit and implicit 'open/export' options", p.pos());
            p.check_token_next(get_rparen_tk(), "invalid 'open/export' command option, ')' expected");
        }
        export_decl edecl(ns, as, found_explicit, renames, exception_names);
        if (!open) {
            env = add_export_decl(env, edecl);
        }
        env = execute_open(env, p.ios(), edecl);
        if (!p.curr_is_identifier())
            break;
    }
    return env;
}
static environment open_cmd(parser & p) { return open_export_cmd(p, true); }
static environment export_cmd(parser & p) { return open_export_cmd(p, false); }

static environment init_quot_cmd(parser & p) {
    return p.env().add(mk_quot_decl());
}

environment import_cmd(parser & p) {
    throw parser_error("invalid 'import' command, it must be used in the beginning of the file", p.cmd_pos());
}

environment hide_cmd(parser & p) {
    buffer<name> ids;
    while (p.curr_is_identifier()) {
        name id = p.get_name_val();
        p.next();
        ids.push_back(id);
    }
    if (ids.empty())
        throw parser_error("invalid 'hide' command, identifier expected", p.cmd_pos());
    environment new_env = p.env();
    for (name id : ids) {
        if (get_expr_aliases(new_env, id)) {
            new_env = erase_expr_aliases(new_env, id);
        } else {
            /* TODO(Leo): check if `id` is a declaration and hide it too. */
            throw parser_error(sstream() << "invalid 'hide' command, '" << id << "' is not an alias",
                               p.cmd_pos());
        }
    }
    return new_env;
}

static environment eval_cmd(parser & p) {
    transient_cmd_scope cmd_scope(p);
    auto pos = p.pos();
    expr e; names ls;
    std::tie(e, ls) = parse_local_expr(p, "_eval", /* relaxed */ false);
    if (has_synthetic_sorry(e))
        return p.env();

    type_context_old tc(p.env(), p.get_options());
    auto type = tc.infer(e);
    std::vector<object *> args;

    optional<expr> meta_eval_instance;
    try {
        expr meta_has_eval_type = mk_app(tc, {"Lean", "MetaHasEval"}, type);
        meta_eval_instance = tc.mk_class_instance(meta_has_eval_type);
    } catch (exception &) {}

    if (meta_eval_instance) {
        /* Modify the 'program' to (fun env opts => MetaHasEval.eval env opts e) */
        expr env = tc.push_local("env", mk_const({"Lean", "Environment"}));
        expr opts = tc.push_local("opts", mk_const({"Lean", "Options"}));
        e = tc.mk_lambda(env, tc.mk_lambda(opts,
                                           mk_app(tc, {"Lean", "MetaHasEval", "eval"}, 5,
                                                  {type, *meta_eval_instance, env, opts, e})));
        // run `Environment -> Options -> IO Unit`
        args = { p.env().to_obj_arg(), p.get_options().to_obj_arg(), io_mk_world() };
    } else {
        optional<expr> eval_instance;
        try {
            expr has_eval_type = mk_app(tc, {"Lean", "HasEval"}, type);
            eval_instance = tc.mk_class_instance(has_eval_type);
        } catch (exception &) {}

        if (eval_instance) {
            /* Modify the 'program' to (HasEval.eval e) */
            e = mk_app(tc, {"Lean", "HasEval", "eval"}, 3, type, *eval_instance, e);
            // run `IO Unit`
            args = { io_mk_world() };
        } else {
            // NOTE: HasRepr implies HasEval
            // NOTE: could also mention MetaHasEval but probably shouldn't
            throw exception("result type does not have an instance of type class 'HasRepr' or 'Lean.HasEval'");
        }
    }

    name fn_name = "_main";
    type = tc.infer(e);
    auto new_env = compile_expr(p.env(), p.get_options(), fn_name, ls, type, e, pos);

    auto out = p.mk_message(p.cmd_pos(), p.pos(), INFORMATION);
    out.set_caption("eval result");
    scope_traces_as_messages scope_traces(p.get_stream_name(), p.cmd_pos());
    std::streambuf * saved_cout = std::cout.rdbuf(out.get_text_stream().get_stream().rdbuf());

    object_ref r;

    try {
        if (p.profiling()) {
            timeit timer(out.get_text_stream().get_stream(), "eval time");
            r = object_ref(ir::run_boxed(new_env, fn_name, args.size(), &args[0]));
        } else {
            r = object_ref(ir::run_boxed(new_env, fn_name, args.size(), &args[0]));
        }
    } catch (exception & ex) {
        std::cout.rdbuf(saved_cout);
        out.report();
        throw ex;
    }

    std::cout.rdbuf(saved_cout);
    out.report();
    if (io_result_is_error(r.raw())) {
        message_builder msg = p.mk_message(p.cmd_pos(), p.pos(), ERROR);
        msg << string_to_std(io_result_get_error(r.raw()));
        msg.report();
    }
    return p.env();
}

environment compact_tst_cmd(parser & p) {
    environment env = p.env();
    unsigned num_copies = 0;
    if (p.curr_is_numeral())
        num_copies = p.parse_small_nat();
    buffer<expr> objects_to_write;
    env.for_each_constant([&](constant_info const & d) {
            for (unsigned i = 0; i < num_copies + 1; i++) {
                objects_to_write.push_back(deep_copy(d.get_type()));
                if (d.is_definition())
                    objects_to_write.push_back(deep_copy(d.get_value()));
            }
        });
    tout() << "number of root objects: " << objects_to_write.size() << "\n";
    {
        std::ostringstream out;
        object_compactor compactor;
        {
            timeit timer(out, "compacting objects");
            for (expr const & e : objects_to_write) {
                compactor(e.raw());
            }
            tout() << "compactor size: " << compactor.size() << "\n";
        }
        {
            timeit timer(out, "saving file 'compact.out'");
            FILE * fp = fopen("compact.out", "wb");
            if (fp == nullptr) throw exception("failed to open file 'compact.out'");
            size_t sz = compactor.size();
            fwrite(&sz, sizeof(size_t), 1, fp);
            if (fwrite(compactor.data(), 1, sz, fp) != sz)
                throw exception("failed to write file 'compact.out'");
            fclose(fp);
        }
        void * in_buffer;
        size_t in_sz;
        {
            timeit timer(out, "reading file 'compact.out'");
            FILE * fp = fopen("compact.out", "rb");
            if (fp == nullptr) throw exception("failed to open file 'compact.out'");
            if (fread(&in_sz, sizeof(size_t), 1, fp) != 1)
                throw exception("failed to read file 'compact.out'");
            in_buffer = malloc(in_sz);
            if (fread(in_buffer, 1, in_sz, fp) != in_sz)
                throw exception("failed to read file 'compact.out'");
            fclose(fp);
        }
        compacted_region r(in_sz, in_buffer);
        {
            timeit timer(out, "compacted region fixing pointers time");
            unsigned i = 0;
            while (r.read() != nullptr) {
                i++;
            }
            tout() << "number of read root objects: " << i << "\n";
        }
        tout() << out.str() << "\n";
    }
    {
        std::ostringstream out;
        std::ostringstream sout;
        {
            serializer s(sout);
            timeit timer1(out, "serializing objects");
            for (expr const & e : objects_to_write)
                s << e;
            tout() << "serialization size: " << sout.str().size() << "\n";
        }
        std::istringstream in(sout.str());
        deserializer d(in);
        {
            timeit timer1(out, "deserializing objects");
            for (unsigned i = 0; i < objects_to_write.size(); i++) {
                d.read_object();
            }
        }
        tout() << out.str() << "\n";
    }
    return env;
}

void init_cmd_table(cmd_table & r) {
    add_cmd(r, cmd_info("open",              "create aliases for declarations, and use objects defined in other namespaces",
                        open_cmd));
    add_cmd(r, cmd_info("export",            "create aliases for declarations", export_cmd));
    add_cmd(r, cmd_info("set_option",        "set configuration option", set_option_cmd));
    add_cmd(r, cmd_info("#exit",             "exit", exit_cmd));
    add_cmd(r, cmd_info("#print",            "print a string or information about an indentifier", print_cmd));
    add_cmd(r, cmd_info("section",           "open a new section", section_cmd));
    add_cmd(r, cmd_info("namespace",         "open a new namespace", namespace_cmd));
    add_cmd(r, cmd_info("end",               "close the current namespace/section", end_scoped_cmd));
    add_cmd(r, cmd_info("#check",            "type check given expression, and display its type", check_cmd));
    add_cmd(r, cmd_info("init_quot",         "initialize `quot` type computational rules", init_quot_cmd));
    add_cmd(r, cmd_info("import",            "import module(s)", import_cmd));
    add_cmd(r, cmd_info("hide",              "hide aliases in the current scope", hide_cmd));
    add_cmd(r, cmd_info("#eval",             "evaluate given expression using interpreter/precompiled code", eval_cmd));
    register_decl_cmds(r);
    register_inductive_cmds(r);
    register_structure_cmd(r);
    register_notation_cmds(r);
    // register_tactic_hint_cmd(r);
}

static cmd_table * g_cmds = nullptr;

cmd_table get_builtin_cmds() {
    return *g_cmds;
}

void initialize_builtin_cmds() {
    g_cmds = new cmd_table();
    init_cmd_table(*g_cmds);
}

void finalize_builtin_cmds() {
    delete g_cmds;
}
}
