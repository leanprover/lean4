/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <util/utf8.h>
#include "library/library_task_builder.h"
#include "frontends/lean/module_parser.h"
#include "frontends/lean/info_manager.h"
#include <string>
#include <vector>

namespace lean {

pos_info find_end_pos(std::string const & src) {
    std::istringstream in(src);

    unsigned line_no = 0;
    std::string line;
    while (!in.eof()) {
        line_no++;
        std::getline(in, line);
    }
    return {line_no, static_cast<unsigned>(utf8_strlen(line.c_str())) + 1};
}

module_parser::module_parser(std::string const & file_name, std::string const & content,
                                   environment const & initial_env, module_loader const & import_fn) :
    m_in(content), m_parser(initial_env, get_global_ios(), import_fn, m_in, file_name), m_end_pos(find_end_pos(content)) {
}

module_parser::~module_parser() {}

pair<cancellation_token, task<module_parser_result>>
module_parser::resume(module_parser_result const & res, optional<std::vector<gtask>> const & dependencies) {
    snapshot const & s = *res.m_snapshot_at_end;
    m_parser.m_scanner.skip_to_pos(s.m_pos);
    m_parser.m_env                = s.m_env;
    m_parser.m_ngen               = s.m_ngen;
    m_parser.m_ios.set_options(s.m_options);
    m_parser.m_local_level_decls  = s.m_lds;
    m_parser.m_local_decls        = s.m_eds;
    m_parser.m_level_variables    = s.m_lvars;
    m_parser.m_variables          = s.m_vars;
    m_parser.m_include_vars       = s.m_include_vars;
    m_parser.m_imports_parsed     = s.m_imports_parsed;
    m_parser.m_ignore_noncomputable = s.m_noncomputable_theory;
    m_parser.m_parser_scope_stack = s.m_parser_scope_stack;
    m_parser.m_next_inst_idx      = s.m_next_inst_idx;
    auto lt = res.m_lt;
    scope_log_tree_core scope_lt(&lt);
    return parse_next_command_like(dependencies);
}

module_parser_result module_parser::parse(optional<std::vector<gtask>> const & dependencies) {
    scope_log_tree lt(logtree().mk_child(
        "_next", "parsing", {m_parser.m_file_name, {{0, 1}, m_end_pos}},
        log_tree::DefaultLevel, true));

    module_parser_result res;
    if (m_save_info)
        res.m_snapshot_at_end = m_parser.mk_snapshot();
    res.m_range = {{1, 0}, {1, 0}};
    res.m_lt = lt.get();
    std::tie(res.m_cancel, res.m_next) = parse_next_command_like(dependencies);
    return res;
}

pair<cancellation_token, task<module_parser_result>>
module_parser::parse_next_command_like(optional<std::vector<gtask>> const & dependencies) {
    auto self = shared_from_this();
    auto begin_pos = m_parser.pos();
    lean_assert(begin_pos >= pos_info(1, 0));

    auto fn = [self, begin_pos] {
        scope_pos_info_provider scope_pip(self->m_parser); // for nested_elaborator_exception::pp

        bool done = false;
        try {
            check_system("module_parser::parse_next_command_like");
            auto_reporting_info_manager_scope scope_infom(self->m_parser.m_file_name, self->m_save_info);
            done = self->m_parser.parse_command_like();
        } catch (parser_exception & ex) {
            report_message(ex);
            self->m_parser.sync_command();
        } catch (throwable & ex) {
            self->m_parser.mk_message(self->m_parser.m_last_cmd_pos, ERROR).set_exception(ex).report();
            self->m_parser.sync_command();
        } catch (interrupt_parser) {
            // this exception is thrown by the exit command
            done = true;
        }
        auto end_pos = self->m_parser.pos();
        if (done) end_pos = self->m_end_pos;
        lean_assert(end_pos >= begin_pos);

        module_parser_result res;
        if (done || self->m_save_info)
            res.m_snapshot_at_end = self->m_parser.mk_snapshot();
        res.m_range = {begin_pos, end_pos};
        res.m_lt = logtree();
        if (!done) {
            std::tie(res.m_cancel, res.m_next) = self->parse_next_command_like();
        }
        return res;
    };

    auto ctok = mk_cancellation_token(global_cancellation_token());
    scope_cancellation_token scope_ctok(&ctok);
    auto lt = logtree().mk_child(
            "_next",
            (sstream() << "parsing at line " << begin_pos.first).str(),
            {m_parser.m_file_name, {begin_pos, m_end_pos}},
            log_tree::DefaultLevel, true);
    if (dependencies || m_separate_tasks) {
        auto task = task_builder<module_parser_result>(std::move(fn))
                .set_cancellation_token(ctok)
                .wrap(library_scopes(lt))
                .depends_on(dependencies ? *dependencies : std::vector<gtask>())
                .build();
        lt.set_producer(task);
        return {ctok, task};
    } else {
        scope_log_tree scope_lt(lt);
        return {ctok, mk_pure_task(fn())};
    }
}

void module_parser::break_at_pos(pos_info const & pos, bool complete) {
    m_parser.set_break_at_pos(pos);
    m_parser.set_complete(complete);
}

module_parser_result module_parser::resume_from_start(
        module_parser_result const & old_res, cancellation_token const & ctok,
        pos_info const & diff_pos,
        optional<std::vector<gtask>> const & dependencies,
        bool cancel_old) {
    auto res = old_res;

    lean_assert(!old_res.m_lt.is_detached());
    lean_assert(!ctok->is_cancelled());

    if (res.m_next && !res.m_cancel->is_cancelled()) {
        if (auto next = peek(res.m_next)) {
            if (next->m_range.m_end < diff_pos) {
                res.m_next = mk_pure_task(resume_from_start(*next, res.m_cancel, diff_pos, dependencies, cancel_old));
                return res;
            }
        }
    }

    auto next_ctok = old_res.m_cancel;
    if (cancel_old) {
        cancel(next_ctok);
        next_ctok = mk_cancellation_token(ctok);
        lean_assert(!next_ctok->is_cancelled());
    }

    scope_cancellation_token scope_cancel(&next_ctok);
    std::tie(res.m_cancel, res.m_next) = resume(old_res, dependencies);
    return res;
}

task<module_parser_result> get_end(module_parser_result const & res) {
    auto cur = std::make_shared<module_parser_result>(res);
    return task_builder<module_parser_result>([cur] {
        while (cur->m_next) *cur = get(cur->m_next);
        return *cur;
    }).depends_on_fn([cur] (buffer<gtask> & deps) {
        while (cur->m_next) {
            if (auto next = peek(cur->m_next)) {
                *cur = *next;
            } else {
                deps.push_back(cur->m_next);
                return;
            }
        }
    }).execute_eagerly().build();
}

}
