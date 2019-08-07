/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include "kernel/kernel_exception.h"
#include "library/message_builder.h"
#include "library/type_context.h"
#include "library/error_msgs.h"

namespace lean {

message_builder::message_builder(std::shared_ptr<abstract_type_context> const & tc,
                                 environment const & env, io_state const & ios,
                                 std::string const & file_name, const pos_info & pos,
                                 message_severity severity) :
    m_tc(tc), m_file_name(file_name), m_pos(pos), m_severity(severity),
    m_caption(), m_text(std::make_shared<string_output_channel>()),
    m_text_stream(env, ios.get_formatter_factory()(env, ios.get_options(), *tc), m_text) {}

message_builder::message_builder(environment const & env, io_state const & ios,
                                 std::string const & file_name, pos_info const & pos,
                                 message_severity severity) :
        message_builder(std::make_shared<type_context_old>(env, ios.get_options()),
                        env, ios, file_name, pos, severity) {}

message message_builder::build() {
    auto text = m_text->str();
    if (!text.empty() && *text.rbegin() == '\n')
        text = text.substr(0, text.size() - 1);
    return message(m_file_name, m_pos, m_end_pos, m_severity, m_caption, text);
}

message_builder & message_builder::set_exception(std::exception const & ex, bool use_pos) {
    if (auto pos_ex = dynamic_cast<exception_with_pos const *>(&ex)) {
        if (use_pos && pos_ex->get_pos()) {
            m_pos = *pos_ex->get_pos();
        }
    }
    if (auto f_ex = dynamic_cast<formatted_exception const *>(&ex)) {
        *this << f_ex->pp();
    } else if (auto nex = dynamic_cast<nested_exception const *>(&ex)) {
        // reimplement nested_exception::pp to handle nested kernel_exceptions
        *this << nex->generic_exception::pp(get_formatter())
                << "\nnested exception message:\n";
        try {
            std::rethrow_exception(nex->get_exception());
        } catch (std::exception & ex) {
            set_exception(ex, false);
        } catch (...) {
        }
    } else if (auto ext_ex = dynamic_cast<ext_exception const *>(&ex)) {
        *this << *ext_ex;
    } else if (auto kex = dynamic_cast<unknown_constant_exception const *>(&ex)) {
        *this << "unknown declaration '" << kex->get_name() << "'";
    } else if (auto kex = dynamic_cast<already_declared_exception const *>(&ex)) {
        *this << "invalid declaration, a declaration named '" << kex->get_name() << "' has already been declared";
    } else if (auto kex = dynamic_cast<definition_type_mismatch_exception const *>(&ex)) {
        type_context_old ctx(kex->get_environment());
        auto fmt = get_global_ios().get_formatter_factory()(kex->get_environment(), get_global_ios().get_options(), ctx);
        if (kex->get_declaration().is_definition()) {
            auto def = kex->get_declaration().to_definition_val();
            *this << pp_def_type_mismatch(fmt, def.get_name(), kex->get_given_type(), def.get_type());
        } else if (kex->get_declaration().is_theorem()) {
            auto def = kex->get_declaration().to_theorem_val();
            *this << pp_def_type_mismatch(fmt, def.get_name(), kex->get_given_type(), def.get_type());
        } else {
            lean_unreachable();
        }
    } else if (auto kex = dynamic_cast<declaration_has_metavars_exception const *>(&ex)) {
        type_context_old ctx(kex->get_environment(), get_global_ios().get_options());
        auto fmt = get_global_ios().get_formatter_factory()(kex->get_environment(), get_global_ios().get_options(),
                                                            ctx);
        *this << pp_decl_has_metavars(fmt, kex->get_decl_name(), kex->get_expr(), /* is_type */ false);
    } else if (dynamic_cast<declaration_has_free_vars_exception const *>(&ex)) {
        *this << "invalid declaration, it contains free variables";
    } else if (auto kex = dynamic_cast<kernel_exception_with_lctx const *>(&ex)) {
        // TODO(Leo) FIX
#if 0
        type_context_old ctx(kex->get_environment(), get_global_ios().get_options(), metavar_context(),
                             local_context(kex->get_local_ctx()));
        auto fmt = get_global_ios().get_formatter_factory()(kex->get_environment(), get_global_ios().get_options(),
                                                            ctx);
        if (auto kex = dynamic_cast<function_expected_exception const *>(&ex)) {
            *this << pp_function_expected(fmt, kex->get_fn());
        } else if (auto kex = dynamic_cast<type_expected_exception const *>(&ex)) {
            *this << pp_type_expected(fmt, kex->get_type());
        } else if (auto kex = dynamic_cast<def_type_mismatch_exception const *>(&ex)) {
            *this << pp_def_type_mismatch(fmt, kex->get_name(), kex->get_given_type(), kex->get_expected_type());
        } else if (auto kex = dynamic_cast<type_mismatch_exception const *>(&ex)) {
            *this << pp_type_mismatch(fmt, kex->get_given_type(), kex->get_expected_type());
        } else if (auto kex = dynamic_cast<expr_type_mismatch_exception const *>(&ex)) {
            *this << pp_type_mismatch(fmt, kex->get_expr(), kex->get_expected_type());
        } else if (auto kex = dynamic_cast<app_type_mismatch_exception const *>(&ex)) {
            *this << pp_app_type_mismatch(fmt, kex->get_app(), kex->get_function_type(), app_arg(kex->get_app()),
                    kex->get_arg_type());
        } else if (auto kex = dynamic_cast<invalid_proj_exception const *>(&ex)) {
            *this << "invalid projection " << pp_indent_expr(fmt, kex->get_proj());
        } else {
            lean_unreachable();
        }
#endif
    } else {
        *this << ex.what();
    }
    return *this;
}

void message_builder::report() {
    report_message(build());
}

}
