/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/message_builder.h"
#include "library/type_context.h"
#include "library/message_buffer.h"
#include <string>

namespace lean {

message_builder::message_builder(pos_info_provider const * provider,
                                 std::shared_ptr<abstract_type_context> const & tc,
                                 environment const & env, io_state const & ios,
                                 std::string const & file_name, const pos_info & pos,
                                 message_severity severity) :
    m_pos_info_provider(provider), m_tc(tc),
    m_file_name(file_name), m_pos(pos), m_severity(severity),
    m_caption(), m_text(std::make_shared<string_output_channel>()),
    m_text_stream(env, ios.get_formatter_factory()(env, ios.get_options(), *tc), m_text) {}

message_builder::message_builder(environment const & env, io_state const & ios,
                                 std::string const & file_name, pos_info const & pos,
                                 message_severity severity) :
        message_builder(nullptr, std::make_shared<type_context>(env, ios.get_options()),
                        env, ios, file_name, pos, severity) {}

message message_builder::build() {
    auto text = m_text->str();
    if (!text.empty() && *text.rbegin() == '\n')
        text = text.substr(0, text.size() - 1);
    return message(m_file_name, m_pos, m_severity, m_caption, text);
}

message_builder & message_builder::set_exception(throwable const & ex, bool use_pos) {
    if (auto ext_ex = dynamic_cast<ext_exception const *>(&ex)) {
        if (use_pos && m_pos_info_provider && ext_ex->get_main_expr()) {
            if (auto main_pos = m_pos_info_provider->get_pos_info(*ext_ex->get_main_expr()))
                m_pos = *main_pos;
        }
        *this << *ext_ex;
    } else if (auto f_ex = dynamic_cast<formatted_exception const *>(&ex)) {
        if (use_pos && m_pos_info_provider && f_ex->get_main_expr()) {
            if (auto main_pos = m_pos_info_provider->get_pos_info(*f_ex->get_main_expr()))
                m_pos = *main_pos;
        }
        *this << f_ex->pp();
    } else {
        *this << ex.what();
    }
    return *this;
}

void message_builder::report() {
    report_message(build());
}

}
