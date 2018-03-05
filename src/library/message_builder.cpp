/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include "library/message_builder.h"
#include "library/type_context.h"

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
    if (auto ext_ex = dynamic_cast<ext_exception const *>(&ex)) {
        *this << *ext_ex;
    } else if (auto f_ex = dynamic_cast<formatted_exception const *>(&ex)) {
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
