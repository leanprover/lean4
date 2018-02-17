/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <string>
#include "util/exception.h"
#include "library/io_state_stream.h"
#include "library/messages.h"
#include "library/type_context.h"

namespace lean {

/** Builder for a message object. */
class message_builder {
    std::shared_ptr<abstract_type_context> m_tc;
    std::string                            m_file_name;
    pos_info                               m_pos;
    optional<pos_info>                     m_end_pos;
    message_severity                       m_severity;
    std::string                            m_caption;
    std::shared_ptr<string_output_channel> m_text;
    io_state_stream                        m_text_stream;

public:
    message_builder(std::shared_ptr<abstract_type_context> const & tc,
                    environment const & env, io_state const & ios,
                    std::string const & file_name, pos_info const & pos,
                    message_severity severity);
    message_builder(environment const & env, io_state const & ios,
                    std::string const & file_name, pos_info const & pos,
                    message_severity severity);

    message build();
    void report();

    message_builder & set_file_name(std::string const & file_name) { m_file_name = file_name; return *this; }
    message_builder & set_pos(pos_info const & pos) { m_pos = pos; return *this; }
    message_builder & set_end_pos(pos_info const & pos) { m_end_pos = pos; return *this; }
    message_builder & set_severity(message_severity severity) { m_severity = severity; return *this; }
    message_builder & set_caption(std::string const & caption) { m_caption = caption; return *this; }

    formatter const & get_formatter() const { return m_text_stream.get_formatter(); }

    io_state_stream & get_text_stream() { return m_text_stream; }
    template <typename T>
    message_builder & operator<<(T const & t) { m_text_stream << t; return *this; }

    message_builder & set_exception(std::exception const & ex, bool use_pos = true);
};

}
