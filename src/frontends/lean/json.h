/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#ifdef LEAN_SERVER
#pragma once
#include "library/message_buffer.h"
#include "util/json.hpp"

namespace lean {

using json = nlohmann::json;

json json_of_severity(message_severity sev);

json json_of_message(message const & msg);

json json_of_name(name const &);

json serialize_decl(name const & short_name, name const & long_name, environment const & env, options const & o);
json serialize_decl(name const & d, environment const & env, options const & o);

class json_message_stream : public message_buffer {
    std::ostream & m_out;
public:
    json_message_stream(std::ostream & out) : m_out(out) {}
    ~json_message_stream() {}
    void report(message_bucket_id const &, message const & msg) override;
};

}
#endif
