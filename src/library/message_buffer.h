/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <string>
#include <vector>
#include "util/output_channel.h"
#include "util/exception.h"
#include "util/name_set.h"
#include "library/messages.h"

namespace lean {

typedef uint64 period;

struct message_bucket_id {
    name m_bucket;
    period m_version;
};

class info_manager;

class message_buffer {
public:
    virtual ~message_buffer() {}
    virtual void start_bucket(message_bucket_id const & bucket);
    virtual void report(message_bucket_id const & bucket, message const & msg);
    virtual void finish_bucket(message_bucket_id const & bucket, name_set const & children);
    virtual void report_info_manager(message_bucket_id const & bucket, info_manager const & infom);
    virtual bool is_bucket_valid(message_bucket_id const & bucket);
};

using null_message_buffer = message_buffer;

class stream_message_buffer : public message_buffer {
    std::ostream & m_out;
public:
    stream_message_buffer(std::ostream & out) : m_out(out) {}
    void report(message_bucket_id const & bucket, message const & msg) override;
};

message_buffer & get_global_message_buffer();
class scoped_message_buffer {
    message_buffer * m_old;
public:
    scoped_message_buffer(message_buffer * msg_buf);
    ~scoped_message_buffer();
};

class scope_message_context {
    scope_message_context * m_old;
    message_bucket_id m_bucket;
    name_set m_sub_buckets;
public:
    scope_message_context(message_bucket_id const &);
    scope_message_context(message_bucket_id const &, name_set const & sub_buckets_to_reuse);
    scope_message_context(std::string const &, name_set const & sub_buckets_to_reuse);
    scope_message_context(std::string const &);
    scope_message_context();
    ~scope_message_context();

    message_bucket_id get_bucket_id() const { return m_bucket; }
    name_set get_sub_buckets() const { return m_sub_buckets; }

    message_bucket_id new_sub_bucket();
    message_bucket_id new_sub_bucket(std::string const &);
};

message_bucket_id get_global_msg_bucket_id();
scope_message_context & get_scope_message_context();
void report_message(message const &);
void report_info_manager(info_manager const &);

}
