/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include <vector>
#include "library/message_buffer.h"
#include "frontends/lean/info_manager.h"

namespace lean {

void message_buffer::start_bucket(message_bucket_id const &) {}
void message_buffer::report(message_bucket_id const &, message const &) {}
void message_buffer::finish_bucket(message_bucket_id const &, name_set const &) {}
bool message_buffer::is_bucket_valid(message_bucket_id const &) { return true; }
void message_buffer::report_info_manager(message_bucket_id const &, info_manager const &) {}

void stream_message_buffer::report(message_bucket_id const &, message const & msg) {
    if (msg.get_severity() != INFORMATION) {
        m_out << msg.get_file_name() << ":" << msg.get_pos().first << ":" << msg.get_pos().second << ": ";
        switch (msg.get_severity()) {
            case INFORMATION: break;
            case WARNING: m_out << "warning: "; break;
            case ERROR:   m_out << "error: ";   break;
        }
        if (!msg.get_caption().empty())
            m_out << msg.get_caption() << ":\n";
    }
    m_out << msg.get_text() << "\n";
}

LEAN_THREAD_PTR(message_buffer, g_msg_buf);
scoped_message_buffer::scoped_message_buffer(message_buffer * buf) :
    m_old(g_msg_buf) { g_msg_buf = buf; }
scoped_message_buffer::~scoped_message_buffer() { g_msg_buf = m_old; }

message_buffer & get_global_message_buffer() {
    if (g_msg_buf) {
        return *g_msg_buf;
    } else {
        throw exception("global message buffer not initialized");
    }
}

LEAN_THREAD_PTR(scope_message_context, g_msg_ctx);

message_bucket_id get_global_msg_bucket_id() {
    return get_scope_message_context().get_bucket_id();
}

void report_message(message const & msg) {
    get_global_message_buffer().report(get_global_msg_bucket_id(), msg);
}

void report_info_manager(info_manager const & infom) {
    get_global_message_buffer().report_info_manager(get_global_msg_bucket_id(), infom);
}

scope_message_context & get_scope_message_context() {
    if (g_msg_ctx) {
        return *g_msg_ctx;
    } else {
        throw exception("message context not initialized");
    }
}

scope_message_context::scope_message_context(message_bucket_id const & bucket) :
        scope_message_context(bucket, {}) {}
scope_message_context::scope_message_context(message_bucket_id const & bucket,
                                             name_set const & sub_buckets_to_reuse) :
        m_old(g_msg_ctx), m_bucket(bucket), m_sub_buckets(sub_buckets_to_reuse) {
    g_msg_ctx = this;
    get_global_message_buffer().start_bucket(m_bucket);
    DEBUG_CODE(m_sub_buckets.for_each([=] (name const & b) {
        lean_assert(b.get_prefix() == m_bucket.m_bucket); });)
}
scope_message_context::scope_message_context() :
    scope_message_context(g_msg_ctx->new_sub_bucket()) {}
scope_message_context::scope_message_context(std::string const & sub_name) :
    scope_message_context(g_msg_ctx->new_sub_bucket(sub_name)) {}
scope_message_context::scope_message_context(std::string const & sub_name, name_set const & sub_buckets_to_reuse) :
    scope_message_context(g_msg_ctx->new_sub_bucket(sub_name), sub_buckets_to_reuse) {}
scope_message_context::~scope_message_context() {
    get_global_message_buffer().finish_bucket(m_bucket, m_sub_buckets);
    if (m_info_manager && !m_info_manager->empty())
        get_global_message_buffer().report_info_manager(m_bucket, *m_info_manager);
    g_msg_ctx = m_old;
}
message_bucket_id scope_message_context::new_sub_bucket() {
    unsigned i = m_sub_buckets.size();
    name n;
    do { n = name(m_bucket.m_bucket, i++); } while (m_sub_buckets.contains(n));
    m_sub_buckets.insert(n);
    return { n, m_bucket.m_version };
}
message_bucket_id scope_message_context::new_sub_bucket(std::string const & s) {
    name n(m_bucket.m_bucket, s.c_str());
    if (m_sub_buckets.contains(n)) {
        unsigned i = 0;
        name n_new;
        do { n_new = n.append_after(i++); } while (m_sub_buckets.contains(n_new));
        n = n_new;
    }
    m_sub_buckets.insert(n);
    return { n, m_bucket.m_version };
}

info_manager * scope_message_context::enable_info_manager(std::string const & file_name) {
    if (!m_info_manager)
        m_info_manager = std::unique_ptr<info_manager>(new info_manager(file_name));
    return m_info_manager.get();
}

}
