/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <utility>
#include <string>
#include <vector>
#include <util/name_set.h>
#include "library/versioned_msg_buf.h"
#include "frontends/lean/info_manager.h"

namespace lean {

void versioned_msg_buf::start_bucket(message_bucket_id const & bucket) {
    unique_lock<mutex> lock(m_mutex);

    if (is_bucket_valid_core(bucket)) {
        auto & buf = m_buf[bucket.m_bucket];
        if (buf.m_version < bucket.m_version) {
            buf.m_version = bucket.m_version;
            buf.m_msgs.clear();
            buf.m_infom.reset();
        }
    }
}

void versioned_msg_buf::report(message_bucket_id const & bucket, message const & msg) {
    unique_lock<mutex> lock(m_mutex);

    auto & buf = m_buf[bucket.m_bucket];
    if (buf.m_version < bucket.m_version) {
        throw exception("missing call to start_bucket");
    } else if (buf.m_version == bucket.m_version) {
        buf.m_msgs.push_back(msg);
    }
}

void versioned_msg_buf::finish_bucket(message_bucket_id const & bucket, name_set const & children) {
    unique_lock<mutex> lock(m_mutex);

    auto & buf = m_buf[bucket.m_bucket];
    if (buf.m_version != bucket.m_version) return;

    auto old_children = buf.m_children;
    buf.m_children.clear();

    children.for_each([&] (name const & c) { buf.m_children.insert(c); });

    old_children.for_each([&] (name const & c) {
        if (!buf.m_children.contains(c)) {
            if (m_buf[c].m_version < bucket.m_version)
                erase_bucket(c);
        }
    });
}

void versioned_msg_buf::erase_bucket(name const & bucket) {
    m_buf[bucket].m_children.for_each(
            [&] (name const & c) { erase_bucket(c); });
    m_buf.erase(bucket);
}

bool versioned_msg_buf::is_bucket_valid_core(message_bucket_id const &bucket) {
    if (!bucket.m_bucket.is_atomic()) {
        name parent = bucket.m_bucket.get_prefix();
        auto & parent_buf = m_buf[parent];
        if (parent_buf.m_version > bucket.m_version &&
            !parent_buf.m_children.contains(bucket.m_bucket))
            return false;
    }

    return m_buf[bucket.m_bucket].m_version <= bucket.m_version;
}

bool versioned_msg_buf::is_bucket_valid(message_bucket_id const & bucket) {
    unique_lock<mutex> lock(m_mutex);
    return is_bucket_valid_core(bucket);
}

void versioned_msg_buf::report_info_manager(message_bucket_id const & bucket, info_manager const & infom) {
    unique_lock<mutex> lock(m_mutex);

    auto & buf = m_buf[bucket.m_bucket];
    if (buf.m_version < bucket.m_version) {
        throw exception("missing call to start_bucket");
    } else if (buf.m_version == bucket.m_version) {
        buf.m_infom = std::unique_ptr<info_manager>(new info_manager(infom));
    }
}

std::vector<message> versioned_msg_buf::get_messages() {
    unique_lock<mutex> lock(m_mutex);
    std::vector<message> msgs;
    for (auto & buf : m_buf) {
        for (auto & msg : buf.second.m_msgs)
            msgs.push_back(msg);
    }
    return msgs;
}

std::vector<info_manager> versioned_msg_buf::get_info_managers() {
    unique_lock<mutex> lock(m_mutex);
    std::vector<info_manager> result;
    for (auto & buf : m_buf) {
        if (buf.second.m_infom)
            result.push_back(*buf.second.m_infom);
    }
    return result;
}

}
