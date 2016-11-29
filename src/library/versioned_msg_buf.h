/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <vector>
#include <unordered_map>
#include "util/name.h"
#include "library/message_buffer.h"
#include "frontends/lean/info_manager.h"

namespace lean {

class versioned_msg_buf : public message_buffer {
    // TODO(gabriel): structure as tree?
    struct msg_bucket {
        std::vector<message> m_msgs;
        std::unique_ptr<info_manager> m_infom;
        period m_version = 0;

        name_set m_children;
    };

    mutex m_mutex;
    std::unordered_map<name, msg_bucket, name_hash> m_buf;

    void erase_bucket(name const & bucket);
    bool is_bucket_valid_core(message_bucket_id const & bucket);

public:
    versioned_msg_buf() {}

    void start_bucket(message_bucket_id const & bucket) override;
    void report(message_bucket_id const & bucket, message const & msg) override;
    void finish_bucket(message_bucket_id const & bucket, name_set const & children) override;
    bool is_bucket_valid(message_bucket_id const & bucket) override;
    void report_info_manager(message_bucket_id const & bucket, info_manager const & infom) override;

    std::vector<message> get_messages();
    std::vector<info_manager> get_info_managers();
};

}
