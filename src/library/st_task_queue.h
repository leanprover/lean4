/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "util/task_queue.h"

namespace lean {

class st_task_queue : public task_queue {
    progress_cb m_progress_cb;

    void prepare_task(generic_task_result const &result) override;

public:
    st_task_queue();

    optional<generic_task_result> get_current_task() override;
    bool empty() override;
    void join() override;
    void wait(generic_task_result const & t) override;
    void cancel(generic_task_result const & t) override;
    void submit(generic_task_result const &) override;

    void cancel_if(std::function<bool(generic_task *)> const & pred) override; // NOLINT

    void set_progress_callback(progress_cb const &) override;
};

}
