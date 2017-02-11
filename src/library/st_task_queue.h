/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "util/task.h"

namespace lean {

class st_task_queue : public task_queue {
public:
    void wait_for_finish(gtask const &) override;
    void fail_and_dispose(gtask const &) override;

    void submit(gtask const &) override;

    void evacuate() override;

    void join() override;
};

}
