/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/st_task_queue.h"

namespace lean {

void st_task_queue::wait_for_finish(gtask const & t) {
    if (t && get_state(t).load() <= task_state::Running) {
        get_state(t).store(task_state::Running);
        execute(t);
        clear(t);
    }
}

void st_task_queue::fail_and_dispose(gtask const & t) {
    if (t && get_state(t).load() < task_state::Running) {
        fail(t, std::make_exception_ptr(cancellation_exception()));
        clear(t);
    }
}

void st_task_queue::submit(gtask const & t) {
    wait_for_finish(t);
}

void st_task_queue::evacuate() {}

void st_task_queue::join() {}

}
