/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include <library/trace.h>
#include <library/message_builder.h>
#include "library/task_helper.h"

namespace lean {

bool execute_task_with_scopes(generic_task_result_cell * task) {
    lean_assert(!task->has_evaluated());
    try {
        scoped_task_context ctx(task->m_task->get_module_id(), task->m_task->get_task_pos());
        scope_message_context scope_msg_ctx(task->m_task->get_bucket());
        try {
            scope_traces_as_messages scope_traces(task->m_task->get_module_id(), task->m_task->get_pos());
            task->execute_and_store_result();
        } catch (task_cancellation_exception) {
            throw;
        } catch (interrupted) {
            throw;
        } catch (throwable & ex) {
            environment env;
            message_builder builder(env, get_global_ios(), task->m_task->get_module_id(), task->m_task->get_pos(), ERROR);
            builder.set_exception(ex);
            builder.report();
            throw;
        }
        return true;
    } catch (interrupted) {
        task->m_ex = std::make_exception_ptr(
                task_cancellation_exception(generic_task_result(task)));
        return false;
    } catch (...) {
        task->m_ex = std::current_exception();
        return false;
    }
}

}
