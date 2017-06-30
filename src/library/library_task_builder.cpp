/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/library_task_builder.h"
#include "library/message_builder.h"

namespace lean {

struct library_scopes_imp : public delegating_task_imp {
    io_state m_ios;
    log_tree::node m_lt;

    library_scopes_imp(std::unique_ptr<gtask_imp> && base, log_tree::node const & lt) :
        delegating_task_imp(std::forward<std::unique_ptr<gtask_imp>>(base)),
        m_ios(get_global_ios()), m_lt(lt) {}

    // TODO(gabriel): set logtree status to cancelled?

    void execute(void * result) override {
        scope_global_ios scope1(m_ios);
        scope_log_tree scope2(m_lt);
        if (m_lt) m_lt.set_state(log_tree::state::Running);
        try {
            delegating_task_imp::execute(result);
        } catch (interrupted) {
            if (m_lt) m_lt.set_state(log_tree::state::Cancelled);
            throw;
        }
    }
};

std::unique_ptr<gtask_imp> library_scopes::operator()(std::unique_ptr<gtask_imp> && base) {
    return std::unique_ptr<gtask_imp>(new library_scopes_imp(
            std::forward<std::unique_ptr<gtask_imp>>(base), m_lt));
}

struct exception_reporter_imp : public delegating_task_imp {
    exception_reporter_imp(std::unique_ptr<gtask_imp> && base) :
        delegating_task_imp(std::forward<std::unique_ptr<gtask_imp>>(base)) {}

    void execute(void * result) override {
        try {
            delegating_task_imp::execute(result);
        } catch (std::exception & ex) {
            message_builder(environment(), get_global_ios(),
                            logtree().get_location().m_file_name,
                            logtree().get_location().m_range.m_begin,
                            ERROR)
                    .set_exception(ex)
                    .report();
            throw;
        }
    }
};

std::unique_ptr<gtask_imp> exception_reporter::operator()(std::unique_ptr<gtask_imp> && base) {
    return std::unique_ptr<gtask_imp>(new exception_reporter_imp(
            std::forward<std::unique_ptr<gtask_imp>>(base)));
}

}
