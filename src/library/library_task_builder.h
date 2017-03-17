/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "util/task_builder.h"
#include "util/log_tree.h"
#include "util/cancellable.h"
#include "library/io_state.h"
#include <string>

namespace lean {

struct library_scopes {
    log_tree::node m_lt;

    library_scopes(log_tree::node const & n) : m_lt(n) {}

    std::unique_ptr<gtask_imp> operator()(std::unique_ptr<gtask_imp> &&);
};

struct exception_reporter {
    std::unique_ptr<gtask_imp> operator()(std::unique_ptr<gtask_imp> &&);
};

template <class Res>
task<Res> add_library_task(task_builder<Res> && builder, std::string const & description,
                           bool add_producer = true, log_tree::detail_level lvl = log_tree::DefaultLevel) {
    auto lt = logtree().mk_child({}, description, logtree().get_location(), lvl);
    auto task = builder.wrap(library_scopes(lt)).build();
    if (add_producer) lt.set_producer(task);
    return task;
}

template <class Res>
task<Res> mk_library_task(task_builder<Res> && builder, std::string const & description) {
    return add_library_task(std::forward<task_builder<Res>>(builder), description, false);
}

template <class Res>
task<Res> add_library_task(task_builder<Res> && builder,
                           log_tree::detail_level lvl = log_tree::DefaultLevel,
                           bool add_producer = true) {
    return add_library_task(std::forward<task_builder<Res>>(builder), {}, add_producer, lvl);
}

}
