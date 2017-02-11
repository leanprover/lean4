/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "util/task_builder.h"

namespace lean {

void test() {
    task<int> a, b;

    task<int> c = task_builder<int>([] () { return 5; }).build();

    task<int> d = map<int>(a, [] (int x) { return x + 1; }).build();
    task<int> e = map<int>(a, [] (int x) { return x + 1; }).build();
    auto f = map<unsigned>(a, [] (int x) { return x + 1; }).build();

    task<std::pair<task<unsigned>, task<char>>> g;
    auto h = mk_deep_dependency(g, [] (buffer<gtask> & deps, std::pair<task<unsigned>, task<char>> const & val) {
        deps.push_back(val.first);
        deps.push_back(val.second);
    });
}

struct cancellable_task_imp : public delegating_task_imp {
    cancellation_token m_ctok;

    cancellable_task_imp(std::unique_ptr<gtask_imp> && base, cancellation_token const & ctok) :
            delegating_task_imp(std::forward<std::unique_ptr<gtask_imp>>(base)), m_ctok(ctok) {}

    ~cancellable_task_imp() { m_ctok->gc(); }

    void execute(void * result) override {
        scope_cancellation_token scope_cancel_tok(&m_ctok);
        m_base->execute(result);
    }
};

std::unique_ptr<gtask_imp> cancellation_support::operator()(std::unique_ptr<gtask_imp> && base) {
    return std::unique_ptr<gtask_imp>(new cancellable_task_imp(
            std::forward<std::unique_ptr<gtask_imp>>(base), m_ctok));
}
}
