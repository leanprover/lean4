/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/test.h"
#include "util/worker_queue.h"
using namespace lean;

static void tst1() {
    worker_queue<int> q(10);
    for (unsigned i = 0; i < 100; i++)
        q.add([=]() { for (unsigned j = 0; j < 1000000; j++) {} return i; });
    std::vector<int> const & r = q.join();
    for (unsigned i = 0; i < r.size(); i++)
        std::cout << r[i] << " ";
    std::cout << "\n";
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}
