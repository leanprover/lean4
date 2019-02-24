#include <cstdlib>
#include <iostream>
#include "init/init.h"
#include "util/rb_map.h"
#include "util/nat.h"
using namespace lean;

struct nat_cmp {
    int operator()(nat const & n1, nat const & n2) const {
        if (n1 < n2) return -1;
        if (n2 < n1) return 1;
        return 0;
    }
};

int main(int argc, char ** argv) {
    lean::initialize();
    rb_map<nat, bool, nat_cmp> m;
    unsigned n = 0;
    if (argc == 2) {
        n = std::atoi(argv[1]);
    }
    for (unsigned i = 0; i < n; i++) {
        m.insert(nat(i), i%10 == 0);
    }
    nat r(0u);
    m.for_each([&](nat const & k, bool v) {
            if (v) r = r + nat(1);
        });
    std::cout << r << "\n";
    return 0;
}
