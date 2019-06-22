#include <iostream>
#include "util/rb_map.h"
#include "util/nat.h"
#include "util/list.h"
using namespace lean;

struct nat_lt_fn {
    bool operator()(nat const & n1, nat const & n2) const { return n1 < n2; }
};

typedef rb_map<nat, bool, nat_lt_fn> map;

list<map> mk_map(unsigned n, unsigned freq) {
    list<map> stack;
    map m;
    while (n > 0) {
        --n;
        m.insert(nat(n), n%10 == 0);
        if (n % freq == 0) stack = cons(m, stack);
    }
    stack = cons(m, stack);
    return stack;
}

nat fold(map const & m) {
    nat r(0);
    m.for_each([&](nat const & k, bool v) { if (v) r = r + nat(1); });
    return r;
}

int main(int argc, char ** argv) {
    if (argc != 3) {
        std::cout << "invalid number of arguments\n";
        return 1;
    }
    unsigned n = atoi(argv[1]);
    unsigned freq = atoi(argv[2]);
    list<map> m = mk_map(n, freq);
    std::cout << fold(head(m)) << "\n";
    return 0;
}
