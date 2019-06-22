#include <iostream>
#include <map>
#include "util/nat.h"
using namespace lean;

struct nat_lt_fn {
    bool operator()(nat const & n1, nat const & n2) const { return n1 < n2; }
};

typedef std::map<nat, bool, nat_lt_fn> map;

map mk_map(unsigned n) {
    map m;
    while (n > 0) {
        --n;
        m.insert(std::make_pair(nat(n), n%10 == 0));
    }
    return m;
}

nat fold(map const & m) {
    nat r(0);
    for_each(m.begin(), m.end(), [&](std::pair<nat, bool> const & p) { if (p.second) r = r + nat(1); });
    return r;
}

int main(int argc, char ** argv) {
    if (argc != 2) {
        std::cout << "invalid number of arguments\n";
        return 1;
    }
    unsigned n = atoi(argv[1]);
    map m = mk_map(n);
    std::cout << fold(m) << "\n";
    return 0;
}
