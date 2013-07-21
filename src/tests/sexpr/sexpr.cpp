/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "sexpr.h"
#include "sexpr_funcs.h"
#include "mpq.h"
#include "name.h"
#include "test.h"
using namespace lean;

static void tst1() {
    sexpr s1(30, nil());
    sexpr s2("name", s1);
    std::cout << s2 << "\n";
    std::cout << sexpr(s2, s2) << "\n";
    lean_assert(len(s2) == 2);
    lean_assert(is_nil(nil()));
    lean_assert(!is_nil(s2));
    lean_assert(is_cons(s2));
    lean_assert(is_cons(sexpr(s2, s2)));
    lean_assert(is_list(s2));
    lean_assert(is_cons(sexpr(s2, s2)));
    lean_assert(is_list(sexpr(s2, s2)));
    lean_assert(!is_list(sexpr(s2, sexpr(10))));
    lean_assert(s2 == sexpr("name", sexpr(30, nil())));
    lean_assert(s2 != sexpr("name", sexpr(11.2, nil())));
    lean_assert(s2 != sexpr("name", sexpr(20, nil())));
    lean_assert(s2 == sexpr("name", sexpr(30, nil())));
    lean_assert(cdr(s2) == sexpr(30, nil()));
    lean_assert(car(s2) == sexpr("name"));
    std::cout << sexpr(name(name("foo"), 1), s2) << "\n";
    lean_assert(to_mpq(sexpr(mpq("1/3"))) == mpq(1, 3));
    lean_assert(to_int(sexpr(1)) == 1);
    lean_assert(is_int(sexpr(1)));
    lean_assert(!is_nil(sexpr(2)));
    std::cout << sexpr(sexpr(10), sexpr(20)) << "\n";
    std::cout << sexpr{10, 20, 30, 40} << "\n";
    std::cout << sexpr{"foo", "bla", "tst"} << "\n";
    std::cout << sexpr{10.20, 3.2, 4.3} << "\n";
    std::cout << sexpr(10.2) << "\n";
    std::cout << sexpr{10.2} << "\n";
    lean_assert(!is_list(sexpr(10.2)));
    lean_assert(is_list(sexpr{10.2}));
    lean_assert(len(sexpr{10.2}) == 1);
    // list of pairs
    std::cout << sexpr{ sexpr(1,2), sexpr(2,3), sexpr(0,1) } << "\n";
    // list of lists
    std::cout << sexpr{ sexpr{1,2}, sexpr{2,3}, sexpr{0,1} } << "\n";
    lean_assert(reverse(sexpr{1, 2, 3}) == (sexpr{3, 2, 1}));
    sexpr l = map(sexpr{1, 2, 3},
                  [](sexpr e) {
                      return sexpr(to_int(e) + 10);
                  });
    std::cout << l << std::endl;
    lean_assert(l == (sexpr{11, 12, 13}));
    {
        sexpr l = filter(sexpr{10, -2, 3, -1, 0}, [](sexpr e) { return to_int(e) >= 0; });
        std::cout << l << std::endl;
        lean_assert(l == (sexpr{10, 3, 0}));
    }
    lean_assert(member(3, sexpr{10, 2, 3, 1}));
    lean_assert(!member(3, nil()));
    lean_assert(!member(3, sexpr{10, 2, 1}));
    lean_assert(append(sexpr{1,2}, sexpr{3,4}) == (sexpr{1,2,3,4}));
    lean_assert(append(l, nil()) == l);
    lean_assert(append(nil(), l) == l);
    lean_assert(contains(sexpr{10,20,-2,0,10}, [](sexpr e) { return to_int(e) < 0; }));
    lean_assert(!contains(sexpr{10,20,-2,0,10}, [](sexpr e) { return to_int(e) < -10; }));
}

int main() {
    continue_on_violation(true);
    tst1();
    return 0;
}
