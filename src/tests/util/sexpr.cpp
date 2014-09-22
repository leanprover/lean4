/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <string>
#include "util/test.h"
#include "util/name.h"
#include "util/init_module.h"
#include "util/numerics/mpq.h"
#include "util/sexpr/sexpr.h"
#include "util/sexpr/sexpr_fn.h"
#include "util/sexpr/format.h"
#include "util/sexpr/options.h"
#include "util/sexpr/init_module.h"
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
    std::cout << sexpr{ sexpr(1, 2), sexpr(2, 3), sexpr(0, 1) } << "\n";
    // list of lists
    std::cout << sexpr{ sexpr{1, 2}, sexpr{2, 3}, sexpr{0, 1} } << "\n";
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
    lean_assert(append(sexpr{1, 2}, sexpr{3, 4}) == (sexpr{1, 2, 3, 4}));
    lean_assert(append(l, nil()) == l);
    lean_assert(append(nil(), l) == l);
    lean_assert(contains(sexpr{10, 20, -2, 0, 10}, [](sexpr e) { return to_int(e) < 0; }));
    lean_assert(!contains(sexpr{10, 20, -2, 0, 10}, [](sexpr e) { return to_int(e) < -10; }));
    lean_assert(is_eqp(s1, s1));
    sexpr s3 = s1;
    lean_assert(is_eqp(s1, s3));
    lean_assert(!is_eqp(sexpr(1), sexpr(1)));
    lean_assert(is_list(nil()));
}

static void tst2() {
    sexpr a;
    a = 2;
    lean_assert(a == sexpr(2));
    lean_assert(a == 2);
    lean_assert(2 == a);
    a = 0.125;
    lean_assert(a == sexpr(0.125));
    lean_assert(a == 0.125);
    lean_assert(0.125 == a);
    a = "foo";
    lean_assert(a == sexpr("foo"));
    lean_assert(a == "foo");
    lean_assert("foo" == a);
    lean_assert(a != "blah");
    lean_assert(a != name("foo"));
    lean_assert(std::string("foo") == a);
    lean_assert(a == std::string("foo"));
    a = name(name("foo"), 1);
    lean_assert(a == sexpr(name(name("foo"), 1)));
    lean_assert(a == name(name("foo"), 1));
    lean_assert(name(name("foo"), 1) == a);
    a = mpq(1, 3);
    lean_assert(a == sexpr(mpq(1, 3)));
    lean_assert(a == mpq(1, 3));
    lean_assert(mpq(1, 3) == a);
    lean_assert(mpq(2, 3) != a);
    a = pow(mpz(2), 100);
    lean_assert(a == sexpr(pow(mpz(2), 100)));
    lean_assert(a == pow(mpz(2), 100));
    lean_assert(pow(mpz(2), 100) == a);
    lean_assert(mpq(pow(mpz(2), 100)) != a);
    lean_assert(sexpr(1, 2) != sexpr(2, 1));
    lean_assert(sexpr(1, 2) != sexpr(1, sexpr(2, nil())));
    lean_assert(sexpr(1, 2) == sexpr(1, sexpr(2)));
}

static void tst3() {
    int sum = 0;
    for_each(sexpr{0, 1, 2, 3, 4},
            [&](sexpr const & e) { sum += to_int(e); });
    lean_assert(sum == 10);
}

static void tst4() {
    lean_assert(sexpr(1) < sexpr(2));
    lean_assert(sexpr() < sexpr(2));
    lean_assert(sexpr("foo") < sexpr(2));
    lean_assert(sexpr(3) > sexpr(2));
    lean_assert(sexpr(2) < sexpr(1.0));
    lean_assert(sexpr("foo") < sexpr(name("foo")));
    lean_assert(!(sexpr(name("foo")) < sexpr(name("foo"))));
    auto e = sexpr(1);
    lean_assert(e == e);
    lean_assert((sexpr{1, 2, 3}) <= (sexpr{1, 2, 3}));
    lean_assert((sexpr{1, 2, 3}) >= (sexpr{1, 2, 3}));
    lean_assert((sexpr{1, 1, 3}) < (sexpr{1, 2, 3}));
    lean_assert((sexpr{2, 1, 3}) > (sexpr{1, 2, 3}));
    lean_assert((sexpr{2, 1, 3}) > (sexpr("foo")));
    lean_assert(sexpr(1, 2) > sexpr(0, 1));
}

static void tst5() {
    lean_assert(foldl(sexpr{1, 2, 3, 4, 5, 6, 7, 8, 9},
                      0,
                      [](int result, sexpr const & s) {
                          return result * 10 + to_int(s);
                      })
                == 123456789);

    lean_assert(foldr(sexpr{1, 2, 3, 4, 5, 6, 7, 8, 9},
                      0,
                      [](sexpr const & s, int result) {
                          return result * 10 + to_int(s);
                      })
                == 987654321);
}

static void tst6() {
    std::ostringstream s;
    sexpr foo("str with \"quote\"");
    s << foo;
    lean_assert(s.str() == "\"str with \\\"quote\\\"\"");
}

static void tst7() {
    sexpr s = sexpr{ sexpr(1, 2), sexpr(2, 3), sexpr(0, 1) };
    std::cout << pp(sexpr{s, s, s, s, s}) << "\n";
    std::cout << pp(sexpr{sexpr(name{"test", "name"}), sexpr(10), sexpr(10.20)}) << "\n";
    format f = highlight(pp(sexpr{s, s, s, s, s}));
    std::cout << f << "\n";
    std::cout << mk_pair(f, options({"pp", "width"}, 1000)) << "\n";
    std::cout << mk_pair(f, update(options({"pp", "width"}, 1000), {"pp", "colors"}, false)) << "\n";
}

static void tst8() {
    lean_assert(!(sexpr("foo") == sexpr(10)));
    lean_assert(sexpr() == sexpr());
    lean_assert(sexpr(true) == sexpr(true));
    lean_assert(sexpr(false) != sexpr(true));
    sexpr s1(10);
    sexpr s2 = s1;
    lean_assert(cmp(s1, s2) == 0);
    lean_assert(cmp(s1, sexpr(20)) < 0);
    lean_assert(cmp(sexpr(), sexpr()) == 0);
    lean_assert(cmp(sexpr("aaa"), sexpr("aaa")) == 0);
    lean_assert(cmp(sexpr("bbb"), sexpr("aaa")) > 0);
    lean_assert(cmp(sexpr(true), sexpr(true)) == 0);
    lean_assert(cmp(sexpr(true), sexpr(false)) > 0);
    lean_assert(cmp(sexpr(false), sexpr(true)) < 0);
    lean_assert(cmp(sexpr(1.0), sexpr(2.0)) < 0);
    lean_assert(cmp(sexpr(name("aaa")), sexpr(name("aaa"))) == 0);
    lean_assert(cmp(sexpr(name("aaa")), sexpr(name("bbb"))) < 0);
    lean_assert(cmp(sexpr(mpz(10)), sexpr(mpz(10))) == 0);
    lean_assert(cmp(sexpr(mpz(20)), sexpr(mpz(10))) > 0);
    lean_assert(cmp(sexpr(mpq(1, 2)), sexpr(mpq(1, 2))) == 0);
    lean_assert(cmp(sexpr(mpq(1, 3)), sexpr(mpq(1, 2))) < 0);
    std::ostringstream s;
    s << sexpr() << " " << sexpr(mpq(1, 2));
    std::cout << s.str() << "\n";
    lean_assert(s.str() == "nil 1/2");
}

static void tst9() {
    int sz = 100000;
    sexpr r;
    for (int i = 0; i < sz; i++) {
        r = sexpr(sexpr(i), r);
    }
}

static sexpr mk_shared(unsigned n) {
    sexpr f("f");
    sexpr a(10);
    sexpr b(true);
    sexpr r(f, sexpr({a, b, sexpr(name({"foo", "bla"})), sexpr(mpz("10")), sexpr(mpq(1, 3))}));
    for (unsigned i = 0; i < n; i++) {
        r = sexpr(f, sexpr(r, r));
    }
    return r;
}

static void tst10() {
    sexpr r = mk_shared(20);
    std::ostringstream out;
    serializer s(out);
    s << r << r;
    std::cout << "Stream Size: " << out.str().size() << "\n";
    std::istringstream in(out.str());
    deserializer d(in);
    sexpr r2, r3;
    d >> r2 >> r3;
    lean_assert(is_eqp(head(tail(r2)), tail(tail(r2))));
    lean_assert(is_eqp(r2, r3));
    lean_assert(r == r2);
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    tst9();
    tst10();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
