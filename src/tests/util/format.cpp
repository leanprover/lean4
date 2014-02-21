/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <vector>
#include <algorithm>
#include <sstream>
#include <utility>
#include <string>
#include "util/test.h"
#include "util/numerics/mpq.h"
#include "util/sexpr/format.h"
#include "util/sexpr/sexpr_fn.h"
#include "util/sexpr/options.h"
using namespace lean;

using std::cout;
using std::endl;

static void tst1() {
    format f_atom1("foo");
    format f_atom2("bar");
    format f_atom3(1);
    format f_atom4(3.1415);
    format f1(highlight(f_atom1), f_atom2);
    format f2{f_atom1, f_atom2, highlight(f_atom3, format::format_color::ORANGE), f_atom4};
    format f3 = compose(f1, f2);
    format f4 = nest(3, f3);
    format f5 = line();
    format f6(f4, f5);
    format f7 = nest(10, format{f6, f4, f6, f4});
    format f8(f_atom1, nest(3, format(line(), f_atom1)));
    format f9 = f7 + f8;
    format f10;
    f10 += f6 + f5 + f3;
    format f11 = above(f1, above(above(f2, f3), f4));
    format f12 = paren(format{format("a"),
                              format("b"),
                              format("c"),
                              format("d")});

    std::vector<std::pair<std::string, format> > v =
        {{"f1",  f1},
         {"f2",  f2},
         {"f3",  f3},
         {"f4",  f4},
         {"f5",  f5},
         {"f6",  f6},
         {"f7",  f7},
         {"f8",  f8},
         {"f9",  f9},
         {"f10", f10},
         {"f11", f11},
         {"f12", f12},
        };

    std::for_each(v.begin(), v.end(),
                  [](std::pair<std::string, format> const & p) {
                      cout << "---- " << p.first << " ----------" << endl
                           << p.second << endl
                           << "--------------------" << endl << endl;
                  });

    std::vector<std::string> ss = {"Last", "weekend's", "revelation", "that", "J.K.", "Rowling", "is", "the", "author", "of", "the", "critically", "acclaimed", "and", "--", "until", "now", "--", "commercially", "unsuccessful", "crime", "novel", "The", "Cuckoo's", "Calling", "has", "electrified", "the", "book", "world", "and", "solidified", "Rowling's", "reputation", "as", "a", "genuine", "writing", "talent:", "After", "all,", "if", "she", "can", "impress", "the", "critics", "without", "the", "benefit", "of", "her", "towering", "reputation,", "then", "surely", "her", "success", "is", "deserved."};

    cout << fillwords(ss.begin(), ss.end());

    std::vector<format> sl = {f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12};

    cout << "fill" << endl;
    cout << std::string(40, '=') << endl;
    pretty(cout, 60, fill(sl.begin(), sl.end()));
    cout << endl;
    cout << std::string(40, '=') << endl;

    cout << "stack" << endl;
    cout << std::string(40, '=') << endl;
    pretty(cout, 60, stack(sl.begin(), sl.end()));
    cout << endl;
    cout << std::string(40, '=') << endl;

    cout << "spread" << endl;
    cout << std::string(40, '=') << endl;
    pretty(cout, 60, spread(sl.begin(), sl.end()));
    cout << endl;
    cout << std::string(40, '=') << endl;
}

static void tst2() {
    format f4 = nest(3, compose(format("foo"), compose(line(), format("bla"))));
    cout << f4 << "\n";
    cout << paren(f4) << "\n";
}

static void tst3() {
    format f_atom1("foo");
    format f_atom2("bar");
    format f1(highlight(f_atom1), f_atom2);
    cout << f1 << "\n";
    cout << mk_pair(f1, options({"pp", "colors"}, false)) << "\n";
}

static void tst4() {
    std::ostringstream s;
    s << "(" << format() << ") ";
    s << "(" << (format("foo") ^ format("bar")) << ") ";
    s << pp(sexpr()) << " ";
    s << pp(sexpr("test")) << " ";
    sexpr s1(mpz(100));
    sexpr s2(mpq(1, 2));
    sexpr s3{s1, s2};
    s << pp(s3);
    std::cout << s.str() << "\n";
    lean_assert_eq(s.str(), "() (foo bar) nil \"test\" (100 1/2)");
}

static void tst5() {
    std::cout << "{" << format() << "}" << "\n";
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    return has_violations() ? 1 : 0;
}
