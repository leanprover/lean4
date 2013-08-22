/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstring>
#include <sstream>
#include "test.h"
#include "options.h"
using namespace lean;

static void tst1() {
    options opt;
    std::cout << opt << "\n";
    opt = opt.update("tst", 10);
    std::cout << opt << "\n";
    opt = opt.update("foo", true);
    std::cout << opt << "\n";
}

static void tst2() {
    options opt;
    opt = update(opt, name{"test", "foo"}, 10);
    opt = update(opt, name{"color"}, 20);
    opt = update(opt, name{"ratio"}, 10.5);
    sexpr s{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
    opt = update(opt, name{"sp", "order"}, sexpr{s, s, s, s, s, s});
    opt = update(opt, name{"test", "long", "names", "with", "several", "parts"}, true);
    std::cout << pp(opt) << "\n";
}

static void tst3() {
    options opt;
    opt = update(opt, name{"test", "foo"}, 10);
    opt = update(opt, name{"color"}, 20);
    std::cout << pp(opt) << "\n";
    opt = update(opt, name{"color"}, 20);
    std::cout << pp(opt) << "\n";
    opt = update(opt, name{"color"}, 30);
    std::cout << pp(opt) << "\n";
}

static void tst4() {
    options opt;
    lean_assert(opt.empty());
    lean_assert(opt.size() == 0);
    opt = update(opt, "color", 10);
    lean_assert(!opt.empty());
    lean_assert(opt.size() == 1);
    lean_assert(opt.contains("color"));
    lean_assert(!opt.contains("name"));
    std::cout << opt << "\n";
    lean_assert(opt.get_int(name("color"), 0) == 10);
    lean_assert(opt.get_int("color", 0) == 10);
    lean_assert(opt.get_int("name", 20) == 20);
    opt = update(opt, "color", 3);
    lean_assert(opt.size() == 1);
    lean_assert(opt.get_int("color", 0) == 3);
    opt = update(opt, "freq", 0.5);
    std::cout << opt << "\n";
    lean_assert(opt.size() == 2);
    lean_assert(opt.get_double("freq", 0.0) == 0.5);
    lean_assert(opt.get_double(name("freq"), 0.0) == 0.5);
    lean_assert(opt.get_unsigned("color", 0) == 3);
    lean_assert(opt.get_unsigned(name("color"), 0) == 3);
    opt = update(opt, "name", "Leo");
    lean_assert(opt.size() == 3);
    lean_assert(strcmp(opt.get_string("name", ""), "Leo") == 0);
    lean_assert(strcmp(opt.get_string("name2", ""), "Leo") != 0);
    lean_assert(strcmp(opt.get_string("name2", ""), "") == 0);
    opt = update(opt, "name", "Soon Ho");
    lean_assert(opt.size() == 3);
    lean_assert(strcmp(opt.get_string("name", ""), "Soon Ho") == 0);
    opt = update(opt, "flag", true);
    lean_assert(opt.get_bool("flag", false));
    lean_assert(opt.get_bool(name("flag"), false));
    lean_assert(!opt.get_bool("flag2", false));
    opt = update(opt, "list", sexpr{1, 2, 3});
    std::cout << opt << "\n";
    lean_assert(opt.get_sexpr("list", sexpr()) == sexpr({1, 2, 3}));
    lean_assert(opt.get_sexpr(name("list"), sexpr()) == sexpr({1, 2, 3}));
    lean_assert(opt.contains("name"));
    lean_assert(!opt.contains("name2"));
    lean_assert(opt.contains("color"));
    options opt2;
    opt2 = update(opt2, "name", "Leo");
    opt2 = update(opt2, "value", 10);
    opt2 = update(opt2, "flag", false);
    std::cout << "# " << opt << "\n# " << opt2 << "\n";
    options opt3 = join(opt, opt2);
    std::cout << "> " << opt3 << "\n";
    lean_assert(strcmp(opt3.get_string("name", ""), "Leo") == 0);
    lean_assert(opt3.get_unsigned("value", 0) == 10);
    lean_assert(opt3.get_unsigned("color", 0) == 3);
    lean_assert(opt3.get_double(name("freq"), 0.0) == 0.5);
    lean_assert(opt3.get_unsigned(name("freq"), 0) == 0);
    std::ostringstream s;
    option_kind k;
    k = BoolOption; s << k << " ";
    k = IntOption; s << k << " ";
    k = UnsignedOption; s << k << " ";
    k = DoubleOption; s << k << " ";
    k = StringOption; s << k << " ";
    k = SExprOption; s << k;
    std::cout << s.str() << "\n";
    lean_assert(s.str() == "Bool Int Unsigned Int Double String S-Expression");
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    return has_violations() ? 1 : 0;
}
