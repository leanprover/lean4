/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstring>
#include <sstream>
#include "util/test.h"
#include "util/init_module.h"
#include "util/sexpr/options.h"
#include "util/sexpr/option_declarations.h"
#include "util/sexpr/init_module.h"
using namespace lean;

static void tst1() {
    options opt;
    opt = opt.update("tst", 10u);
    opt = opt.update("foo", true);
}

static void check_serializer(options const &) {
}

static void tst2() {
    options opt;
    opt = opt.update(name{"test", "foo"}, 10u);
    opt = opt.update(name{"color"}, 20u);
    opt = opt.update(name{"test", "long", "names", "with", "several", "parts"}, true);
    check_serializer(opt);
}

static void tst3() {
    options opt;
    opt = opt.update(name{"test", "foo"}, 10u);
    opt = opt.update(name{"color"}, 20u);
    opt = opt.update(name{"color"}, 20u);
    opt = opt.update(name{"color"}, 30u);
    check_serializer(opt);
}

static void tst4() {
    options opt;
    lean_assert(opt.empty());
    lean_assert(opt.size() == 0);
    opt = opt.update("color", 10u);
    opt = opt.update(name("color"), 10u);
    lean_assert(!opt.empty());
    lean_assert(opt.size() == 1);
    lean_assert(opt.contains("color"));
    lean_assert(!opt.contains("name"));
    opt = opt.update("color", 3u);
    lean_assert(opt.size() == 1);
    lean_assert(opt.size() == 2);
    lean_assert(opt.get_unsigned("color", 0) == 3);
    lean_assert(opt.get_unsigned(name("color"), 0) == 3);
    opt = opt.update("name", "Leo");
    lean_assert(opt.size() == 3);
    lean_assert(strcmp(opt.get_string("name", ""), "Leo") == 0);
    lean_assert(strcmp(opt.get_string(name("name"), ""), "Leo") == 0);
    lean_assert(strcmp(opt.get_string("name2", ""), "Leo") != 0);
    lean_assert(strcmp(opt.get_string("name2", ""), "") == 0);
    opt = opt.update("name", "Soon Ho");
    lean_assert(opt.size() == 3);
    lean_assert(strcmp(opt.get_string("name", ""), "Soon Ho") == 0);
    opt = opt.update("flag", true);
    lean_assert(opt.get_bool("flag", false));
    lean_assert(opt.get_bool(name("flag"), false));
    lean_assert(!opt.get_bool("flag2", false));
    lean_assert(opt.contains("name"));
    lean_assert(!opt.contains("name2"));
    lean_assert(opt.contains("color"));
    check_serializer(opt);
    options opt2;
    opt2 = opt2.update(name("name"), "Leo");
    opt2 = opt2.update(name("value"), 10u);
    opt2 = opt2.update(name("flag"), false);
    check_serializer(opt2);
    options opt3 = join(opt, opt2);
    lean_assert(strcmp(opt3.get_string("name", ""), "Leo") == 0);
    lean_assert(opt3.get_unsigned("value", 0) == 10);
    lean_assert(opt3.get_unsigned("color", 0) == 3);
    lean_assert(opt3.get_unsigned(name("freq"), 0) == 0);
    check_serializer(opt3);
    std::ostringstream s;
    option_kind k;
    k = BoolOption; s << k << " ";
    k = IntOption; s << k << " ";
    k = UnsignedOption; s << k << " ";
    k = StringOption; s << k << " ";
}

static void tst5() {
    option_declarations const & decls = get_option_declarations();
    auto it = decls.find("fakeopt");
    lean_assert(it);
    lean_assert(it->get_name() == "fakeopt");
    lean_assert(it->get_default_value() == "false");
    lean_assert(it->get_description() == "fake option");
    auto it2 = decls.find("fakeopt2");
    lean_assert(!it2);
}

static void tst6() {
    options opt, opt2;
    lean_assert(is_eqp(opt, opt2));
    opt = opt.update(name{"test", "foo"}, 10u);
    lean_assert(!is_eqp(opt, opt2));
    opt2 = opt2.update(name{"test", "foo"}, 10u);
    lean_assert(!is_eqp(opt, opt2));
    opt2 = opt;
    lean_assert(is_eqp(opt, opt2));
    check_serializer(opt);
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    name fakeopt("fakeopt");
    register_bool_option(fakeopt, false, "fake option");

    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();

    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}
