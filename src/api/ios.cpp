/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/error_handling/error_handling.h"
#include "frontends/lean/pp.h"
#include "api/string.h"
#include "api/exception.h"
#include "api/decl.h"
#include "api/lean_env.h"
#include "api/ios.h"
using namespace lean; // NOLINT

lean_bool lean_ios_mk_std(lean_options o, lean_ios * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(o);
    io_state ios(mk_pretty_formatter_factory(), to_options_ref(o));
    *r = of_io_state(new io_state(ios));
    LEAN_CATCH;
}

lean_bool lean_ios_mk_buffered(lean_options o, lean_ios * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(o);
    io_state ios(mk_pretty_formatter_factory(), to_options_ref(o));
    ios.set_regular_channel(std::make_shared<string_output_channel>());
    ios.set_diagnostic_channel(std::make_shared<string_output_channel>());
    *r = of_io_state(new io_state(ios));
    LEAN_CATCH;
}

void lean_ios_del(lean_ios ios) {
    delete to_io_state(ios);
}

lean_bool lean_ios_is_std(lean_ios ios) {
    if (!ios)
        return lean_false;
    return dynamic_cast<string_output_channel*>(&to_io_state_ref(ios).get_regular_channel()) == nullptr;
}

lean_bool lean_ios_set_options(lean_ios ios, lean_options o, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(ios);
    check_nonnull(o);
    to_io_state(ios)->set_options(to_options_ref(o));
    LEAN_CATCH;
}

lean_bool lean_ios_get_options(lean_ios ios, lean_options * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(ios);
    *r = of_options(new options(to_io_state_ref(ios).get_options()));
    LEAN_CATCH;
}

static void check_nonstd(lean_ios ios) {
    check_nonnull(ios);
    if (lean_ios_is_std(ios))
        throw exception("invalid argument, buffered IO state expected");
}

lean_bool lean_ios_get_regular(lean_ios ios, char const ** r, lean_exception * ex) {
    LEAN_TRY;
    check_nonstd(ios);
    *r = mk_string(static_cast<string_output_channel&>(to_io_state_ref(ios).get_regular_channel()).str());
    LEAN_CATCH;
}

lean_bool lean_ios_get_diagnostic(lean_ios ios, char const ** r, lean_exception * ex) {
    LEAN_TRY;
    check_nonstd(ios);
    *r = mk_string(static_cast<string_output_channel&>(to_io_state_ref(ios).get_diagnostic_channel()).str());
    LEAN_CATCH;
}

lean_bool lean_ios_reset_regular(lean_ios ios, lean_exception * ex) {
    LEAN_TRY;
    check_nonstd(ios);
    to_io_state(ios)->set_regular_channel(std::make_shared<string_output_channel>());
    LEAN_CATCH;
}

lean_bool lean_ios_reset_diagnostic(lean_ios ios, lean_exception * ex) {
    LEAN_TRY;
    check_nonstd(ios);
    to_io_state(ios)->set_diagnostic_channel(std::make_shared<string_output_channel>());
    LEAN_CATCH;
}

lean_bool lean_expr_to_pp_string(lean_env env, lean_ios ios, lean_expr e, char const ** r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(ios);
    check_nonnull(e);
    options const & o = to_io_state_ref(ios).get_options();
    formatter fmt = to_io_state_ref(ios).get_formatter_factory()(to_env_ref(env), o);
    std::ostringstream out;
    out << mk_pair(fmt(to_expr_ref(e)), o);
    *r = mk_string(out.str());
    LEAN_CATCH;
}

lean_bool lean_exception_to_pp_string(lean_env env, lean_ios ios, lean_exception e, char const ** r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(env);
    check_nonnull(ios);
    check_nonnull(e);
    io_state new_ios(to_io_state_ref(ios));
    std::shared_ptr<output_channel> aux(new string_output_channel());
    new_ios.set_regular_channel(aux);
    new_ios.set_diagnostic_channel(aux);
    io_state_stream ioss(to_env_ref(env), new_ios);
    throwable * _e = to_exception(e);
    display_error(ioss, nullptr, *_e);
    *r = mk_string(static_cast<string_output_channel const *>(aux.get())->str());
    LEAN_CATCH;
}
