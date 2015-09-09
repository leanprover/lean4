/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/kernel_exception.h"
#include "library/unifier.h"
#include "library/print.h"
#include "library/tactic/tactic.h"
#include "library/error_handling/error_handling.h"
#include "api/exception.h"
#include "api/string.h"
using namespace lean; // NOLINT

namespace lean {
memout_exception * get_memout_exception() {
    static memout_exception g_memout;
    return &g_memout;
}

void check_nonnull(void const * ptr) {
    if (!ptr)
        throw exception("invalid argument, it must be a nonnull pointer");
}
}

void lean_exception_del(lean_exception e) {
    lean::throwable * t = lean::to_exception(e);
    if (t != lean::get_memout_exception()) {
        delete t;
    }
}

char const * lean_exception_get_message(lean_exception e) {
    if (!e)
        return 0;
    try {
        return lean::mk_string(lean::to_exception(e)->what());
    } catch (...) {
        return 0;
    }
}

char const * lean_exception_get_detailed_message(lean_exception e) {
    if (!e)
        return 0;
    try {
        formatter_factory fmtf = mk_print_formatter_factory();
        std::shared_ptr<output_channel> out(new string_output_channel());
        io_state ios(fmtf);
        ios.set_regular_channel(out);
        ios.set_diagnostic_channel(out);
        environment env;
        io_state_stream ioss(env, ios);
        display_error(ioss, nullptr, *lean::to_exception(e));
        return mk_string(static_cast<string_output_channel const *>(out.get())->str());
    } catch (...) {
        return 0;
    }
}

lean_exception_kind lean_exception_get_kind(lean_exception e) {
    lean::throwable * ex = lean::to_exception(e);
    if (!ex)
        return LEAN_NULL_EXCEPTION;
    if (dynamic_cast<lean::memout_exception*>(ex))
        return LEAN_OUT_OF_MEMORY;
    if (dynamic_cast<lean::system_exception*>(ex))
        return LEAN_SYSTEM_EXCEPTION;
    if (dynamic_cast<lean::kernel_exception*>(ex))
        return LEAN_KERNEL_EXCEPTION;
    if (dynamic_cast<lean::interrupted*>(ex))
        return LEAN_INTERRUPTED;
    if (dynamic_cast<lean::unifier_exception*>(ex))
        return LEAN_UNIFIER_EXCEPTION;
    if (dynamic_cast<lean::tactic_exception*>(ex))
        return LEAN_TACTIC_EXCEPTION;
    if (dynamic_cast<lean::parser_exception*>(ex))
        return LEAN_PARSER_EXCEPTION;
    return LEAN_OTHER_EXCEPTION;
}
