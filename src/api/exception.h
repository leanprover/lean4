/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "util/exception.h"
#include "library/exception.h"
#include "api/lean_macros.h"
#include "api/lean_bool.h"
#include "api/lean_exception.h"

namespace lean {
inline throwable * to_exception(lean_exception e) { return reinterpret_cast<throwable *>(e); }
inline lean_exception of_exception(throwable * e) { return reinterpret_cast<lean_exception>(e); }

class memout_exception : public throwable {
public:
    memout_exception() {}
    virtual ~memout_exception() noexcept {}
    virtual char const * what() const noexcept { return "out of memory"; }
    virtual throwable * clone() const { return new memout_exception(); }
    virtual void rethrow() const { throw *this; }
};

class system_exception : public throwable {
public:
    system_exception():throwable("unknown exception") {}
    system_exception(std::string const & msg):throwable(msg) {}
    system_exception(std::exception const & ex):throwable(ex.what()) {}
    virtual ~system_exception() noexcept {}
    virtual throwable * clone() const { return new system_exception(what()); }
    virtual void rethrow() const { throw *this; }
};

memout_exception * get_memout_exception();
void check_nonnull(void const *);
}

#define LEAN_TRY try {
#define LEAN_CATCH                                      \
} catch (lean::parser_nested_exception & e) {           \
    *ex = of_exception(e.get_exception().clone());      \
    return lean_false;                                  \
} catch (lean::exception & e) {                         \
    *ex = of_exception(e.clone());                      \
    return lean_false;                                  \
} catch (std::bad_alloc &) {                            \
    *ex = of_exception(lean::get_memout_exception());   \
    return lean_false;                                  \
} catch (std::exception & e) {                          \
    *ex = of_exception(new lean::system_exception(e));  \
    return lean_false;                                  \
} catch (...) {                                         \
    *ex = of_exception(new lean::system_exception());   \
    return lean_false;                                  \
}                                                       \
return lean_true
