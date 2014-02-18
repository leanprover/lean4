/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <functional>
#include "util/test.h"
#include "util/exception.h"
#include "util/sstream.h"
using namespace lean;

static void tst1() {
    try {
        throw exception(std::string("foo"));
    } catch (exception & ex) {
        lean_assert(std::string("foo") == ex.what());
    }
}

static void tst2() {
    try {
        throw parser_exception(std::string("foo"), "[string]", 10, 100);
    } catch (parser_exception & ex) {
        lean_assert(std::string("[string]:10:100: error: foo") == ex.what());
    }
}

static void tst3() {
    try {
        throw parser_exception(sstream() << "msg " << 10 << " " << 20, "[stream]", 10, 100);
    } catch (parser_exception & ex) {
        lean_assert(std::string("[stream]:10:100: error: msg 10 20") == ex.what());
    }
}

static void tst4() {
    try {
        throw interrupted();
    } catch (exception & ex) {
        lean_assert(std::string("interrupted") == ex.what());
    }
}

class ex : public exception {
    std::function<char const *()> m_f;
    ex(std::function<char const *()> const & f):m_f(f) {}
public:
    template<typename F> ex(F && f):m_f(f) {}
    virtual exception * clone() const { return new ex(m_f); }
    virtual void rethrow() const { throw *this; }
    virtual char const * what() const noexcept { return m_f(); }
};

static void throw_ex() {
    int x = 10;
    std::string msg = "foo";
    throw ex([=]() {
            static std::string m;
            std::ostringstream buffer;
            buffer << "error, x: " << x << " " << msg;
            m = buffer.str();
            return m.c_str();
        });
}

static void throw_catch_rethrow() {
    try {
        throw_ex();
    } catch (ex & e) {
        std::cout << "CATCH 1: {" << e.what() << "}\n";
        std::unique_ptr<exception> new_e(e.clone());
        new_e->rethrow();
    }
}

static void tst5() {
    try {
        throw_catch_rethrow();
    } catch (ex & e) {
        std::cout << "CATCH 2: {" << e.what() << "}\n";
    }
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    return has_violations() ? 1 : 0;
}
