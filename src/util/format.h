/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include "sexpr.h"
#include <iostream>

namespace lean {
/**
   \brief Format

   uses `sexpr` as an internal representation.

   nil           = nil sexpr
   text    s     = ("TEXT"    s    )
   nest    f     = ("NEST"    f    )
   choice  f1 f2 = ("CHOICE"  f1 f2)
   compose f1 f2 = ("COMPOSE" f1 f2)
   line          = ("LINE")
   nest    n  f  = ("NEST"    n   f)

*/

class format {
    sexpr m_value;

public:
    enum format_kind { NIL, NEST, COMPOSE, CHOICE, LINE, TEXT };

    format():m_value(sexpr()) {}
    explicit format(sexpr const & v):m_value(v) {}
    explicit format(char const * v):m_value(v) {}
    explicit format(std::string const & v):m_value(v) {}
    explicit format(int v):m_value(v) {}
    explicit format(double v):m_value(v) {}
    explicit format(name const & v):m_value(v) {}
    explicit format(mpz const & v):m_value(v) {}
    explicit format(mpq const & v):m_value(v) {}
    format(format const & f1, format const & f2) {
        m_value = sexpr(sexpr(COMPOSE), sexpr(f1.m_value, f2.m_value));
    }
    format(format const & f):m_value(f.m_value) {}

    format_kind kind() const {
        if(is_nil(m_value)) {
            return NIL;
        }
        if(is_cons(m_value)) {
            /* CHOICE, COMPOSE, LINE, NEST */
            return static_cast<format_kind>(to_int(car(m_value)));
        }
        return TEXT;
    }

    unsigned hash() const { return m_value.hash(); }

    format & operator=(format const & s);
    format & operator=(format&& s);
    template<typename T>
    format & operator=(T const & v) { return operator=(format(v)); }

    std::ostream & display(std::ostream & out, sexpr const & s);
    friend std::ostream & operator<<(std::ostream & out, format const & f);

    friend format compose(format const & f1, format const & f2) {
        return format(f1, f2);
    }
    friend format choice(format const & f1, format const & f2) {
        return format(sexpr(sexpr(CHOICE), sexpr(f1.m_value, f2.m_value)));
    }
    friend format nest(int i, format const & f) {
        return format(sexpr(sexpr(NEST), sexpr(sexpr(i), f.m_value)));
    }

    friend bool is_compose(format const & f)   {
        return is_cons(f.m_value) && to_int(car(f.m_value)) == format_kind::COMPOSE;
    }
    friend bool is_nest(format const & f) {
        return is_cons(f.m_value) && to_int(car(f.m_value)) == format_kind::NEST;
    }
    friend bool is_text(format const & f) {
        return !is_cons(f.m_value);
    }
    friend bool is_line(format const & f) {
        return is_cons(f.m_value) && to_int(car(f.m_value)) == format_kind::LINE;
    }
    friend bool is_choice(format const & f) {
        return is_cons(f.m_value) && to_int(car(f.m_value)) == format_kind::CHOICE;
    }

    friend format flatten(format const & f);
};

inline format line() {
    return format(sexpr(format::format_kind::LINE));
}

}
