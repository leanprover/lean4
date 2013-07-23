/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <cstring>
#include "sexpr.h"
#include "format.h"

namespace lean {
std::ostream & layout(std::ostream & out, sexpr const & s) {
    if(is_cons(s)) {
        sexpr v = cdr(s);

        switch (to_int(car(s))) {
        case format::format_kind::NIL:
            out << "NIL";
            break;
        case format::format_kind::NEST:
            out << "NEST("
                << car(v)
                << ", ";
            layout(out, cdr(v));
            out << ")";
            break;
        case format::format_kind::COMPOSE:
            out << "COMPOSE(";
            layout(out, car(v));
            out << ", ";
            layout(out, cdr(v));
            out << ")";
            break;
        case format::format_kind::CHOICE:
            out << "CHOICE(";
            layout(out, car(v));
            out << ", ";
            layout(out, cdr(v));
            out << ")";
            break;
        case format::format_kind::LINE:
            out << "LINE()";
            break;
        }
    } else {
        out << s;
    }
    return out;
}

std::ostream & operator<<(std::ostream & out, format const & f) {
    return layout(out, f.m_value);
}

sexpr flatten(sexpr const & s) {
    if(is_cons(s)) {
        sexpr v = cdr(s);
        switch (to_int(car(s))) {
        case format::format_kind::NIL:
            /* flatten NIL = NIL */
            return s;

        case format::format_kind::NEST:
            /* flatten (NEST i x) = flatten x */
            return flatten(cdr(v));

        case format::format_kind::COMPOSE:
            /* flatten (x <> y) = flatten x <> flatten y */
            return sexpr(format::format_kind::COMPOSE,
                         sexpr(flatten(car(v)),
                               flatten(cdr(v))));

        case format::format_kind::CHOICE:
            /* flatten (x <|> y) = flatten x */
            return flatten(car(v));

        case format::format_kind::LINE:
            return sexpr(" ");

        }
    }
    return s;
}

format flatten(format const & f){
    return format(flatten(f.m_value));
}

format group(format const & f) {
    return choice(flatten(f), f);
}

}


void pp(lean::format const & n) { std::cout << "pp" << "\n"; }
