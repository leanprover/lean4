/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#pragma once
#include <algorithm>
#include <iostream>
#include <numeric>
#include <sstream>
#include <utility>
#include <string>
#include <vector>
#include "runtime/debug.h"
#include "runtime/object_ref.h"
#include "util/name.h"
#include "util/pair.h"

namespace lean {
class options;
/**
inductive Format
| nil          : Format
| line         : Format
| text         : String → Format
| nest         : Nat → Format → Format
| compose      : Bool → Format → Format → Format
| choice       : Format → Format → Format
*/
class format : public object_ref {
    enum format_kind { NIL, LINE, TEXT, NEST, COMPOSE, CHOICE };
public:
    // Constructors
    format():object_ref(box(static_cast<unsigned>(NIL))) {}
    explicit format(object * o):object_ref(o) {}
    explicit format(object_ref const & o):object_ref(o) {}
    format(object * o, bool b):object_ref(o, b) {}
    explicit format(char const * v):object_ref(mk_cnstr(static_cast<unsigned>(TEXT), mk_string(v))) {}
    explicit format(std::string const & v):object_ref(mk_cnstr(static_cast<unsigned>(TEXT), mk_string(v))) {}
    explicit format(string_ref const & v):object_ref(mk_cnstr(static_cast<unsigned>(TEXT), v)) {}
    explicit format(int v):format(std::to_string(v)) {}
    explicit format(unsigned v):format(std::to_string(v)) {}
    explicit format(name const & v):format(v.to_string()) {}
    format(format const & f):object_ref(f) {}
    format(format && other):object_ref(other) {}
    format & operator=(format const & other) { object_ref::operator=(other); return *this; }
    format & operator=(format && other) { object_ref::operator=(other); return *this; }
    format(format const & f1, format const & f2);

    format_kind kind() const { return static_cast<format_kind>(cnstr_tag(raw())); }
    bool is_nil_fmt() const { return kind() == format_kind::NIL; }

    friend format compose(format const & f1, format const & f2);
    friend format nest(int i, format const & f);
    friend format group(format const & f);
    friend format bracket(std::string const & l, format const & x, std::string const & r);

    // x + y = x <> y
    friend format operator+(format const & f1, format const & f2);
    format & operator+=(format const & f) {
        *this = *this + f;
        return *this;
    }

    static std::ostream & pretty(std::ostream & out, unsigned w, format const & f);
    friend std::ostream & pretty(std::ostream & out, unsigned w, format const & f);
    friend std::ostream & pretty(std::ostream & out, options const & o, format const & f);

    friend std::ostream & operator<<(std::ostream & out, format const & f);
    friend std::ostream & operator<<(std::ostream & out, pair<format const &, options const &> const & p);
    friend void initialize_format();
};

format compose(format const & f1, format const & f2);
format nest(int i, format const & f);
format line();
format space();
format bracket(std::string const & l, format const & x, std::string const & r);
format group(format const & f);
format paren(format const & x);

class options;
/** \brief Extract indentation from options */
unsigned get_pp_indent(options const & o);
/** \brief Return unicode characters flag */
bool get_pp_unicode(options const & o);

/** \brief Format a hierarchical name */
format pp(name const & n);

/** \brief Return true iff \c f1 and \c f2 are equal when formatted with options \c o */
bool format_pp_eq(format const & f1, format const & f2, options const & o);

void initialize_format();
void finalize_format();
}
