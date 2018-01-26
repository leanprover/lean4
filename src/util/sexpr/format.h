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
#include "util/pair.h"
#include "util/debug.h"
#include "util/sexpr/sexpr.h"

namespace lean {
class options;
/**
   \brief Format

   uses `sexpr` as an internal representation.

   nil                    = ["NIL"]
   text         s         = ("TEXT"  . s)
   choice       f1 f2     = ("CHOICE"  f1 . f2)
   compose      f1 ... fn = ["COMPOSE" f1 ... fn]
   line                   = ["LINE"]
   nest         n  f      = ("NEST" n . f)
   highlight    c  f      = ("HIGHLIGHT" c . f)
*/

class format {
public:
    enum format_kind { NIL, NEST, COMPOSE, FLAT_COMPOSE, CHOICE, LINE, TEXT, COLOR_BEGIN, COLOR_END};
    enum format_color {RED, GREEN, ORANGE, BLUE, PINK, CYAN, GREY};
private:
    sexpr m_value;
    static sexpr flatten(sexpr const & s);

    // Functions for the internal sexpr representation
    static inline format_kind sexpr_kind(sexpr const & s) {
        lean_assert(is_cons(s));
        return static_cast<format_kind>(to_int(car(s)));
    }
    static inline sexpr sexpr_compose(sexpr const & l) {
        lean_assert(is_list(l));
        return sexpr(sexpr(format_kind::COMPOSE), l);
    }
    static inline sexpr sexpr_flat_compose(sexpr const & l) {
        lean_assert(is_list(l));
        return sexpr(sexpr(format_kind::FLAT_COMPOSE), l);
    }
    static inline sexpr const & sexpr_compose_list(sexpr const & s) {
        lean_assert(sexpr_kind(s) == format_kind::COMPOSE || sexpr_kind(s) == format_kind::FLAT_COMPOSE);
        return cdr(s);
    }
    static inline sexpr sexpr_choice(sexpr const & s1, sexpr const & s2) {
        return sexpr(sexpr(format_kind::CHOICE), sexpr(s1, s2));
    }
    static inline sexpr const & sexpr_choice_1(sexpr const & s) {
        return car(cdr(s));
    }
    static inline sexpr const & sexpr_choice_2(sexpr const & s) {
        return cdr(cdr(s));
    }
    static inline sexpr sexpr_nest(int i, sexpr const & s) {
        return sexpr(sexpr(format_kind::NEST), sexpr(i, s));
    }
    static inline int sexpr_nest_i(sexpr const & s) {
        lean_assert(sexpr_kind(s) == format_kind::NEST);
        return to_int(car(cdr(s)));
    }
    static inline sexpr const & sexpr_nest_s(sexpr const & s) {
        lean_assert(sexpr_kind(s) == format_kind::NEST);
        return cdr(cdr(s));
    }
    static inline sexpr sexpr_text(sexpr const & s) {
        return sexpr(sexpr(format_kind::TEXT), s);
    }
    static inline sexpr const & sexpr_text_t(sexpr const & s) {
        lean_assert(sexpr_kind(s) == format_kind::TEXT);
        return cdr(s);
    }
    static inline size_t sexpr_text_length(sexpr const & s) {
        lean_assert(sexpr_kind(s) == format_kind::TEXT);
        sexpr const & content = cdr(s);
        if (is_string(content)) {
            return to_string(content).length();
        } else {
            std::stringstream ss;
            ss << content;
            return ss.str().length();
        }
    }
    static inline sexpr sexpr_text(std::string const & s) {
        return sexpr(sexpr(format_kind::TEXT), sexpr(s));
    }
    static inline sexpr sexpr_color_begin(format_color c) {
        return sexpr(sexpr(format_kind::COLOR_BEGIN), sexpr(c));
    }
    static inline format_color sexpr_color_begin(sexpr const & s) {
        lean_assert(sexpr_kind(s) == format_kind::TEXT);
        return static_cast<format_color>(to_int(cdr(s)));
    }
    static inline sexpr sexpr_color_end() {
        return sexpr(sexpr(format_kind::COLOR_END), sexpr());
    }
    static inline sexpr sexpr_highlight(sexpr const & s, format_color c) {
        return sexpr_compose(sexpr(sexpr_color_begin(c), sexpr(s, sexpr(sexpr_color_end(), sexpr()))));
    }
    static inline sexpr sexpr_nil() {
        return sexpr(sexpr(format::format_kind::NIL), sexpr());
    }
    static inline sexpr sexpr_line() {
        return sexpr(sexpr(format::format_kind::LINE), sexpr());
    }

    struct separate_tokens_fn;

    // Functions used inside of pretty printing
    static bool space_upto_line_break_list_exceeded(sexpr const & s, int available, std::vector<pair<sexpr, unsigned>> const & todo);
    static int space_upto_line_break(sexpr const & s, int available, bool & found);

    static bool is_fnil(format const & f)   {
        return to_int(car(f.m_value)) == format_kind::NIL;
    }
    static bool is_compose(format const & f)   {
        return to_int(car(f.m_value)) == format_kind::COMPOSE;
    }
    static bool is_flat_compose(format const & f)   {
        return to_int(car(f.m_value)) == format_kind::FLAT_COMPOSE;
    }
    static bool is_nest(format const & f) {
        return to_int(car(f.m_value)) == format_kind::NEST;
    }
    static bool is_text(format const & f) {
        return to_int(car(f.m_value)) == format_kind::TEXT;
    }
    static bool is_line(format const & f) {
        return to_int(car(f.m_value)) == format_kind::LINE;
    }
    static bool is_choice(format const & f) {
        return to_int(car(f.m_value)) == format_kind::CHOICE;
    }
    friend format choice(format const & f1, format const & f2) {
        return format(sexpr_choice(f1.m_value, f2.m_value));
    }

public:
    // Constructors
    format():m_value(sexpr_nil()) {}
    explicit format(sexpr const & v):m_value(v) {}
    explicit format(char const * v):m_value(sexpr_text(sexpr(v))) {}
    explicit format(std::string const & v):m_value(sexpr_text(sexpr(v))) {}
    explicit format(int v):m_value(sexpr_text(sexpr(v))) {}
    explicit format(double v):m_value(sexpr_text(sexpr(v))) {}
    explicit format(unsigned v) {
        std::ostringstream out;
        out << v;
        m_value = sexpr_text(out.str());
    }
    explicit format(name const & v):m_value(sexpr_text(sexpr(v))) {}
    format(format const & f1, format const & f2):m_value(sexpr_compose({f1.m_value, f2.m_value})) {}
    format(format const & f):m_value(f.m_value) {}
    format_kind kind() const {
        return sexpr_kind(m_value);
    }
    bool is_nil_fmt() const { return kind() == format_kind::NIL; }
    unsigned hash() const { return m_value.hash(); }

    format separate_tokens(std::function<bool(sexpr const &, sexpr const &)> sep) const; // NOLINT

    friend format compose(format const & f1, format const & f2);
    friend format nest(int i, format const & f);
    friend format highlight(format const & f, format::format_color const c);
    friend format mk_line();

    friend format group(format const & f);
    friend format above(format const & f1, format const & f2);
    friend format bracket(std::string const & l, format const & x, std::string const & r);
    friend format wrap(format const & f1, format const & f2);
    friend format flatten(format const & f);

    // x + y = x <> y
    friend format operator+(format const & f1, format const & f2);
    format & operator+=(format const & f) {
        *this = *this + f;
        return *this;
    }

    // x ^ y = x <> " " <> y
    friend format operator^(format const & f1, format const & f2);
    format & operator^=(format const & f) {
        *this = *this ^ f;
        return *this;
    }

    static std::ostream & pretty(std::ostream & out, unsigned w, bool colors, format const & f);
    friend std::ostream & pretty(std::ostream & out, unsigned w, bool colors, format const & f);
    friend std::ostream & pretty(std::ostream & out, unsigned w, format const & f);
    friend std::ostream & pretty(std::ostream & out, options const & o, format const & f);

    friend std::ostream & operator<<(std::ostream & out, format const & f);
    friend std::ostream & operator<<(std::ostream & out, pair<format const &, options const &> const & p);

    /** \brief Return true iff f is just a name */
    friend bool is_name(format const & f) { return format::is_text(f) && ::lean::is_name(cdr(f.m_value)); }
};

format wrap(format const & f1, format const & f2);
format compose(format const & f1, format const & f2);
format nest(int i, format const & f);
format highlight(format const & f, format::format_color const c = format::RED);
format highlight_keyword(format const & f);
format highlight_builtin(format const & f);
format highlight_command(format const & f);
format const & line();
format const & space();
format const & lp();
format const & rp();
format const & lsb();
format const & rsb();
format const & lcurly();
format const & rcurly();
format const & comma();
format const & colon();
format const & dot();
format group(format const & f);
format above(format const & f1, format const & f2);
format bracket(std::string const & l, format const & x, std::string const & r);
format paren(format const & x);
format wrap(format const & f1, format const & f2);

// is_iterator
template<typename T, typename = void>
struct is_iterator {
    static constexpr bool value = false;
};
template<typename T>
struct is_iterator<T, typename std::enable_if<!std::is_same<typename std::iterator_traits<T>::value_type, void>::value>::type> {
    static constexpr bool value = true;
};

template <class InputIterator, typename F>
format folddoc(InputIterator first, InputIterator last, F f) {
    // InputIterator : iterator<T>
    static_assert(is_iterator<InputIterator>::value, "folddoc takes non-iterator type arguments");
    // F : T x format -> format
    static_assert(std::is_same<typename std::result_of<F(typename std::iterator_traits<InputIterator>::value_type,
                                                         format)>::type, format>::value,
                  "folddoc: return type of f is not format");
    if (first == last) { return format(); }
    return f(*first, folddoc(first + 1, last, f));
}
template <class InputIterator>
format spread(InputIterator first, InputIterator last) {
    static_assert(std::is_same<typename std::iterator_traits<InputIterator>::value_type, format>::value,
                  "stack takes an argument which is not an iterator containing format.");
    return folddoc(first, last, compose);
}
inline format spread(std::initializer_list<format> const & l) {
    return spread(l.begin(), l.end());
}
template <class InputIterator>
format stack(InputIterator first, InputIterator last) {
    static_assert(std::is_same<typename std::iterator_traits<InputIterator>::value_type, format>::value,
                  "stack takes an argument which is not an iterator containing format.");
    return folddoc(first, last, above);
}
inline format stack(std::initializer_list<format> const & l) {
    return stack(l.begin(), l.end());
}
template <typename InputIterator>
format fill(InputIterator first, InputIterator last) {
    static_assert(std::is_same<typename std::iterator_traits<InputIterator>::value_type, format>::value,
                  "fill takes an argument which is not an iterator containing format.");
    return folddoc(first, last, wrap);
}
inline format fill(std::initializer_list<format> const & l) {
    return fill(l.begin(), l.end());
}
template <typename InputIterator>
format fillwords(InputIterator first, InputIterator last) {
    static_assert(std::is_same<typename std::iterator_traits<InputIterator>::value_type,
                  typename std::string>::value,
                  "fillwords takes an argument which is not an iterator containing std::string.");
    return folddoc(first, last, [](std::string const & s, format const & r) { return wrap(format(s), r); } );
}
inline format fillwords(std::initializer_list<std::string> const & l) {
    return fillwords(l.begin(), l.end());
}
class options;
/** \brief Extract indentation from options */
unsigned get_pp_indent(options const & o);
/** \brief Return unicode characters flag */
bool get_pp_unicode(options const & o);

/** \brief Format a hierarchical name */
format pp(name const & n);

/** \brief Format a S-expression */
format pp(sexpr const & s);

/** \brief Return true iff \c f1 and \c f2 are equal when formatted with options \c o */
bool format_pp_eq(format const & f1, format const & f2, options const & o);

void initialize_format();
void finalize_format();
}
