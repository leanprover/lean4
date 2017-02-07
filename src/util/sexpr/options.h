/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/name.h"
#include "util/sexpr/sexpr.h"
#include "util/sexpr/format.h"
#include "util/serializer.h"

namespace lean {
enum option_kind { BoolOption, IntOption, UnsignedOption, DoubleOption, StringOption, SExprOption };
std::ostream & operator<<(std::ostream & out, option_kind k);

/** \brief Configuration options. */
class options {
    sexpr m_value;
    options(sexpr const & v):m_value(v) {}
public:
    options() {}
    options(options const & o):m_value(o.m_value) {}
    options(options && o):m_value(std::move(o.m_value)) {}
    template<typename T> options(name const & n, T const & t) { *this = update(n, t); }
    ~options() {}

    options & operator=(options const & o) { m_value = o.m_value; return *this; }

    bool empty() const;
    unsigned size() const;
    bool contains(name const & n) const;
    bool contains(char const * n) const;
    unsigned hash() const { return m_value.hash(); }

    bool         get_bool(name const & n, bool default_value = false) const;
    int          get_int(name const & n, int default_value = 0) const;
    unsigned     get_unsigned(name const & n, unsigned default_value = 0) const;
    double       get_double(name const & n, double default_value = 0.0) const;
    char const * get_string(name const & n, char const * default_value = nullptr) const;
    sexpr        get_sexpr(name const & n, sexpr const & default_value = sexpr()) const;

    bool         get_bool(char const * n, bool default_value = false) const;
    int          get_int(char const * n, int default_value = 0) const;
    unsigned     get_unsigned(char const * n, unsigned default_value = 0) const;
    double       get_double(char const * n, double default_value = 0.0) const;
    char const * get_string(char const * n, char const * default_value = nullptr) const;
    sexpr        get_sexpr(char const * n, sexpr const & default_value = sexpr()) const;

    void for_each(std::function<void(name const &)> const & fn) const;

    options update(name const & n, sexpr const & v) const;
    template<typename T> options update(name const & n, T v) const { return update(n, sexpr(v)); }
    options update(name const & n, unsigned v) const { return update(n, sexpr(static_cast<int>(v))); }
    options update(char const * n, sexpr const & v) const { return update(name(n), v); }
    template<typename T> options update(char const * n, T v) const { return update(n, sexpr(v)); }

    template<typename T> options update_if_undef(name const & n, T v) const {
        if (contains(n))
            return *this;
        else
            return update(n, sexpr(v));
    }

    friend bool is_eqp(options const & a, options const & b) { return is_eqp(a.m_value, b.m_value); }

    /**
       \brief Combine the options opts1 and opts2. The assignment in
       opts2 overrides the ones in opts1.
    */
    friend options join(options const & opts1, options const & opts2);

    /**
       \brief Return a new set of options based on \c opts by adding the prefix \c prefix.

       The procedure throws an exception if \c opts contains an options (o, v), s.t. prefix + o is
       an unknown option in Lean.
    */
    friend options add_prefix(name const & prefix, options const & opts);

    /**
        \brief Remove all options that have the given prefix.
    */
    friend options remove_all_with_prefix(name const & prefix, options const & opts);

    friend format pp(options const & o);
    friend std::ostream & operator<<(std::ostream & out, options const & o);

    friend serializer & operator<<(serializer & s, options const & o) { s << o.m_value; return s; }
    friend options read_options(deserializer & d);

    friend bool operator==(options const & a, options const & b) { return a.m_value == b.m_value; }
};
bool get_verbose(options const & opts);
name const & get_verbose_opt_name();
name const & get_max_memory_opt_name();
name const & get_timeout_opt_name();

inline options read_options(deserializer & d) { return options(read_sexpr(d)); }
inline deserializer & operator>>(deserializer & d, options & o) { o = read_options(d); return d; }
template<typename T> options update(options const & o, name const & n, T const & v) { return o.update(n, sexpr(v)); }

inline options operator+(options const & opts1, options const & opts2) {
    return join(opts1, opts2);
}

struct mk_option_declaration {
    mk_option_declaration(name const & n, option_kind k, char const * default_value, char const * description);
};

void initialize_options();
void finalize_options();
}
