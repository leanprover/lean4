/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "sexpr.h"
#include "format.h"
#include "name.h"

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
    bool size() const;
    bool contains(name const & n) const;
    bool contains(char const * n) const;

    bool         get_bool(name const & n, bool default_value=false) const;
    int          get_int(name const & n, int default_value=0) const;
    unsigned     get_unsigned(name const & n, unsigned default_value=0) const;
    double       get_double(name const & n, double default_value=0.0) const;
    char const * get_string(name const & n, char const * default_value=nullptr) const;
    sexpr        get_sexpr(name const & n, sexpr const & default_value=sexpr()) const;

    bool         get_bool(char const * n, bool default_value=false) const;
    int          get_int(char const * n, int default_value=0) const;
    unsigned     get_unsigned(char const * n, unsigned default_value=0) const;
    double       get_double(char const * n, double default_value=0.0) const;
    char const * get_string(char const * n, char const * default_value=nullptr) const;
    sexpr        get_sexpr(char const * n, sexpr const & default_value=sexpr()) const;

    options update(name const & n, sexpr const & v) const;
    template<typename T> options update(name const & n, T v) const { return update(n, sexpr(v)); }
    options update(name const & n, unsigned v) const { return update(n, sexpr(static_cast<int>(v))); }
    options update(char const * n, sexpr const & v) const { return update(name(n), v); }
    template<typename T> options update(char const * n, T v) const { return update(n, sexpr(v)); }

    /**
       \brief Combine the options opts1 and opts2. The assignment in
       opts2 overrides the ones in opts1.
    */
    friend options join(options const & opts1, options const & opts2);

    friend format pp(options const & o);
    friend std::ostream & operator<<(std::ostream & out, options const & o);
};
template<typename T> options update(options const & o, name const & n, T const & v) { return o.update(n, sexpr(v)); }

struct mk_option_declaration {
    mk_option_declaration(name const & n, option_kind k, char const * default_value, char const * description);
};

#define LEAN_MAKE_OPTION_NAME_CORE(LINE) LEAN_OPTION_ ## LINE
#define LEAN_MAKE_OPTION_NAME(LINE) LEAN_MAKE_OPTION_NAME_CORE(LINE)
#define LEAN_OPTION_UNIQUE_NAME LEAN_MAKE_OPTION_NAME(__LINE__)
#define RegisterOption(N,K,D,DESC) ::lean::mk_option_declaration LEAN_OPTION_UNIQUE_NAME(N,K,D,DESC)
#define RegisterOptionCore(N,K,D,DESC) RegisterOption(N,K,#D,DESC)
#define RegisterBoolOption(N,D,DESC) RegisterOptionCore(N, BoolOption, D, DESC);
#define RegisterUnsignedOption(N,D,DESC) RegisterOptionCore(N, UnsignedOption, D, DESC);
}
