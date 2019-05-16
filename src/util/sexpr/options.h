/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "runtime/serializer.h"
#include "util/name.h"
#include "util/sexpr/sexpr.h"
#include "util/sexpr/format.h"

namespace lean {
enum option_kind { BoolOption, IntOption, UnsignedOption, StringOption };

/** \brief Configuration options. */
class options {
    sexpr m_value;
    options(sexpr const & v):m_value(v) {}
    unsigned hash() const { return m_value.hash(); }
    sexpr        get_sexpr(name const & n, sexpr const & default_value = sexpr()) const;
    sexpr        get_sexpr(char const * n, sexpr const & default_value = sexpr()) const;
    options update(name const & n, sexpr const & v) const;
    options update(char const * n, sexpr const & v) const { return update(name(n), v); }
public:
    options() {}
    options(options const & o):m_value(o.m_value) {}
    options(options && o):m_value(std::move(o.m_value)) {}
    options(name const & n, bool v) { *this = update(n, v); }
    ~options() {}

    options & operator=(options const & o) { m_value = o.m_value; return *this; }

    bool empty() const;
    unsigned size() const;
    bool contains(name const & n) const;
    bool contains(char const * n) const;

    bool         get_bool(name const & n, bool default_value = false) const;
    unsigned     get_unsigned(name const & n, unsigned default_value = 0) const;
    char const * get_string(name const & n, char const * default_value = nullptr) const;

    options update(name const & n, unsigned v) const { return update(n, sexpr(static_cast<int>(v))); }
    options update(name const & n, bool v) const { return update(n, sexpr(static_cast<bool>(v))); }
    options update(name const & n, char const * v) const { return update(n, sexpr(static_cast<bool>(v))); }

    void for_each(std::function<void(name const &)> const & fn) const;

    options update_if_undef(name const & n, bool v) const {
        if (contains(n))
            return *this;
        else
            return update(n, v);
    }

    friend bool is_eqp(options const & a, options const & b) { return is_eqp(a.m_value, b.m_value); }

    /**
       \brief Combine the options opts1 and opts2. The assignment in
       opts2 overrides the ones in opts1.
    */
    friend options join(options const & opts1, options const & opts2);
};

bool get_verbose(options const & opts);
name const & get_verbose_opt_name();
name const & get_max_memory_opt_name();
name const & get_timeout_opt_name();

inline options operator+(options const & opts1, options const & opts2) {
    return join(opts1, opts2);
}

struct mk_option_declaration {
    mk_option_declaration(name const & n, option_kind k, char const * default_value, char const * description);
};

void initialize_options();
void finalize_options();
}
