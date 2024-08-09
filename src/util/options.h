/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/name.h"
#include "util/kvmap.h"

namespace lean {
/** \brief Configuration options. */
class options {
    kvmap m_value;
    options(kvmap const & v):m_value(v) {}
public:
    options() {}
    explicit options(obj_arg o):m_value(o) {}
    options(b_obj_arg o, bool v):m_value(o, v) {}
    options(options const & o):m_value(o.m_value) {}
    options(options && o):m_value(std::move(o.m_value)) {}
    options(name const & n, bool v) { *this = update(n, v); }
    options & operator=(options const & o) { m_value = o.m_value; return *this; }

    bool empty() const { return is_nil(m_value); }
    unsigned size() const { return length(m_value); }
    bool contains(name const & n) const { return static_cast<bool>(find(m_value, n)); }
    bool contains(char const * n) const { return contains(name(n)); }

    bool get_bool(name const & n, bool default_value = false) const {
        if (auto r = ::lean::get_bool(m_value, n))
            return *r;
        return default_value;
    }

    unsigned get_unsigned(name const & n, unsigned default_value = 0) const {
        if (auto r = ::lean::get_nat(m_value, n))
            if (r->is_small())
                return r->get_small_value();
        return default_value;
    }

    char const * get_string(name const & n, char const * default_value = nullptr) const {
        if (auto r = ::lean::get_string(m_value, n))
            return r->data(); // unsafe
        return default_value;
    }

    options update(name const & n, unsigned v) const { return options(set_nat(m_value, n, v)); }
    options update(name const & n, bool v) const { return options(set_bool(m_value, n, v)); }
    options update(name const & n, char const * v) const { return options(set_string(m_value, n, v)); }

    void for_each(std::function<void(name const &)> const & fn) const;

    options update_if_undef(name const & n, bool v) const {
        if (contains(n))
            return *this;
        else
            return update(n, v);
    }

    friend bool is_eqp(options const & a, options const & b) { return a.m_value.raw() == b.m_value.raw(); }

    /**
       \brief Combine the options opts1 and opts2. The assignment in
       opts2 overrides the ones in opts1.
    */
    friend options join(options const & opts1, options const & opts2);

    object * to_obj_arg() const { return m_value.to_obj_arg(); }
};

LEAN_EXPORT bool get_verbose(options const & opts);
LEAN_EXPORT name const & get_verbose_opt_name();
LEAN_EXPORT name const & get_max_memory_opt_name();
LEAN_EXPORT name const & get_timeout_opt_name();

inline options operator+(options const & opts1, options const & opts2) {
    return join(opts1, opts2);
}

struct mk_option_declaration {
    mk_option_declaration(name const & n, data_value_kind k, char const * default_value, char const * description);
};

void initialize_options();
void finalize_options();
}
