/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/thread.h"
#include "util/name_map.h"
#include "util/optional.h"
#include "kernel/expr.h"

namespace lean {
/** \brief Cache for mapping definitions (type, value) before elaboration to (level_names, type, value)
    after elaboration.
*/
class definition_cache {
    typedef std::tuple<expr, expr, level_param_names, expr, expr> entry;
    mutex           m_mutex;
    name_map<entry> m_definitions;
    void add_core(name const & n, expr const & pre_type, expr const & pre_value, level_param_names const & ls,
                  expr const & type, expr const & value);
public:
    definition_cache();
    /** \brief Add the cache entry (n, pre_type, pre_value) -> (ls, type, value) */
    void add(name const & n, expr const & pre_type, expr const & pre_value, level_param_names const & ls, expr const & type, expr const & value);
    /** \brief Return (if available) elaborated (level_names, type, value) for (n, pre_type, pre_value).
        The pre_type and pre_value are compared modulo placeholders names if the cached values.
        In principle, we could have compared only the name and pre_type, but we only want to use cached values if the
        user intent (captured by pre_value) did not change.
    */
    optional<std::tuple<level_param_names, expr, expr>> find(name const & n, expr const & pre_type, expr const & pre_value);
    /** \brief Store the cache content into the given stream */
    void save(std::ostream & out);
    /** \brief Load the cache content from the given stream */
    void load(std::istream & in);
    /** \brief Remove the entry named \c n from the cache. */
    void erase(name const & n);
    /** \brief Clear the whole cache */
    void clear();
};
}
