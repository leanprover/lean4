/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/type_checker.h"
#include "kernel/default_converter.h"

namespace lean {
enum class reducible_status { Reducible, Irreducible, Semireducible };
/** \brief Mark the definition named \c n as reducible or not.

    The method throws an exception if \c n is
      - not a definition
      - a theorem
      - an opaque definition that was not defined in main module

    "Reducible" definitions can be freely unfolded by automation (i.e., elaborator, simplifier, etc).
    We should view it as a hint to automation.
*/
environment set_reducible(environment const & env, name const & n, reducible_status s, bool persistent = true);
/** \brief Return true iff \c n was explicitly marked as reducible in the given environment.

    \remark is_reducible_on(env, n) and is_reducible_off(env, n) cannot be simultaneously true,
    but both can be false (when set_reducible(env, n, None))
*/
bool is_reducible_on(environment const & env, name const & n);
/** \brief Return true iff \c n was explicitly marked as not reducible in the given environment.

    \see is_reducible_on
*/
bool is_reducible_off(environment const & env, name const & n);

class reducible_on_converter : public default_converter {
    name_set m_reducible_on;
public:
    reducible_on_converter(environment const & env, bool relax_main_opaque, bool memoize);
    virtual bool is_opaque(declaration const & d) const;
};

class reducible_off_converter : public default_converter {
    name_set m_reducible_off;
public:
    reducible_off_converter(environment const & env, bool relax_main_opaque, bool memoize);
    virtual bool is_opaque(declaration const & d) const;
};

enum reducible_behavior { OpaqueIfNotReducibleOn, OpaqueIfReducibleOff };

/** \brief Create a type checker that takes the "reducibility" hints into account. */
std::unique_ptr<type_checker> mk_type_checker(environment const & env, name_generator const & ngen,
                                              bool relax_main_opaque = true, reducible_behavior r = OpaqueIfReducibleOff,
                                              bool memoize = true);
std::unique_ptr<type_checker> mk_type_checker(environment const & env, bool relax_main_opaque,
                                              reducible_behavior r = OpaqueIfReducibleOff);

/** \brief Create a type checker that treats all definitions as opaque. */
std::unique_ptr<type_checker> mk_opaque_type_checker(environment const & env, name_generator const & ngen);

void initialize_reducible();
void finalize_reducible();
void open_reducible(lua_State * L);
}
