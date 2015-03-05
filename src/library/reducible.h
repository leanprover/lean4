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
enum class reducible_status { Reducible, Quasireducible, Semireducible, Irreducible };
/** \brief Mark the definition named \c n as reducible or not.

    The method throws an exception if \c n is
      - not a definition
      - a theorem
      - an opaque definition that was not defined in main module

    "Reducible" definitions can be freely unfolded by automation (i.e., elaborator, simplifier, etc).
    We should view it as a hint to automation.
*/
environment set_reducible(environment const & env, name const & n, reducible_status s, bool persistent = true);

reducible_status get_reducible_status(environment const & env, name const & n);

bool is_at_least_quasireducible(environment const & env, name const & n);

struct reducible_entry;

class reducible_state {
    name_map<reducible_status> m_status;
public:
    void add(reducible_entry const & e);
    reducible_status get_status(name const & n) const;
};

/** \brief Unfold only constants marked as reducible */
class unfold_reducible_converter : public default_converter {
    reducible_state m_state;
public:
    unfold_reducible_converter(environment const & env, bool relax_main_opaque, bool memoize);
    virtual bool is_opaque(declaration const & d) const;
};

/** \brief Unfold only constants marked as reducible or quasireducible */
class unfold_quasireducible_converter : public default_converter {
    reducible_state m_state;
public:
    unfold_quasireducible_converter(environment const & env, bool relax_main_opaque, bool memoize);
    virtual bool is_opaque(declaration const & d) const;
};

/** \brief Unfold only constants marked as reducible, quasireducible, or semireducible */
class unfold_semireducible_converter : public default_converter {
    reducible_state m_state;
public:
    unfold_semireducible_converter(environment const & env, bool relax_main_opaque, bool memoize);
    virtual bool is_opaque(declaration const & d) const;
};

enum reducible_behavior { UnfoldReducible, UnfoldQuasireducible, UnfoldSemireducible };

/** \brief Create a type checker that takes the "reducibility" hints into account. */
std::unique_ptr<type_checker> mk_type_checker(environment const & env, name_generator const & ngen,
                                              bool relax_main_opaque = true, reducible_behavior r = UnfoldSemireducible,
                                              bool memoize = true);
std::unique_ptr<type_checker> mk_type_checker(environment const & env, bool relax_main_opaque,
                                              reducible_behavior r = UnfoldSemireducible);

/** \brief Create a type checker that treats all definitions as opaque. */
std::unique_ptr<type_checker> mk_opaque_type_checker(environment const & env, name_generator const & ngen);

void initialize_reducible();
void finalize_reducible();
void open_reducible(lua_State * L);
}
