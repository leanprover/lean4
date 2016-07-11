/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
/** \brief Information for a user defined recursor */
class recursor_info {
    name                     m_recursor;
    name                     m_type_name;
    list<unsigned>           m_universe_pos; // position of the recursor universe level parameters.
    bool                     m_dep_elim;
    bool                     m_recursive;
    unsigned                 m_num_args; // total number of arguments
    unsigned                 m_major_pos;
    // if param is <none>, then it should be resolved by type class resolution
    list<optional<unsigned>> m_params_pos;  // position of the recursor parameters in the major premise
    list<unsigned>           m_indices_pos; // position of the recursor indices in the major premise
    list<bool>               m_produce_motive; // "bit-map" indicating whether the i-th element is true, if
                                               // the i-th minor premise produces the motive

public:
    recursor_info(name const & r, name const & I, list<unsigned> const & univ_pos,
                  bool dep_elim, bool is_rec, unsigned num_args, unsigned major_pos,
                  list<optional<unsigned>> const & params_pos, list<unsigned> const & indices_pos,
                  list<bool> const & produce_motive);
    recursor_info();

    /** \brief Return a list containing the position of the recursor universe parameters in the major premise.
        The value get_motive_univ_idx() is used to identify the position of the motive universe. */
    list<unsigned> const & get_universe_pos() const { return m_universe_pos; }

    static unsigned get_motive_univ_idx() { return static_cast<unsigned>(-1); }

    name const & get_name() const { return m_recursor; }
    name const & get_type_name() const { return m_type_name; }
    unsigned get_num_args() const { return m_num_args; }
    unsigned get_num_params() const { return length(m_params_pos); }
    unsigned get_num_indices() const { return length(m_indices_pos); }
    unsigned get_motive_pos() const { return get_num_params(); }
    unsigned get_first_index_pos() const { return m_major_pos - get_num_indices(); }
    unsigned get_major_pos() const { return m_major_pos; }
    list<optional<unsigned>> const & get_params_pos() const { return m_params_pos; }
    /** \brief Return position of the recursor indices in the major premise. */
    list<unsigned> const & get_indices_pos() const { return m_indices_pos; }
    list<bool> const & get_produce_motive() const { return m_produce_motive; }
    bool has_dep_elim() const { return m_dep_elim; }
    bool is_recursive() const { return m_recursive; }
    bool is_minor(unsigned pos) const;
    unsigned get_num_minors() const;

    void write(serializer & s) const;
    static recursor_info read(deserializer & d);
};

environment add_user_recursor(environment const & env, name const & r, optional<unsigned> const & major_pos,
                              bool persistent);
recursor_info get_recursor_info(environment const & env, name const & r);
list<name> get_recursors_for(environment const & env, name const & I);
bool is_user_defined_recursor(environment const & env, name const & r);

class has_recursors_pred {
    name_map<list<name>>    m_type2recursors;
public:
    has_recursors_pred(environment const & env);
    bool operator()(name const & n) const { return m_type2recursors.contains(n); }
};

void initialize_user_recursors();
void finalize_user_recursors();
}
