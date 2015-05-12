/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
/** \brief Information for a user defined recursor */
class recursor_info {
    name               m_recursor;
    name               m_type_name;
    unsigned           m_num_params;
    unsigned           m_num_indices;
    unsigned           m_major_pos;
    optional<unsigned> m_motive_univ_pos; // if none, then recursor can only eliminate to Prop
    bool               m_dep_elim;

public:
    recursor_info(name const & r, name const & I, unsigned num_params, unsigned num_indices, unsigned major,
                  optional<unsigned> const & motive_univ_pos, bool dep_elim);
    recursor_info();

    name const & get_name() const { return m_recursor; }
    name const & get_type_name() const { return m_type_name; }
    unsigned get_num_params() const { return m_num_params; }
    unsigned get_num_indices() const { return m_num_indices; }
    unsigned get_motive_pos() const { return m_num_params; }
    unsigned get_first_index_pos() const { return m_major_pos - m_num_indices; }
    unsigned get_major_pos() const { return m_major_pos; }
    optional<unsigned> get_motive_univ_pos() const { return m_motive_univ_pos; }
    bool has_dep_elim() const { return m_dep_elim; }
    bool is_minor(unsigned pos) const;

    void write(serializer & s) const;
    static recursor_info read(deserializer & d);
};

environment add_user_recursor(environment const & env, name const & r, bool persistent);
recursor_info get_recursor_info(environment const & env, name const & r);
list<name> get_recursors_for(environment const & env, name const & I);
void initialize_user_recursors();
void finalize_user_recursors();
}
