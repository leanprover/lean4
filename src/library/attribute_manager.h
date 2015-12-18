/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/io_state.h"

#ifndef LEAN_DEFAULT_PRIORITY
#define LEAN_DEFAULT_PRIORITY 1000u
#endif

namespace lean {
typedef std::function<environment(environment const &, io_state const &, name const &,
                                  name const &, bool)> set_attribute_proc;
typedef std::function<environment(environment const &, io_state const &, name const &,
                                  unsigned, name const &, bool)> set_prio_attribute_proc;
typedef std::function<environment(environment const &, io_state const &, name const &,
                                  unsigned const &, name const &, bool)> set_param_attribute_proc;
typedef std::function<environment(environment const &, io_state const &, name const &,
                                  optional<unsigned> const &, name const &, bool)> set_opt_param_attribute_proc;
typedef std::function<environment(environment const &, io_state const &, name const &, list<unsigned> const &,
                                  name const &, bool)> set_params_attribute_proc;
typedef std::function<bool(environment const &, name const &)> has_attribute_proc; // NOLINT
typedef std::function<unsigned(environment const &, name const &)> get_attribute_prio_proc;
typedef std::function<unsigned(environment const &, name const &)> get_attribute_param_proc;
typedef std::function<list<unsigned>(environment const &, name const &)> get_attribute_params_proc;

void register_attribute(char const * attr, char const * descr, set_attribute_proc const & setter,
                        has_attribute_proc const & tester);
void register_prio_attribute(char const * attr, char const * descr, set_prio_attribute_proc const & setter,
                             has_attribute_proc const & tester, get_attribute_prio_proc const & getter);
void register_opt_param_attribute(char const * attr, char const * descr, set_opt_param_attribute_proc const & setter,
                                  has_attribute_proc const & tester, get_attribute_param_proc const & getter);
void register_param_attribute(char const * attr, char const * descr, set_param_attribute_proc const & setter,
                              has_attribute_proc const & tester, get_attribute_param_proc const & getter);
void register_params_attribute(char const * attr, char const * descr, set_params_attribute_proc const & setter,
                               has_attribute_proc const & tester, get_attribute_params_proc const & getter);

void register_incompatible(char const * attr1, char const * attr2);

enum class attribute_kind { Default, Prioritized, Parametric, OptParametric, MultiParametric };

bool is_attribute(char const * attr);
void get_attributes(buffer<char const *> &);
void get_attribute_tokens(buffer<char const *> &);
char const * get_attribute_from_token(char const * attr_token);
char const * get_attribute_token(char const * attr);
attribute_kind get_attribute_kind (char const * attr);

environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, name const & ns, bool persistent);
environment set_prio_attribute(environment const & env, io_state const & ios, char const * attr,
                               name const & d, unsigned prio, name const & ns, bool persistent);
environment set_param_attribute(environment const & env, io_state const & ios, char const * attr,
                                name const & d, unsigned param, name const & ns, bool persistent);
environment set_opt_param_attribute(environment const & env, io_state const & ios, char const * attr,
                                    name const & d, optional<unsigned> const & param, name const & ns, bool persistent);
environment set_params_attribute(environment const & env, io_state const & ios, char const * attr,
                                 name const & d, list<unsigned> const & params, name const & ns, bool persistent);

bool has_attribute(environment const & env, char const * attr, name const & d);

unsigned get_attribute_prio(environment const & env, char const * attr, name const & d);
unsigned get_attribute_param(environment const & env, char const * attr, name const & d);
list<unsigned> get_attribute_params(environment const & env, char const * attr, name const & d);

bool are_incompatible(char const * attr1, char const * attr2);

void initialize_attribute_manager();
void finalize_attribute_manager();
}
