/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/io_state.h"
#include "util/priority_queue.h"

#ifndef LEAN_DEFAULT_PRIORITY
#define LEAN_DEFAULT_PRIORITY 1000u
#endif

namespace lean {
typedef std::function<environment(environment const &, io_state const &, name const &, unsigned, list<unsigned> const &,
                                  bool)> set_attribute_proc;
typedef std::function<environment(environment const &, io_state const &, name const &,
                                  bool)> set_no_params_attribute_proc;
typedef std::function<environment(environment const &, io_state const &, name const &,
                                  unsigned, bool)> set_prio_attribute_proc;
typedef std::function<environment(environment const &, io_state const &, name const &,
                                  optional<unsigned> const &, bool)> set_opt_param_attribute_proc;
typedef std::function<environment(environment const &, io_state const &, name const &, list<unsigned> const &,
                                  bool)> set_params_attribute_proc;

void register_attribute(char const * attr, char const * descr, set_attribute_proc const & on_set);
void register_no_params_attribute(char const * attr, char const * descr, set_no_params_attribute_proc const & on_set);
void register_no_params_attribute(char const * attr, char const * descr);
void register_prio_attribute(char const * attr, char const * descr, set_prio_attribute_proc const & on_set);
void register_prio_attribute(char const * attr, char const * descr);
void register_opt_param_attribute(char const * attr, char const * descr, set_opt_param_attribute_proc const & on_set);
void register_params_attribute(char const * attr, char const * descr, set_params_attribute_proc const & on_set);
void register_params_attribute(char const * attr, char const * descr);

void register_incompatible(char const * attr1, char const * attr2);

bool is_attribute(char const * attr);
void get_attributes(buffer<char const *> &);
void get_attribute_tokens(buffer<char const *> &);
char const * get_attribute_from_token(char const * attr_token);
char const * get_attribute_token(char const * attr);

environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, unsigned prio, list<unsigned> const & params, bool persistent);
environment set_attribute(environment const & env, io_state const & ios, char const * attr,
                          name const & d, bool persistent);

bool has_attribute(environment const & env, char const * attr, name const & d);
void get_attribute_instances(environment const & env, name const & attr, buffer<name> &);
priority_queue<name, name_quick_cmp> get_attribute_instances_by_prio(environment const & env, name const & attr);

unsigned get_attribute_prio(environment const & env, name const & attr, name const & d);
list<unsigned> get_attribute_params(environment const & env, name const & attr, name const & d);

bool are_incompatible(char const * attr1, char const * attr2);

void initialize_attribute_manager();
void finalize_attribute_manager();
}
