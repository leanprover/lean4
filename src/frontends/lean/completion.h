/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Leonardo de Moura, Sebastian Ullrich
*/
#pragma once
#include <string>
#include <vector>
#include "kernel/environment.h"
#include "util/sexpr/options.h"
#include "frontends/lean/json.h"
#include "util/lean_path.h"

namespace lean {
std::vector<json> get_decl_completions(std::string const & pattern, environment const & env, options const & o);
std::vector<json> get_field_completions(name const & s, std::string const & pattern, environment const & env, options const & o);
std::vector<json> get_option_completions(std::string const & pattern, options const & opts);
pair<optional<unsigned>, std::string> parse_import(std::string s);
std::vector<json> get_import_completions(std::string const & pattern, std::string const & curr_dir,
                                         search_path const & path, options const & opts);
std::vector<json> get_interactive_tactic_completions(std::string const & pattern, name const & tac_class,
                                                     environment const & env, options const & opts);
std::vector<json> get_attribute_completions(std::string const & pattern, environment const & env, options const & opts);
std::vector<json> get_namespace_completions(std::string const & pattern, environment const & env, options const & opts);

void search_decls(std::string const & pattern, std::vector<pair<std::string, environment>> const & envs,
                  options const & opts, std::vector<json> & completions);

void initialize_completion();
void finalize_completion();
}
