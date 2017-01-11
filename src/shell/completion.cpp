/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Leonardo de Moura, Sebastian Ullrich
*/
#if defined(LEAN_JSON)
#include <algorithm>
#include <string>
#include <vector>
#include "util/lean_path.h"
#include "util/sexpr/option_declarations.h"
#include "util/bitap_fuzzy_search.h"
#include "library/protected.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/class.h"
#include "frontends/lean/util.h"
#include "shell/server.h"
#include "shell/completion.h"

namespace lean {

#define LEAN_FUZZY_MAX_ERRORS          3
#define LEAN_FUZZY_MAX_ERRORS_FACTOR   3

/** \brief Return an (atomic) name if \c n can be referenced by this atomic
    name in the given environment. */
optional<name> is_essentially_atomic(environment const & env, name const & n) {
    if (n.is_atomic())
        return optional<name>(n);
    list<name> const & ns_list = get_namespaces(env);
    for (name const & ns : ns_list) {
        if (is_prefix_of(ns, n)) {
            auto n_prime = n.replace_prefix(ns, name());
            if (n_prime.is_atomic() && !is_protected(env, n))
                return optional<name>(n_prime);
            break;
        }
    }
    if (auto it = is_uniquely_aliased(env, n))
        if (it->is_atomic())
            return it;
    return optional<name>();
}

unsigned get_fuzzy_match_max_errors(unsigned prefix_sz) {
    unsigned r = (prefix_sz / LEAN_FUZZY_MAX_ERRORS_FACTOR);
    if (r > LEAN_FUZZY_MAX_ERRORS)
        return LEAN_FUZZY_MAX_ERRORS;
    return r;
}

optional<name> exact_prefix_match(environment const & env, std::string const & pattern, declaration const & d) {
    if (auto it = is_essentially_atomic(env, d.get_name())) {
        std::string it_str = it->to_string();
        // if pattern "perfectly" matches beginning of declaration name, we just display d on the top of the list
        if (it_str.compare(0, pattern.size(), pattern) == 0)
            return it;
    }
    return optional<name>();
}

template<class T>
void filter_completions(std::string const & pattern, std::vector<pair<std::string, T>> & selected,
                        std::vector<json> & completions, unsigned max_results, std::function<json(T const &)> serialize) {
    unsigned max_errors = get_fuzzy_match_max_errors(pattern.size());
    std::vector<pair<name, name>> exact_matches;
    bitap_fuzzy_search matcher(pattern, max_errors);
    unsigned num_results = 0;
    unsigned sz = selected.size();
    if (sz == 1) {
        completions.push_back(serialize(selected[0].second));
    } else if (sz > 1) {
        std::sort(selected.begin(), selected.end());
        auto it = std::unique(selected.begin(), selected.end(), [](pair<std::string, T> const & s1, pair<std::string, T> const & s2) {
            return s1.first == s2.first;
        });
        selected.resize(it - selected.begin());
        std::vector<pair<std::string, T>> next_selected;
        auto process = [&](pair<std::string, T> const & s, bool select) {
            if (select) {
                completions.push_back(serialize(s.second));
                num_results++;
                if (num_results >= max_results)
                    return false;
            } else {
                next_selected.push_back(s);
            }
            return true;
        };

        // 1. exact prefix matches
        for (auto const & s : selected) {
            if (!process(s, s.first.compare(0, pattern.size(), pattern) == 0))
                break;
        }
        std::swap(selected, next_selected);
        next_selected.clear();

        // 2. fuzzy matches by increasing error count
        for (unsigned k = 0; k <= max_errors && num_results < max_results; k++) {
            bitap_fuzzy_search matcher(pattern, k);
            for (auto const & s : selected) {
                if (!process(s, matcher.match(s.first)))
                    break;
            }
            std::swap(selected, next_selected);
            next_selected.clear();
        }
    }
}

std::vector<json> get_decl_completions(std::string const & pattern, environment const & env, options const & opts) {
    std::vector<json> completions;

    unsigned max_results = get_auto_completion_max_results(opts);
    unsigned max_errors = get_fuzzy_match_max_errors(pattern.size());
    std::vector<pair<name, name>> exact_matches;
    std::vector<pair<std::string, name>> selected;
    bitap_fuzzy_search matcher(pattern, max_errors);
    env.for_each_declaration([&](declaration const & d) {
        if (is_projection(env, d.get_name())) {
            auto s_name = d.get_name().get_prefix();
            if (is_class(env, s_name))
                return;
        }
        if (is_internal_name(d.get_name())) {
            return;
        }
        if (auto it = exact_prefix_match(env, pattern, d)) {
            exact_matches.emplace_back(*it, d.get_name());
        } else {
            std::string text = d.get_name().to_string();
            if (matcher.match(text))
                selected.emplace_back(text, d.get_name());
        }
    });
    unsigned num_results = 0;
    if (!exact_matches.empty()) {
        std::sort(exact_matches.begin(), exact_matches.end(),
                  [](pair<name, name> const & p1, pair<name, name> const & p2) {
                      return p1.first.size() < p2.first.size();
                  });
        for (pair<name, name> const & p : exact_matches) {
            completions.push_back(serialize_decl(p.first, p.second, env, opts));
            num_results++;
            if (num_results >= max_results)
                break;
        }
    }
    filter_completions<name>(pattern, selected, completions, max_results - num_results, [&](name const & n) {
        return serialize_decl(n, env, opts);
    });
    return completions;
}

std::vector<json> get_option_completions(std::string const & pattern, options const & opts) {
    unsigned max_results = get_auto_completion_max_results(opts);
    unsigned max_errors = get_fuzzy_match_max_errors(pattern.size());
    std::vector<pair<std::string, name>> selected;
    bitap_fuzzy_search matcher(pattern, max_errors);
    std::vector<json> completions;

    get_option_declarations().for_each([&](name const & n, option_declaration const &) {
        std::string text = n.to_string();
        if (matcher.match(text))
            selected.emplace_back(text, n);
    });
    filter_completions<name>(pattern, selected, completions, max_results, [&](name const & n) {
        json completion;
        completion["text"] = n.to_string();
        std::stringstream ss;
        auto const & decl = *get_option_declarations().find(n);
        decl.display_value(ss, opts);
        completion["type"] = ss.str();
        completion["doc"] = decl.get_description();
        return completion;
    });
    return completions;
}

pair<optional<unsigned>, std::string> parse_import(std::string s) {
    if (s.size() && s[0] == '.') {
        unsigned i = 1;
        while (i < s.size() && s[i] == '.')
            i++;
        return {some(i - 1), s.substr(i)};
    }
    return {{}, s};
}

std::vector<json> get_import_completions(std::string const & pattern, std::string const & curr_dir,
                                         options const & opts) {
    unsigned max_results = get_auto_completion_max_results(opts);
    unsigned max_errors = get_fuzzy_match_max_errors(pattern.size());
    std::vector<pair<std::string, pair<std::string, std::string>>> selected;
    bitap_fuzzy_search matcher(pattern, max_errors);
    std::vector<json> completions;

    optional<unsigned> depth = parse_import(pattern).first;
    std::vector<pair<std::string, std::string>> imports;
    find_imports(curr_dir, depth, imports);

    for (auto const & candidate : imports) {
        if (matcher.match(candidate.first))
            selected.emplace_back(candidate.first, candidate);
    }
    filter_completions<pair<std::string, std::string>>(pattern, selected, completions, max_results, [&](pair<std::string, std::string> const & c) {
        json completion;
        completion["text"] = c.first;
        completion["type"] = c.second;
        completion["source"]["file"] = c.second;
        completion["source"]["line"] = 1;
        completion["source"]["column"] = 0;
        return completion;
    });
    return completions;
}

std::vector<json> get_interactive_tactic_completions(std::string const & pattern, name const & tac_class,
                                                     environment const & env, options const & opts) {
    std::vector<json> completions;

    unsigned max_results = get_auto_completion_max_results(opts);
    unsigned max_errors = get_fuzzy_match_max_errors(pattern.size());
    std::vector<pair<std::string, name>> selected;
    bitap_fuzzy_search matcher(pattern, max_errors);
    name namespc = tac_class + name("interactive");
    env.for_each_declaration([&](declaration const & d) {
        auto const & n = d.get_name();
        if (n.get_prefix() == namespc && n.is_string() && matcher.match(n.get_string())) {
            selected.emplace_back(n.get_string(), n);
        }
    });
    filter_completions<name>(pattern, selected, completions, max_results, [&](name const & n) {
        return serialize_decl(n.get_string(), n, env, opts);
    });
    // append regular completions
    for (auto candidate : get_decl_completions(pattern, env, opts))
        completions.push_back(candidate);
    return completions;
}

std::vector<json> get_attribute_completions(std::string const & pattern, environment const & env,
                                            options const & opts) {
    unsigned max_results = get_auto_completion_max_results(opts);
    unsigned max_errors = get_fuzzy_match_max_errors(pattern.size());
    std::vector<pair<std::string, name>> selected;
    bitap_fuzzy_search matcher(pattern, max_errors);
    std::vector<json> completions;

    buffer<attribute const *> attrs;
    get_attributes(env, attrs);
    for (auto const & attr : attrs) {
        auto s = attr->get_name().to_string();
        if (matcher.match(s))
            selected.emplace_back(s, attr->get_name());
    }
    filter_completions<name>(pattern, selected, completions, max_results, [&](name const & n) {
        json completion;
        completion["text"] = n.to_string();
        completion["doc"] = get_attribute(env, n).get_description();
        add_source_info(env, n, completion);
        return completion;
    });
    return completions;
}

std::vector<json> get_namespace_completions(std::string const & pattern, environment const & env,
                                            options const & opts) {
    unsigned max_results = get_auto_completion_max_results(opts);
    unsigned max_errors = get_fuzzy_match_max_errors(pattern.size());
    std::vector<pair<std::string, name>> selected;
    bitap_fuzzy_search matcher(pattern, max_errors);
    std::vector<json> completions;

    for (auto const & ns : get_namespace_completion_candidates(env)) {
        if (ns.is_anonymous())
            continue;
        auto s = ns.to_string();
        if (matcher.match(s))
            selected.emplace_back(s, ns);
    }
    filter_completions<name>(pattern, selected, completions, max_results, [&](name const & n) {
        json completion;
        completion["text"] = n.to_string();
        return completion;
    });
    return completions;
}
}
#endif
