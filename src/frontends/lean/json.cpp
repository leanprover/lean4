/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#ifdef LEAN_JSON
#include "frontends/lean/json.h"
#include <string>
#include "library/documentation.h"
#include "library/scoped_ext.h"
#include "library/protected.h"
#include "kernel/declaration.h"
#include "library/type_context.h"
#include "kernel/instantiate.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/util.h"
#include "frontends/lean/interactive.h"

namespace lean {

json json_of_severity(message_severity sev) {
    switch (sev) {
        case INFORMATION: return "information";
        case WARNING:     return "warning";
        case ERROR:       return "error";
        default: lean_unreachable();
    }
}

json json_of_message(message const & msg) {
    json j;
    j["file_name"] = msg.get_file_name();
    j["pos_line"]  = msg.get_pos().first;
    j["pos_col"]   = msg.get_pos().second;
    if (auto end_pos = msg.get_end_pos()) {
        j["end_pos_line"] = end_pos->first;
        j["end_pos_col"]  = end_pos->second;
    }
    j["severity"]  = json_of_severity(msg.get_severity());
    j["caption"]   = msg.get_caption();
    j["text"]      = msg.get_text();
    return j;
}

#define LEAN_COMPLETE_CONSUME_IMPLICIT true // lean will add metavariables for implicit arguments in serialize_decl()

void add_source_info(environment const & env, name const & d, json & record) {
    if (auto olean = get_decl_olean(env, d))
        record["source"]["file"] = *olean;
    if (auto pos = get_decl_pos_info(env, d)) {
        record["source"]["line"] = pos->first;
        record["source"]["column"] = pos->second;
    }
}

json serialize_decl(name const & short_name, name const & long_name, environment const & env, options const & o) {
    declaration const & d = env.get(long_name);
    type_context_old tc(env);
    auto fmter = mk_pretty_formatter_factory()(env, o, tc);
    expr type = d.get_type();
    if (LEAN_COMPLETE_CONSUME_IMPLICIT) {
        while (true) {
            if (!is_pi(type))
                break;
            if (!binding_info(type).is_implicit() && !binding_info(type).is_inst_implicit())
                break;
            std::string q("?");
            q += binding_name(type).to_string();
            expr m = mk_constant(name(q.c_str()));
            type   = instantiate(binding_body(type), m);
        }
    }
    json completion;
    completion["text"] = short_name.to_string();
    interactive_report_type(env, o, type, completion);
    add_source_info(env, long_name, completion);
    if (auto doc = get_doc_string(env, long_name))
        completion["doc"] = *doc;
    return completion;
}

json serialize_decl(name const & d, environment const & env, options const & o) {
    // using namespace override resolution rule
    list<name> const & ns_list = get_namespaces(env);
    for (name const & ns : ns_list) {
        name new_d = d.replace_prefix(ns, name());
        if (new_d != d &&
            !new_d.is_anonymous() &&
            (!new_d.is_atomic() || !is_protected(env, d))) {
            return serialize_decl(new_d, d, env, o);
        }
    }
    // if the alias is unique use it
    if (auto it = is_uniquely_aliased(env, d)) {
        return serialize_decl(*it, d, env, o);
    } else {
        return serialize_decl(d, d, env, o);
    }
}

json json_of_name(name const & n0) {
    json j = json::array();

    name n = n0;
    while (!n.is_anonymous()) {
        if (n.is_numeral()) {
            j.push_back(n.get_numeral());
        } else if (n.is_string()) {
            j.push_back(n.get_string());
        } else {
            j.push_back(json());
        }
        n = n.get_prefix();
    }

    return j;
}

void print_json(std::ostream & out, message const & msg) {
    out << json_of_message(msg) << std::endl;
}

}
#endif
