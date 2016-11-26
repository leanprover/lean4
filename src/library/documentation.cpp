/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <algorithm>
#include <functional>
#include "util/sstream.h"
#include "library/module.h"

namespace lean {
struct documentation_ext : public environment_extension {
    name_map<std::string> m_doc_strings;  // map: declaration/namespace -> doc string
};

struct documentation_ext_reg {
    unsigned m_ext_id;
    documentation_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<documentation_ext>()); }
};

static documentation_ext_reg * g_ext = nullptr;
static documentation_ext const & get_extension(environment const & env) {
    return static_cast<documentation_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, documentation_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<documentation_ext>(ext));
}

static name * g_documentation = nullptr;
static std::string * g_doc_key = nullptr;

static void remove_blank_lines_begin(std::string & s) {
    optional<std::string::iterator> found;
    for (auto it = s.begin(); it != s.end(); it++) {
        if (*it == '\n') {
            found = it + 1;
        } else if (!isspace(*it)) {
            break;
        }
    }
    if (found)
        s.erase(s.begin(), *found);
}

static void rtrim(std::string & s) {
    s.erase(std::find_if(s.rbegin(), s.rend(),
                         std::not1(std::ptr_fun<int, int>(std::isspace))).base(), s.end());
}

static unsigned get_indentation(std::string const & s) {
    optional<unsigned> r;
    bool searching = true;
    unsigned i = 0;
    for (auto it = s.begin(); it != s.end(); it++) {
        if (*it == '\n') {
            i = 0;
            searching = true;
        } else if (isspace(*it) && searching) {
            i++;
        } else if (searching) {
            searching = false;
            if (r)
                r = std::min(*r, i);
            else
                r = i;
        }
    }
    return r ? *r : 0;
}

static std::string unindent(std::string const & s) {
    unsigned i = get_indentation(s);
    if (i > 0) {
        std::string r;
        unsigned j = 0;
        for (auto it = s.begin(); it != s.end(); it++) {
            if (*it == '\n') {
                j = 0;
                r += *it;
            } else if (j < i) {
                j++;
            } else {
                r += *it;
            }
        }
        return r;
    } else {
        return s;
    }
}

static std::string process_doc(std::string s) {
    remove_blank_lines_begin(s);
    rtrim(s);
    return unindent(s);
}

environment add_doc_string(environment const & env, name const & n, std::string doc) {
    doc = process_doc(doc);
    auto ext = get_extension(env);
    if (ext.m_doc_strings.contains(n)) {
        throw exception(sstream() << "environment already contains a doc string for '" << n << "'");
    }
    ext.m_doc_strings.insert(n, doc);
    auto new_env = update(env, ext);
    return module::add(new_env, *g_doc_key, [=](environment const &, serializer & s) { s << n << doc; });
}

optional<std::string> get_doc_string(environment const & env, name const & n) {
    auto ext = get_extension(env);
    if (auto r = ext.m_doc_strings.find(n))
        return optional<std::string>(*r);
    else
        return optional<std::string>();
}

static void documentation_reader(deserializer & d, shared_environment & senv,
                                 std::function<void(asynch_update_fn const &)> &,
                                 std::function<void(delayed_update_fn const &)> &) {
    name n; std::string doc;
    d >> n >> doc;
    senv.update([=](environment const & env) -> environment {
            auto ext = get_extension(env);
            ext.m_doc_strings.insert(n, doc);
            return update(env, ext);
        });
}

void initialize_documentation() {
    g_ext     = new documentation_ext_reg();
    g_documentation = new name("documentation");
    g_doc_key = new std::string("doc");
    register_module_object_reader(*g_doc_key, documentation_reader);
}

void finalize_documentation() {
    delete g_doc_key;
    delete g_documentation;
    delete g_ext;
}
}
