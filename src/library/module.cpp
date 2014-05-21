/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <utility>
#include <string>
#include "util/hash.h"
#include "kernel/type_checker.h"
#include "library/module.h"
#include "library/kernel_serializer.h"

namespace lean {
typedef std::pair<std::string, std::function<void(serializer &)>> writer;
typedef std::pair<std::string, unsigned> import_info; // imported module and its hashcode

struct module_ext : public environment_extension {
    list<import_info> m_direct_imports;
    list<writer> m_writers;
};

struct module_ext_reg {
    unsigned m_ext_id;
    module_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<module_ext>()); }
};

static module_ext_reg g_ext;
static module_ext const & get_extension(environment const & env) {
    return static_cast<module_ext const &>(env.get_extension(g_ext.m_ext_id));
}
static environment update(environment const & env, module_ext const & ext) {
    return env.update(g_ext.m_ext_id, std::make_shared<module_ext>(ext));
}

void export_module(std::ostream & out, environment const & env) {
    module_ext const & ext = get_extension(env);
    buffer<import_info> imports;
    buffer<writer const *> writers;
    to_buffer(ext.m_direct_imports, imports);
    std::reverse(imports.begin(), imports.end());
    for (writer const & w : ext.m_writers)
        writers.push_back(&w);
    std::reverse(writers.begin(), writers.end());

    std::string r;
    std::ostringstream out1(r);
    serializer s1(out1);

    // store imported files
    s1 << imports.size();
    for (auto p : imports)
        s1 << p.first << p.second;

    // store objects
    for (auto p : writers) {
        s1 << p->first;
        p->second(s1);
    }

    serializer s2(out);
    unsigned h = hash_str(r.size(), r.c_str(), 13);
    s2 << h;
    for (unsigned i = 0; i < r.size(); i++)
        s2.write_char(r[i]);
}

typedef std::unordered_map<std::string, module_object_reader> object_readers;
static std::unique_ptr<object_readers> g_object_readers;
static object_readers & get_object_readers() {
    if (!g_object_readers)
        g_object_readers.reset(new object_readers());
    return *(g_object_readers.get());
}

void register_module_object_reader(std::string const & k, module_object_reader r) {
    object_readers & readers = get_object_readers();
    lean_assert(readers.find(k) == readers.end());
    readers[k] = r;
}

environment add(environment const & env, std::string const & k, std::function<void(serializer &)> const & wr) {
    module_ext ext = get_extension(env);
    ext.m_writers  = list<writer>(writer(k, wr), ext.m_writers);
    return update(env, ext);
}

static std::string g_decl("decl");

static void declaration_reader(deserializer & d, module_idx midx, shared_environment & senv,
                               std::function<void(asynch_update_fn const &)> & add_asynch_update,
                               std::function<void(delayed_update_fn const &)> &) {
    declaration decl = read_declaration(d, midx);
    environment env  = senv.env();
    if (env.trust_lvl() > LEAN_BELIEVER_TRUST_LEVEL) {
        senv.add(decl);
    } else if (decl.is_theorem()) {
        // First, we add the theorem as an axiom, and create an asychronous task for
        // checking the actual theorem, and replace the axiom with the actual theorem.
        certified_declaration tmp_c = check(env, mk_axiom(decl.get_name(), decl.get_params(), decl.get_type()));
        senv.add(tmp_c);
        add_asynch_update([=](shared_environment & senv) {
                certified_declaration c = check(env, decl);
                senv.replace(c);
            });
    } else {
        certified_declaration c = check(env, decl);
        senv.add(c);
    }
}

static register_module_object_reader_fn g_reg_decl_reader(g_decl, declaration_reader);

environment add(environment const & env, certified_declaration const & d) {
    environment new_env = env.add(d);
    new_env = add(new_env, g_decl, [=](serializer & s) { s << d.get_declaration(); });
    return new_env;
}

environment import_modules(environment const & env, unsigned num_modules, std::string const * modules) {
    // TODO(Leo)
    for (unsigned i = 0; i < num_modules; i++) std::cout << modules[i];
    return env;
}

environment import_module(environment const & env, std::string const & module) {
    return import_modules(env, 1, &module);
}
}
