/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <vector>
#include <utility>
#include <string>
#include <sstream>
#include <fstream>
#include <algorithm>
#include <sys/stat.h>
#include "util/hash.h"
#include "util/thread.h"
#include "util/lean_path.h"
#include "util/sstream.h"
#include "util/buffer.h"
#include "util/interrupt.h"
#include "util/name_map.h"
#include "util/file_lock.h"
#include "kernel/type_checker.h"
#include "kernel/quotient/quotient.h"
#include "library/module.h"
#include "library/noncomputable.h"
#include "library/sorry.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"
#include "library/unfold_macros.h"
#include "library/module_mgr.h"
#include "version.h"

#ifndef LEAN_ASYNCH_IMPORT_THEOREM
#define LEAN_ASYNCH_IMPORT_THEOREM false
#endif

namespace lean {
corrupted_file_exception::corrupted_file_exception(std::string const & fname):
    exception(sstream() << "failed to import '" << fname << "', file is corrupted, please regenerate the file from sources") {
}

typedef pair<std::string, std::function<void(environment const &, serializer &)>> writer;

struct module_ext : public environment_extension {
    list<module_name>  m_direct_imports;
    list<writer>      m_writers;
    list<name>        m_module_univs;
    list<name>        m_module_decls;
    name_set          m_module_defs;
    name_set          m_imported;
    // Map from declaration name to olean file where it was defined
    name_map<std::string>     m_decl2olean;
    name_map<pos_info>        m_decl2pos_info;
};

struct module_ext_reg {
    unsigned m_ext_id;
    module_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<module_ext>()); }
};

static module_ext_reg * g_ext = nullptr;

static module_ext const & get_extension(environment const & env) {
    return static_cast<module_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, module_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<module_ext>(ext));
}

list<name> const & get_curr_module_decl_names(environment const & env) {
    return get_extension(env).m_module_decls;
}

list<name> const & get_curr_module_univ_names(environment const & env) {
    return get_extension(env).m_module_univs;
}

list<module_name> get_curr_module_imports(environment const & env) {
    return get_extension(env).m_direct_imports;
}

/* Add the entry decl_name -> fname to the environment. fname is the name of the .olean file
   where decl_name was defined. */
static environment add_decl_olean(environment const & env, name const & decl_name, std::string const & fname) {
    module_ext ext = get_extension(env);
    ext.m_decl2olean.insert(decl_name, fname);
    return update(env, ext);
}

optional<std::string> get_decl_olean(environment const & env, name const & decl_name) {
    module_ext const & ext = get_extension(env);
    name d;
    if (auto r = inductive::is_intro_rule(env, decl_name))
        d = *r;
    else if (auto r = inductive::is_elim_rule(env, decl_name))
        d = *r;
    else
        d = decl_name;
    if (auto r = ext.m_decl2olean.find(d))
        return optional<std::string>(*r);
    else
        return optional<std::string>();
}

static std::string * g_pos_info_key = nullptr;
LEAN_THREAD_VALUE(bool, g_has_pos, false);
LEAN_THREAD_VALUE(unsigned, g_curr_line, 0);
LEAN_THREAD_VALUE(unsigned, g_curr_column, 0);

module::scope_pos_info::scope_pos_info(pos_info const & pos_info) {
    g_has_pos     = true;
    g_curr_line   = pos_info.first;
    g_curr_column = pos_info.second;
}

module::scope_pos_info::~scope_pos_info() {
    g_has_pos = false;
}

static environment add_decl_pos_info(environment const & env, name const & decl_name) {
    if (!g_has_pos)
        return env;
    module_ext ext = get_extension(env);
    unsigned line   = g_curr_line;
    unsigned column = g_curr_column;
    ext.m_decl2pos_info.insert(decl_name, mk_pair(line, column));
    environment new_env = update(env, ext);
    return module::add(new_env, *g_pos_info_key, [=](environment const &, serializer & s) {
            s << decl_name << line << column;
        });
}

optional<pos_info> get_decl_pos_info(environment const & env, name const & decl_name) {
    module_ext const & ext = get_extension(env);
    name d;
    if (auto r = inductive::is_intro_rule(env, decl_name))
        d = *r;
    else if (auto r = inductive::is_elim_rule(env, decl_name))
        d = *r;
    else
        d = decl_name;
    if (auto r = ext.m_decl2pos_info.find(d))
        return optional<pos_info>(*r);
    else
        return optional<pos_info>();
}

environment add_transient_decl_pos_info(environment const & env, name const & decl_name, pos_info const & pos) {
    module_ext ext = get_extension(env);
    ext.m_decl2pos_info.insert(decl_name, pos);
    return update(env, ext);
}

static void pos_info_reader(deserializer & d, environment & env) {
    name decl_name;
    unsigned line, column;
    d >> decl_name >> line >> column;
    env = add_transient_decl_pos_info(env, decl_name, pos_info(line, column));
}

static char const * g_olean_end_file = "EndFile";
static char const * g_olean_header   = "oleanfile";

serializer & operator<<(serializer & s, module_name const & n) {
    if (n.m_relative)
        s << true << *n.m_relative << n.m_name;
    else
        s << false << n.m_name;
    return s;
}

deserializer & operator>>(deserializer & d, module_name & r) {
    if (d.read_bool()) {
        unsigned k;
        d >> k >> r.m_name;
        r.m_relative = { k };
    } else {
        d >> r.m_name;
        r.m_relative = optional<unsigned>();
    }
    return d;
}

LEAN_THREAD_PTR(std::vector<task_result<expr>>, g_export_delayed_proofs);
class scoped_delayed_proofs {
    std::vector<task_result<expr>> * m_old;
public:
    scoped_delayed_proofs(std::vector<task_result<expr>> & r) {
        m_old = g_export_delayed_proofs;
        g_export_delayed_proofs = &r;
    }
    ~scoped_delayed_proofs() {
        g_export_delayed_proofs = m_old;
    }
};

void export_module(std::ostream & out, environment const & env) {
    module_ext const & ext = get_extension(env);

    buffer<module_name> imports;
    to_buffer(ext.m_direct_imports, imports);
    std::reverse(imports.begin(), imports.end());

    buffer<writer const *> writers;
    for (writer const & w : ext.m_writers)
        writers.push_back(&w);
    std::reverse(writers.begin(), writers.end());

    std::ostringstream out1(std::ios_base::binary);
    serializer s1(out1);

    // store objects
    for (auto p : writers) {
        s1 << p->first;
        p->second(env, s1);
    }
    s1 << g_olean_end_file;

    serializer s2(out);
    std::string r = out1.str();
    unsigned h    = hash(r.size(), [&](unsigned i) { return r[i]; });
    s2 << g_olean_header << LEAN_VERSION_MAJOR << LEAN_VERSION_MINOR << LEAN_VERSION_PATCH;
    s2 << h;
    // store imported files
    s2 << imports.size();
    for (auto m : imports)
        s2 << m;
    // store object code
    s2.write_unsigned(r.size());
    for (unsigned i = 0; i < r.size(); i++)
        s2.write_char(r[i]);
}

std::vector<task_result<expr>> export_module_delayed(std::ostream & out, environment const & env) {
    std::vector<task_result<expr>> delayed_proofs;
    scoped_delayed_proofs _(delayed_proofs);
    export_module(out, env);
    return delayed_proofs;
}

typedef std::unordered_map<std::string, module_object_reader> object_readers;
static object_readers * g_object_readers = nullptr;
static object_readers & get_object_readers() { return *g_object_readers; }

void register_module_object_reader(std::string const & k, module_object_reader r) {
    object_readers & readers = get_object_readers();
    lean_assert(readers.find(k) == readers.end());
    readers[k] = r;
}

static std::string * g_glvl_key  = nullptr;
static std::string * g_decl_key  = nullptr;
static std::string * g_inductive = nullptr;
static std::string * g_quotient  = nullptr;

namespace module {
environment add(environment const & env, std::string const & k, std::function<void(environment const &, serializer &)> const & wr) {
    module_ext ext = get_extension(env);
    ext.m_writers  = cons(writer(k, wr), ext.m_writers);
    return update(env, ext);
}

environment add_universe(environment const & env, name const & l) {
    environment new_env = env.add_universe(l);
    module_ext ext = get_extension(env);
    ext.m_module_univs = cons(l, ext.m_module_univs);
    new_env = update(new_env, ext);
    return add(new_env, *g_glvl_key, [=](environment const &, serializer & s) { s << l; });
}

environment update_module_defs(environment const & env, declaration const & d) {
    if (d.is_definition() && !d.is_theorem()) {
        module_ext ext = get_extension(env);
        ext.m_module_decls = cons(d.get_name(), ext.m_module_decls);
        ext.m_module_defs.insert(d.get_name());
        return update(env, ext);
    } else {
        module_ext ext = get_extension(env);
        ext.m_module_decls = cons(d.get_name(), ext.m_module_decls);
        return update(env, ext);
    }
}

static declaration theorem2axiom(declaration const & decl) {
    lean_assert(decl.is_theorem());
    return mk_axiom(decl.get_name(), decl.get_univ_params(), decl.get_type());
}

static environment export_decl(environment const & env, declaration const & d) {
    name n = d.get_name();
    return add(env, *g_decl_key, [=](environment const & env, serializer & s) {
            auto d = env.get(n);
            if (g_export_delayed_proofs && d.is_theorem()) {
                s << true << theorem2axiom(d) << static_cast<unsigned>(g_export_delayed_proofs->size());
                g_export_delayed_proofs->push_back(d.get_value_task());
            } else {
                s << false << d;
            }
        });
}

environment add(environment const & env, certified_declaration const & d) {
    environment new_env = env.add(d);
    declaration _d = d.get_declaration();
    if (!check_computable(new_env, _d.get_name()))
        new_env = mark_noncomputable(new_env, _d.get_name());
    new_env = export_decl(update_module_defs(new_env, _d), _d);
    return add_decl_pos_info(new_env, _d.get_name());
}

bool is_definition(environment const & env, name const & n) {
    module_ext const & ext = get_extension(env);
    return ext.m_module_defs.contains(n);
}

environment declare_quotient(environment const & env) {
    environment new_env = ::lean::declare_quotient(env);
    return add(new_env, *g_quotient, [=](environment const &, serializer &) {});
}

static void quotient_reader(deserializer &, environment & env) {
    env = ::lean::declare_quotient(env);
}

using inductive::certified_inductive_decl;

environment add_inductive(environment                       env,
                          inductive::inductive_decl const & decl,
                          bool                              is_trusted) {
    pair<environment, certified_inductive_decl> r = inductive::add_inductive(env, decl, is_trusted);
    environment new_env            = r.first;
    certified_inductive_decl cdecl = r.second;
    module_ext ext = get_extension(env);
    ext.m_module_decls = cons(decl.m_name, ext.m_module_decls);
    new_env = update(new_env, ext);
    new_env = add_decl_pos_info(new_env, decl.m_name);
    return add(new_env, *g_inductive, [=](environment const &, serializer & s) {
            s << cdecl;
        });
}
} // end of namespace module

std::pair<std::vector<module_name>, std::vector<char>> parse_olean(std::istream & in, std::string const & file_name, bool check_hash) {
    unsigned major, minor, patch, claimed_hash;
    unsigned code_size;
    std::vector<module_name> imports;
    std::vector<char> code;

    deserializer d1(in, optional<std::string>(file_name));
    std::string header;
    d1 >> header;
    if (header != g_olean_header)
        throw exception(sstream() << "file '" << file_name << "' does not seem to be a valid object Lean file, invalid header");
    d1 >> major >> minor >> patch >> claimed_hash;
    // Enforce version?

    unsigned num_imports  = d1.read_unsigned();
    for (unsigned i = 0; i < num_imports; i++) {
        module_name r;
        d1 >> r;
        imports.push_back(r);
    }

    code_size = d1.read_unsigned();
    code.resize(code_size);
    d1.read(code);

//    if (m_senv.env().trust_lvl() <= LEAN_BELIEVER_TRUST_LEVEL) {
    if (check_hash) {
        unsigned computed_hash = hash(code_size, [&](unsigned i) { return code[i]; });
        if (claimed_hash != computed_hash)
            throw exception(sstream() << "file '" << file_name << "' has been corrupted, checksum mismatch");
    }

    return { imports, code };
}

struct import_helper {
    static environment add_unchecked(environment const & env, declaration const & decl) {
        return env.add(certify_or_check(env, decl));
    }
    static certified_declaration certify_or_check(environment const & env, declaration const & decl) {
        return certify_unchecked::certify_or_check(env, decl);
    }
};

static void import_module(environment & env, std::string const & module_file_name, module_name const & ref,
                          module_loader const & mod_ldr) {
    auto res = mod_ldr(module_file_name, ref);
    if (get_extension(env).m_imported.contains(res.m_module_name)) return;
    std::istringstream in(res.m_obj_code, std::ios_base::binary);
    auto olean = parse_olean(in, res.m_module_name, false);
    for (auto & dep : olean.first) {
        import_module(env, res.m_module_name, dep, mod_ldr);
    }
    auto ext = get_extension(env);
    ext.m_imported.insert(res.m_module_name);
    env = update(env, ext);
    import_module(olean.second, res.m_module_name, env, res.m_delayed_proofs);
}

environment import_module(environment const & env0, std::string const & module_file_name,
                          module_name const & ref,
                          module_loader const & mod_ldr) {
    environment env = env0;
    module_ext ext = get_extension(env);
    ext.m_direct_imports = cons(ref, ext.m_direct_imports);
    env = update(env, ext);
    import_module(env, module_file_name, ref, mod_ldr);
    return env;
}

static optional<name> import_decl(deserializer & d, environment & env,
                                  std::vector<task_result<expr>> const & delayed_proofs) {
    bool is_delayed; d >> is_delayed;
    declaration decl = read_declaration(d);
    decl = unfold_untrusted_macros(env, decl);
    if (decl.get_name() == get_sorry_name() && has_sorry(env)) {
        // TODO(gabriel): not sure why this is here
        return optional<name>();
    }
    if (is_delayed) {
        unsigned i; d >> i;
        auto delayed_proof = delayed_proofs.at(i);
        decl = mk_theorem(decl.get_name(), decl.get_univ_params(), decl.get_type(), delayed_proof);
    }
    env = import_helper::add_unchecked(env, decl);
    return optional<name>(decl.get_name());
}

static void import_universe(deserializer & d, environment & env) {
    name const l = read_name(d);
    env = env.add_universe(l);
}

void import_module(std::vector<char> const & olean_code, std::string const & file_name, environment & env,
                   std::vector<task_result<expr>> const & delayed_proofs) {
    // TODO(gabriel): update extension
    std::string s(olean_code.data(), olean_code.size());
    std::istringstream in(s, std::ios_base::binary);
    scoped_expr_caching enable_caching(true);
    deserializer d(in, optional<std::string>(file_name));
    unsigned obj_counter = 0;
    while (true) {
        std::string k;
        d >> k;
        if (k == g_olean_end_file) {
            break;
        } else if (k == *g_decl_key) {
            if (auto decl_name = import_decl(d, env, delayed_proofs))
                env = add_decl_olean(env, *decl_name, file_name);
        } else if (k == *g_glvl_key) {
            import_universe(d, env);
        } else if (k == *g_inductive) {
            inductive::certified_inductive_decl cdecl = read_certified_inductive_decl(d);
            env = cdecl.add(env);
            env = add_decl_olean(env, cdecl.get_decl().m_name, file_name);
        } else {
            object_readers & readers = get_object_readers();
            auto it = readers.find(k);
            if (it == readers.end())
                throw exception(sstream() << "file '" << file_name << "' has been corrupted, unknown object: " << k);
            it->second(d, env);
        }
        obj_counter++;
    }
}

module_loader mk_olean_loader() {
    return[=] (std::string const & module_fn, module_name const & ref) {
        auto base_dir = dirname(module_fn.c_str());
        auto fn = find_file(base_dir, ref.m_relative, ref.m_name, ".olean");
        auto contents = read_file(fn, std::ios_base::binary);
        return loaded_module { fn, contents, {} };
    };
}

module_loader mk_dummy_loader() {
    return[=] (std::string const &, module_name const &) -> loaded_module {
        throw exception("module importing disabled");
    };
}

void initialize_module() {
    g_ext            = new module_ext_reg();
    g_object_readers = new object_readers();
    g_glvl_key       = new std::string("glvl");
    g_decl_key       = new std::string("decl");
    g_inductive      = new std::string("ind");
    g_quotient       = new std::string("quot");
    g_pos_info_key   = new std::string("PInfo");
    register_module_object_reader(*g_quotient, module::quotient_reader);
    register_module_object_reader(*g_pos_info_key, pos_info_reader);
}

void finalize_module() {
    delete g_inductive;
    delete g_quotient;
    delete g_decl_key;
    delete g_glvl_key;
    delete g_object_readers;
    delete g_ext;
    delete g_pos_info_key;
}
}
