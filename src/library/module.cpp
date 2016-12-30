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

struct module_ext : public environment_extension {
    std::vector<module_name> m_direct_imports;
    list<std::shared_ptr<modification const>> m_modifications;
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

std::vector<module_name> get_curr_module_imports(environment const & env) {
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

struct pos_info_mod : public modification {
    LEAN_MODIFICATION("PInfo")

    name m_decl_name;
    pos_info m_pos_info;

    pos_info_mod(name const & decl_name, pos_info const & pos) :
        m_decl_name(decl_name), m_pos_info(pos) {}

    void perform(environment & env) const override {
        auto ext = get_extension(env);
        ext.m_decl2pos_info.insert(m_decl_name, m_pos_info);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_decl_name << m_pos_info.first << m_pos_info.second;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name decl_name; unsigned line, column;
        d >> decl_name >> line >> column;
        return std::make_shared<pos_info_mod>(decl_name, pos_info {line, column});
    }
};

static environment add_decl_pos_info(environment const & env, name const & decl_name) {
    if (!g_has_pos)
        return env;
    return module::add_and_perform(env, std::make_shared<pos_info_mod>(decl_name, pos_info {g_curr_line, g_curr_column}));
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

void write_module(loaded_module const & mod, std::ostream & out) {
    std::ostringstream out1(std::ios_base::binary);
    serializer s1(out1);

    // store objects
    for (auto p : mod.m_modifications) {
        s1 << std::string(p->get_key());
        p->serialize(s1);
    }
    s1 << g_olean_end_file;

    serializer s2(out);
    std::string r = out1.str();
    unsigned h    = hash(r.size(), [&](unsigned i) { return r[i]; });
    s2 << g_olean_header << LEAN_VERSION_MAJOR << LEAN_VERSION_MINOR << LEAN_VERSION_PATCH;
    s2 << h;
    // store imported files
    s2 << static_cast<unsigned>(mod.m_imports.size());
    for (auto m : mod.m_imports)
        s2 << m;
    // store object code
    s2.write_unsigned(r.size());
    for (unsigned i = 0; i < r.size(); i++)
        s2.write_char(r[i]);
}

loaded_module export_module(environment const & env, std::string const & mod_name) {
    loaded_module out;
    out.m_module_name = mod_name;

    module_ext const & ext = get_extension(env);

    out.m_imports = ext.m_direct_imports;

    for (auto & w : ext.m_modifications)
        out.m_modifications.push_back(w);
    std::reverse(out.m_modifications.begin(), out.m_modifications.end());

    return out;
}

typedef std::unordered_map<std::string, module_modification_reader> object_readers;
static object_readers * g_object_readers = nullptr;
static object_readers & get_object_readers() { return *g_object_readers; }

void register_module_object_reader(std::string const & k, module_modification_reader && r) {
    object_readers & readers = get_object_readers();
    lean_assert(readers.find(k) == readers.end());
    readers[k] = r;
}

struct import_helper {
    static environment add_unchecked(environment const & env, declaration const & decl) {
        return env.add(certify_or_check(env, decl));
    }
    static certified_declaration certify_or_check(environment const & env, declaration const & decl) {
        return certify_unchecked::certify_or_check(env, decl);
    }
};

struct glvl_modification : public modification {
    LEAN_MODIFICATION("glvl")

    name m_name;

    glvl_modification() {}
    glvl_modification(name const & name) : m_name(name) {}

    void perform(environment & env) const override {
        env = env.add_universe(m_name);
    }

    void serialize(serializer & s) const override {
        s << m_name;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<glvl_modification>(read_name(d));
    }
};

struct decl_modification : public modification {
    LEAN_MODIFICATION("decl")

    declaration m_decl;
    bool        m_from_olean;

    decl_modification() {}
    decl_modification(declaration const & decl, bool from_olean = false):
        m_decl(decl), m_from_olean(from_olean) {}

    void perform(environment & env) const override {
        auto decl = m_decl;
        /* Gabriel, I had to add the following condition to avoid a deadlock that was happening at Travis.
           I managed to reproduce the deadlock on my macbook, but it doesn't happen in my Ubuntu desktop.
           The problem was exposed by commit 7f86ad64eb9d5f644. Before this commit, unfold_untrusted_macros
           was a no-op if the user did not set the trust level in the command line.

           The procedure unfold_untrusted_macros tries to access decl.get_value(). I believe the dead lock
           occurs when we try to perform the modification but the proof elaboration did not finish yet.

           The unfold_untrusted_macros is only needed when we are importing the declaration from a .olean
           file that has been created with a different (and higher) trust level. So, it may contain macros
           that will not be accepted by the current kernel, and they must be unfolded.

           In a single Lean session, the trust level is fixed, and we invoke unfold_untrusted_macros
           at frontends/lean/definition_cmds.cpp before we even create the declaration. So, I added
           the flag m_from_olean to distinguish whether the modification came from a .olean or a .lean file.
           I'm setting it to true at deserialize.
        */
        if (m_from_olean) {
            decl = unfold_untrusted_macros(env, decl);
        }

        if (decl.get_name() == get_sorry_name() && has_sorry(env)) {
            // ignore double sorrys
            return;
        }
        // TODO(gabriel): this might be a bit more unsafe here than before
        env = import_helper::add_unchecked(env, decl);
    }

    void serialize(serializer & s) const override {
        s << m_decl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<decl_modification>(read_declaration(d), true);
    }

    void get_task_dependencies(std::vector<generic_task_result> & deps) const override {
        if (m_decl.is_theorem())
            deps.push_back(m_decl.get_value_task());
    }
};

struct inductive_modification : public modification {
    LEAN_MODIFICATION("ind")

    inductive::certified_inductive_decl m_decl;

    inductive_modification(inductive::certified_inductive_decl const & decl) : m_decl(decl) {}

    void perform(environment & env) const override {
        env = m_decl.add(env);
    }

    void serialize(serializer & s) const override {
        s << m_decl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<inductive_modification>(read_certified_inductive_decl(d));
    }
};

struct quot_modification : public modification {
    LEAN_MODIFICATION("quot")

    void perform(environment & env) const override {
        env = ::lean::declare_quotient(env);
    }

    void serialize(serializer &) const override {}

    static std::shared_ptr<modification const> deserialize(deserializer &) {
        return std::make_shared<quot_modification>();
    }
};

namespace module {
environment add(environment const & env, std::shared_ptr<modification const> const & modf) {
    module_ext ext = get_extension(env);
    ext.m_modifications = cons(modf, ext.m_modifications);
    return update(env, ext);
}

environment add_and_perform(environment const & env, std::shared_ptr<modification const> const & modf) {
    auto new_env = env;
    modf->perform(new_env);
    module_ext ext = get_extension(new_env);
    ext.m_modifications = cons(modf, ext.m_modifications);
    return update(new_env, ext);
}

environment add_universe(environment const & env, name const & l) {
    module_ext ext = get_extension(env);
    ext.m_module_univs = cons(l, ext.m_module_univs);
    return add_and_perform(update(env, ext), std::make_shared<glvl_modification>(l));
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

environment add(environment const & env, certified_declaration const & d) {
    environment new_env = env.add(d);
    declaration _d = d.get_declaration();
    if (!check_computable(new_env, _d.get_name()))
        new_env = mark_noncomputable(new_env, _d.get_name());
    new_env = update_module_defs(new_env, _d);
    new_env = add(new_env, std::make_shared<decl_modification>(_d));
    return add_decl_pos_info(new_env, _d.get_name());
}

bool is_definition(environment const & env, name const & n) {
    module_ext const & ext = get_extension(env);
    return ext.m_module_defs.contains(n);
}

environment declare_quotient(environment const & env) {
    return add_and_perform(env, std::make_shared<quot_modification>());
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
    return add(new_env, std::make_shared<inductive_modification>(cdecl));
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

static void import_module(environment & env, std::string const & module_file_name, module_name const & ref,
                          module_loader const & mod_ldr, buffer<import_error> & import_errors) {
    try {
        auto res = mod_ldr(module_file_name, ref);

        auto & ext0 = get_extension(env);
        if (ext0.m_imported.contains(res->m_module_name)) return;

        if (ext0.m_imported.empty() && res->m_env) {
            env = *res->m_env;
        } else {
            for (auto &dep : res->m_imports) {
                import_module(env, res->m_module_name, dep, mod_ldr, import_errors);
            }
            import_module(res->m_modifications, res->m_module_name, env);
        }

        auto ext = get_extension(env);
        ext.m_imported.insert(res->m_module_name);
        env = update(env, ext);
    } catch (throwable) {
        import_errors.push_back({module_file_name, ref, std::current_exception()});
    }
}

environment import_modules(environment const & env0, std::string const & module_file_name,
                           std::vector<module_name> const & refs, module_loader const & mod_ldr,
                           buffer<import_error> & import_errors) {
    environment env = env0;

    for (auto & ref : refs)
        import_module(env, module_file_name, ref, mod_ldr, import_errors);

    module_ext ext = get_extension(env);
    ext.m_direct_imports = refs;
    return update(env, ext);
}

environment import_modules(environment const & env0, std::string const & module_file_name,
                           std::vector<module_name> const & refs, module_loader const & mod_ldr) {
    buffer<import_error> import_errors;
    auto env = import_modules(env0, module_file_name, refs, mod_ldr, import_errors);
    if (!import_errors.empty()) std::rethrow_exception(import_errors.back().m_ex);
    return env;
}

static environment mk_preimported_module(environment const & initial_env, loaded_module const & lm, module_loader const & mod_ldr) {
    auto env = initial_env;
    buffer<import_error> import_errors;
    for (auto & dep : lm.m_imports) {
        import_module(env, lm.m_module_name, dep, mod_ldr, import_errors);
    }
    if (!import_errors.empty()) std::rethrow_exception(import_errors.back().m_ex);
    import_module(lm.m_modifications, lm.m_module_name, env);
    return env;
}

std::shared_ptr<loaded_module const> cache_preimported_env(
        loaded_module && lm_ref, environment const & env0,
        std::function<module_loader()> const & mk_mod_ldr) {
    auto lm_ptr = std::make_shared<loaded_module>(lm_ref);
    auto & lm = *lm_ptr;
    lm_ptr->m_env = lazy_value<environment>([&lm, env0, mk_mod_ldr] {
        return mk_preimported_module(env0, lm, mk_mod_ldr());
    });
    return lm_ptr;
}

modification_list parse_olean_modifications(std::vector<char> const & olean_code, std::string const & file_name) {
    modification_list ms;
    std::string s(olean_code.data(), olean_code.size());
    std::istringstream in(s, std::ios_base::binary);
    scoped_expr_caching enable_caching(false);
    deserializer d(in, optional<std::string>(file_name));
    object_readers & readers = get_object_readers();
    unsigned obj_counter = 0;
    while (true) {
        std::string k;
        d >> k;
        if (k == g_olean_end_file) {
            break;
        }

        auto it = readers.find(k);
        if (it == readers.end())
            throw exception(sstream() << "file '" << file_name << "' has been corrupted, unknown object: " << k);
        ms.emplace_back(it->second(d));

        obj_counter++;
    }
    return ms;
}

void import_module(modification_list const & modifications, std::string const & file_name, environment & env) {
    for (auto & m : modifications) {
        m->perform(env);

        if (auto dm = dynamic_cast<decl_modification const *>(m.get())) {
            env = add_decl_olean(env, dm->m_decl.get_name(), file_name);
        } else if (auto im = dynamic_cast<inductive_modification const *>(m.get())) {
            env = add_decl_olean(env, im->m_decl.get_decl().m_name, file_name);
        }
    }
}

module_loader mk_olean_loader() {
    bool check_hash = false;
    return[=] (std::string const & module_fn, module_name const & ref) {
        auto base_dir = dirname(module_fn.c_str());
        auto fn = find_file(base_dir, ref.m_relative, ref.m_name, ".olean");
        std::ifstream in(fn, std::ios_base::binary);
        auto parsed = parse_olean(in, fn, check_hash);
        auto modifs = parse_olean_modifications(parsed.second, fn);
        return std::make_shared<loaded_module>(loaded_module { fn, parsed.first, modifs, {} });
    };
}

module_loader mk_dummy_loader() {
    return[=] (std::string const &, module_name const &) -> std::shared_ptr<loaded_module const> {
        throw exception("module importing disabled");
    };
}

void initialize_module() {
    g_ext            = new module_ext_reg();
    g_object_readers = new object_readers();
    glvl_modification::init();
    decl_modification::init();
    inductive_modification::init();
    quot_modification::init();
    pos_info_mod::init();
}

void finalize_module() {
    quot_modification::finalize();
    pos_info_mod::finalize();
    inductive_modification::finalize();
    decl_modification::finalize();
    glvl_modification::finalize();
    delete g_object_readers;
    delete g_ext;
}
}
