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
#include "library/library_task_builder.h"

/*
Missing features: non monotonic modifications in .olean files

- Persistent `set_option`. We want to be able to store the option settings in .olean files.
  The main issue is conflict between imported modules. That is, each imported module wants to
  set a particular option with a different value. This can create counter-intuitive behavior.
  Consider the following scenarion

  * A.olean : sets option `foo` to true
  * B.olean : imports A.olean
  * C.olean : sets option `foo` to false
  * We create D.lean containing the following import clause:
    ```
    import B C A
    ```
    The user may expect that `foo` is set to true, since `A` is the last module to be imported,
    but this is not the case. `B` is imported first, then `A` (which sets option `foo` to true),
    then `C` (which sets option `foo` to false), the last import `A` is skipped since `A` has already
    been imported, and we get `foo` set to false.

  To address this issue we consider a persistent option import validator. The validator
  signs an error if there are two direct imports which try to set the same option to different
  values. For example, in the example above, `B` and `C` are conflicting, and an error would
  be signed when trying to import `C`. Then, users would have to resolve the conflict by
  creating an auxiliary import. For example, they could create the module `C_aux.lean` containing
  ```
  import C
  set_option persistent foo true
  ```
  and replace `import B C A` with `import B C_aux A`

- Removing attributes. The validation procedure for persistent options can be extended to attribute
  deletion. In latest version, we can only locally remove attributes. The validator for attribute deletion
  would sign an error if there are two direct imports where one adds an attribute `[foo]` to an declaration
  `bla` and the other removes it.

- Parametric attributes. This is not a missing feature, but a bug. In the current version, we have
  parametric attributes, and different modules may set the same declaration with different parameter values.
  We can fix this bug by using an attribute validator which will check parametric attributes, or
  we can allow parametric attributes to be set only once. That is, we sign an error if the user tries
  to reset them.
*/

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

static unsigned olean_hash(std::string const & data) {
    return hash(data.size(), [&] (unsigned i) { return static_cast<unsigned char>(data[i]); });
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

    if (!out1.good()) {
        throw exception(sstream() << "error during serialization of '" << mod.m_module_name << "'");
    }

    std::string r = out1.str();
    unsigned h    = olean_hash(r);

    bool uses_sorry = get(mod.m_uses_sorry);

    serializer s2(out);
    s2 << g_olean_header << get_version_string();
    s2 << h;
    s2 << uses_sorry;
    // store imported files
    s2 << static_cast<unsigned>(mod.m_imports.size());
    for (auto m : mod.m_imports)
        s2 << m;
    // store object code
    s2.write_blob(r);
}

static task<bool> has_sorry(modification_list const & mods) {
    std::vector<task<expr>> introduced_exprs;
    for (auto & mod : mods) mod->get_introduced_exprs(introduced_exprs);
    return any(introduced_exprs, [] (expr const & e) { return has_sorry(e); });
}

loaded_module export_module(environment const & env, std::string const & mod_name) {
    loaded_module out;
    out.m_module_name = mod_name;

    module_ext const & ext = get_extension(env);

    out.m_imports = ext.m_direct_imports;

    for (auto & w : ext.m_modifications)
        out.m_modifications.push_back(w);
    std::reverse(out.m_modifications.begin(), out.m_modifications.end());

    out.m_uses_sorry = has_sorry(out.m_modifications);

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

struct decl_modification : public modification {
    LEAN_MODIFICATION("decl")

    declaration m_decl;
    unsigned    m_trust_lvl = LEAN_BELIEVER_TRUST_LEVEL + 1;

    decl_modification() {}
    decl_modification(declaration const & decl, unsigned trust_lvl):
        m_decl(decl), m_trust_lvl(trust_lvl) {}

    void perform(environment & env) const override {
        auto decl = m_decl;
        /*
           The unfold_untrusted_macros is only needed when we are importing the declaration from a .olean
           file that has been created with a different (and higher) trust level. So, it may contain macros
           that will not be accepted by the current kernel, and they must be unfolded.

           In a single Lean session, the trust level is fixed, and we invoke unfold_untrusted_macros
           at frontends/lean/definition_cmds.cpp before we even create the declaration.
        */
        if (m_trust_lvl > env.trust_lvl()) {
            decl = unfold_untrusted_macros(env, decl);
        }

        // TODO(gabriel): this might be a bit more unsafe here than before
        env = import_helper::add_unchecked(env, decl);
    }

    void serialize(serializer & s) const override {
        s << m_decl << m_trust_lvl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        auto decl = read_declaration(d);
        unsigned trust_lvl; d >> trust_lvl;
        return std::make_shared<decl_modification>(std::move(decl), trust_lvl);
    }

    void get_introduced_exprs(std::vector<task<expr>> & es) const override {
        es.push_back(mk_pure_task(m_decl.get_type()));
        if (m_decl.is_theorem()) {
            es.push_back(m_decl.get_value_task());
        } else if (m_decl.is_definition()) {
            es.push_back(mk_pure_task(m_decl.get_value()));
        }
    }

    void get_task_dependencies(buffer<gtask> & deps) const override {
        if (m_decl.is_theorem())
            deps.push_back(m_decl.get_value_task());
    }
};

struct inductive_modification : public modification {
    LEAN_MODIFICATION("ind")

    inductive::certified_inductive_decl m_decl;
    unsigned m_trust_lvl = LEAN_BELIEVER_TRUST_LEVEL + 1;


    inductive_modification(inductive::certified_inductive_decl const & decl, unsigned trust_lvl) :
            m_decl(decl), m_trust_lvl(trust_lvl) {}

    void perform(environment & env) const override {
        if (m_trust_lvl > env.trust_lvl()) {
            auto d = m_decl.get_decl();
            d.m_type = unfold_untrusted_macros(env, d.m_type);
            d.m_intro_rules = map(d.m_intro_rules, [&](inductive::intro_rule const & r) {
                return unfold_untrusted_macros(env, r);
            });
            env = add_inductive(env, d, m_decl.is_trusted()).first;
        } else {
            env = m_decl.add(env);
        }
    }

    void serialize(serializer & s) const override {
        s << m_decl << m_trust_lvl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        auto decl = read_certified_inductive_decl(d);
        unsigned trust_lvl;
        d >> trust_lvl;
        return std::make_shared<inductive_modification>(std::move(decl), trust_lvl);
    }

    void get_introduced_exprs(std::vector<task<expr>> & es) const override {
        es.push_back(mk_pure_task(m_decl.get_decl().m_type));
        for (auto & i : m_decl.get_decl().m_intro_rules)
            es.push_back(mk_pure_task(i));
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

static name sorry_decl_name(name const & n) {
    if (n.is_string() && n.get_string()[0] == '_')
        return sorry_decl_name(n.get_prefix());
    return n;
}

struct sorry_warning_tag : public log_entry_cell {};
static bool is_sorry_warning_or_error(log_entry const & e) {
    return is_error_message(e) || dynamic_cast<sorry_warning_tag const *>(e.get()) != nullptr;
}

static task<bool> error_already_reported() {
    for (auto & e : logtree().get_entries())
        if (is_sorry_warning_or_error(e))
            return mk_pure_task(true);

    std::vector<task<bool>> children;
    logtree().get_used_children().for_each([&] (name const &, log_tree::node const & c) {
        children.push_back(c.has_entry(is_sorry_warning_or_error));
    });
    return any(children, [] (bool already_reported) { return already_reported; });
}

environment add(environment const & env, certified_declaration const & d) {
    environment new_env = env.add(d);
    declaration _d = d.get_declaration();
    if (!check_computable(new_env, _d.get_name()))
        new_env = mark_noncomputable(new_env, _d.get_name());
    new_env = update_module_defs(new_env, _d);
    new_env = add(new_env, std::make_shared<decl_modification>(_d, env.trust_lvl()));

    if (_d.is_theorem()) {
        // report errors from kernel type-checker
        add_library_task(task_builder<unit>([_d, env] {
            message_builder msg(env, get_global_ios(),
                logtree().get_location().m_file_name, logtree().get_location().m_range.m_begin,
                ERROR);
            try {
                _d.get_value();
            } catch (std::exception & ex) {
                msg.set_exception(ex).report();
            } catch (...) {
                msg << "unknown exception while type-checking theorem";
                msg.report();
            }
            return unit();
        }).depends_on(_d.is_theorem() ? _d.get_value_task() : nullptr));
    }

    add_library_task(map<unit>(error_already_reported(), [_d] (bool already_reported) {
        if (!already_reported && has_sorry(_d)) {
            report_message(message(logtree().get_location().m_file_name,
                                   logtree().get_location().m_range.m_begin, WARNING,
                                   (sstream() << "declaration '" << sorry_decl_name(_d.get_name()) << "' uses sorry").str()));
            logtree().add(std::make_shared<sorry_warning_tag>());
        }
        return unit {};
    }).depends_on(_d.is_theorem() ? _d.get_value_task() : nullptr));

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
    environment new_env             = r.first;
    certified_inductive_decl cidecl = r.second;
    module_ext ext = get_extension(env);
    ext.m_module_decls = cons(decl.m_name, ext.m_module_decls);
    new_env = update(new_env, ext);
    new_env = add_decl_pos_info(new_env, decl.m_name);
    return add(new_env, std::make_shared<inductive_modification>(cidecl, env.trust_lvl()));
}
} // end of namespace module

bool is_candidate_olean_file(std::string const & file_name) {
    std::ifstream in(file_name);
    deserializer d1(in, optional<std::string>(file_name));
    std::string header, version;
    d1 >> header;
    if (header != g_olean_header)
        return false;
    d1 >> version;
#ifndef LEAN_IGNORE_OLEAN_VERSION
    if (version != get_version_string())
        return false;
#endif
    return true;
}

olean_data parse_olean(std::istream & in, std::string const & file_name, bool check_hash) {
    std::vector<module_name> imports;
    bool uses_sorry;

    deserializer d1(in, optional<std::string>(file_name));
    std::string header, version;
    unsigned claimed_hash;
    d1 >> header;
    if (header != g_olean_header)
        throw exception(sstream() << "file '" << file_name << "' does not seem to be a valid object Lean file, invalid header");
    d1 >> version >> claimed_hash;
    // version has already been checked in `is_candidate_olean_file`

    d1 >> uses_sorry;

    unsigned num_imports  = d1.read_unsigned();
    for (unsigned i = 0; i < num_imports; i++) {
        module_name r;
        d1 >> r;
        imports.push_back(r);
    }

    auto code = d1.read_blob();

    if (!in.good()) {
        throw exception(sstream() << "file '" << file_name << "' has been corrupted");
    }

//    if (m_senv.env().trust_lvl() <= LEAN_BELIEVER_TRUST_LEVEL) {
    if (check_hash) {
        unsigned computed_hash = olean_hash(code);
        if (claimed_hash != computed_hash)
            throw exception(sstream() << "file '" << file_name << "' has been corrupted, checksum mismatch");
    }

    return { imports, code, uses_sorry };
}

static void import_module(environment & env, std::string const & module_file_name, module_name const & ref,
                          module_loader const & mod_ldr, buffer<import_error> & import_errors) {
    try {
        auto res = mod_ldr(module_file_name, ref);

        auto & ext0 = get_extension(env);
        if (ext0.m_imported.contains(res->m_module_name)) return;

        if (ext0.m_imported.empty() && res->m_env) {
            env = get(res->m_env);
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
    auto lm = std::make_shared<loaded_module>(lm_ref);
    std::weak_ptr<loaded_module> wlm = lm;
    lm->m_env = task_builder<environment>([env0, wlm, mk_mod_ldr] {
        if (auto lm = wlm.lock()) {
            return mk_preimported_module(env0, *lm, mk_mod_ldr());
        } else {
            throw exception("loaded_module got deallocated before preimporting");
        }
    }).build();
    return lm;
}

modification_list parse_olean_modifications(std::string const & olean_code, std::string const & file_name) {
    modification_list ms;
    std::istringstream in(olean_code, std::ios_base::binary);
    scoped_expr_caching enable_caching(false);
    deserializer d(in, optional<std::string>(file_name));
    object_readers & readers = get_object_readers();
    unsigned obj_counter = 0;
    while (true) {
        std::string k;
        unsigned offset = in.tellg();
        d >> k;
        if (k == g_olean_end_file) {
            break;
        }

        auto it = readers.find(k);
        if (it == readers.end())
            throw exception(sstream() << "file '" << file_name << "' has been corrupted at offset " << offset
                                      << ", unknown object: " << k);
        ms.emplace_back(it->second(d));

        obj_counter++;
    }
    if (!in.good()) {
        throw exception(sstream() << "file '" << file_name << "' has been corrupted");
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

module_loader mk_olean_loader(std::vector<std::string> const & path) {
    bool check_hash = false;
    return[=] (std::string const & module_fn, module_name const & ref) {
        auto base_dir = dirname(module_fn);
        auto fn = find_file(path, base_dir, ref.m_relative, ref.m_name, ".olean");
        std::ifstream in(fn, std::ios_base::binary);
        auto parsed = parse_olean(in, fn, check_hash);
        auto modifs = parse_olean_modifications(parsed.m_serialized_modifications, fn);
        return std::make_shared<loaded_module>(
                loaded_module { fn, parsed.m_imports, modifs,
                                mk_pure_task<bool>(parsed.m_uses_sorry), {} });
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
    delete g_object_readers;
    delete g_ext;
}
}
