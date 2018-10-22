/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Gabriel Ebner, Sebastian Ullrich
*/
#include <unordered_map>
#include <vector>
#include <utility>
#include <string>
#include <sstream>
#include <fstream>
#include <algorithm>
#include <sys/stat.h>
#include "runtime/thread.h"
#include "runtime/interrupt.h"
#include "runtime/sstream.h"
#include "util/hash.h"
#include "util/lean_path.h"
#include "util/buffer.h"
#include "util/name_map.h"
#include "util/file_lock.h"
#include "library/module.h"
#include "library/constants.h"
#include "library/module_mgr.h"
#include "library/time_task.h"

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
    name_set          m_imported;
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

static char const * g_olean_end_file = "EndFile";
static char const * g_olean_header   = "oleanfile";

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
        throw exception(sstream() << "error during serialization of '" << mod.m_name << "'");
    }

    std::string r = out1.str();
    unsigned h    = olean_hash(r);

    serializer s2(out);
    s2 << g_olean_header << get_version_string();
    s2 << h;
    // store imported files
    s2 << static_cast<unsigned>(mod.m_imports.size());
    for (auto m : mod.m_imports)
        s2 << m;
    // store object code
    s2.write_blob(r);
}

loaded_module export_module(environment const & env, module_name const & mod) {
    loaded_module out;
    out.m_name = mod;

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

struct decl_modification : public modification {
    LEAN_MODIFICATION("decl")
    declaration m_decl;

    decl_modification() {}
    decl_modification(declaration const & decl):
        m_decl(decl) {}

    void perform(environment & env) const override {
        env = env.add(m_decl, false);
    }

    void serialize(serializer & s) const override {
        s << m_decl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        auto decl = read_declaration(d);
        return std::make_shared<decl_modification>(std::move(decl));
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

environment add(environment const & env, declaration const & d, bool check) {
    environment new_env = env.add(d, check);
    return add(new_env, std::make_shared<decl_modification>(d));
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
    time_task t(".olean deserialization",
                message_builder(environment(), get_global_ios(), file_name, pos_info(), message_severity::INFORMATION));

    deserializer d1(in, optional<std::string>(file_name));
    std::string header, version;
    unsigned claimed_hash;
    d1 >> header;
    if (header != g_olean_header)
        throw exception(sstream() << "file '" << file_name << "' does not seem to be a valid object Lean file, invalid header");
    d1 >> version >> claimed_hash;
    // version has already been checked in `is_candidate_olean_file`

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

    if (check_hash) {
        unsigned computed_hash = olean_hash(code);
        if (claimed_hash != computed_hash)
            throw exception(sstream() << "file '" << file_name << "' has been corrupted, checksum mismatch");
    }

    return { imports, code };
}

static void import_module(modification_list const & modifications, environment & env) {
    for (auto & m : modifications) {
        m->perform(env);
    }
}

static void import_module_rec(environment & env, module_name const & mod,
                              module_loader const & mod_ldr, buffer<import_error> & import_errors) {
    try {
        auto res = mod_ldr(mod);

        auto & ext0 = get_extension(env);
        if (ext0.m_imported.contains(name(res->m_name))) return;

        for (auto &dep : res->m_imports) {
            import_module_rec(env, dep, mod_ldr, import_errors);
        }
        import_module(res->m_modifications, env);

        auto ext = get_extension(env);
        ext.m_imported.insert(name(res->m_name));
        env = update(env, ext);
    } catch (throwable) {
        import_errors.push_back({mod, std::current_exception()});
    }
}

environment import_modules(environment const & env0, std::vector<module_name> const & imports, module_loader const & mod_ldr,
                           buffer<import_error> & import_errors) {
    environment env = env0;

    for (auto & import : imports)
        import_module_rec(env, import, mod_ldr, import_errors);

    module_ext ext = get_extension(env);
    ext.m_direct_imports = imports;
    return update(env, ext);
}

environment import_modules(environment const & env0, std::vector<module_name> const & imports, module_loader const & mod_ldr) {
    buffer<import_error> import_errors;
    auto env = import_modules(env0, imports, mod_ldr, import_errors);
    if (!import_errors.empty()) std::rethrow_exception(import_errors.back().m_ex);
    return env;
}

modification_list parse_olean_modifications(std::string const & olean_code, std::string const & file_name) {
    modification_list ms;
    std::istringstream in(olean_code, std::ios_base::binary);
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

void initialize_module() {
    g_ext            = new module_ext_reg();
    g_object_readers = new object_readers();
    decl_modification::init();
}

void finalize_module() {
    decl_modification::finalize();
    delete g_object_readers;
    delete g_ext;
}
}
