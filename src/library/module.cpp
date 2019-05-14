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
#include "runtime/hash.h"
#include "runtime/io.h"
#include "runtime/compact.h"
#include "util/lean_path.h"
#include "util/buffer.h"
#include "util/name_map.h"
#include "util/file_lock.h"
#include "library/module.h"
#include "library/constants.h"
#include "library/time_task.h"
#include "library/util.h"

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
static char const * g_olean_end_file = "EndFile";
static char const * g_olean_header   = "oleanfile";

extern "C" object * lean_save_module_data(object * fname, object * mdata, object * w) {
    std::string olean_fn(string_cstr(fname));
    object_ref mdata_ref(mdata);
    try {
        exclusive_file_lock output_lock(olean_fn);
        std::ofstream out(olean_fn, std::ios_base::binary);
        if (out.fail()) {
            return set_io_error(w, (sstream() << "failed to create file '" << olean_fn << "'").str());
        }
        object_compactor compactor;
        compactor(mdata_ref.raw());
        out.write(g_olean_header, strlen(g_olean_header));
        out.write(static_cast<char const *>(compactor.data()), compactor.size());
        out.close();
        return set_io_result(w, box(0));
    } catch (exception & ex) {
        return set_io_error(w, (sstream() << "failed to write '" << olean_fn << "': " << ex.what()).str());
    }
}

extern "C" object * lean_read_module_data(object * fname, object * w) {
    std::string olean_fn(string_cstr(fname));
    try {
        shared_file_lock olean_lock(olean_fn);
        std::ifstream in(olean_fn, std::ios_base::binary);
        if (in.fail()) {
            return set_io_error(w, (sstream() << "failed to open file '" << olean_fn << "'").str());
        }
        /* Get file size */
        in.seekg(0, in.end);
        size_t size = in.tellg();
        in.seekg(0);
        size_t header_size = strlen(g_olean_header);
        if (size < header_size) {
            return set_io_error(w, (sstream() << "failed to read file '" << olean_fn << "', invalid header").str());
        }
        char header[header_size];
        in.read(header, header_size);
        if (strncmp(header, g_olean_header, header_size) != 0) {
            return set_io_error(w, (sstream() << "failed to read file '" << olean_fn << "', invalid header").str());
        }
        char * buffer = new char[size - header_size];
        in.read(buffer, size - header_size);
        if (!in) {
            return set_io_error(w, (sstream() << "failed to read file '" << olean_fn << "'").str());
        }
        in.close();
        /* We don't free compacted_region objects */
        compacted_region * region = new compacted_region(size - header_size, buffer);
        object * mod = region->read();
        return set_io_result(w, mod);
    } catch (exception & ex) {
        return set_io_error(w, (sstream() << "failed to read '" << olean_fn << "': " << ex.what()).str());
    }
}

static void modification_finalizer(void * ext) {
    delete static_cast<modification*>(ext);
}

static void modification_foreach(void * /* mod */, b_obj_arg /* fn */) {
}

static external_object_class * g_modification_class = nullptr;

static modification & to_modification(b_obj_arg o) {
    lean_assert(external_class(o) == g_modification_class);
    return *static_cast<modification *>(external_data(o));
}

static obj_res to_object(modification * ext) {
    return alloc_external(g_modification_class, ext);
}

extern "C" object * lean_serialize_modifications(object *) {
    // TODO(Leo)
    lean_unreachable();
}

struct module_ext : public environment_extension {
    std::vector<module_name> m_direct_imports;
};

struct module_ext_reg {
    unsigned m_ext_id;
    module_ext_reg() { m_ext_id = environment::register_extension(new module_ext()); }
};

static module_ext_reg * g_ext = nullptr;

static module_ext const & get_extension(environment const & env) {
    return static_cast<module_ext const &>(env.get_extension(g_ext->m_ext_id));
}

static environment update(environment const & env, module_ext const & ext) {
    return env.update(g_ext->m_ext_id, new module_ext(ext));
}

static unsigned olean_hash(std::string const & data) {
    return hash(data.size(), [&] (unsigned i) { return static_cast<unsigned char>(data[i]); });
}

object * environment_add_modification_core(object * env, object * mod);
object * environment_get_modifications_core(object * env);

void write_module(environment const & env, module_name const & mod, std::string const & olean_fn) {
    exclusive_file_lock output_lock(olean_fn);
    std::ofstream out(olean_fn, std::ios_base::binary);
    module_ext const & ext = get_extension(env);

    buffer<modification*> mods;
    object * mod_list = environment_get_modifications_core(env.get_obj_arg());
    while (!is_scalar(mod_list)) {
        object * mod = cnstr_get(mod_list, 0);
        mods.push_back(&to_modification(mod));
        mod_list = cnstr_get(mod_list, 1);
    }

    std::ostringstream out1(std::ios_base::binary);
    serializer s1(out1);

    // store objects
    for (int i = mods.size() - 1; i >= 0; i--) {
        s1 << std::string(mods[i]->get_key());
        mods[i]->serialize(s1);
    }

    dec(mod_list);

    s1 << g_olean_end_file;

    if (!out1.good()) {
        throw exception(sstream() << "error during serialization of '" << mod << "'");
    }

    std::string r = out1.str();
    unsigned h    = olean_hash(r);

    serializer s2(out);
    s2 << g_olean_header << get_version_string();
    s2 << h;
    // store imported files
    s2 << static_cast<unsigned>(ext.m_direct_imports.size());
    for (auto m : ext.m_direct_imports)
        s2 << m;
    // store object code
    s2.write_blob(r);

    out.close();
    if (!out) throw exception("failed to write olean file");
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

    static modification* deserialize(deserializer & d) {
        auto decl = read_declaration(d);
        return new decl_modification(std::move(decl));
    }
};

namespace module {
environment add(environment const & env, modification* modf) {
    return environment(environment_add_modification_core(env.get_obj_arg(), to_object(modf)));
}

environment add_and_perform(environment const & env, modification * modf) {
    auto new_env = env;
    modf->perform(new_env);
    return add(new_env, modf);
}

environment add(environment const & env, declaration const & d, bool check) {
    environment new_env = env.add(d, check);
    return add(new_env, new decl_modification(d));
}
} // end of namespace module

struct olean_data {
    std::vector<module_name> m_imports;
    std::string m_serialized_modifications;
};
static olean_data parse_olean(std::istream & in, std::string const & file_name, bool check_hash) {
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
#ifndef LEAN_IGNORE_OLEAN_VERSION
    if (version != get_version_string()) {
        throw exception(sstream() << "error importing file '" << file_name << "', it is from a different Lean version");
    }
#endif

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

static void import_module_rec(environment & env, module_name const & mod,
                              search_path const & path, buffer<import_error> & import_errors,
                              name_set & already_imported) {
    if (already_imported.contains(mod))
        return;
    try {
        auto olean_fn = find_file(path, mod, {".olean"});
        olean_data parsed_olean;
        {
            shared_file_lock olean_lock(olean_fn);
            std::ifstream in2(olean_fn, std::ios_base::binary);
            bool check_hash = false;
            parsed_olean = parse_olean(in2, olean_fn, check_hash);
        }

        for (auto & dep : parsed_olean.m_imports) {
            import_module_rec(env, dep, path, import_errors, already_imported);
        }
        import_module(parse_olean_modifications(parsed_olean.m_serialized_modifications, olean_fn), env);

        already_imported.insert(mod);
    } catch (throwable) {
        import_errors.push_back({mod, std::current_exception()});
    }
}

environment import_modules(environment const & env0, std::vector<module_name> const & imports, search_path const & path,
                           buffer<import_error> & import_errors) {
    name_set already_imported;
    environment env = env0;

    for (auto & import : imports)
        import_module_rec(env, import, path, import_errors, already_imported);

    module_ext ext = get_extension(env);
    ext.m_direct_imports = imports;
    return update(env, ext);
}

environment import_modules(environment const & env0, std::vector<module_name> const & imports, search_path const & path) {
    buffer<import_error> import_errors;
    auto env = import_modules(env0, imports, path, import_errors);
    if (!import_errors.empty()) std::rethrow_exception(import_errors.back().m_ex);
    return env;
}

void initialize_module() {
    g_modification_class = register_external_object_class(modification_finalizer, modification_foreach);
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
