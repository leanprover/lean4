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

namespace lean {
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
        char * header = new char[header_size];
        in.read(header, header_size);
        if (strncmp(header, g_olean_header, header_size) != 0) {
            return set_io_error(w, (sstream() << "failed to read file '" << olean_fn << "', invalid header").str());
        }
        delete[] header;
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

static search_path * g_search_path = nullptr;
void set_search_path(search_path const & p) {
    *g_search_path = p;
}

extern "C" object * lean_find_olean(object * mod_name, object * w) {
    name mod(mod_name);
    try {
        std::string fn = find_file(*g_search_path, mod, {".olean"});
        return set_io_result(w, mk_string(fn));
    } catch (exception & ex) {
        return set_io_error(w, ex.what());
    }
}

// =======================================
// Legacy support for Lean3 modification objects

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

typedef std::unordered_map<std::string, module_modification_reader> object_readers;
static object_readers * g_object_readers = nullptr;
static object_readers & get_object_readers() { return *g_object_readers; }

void register_module_object_reader(std::string const & k, module_modification_reader && r) {
    object_readers & readers = get_object_readers();
    lean_assert(readers.find(k) == readers.end());
    readers[k] = r;
}

static char const * g_olean_end_file = "EndFile";

extern "C" object * lean_serialize_modifications(object * mod_list, object * w) {
    object_ref mod_list_ref(mod_list);
    try {
        std::ostringstream out(std::ios_base::binary);
        serializer s(out);
        buffer<object *> mod_buffer;
        while (!is_scalar(mod_list)) {
            mod_buffer.push_back(cnstr_get(mod_list, 0));
            mod_list = cnstr_get(mod_list, 1);
        }
        size_t i = mod_buffer.size();
        while (i > 0) {
            --i;
            modification & mod = to_modification(mod_buffer[i]);
            s << std::string(mod.get_key());
            mod.serialize(s);
        }
        s << g_olean_end_file;
        std::string bytes = out.str();

        object * r = alloc_sarray(1, bytes.size(), bytes.size());
        memcpy(sarray_cptr<uint8>(r), bytes.data(), bytes.size());

        return set_io_result(w, r);
    } catch (exception & ex) {
        return set_io_error(w, ex.what());
    }
}

extern "C" object * lean_perform_serialized_modifications(object * env0, object * bytes, object * w) {
    environment env(env0);
    std::string code(sarray_cptr<char>(bytes), sarray_size(bytes));
    dec_ref(bytes);
    try {
        std::istringstream in(code, std::ios_base::binary);
        deserializer d(in);
        object_readers & readers = get_object_readers();
        while (true) {
            std::string k;
            unsigned offset = in.tellg();
            d >> k;
            if (k == g_olean_end_file) {
                break;
            }
            auto it = readers.find(k);
            if (it == readers.end())
                throw exception(sstream() << "olean file has been corrupted at offset " << offset
                                << ", unknown object: " << k);
            modification * mod = it->second(d);
            mod->perform(env);
            delete mod;
        }
        if (!in.good()) {
            throw exception(sstream() << "olean file has been corrupted");
        }
        return set_io_result(w, env.steal());
    } catch (exception & ex) {
        return set_io_error(w, ex.what());
    }
}

// =======================================

/*
@[export lean.write_module_core]
def writeModule (env : Environment) (fname : String) : IO Unit := */
object * write_module_core(object * env, object * fname, object * w);

void write_module(environment const & env, std::string const & olean_fn) {
    object * r = write_module_core(env.to_obj_arg(), mk_string(olean_fn), io_mk_world());
    if (io_result_is_error(r)) {
        dec_ref(r);
        throw exception(sstream() << "failed to write module '" << olean_fn << "'");
    } else {
        dec_ref(r);
    }
}

/*
@[export lean.import_modules_core]
def importModules (modNames : List Name) (trustLevel : UInt32 := 0) : IO Environment :=
*/
object * import_modules_core(object * mod_names, uint32 trust_level, object * w);

environment import_modules(unsigned trust_lvl, std::vector<module_name> const & imports) {
    names mods(imports.begin(), imports.end());
    object * r = import_modules_core(mods.steal(), trust_lvl, io_mk_world());
    if (io_result_is_error(r)) {
        dec_ref(r);
        io_result_show_error(r); // TODO(Leo): move to exception
        throw exception("failed to import modules");
    } else {
        environment env(io_result_get_value(r), true);
        dec_ref(r);
        return env;
    }
}

object * environment_add_modification_core(object * env, object * mod);

namespace module {
environment add(environment const & env, modification* modf) {
    return environment(environment_add_modification_core(env.to_obj_arg(), to_object(modf)));
}

environment add_and_perform(environment const & env, modification * modf) {
    auto new_env = env;
    modf->perform(new_env);
    return add(new_env, modf);
}

environment add(environment const & env, declaration const & d, bool check) {
    return env.add(d, check);
}
} // end of namespace module

void initialize_module() {
    g_modification_class = register_external_object_class(modification_finalizer, modification_foreach);
    g_object_readers = new object_readers();
    g_search_path    = new search_path();
}

void finalize_module() {
    delete g_object_readers;
    delete g_search_path;
}
}
