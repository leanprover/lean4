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
#include "kernel/type_checker.h"
#include "kernel/quotient/quotient.h"
#include "kernel/hits/hits.h"
#include "library/module.h"
#include "library/noncomputable.h"
#include "library/sorry.h"
#include "library/kernel_serializer.h"
#include "library/unfold_macros.h"
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
    list<module_name> m_direct_imports;
    list<writer>      m_writers;
    list<name>        m_module_univs;
    list<name>        m_module_decls;
    name_set          m_module_defs;
    // auxiliary information for detecting whether
    // directly imported files have changed
    list<time_t>      m_direct_imports_mod_time;
    std::string       m_base;
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

list<module_name> get_direct_imports(environment const & env) {
    return get_extension(env).m_direct_imports;
}

list<name> const & get_curr_module_decl_names(environment const & env) {
    return get_extension(env).m_module_decls;
}

list<name> const & get_curr_module_univ_names(environment const & env) {
    return get_extension(env).m_module_univs;
}

list<module_name> const & get_curr_module_imports(environment const & env) {
    return get_extension(env).m_direct_imports;
}

bool direct_imports_have_changed(environment const & env) {
    module_ext const & ext   = get_extension(env);
    std::string const & base = ext.m_base;
    list<module_name> mods   = ext.m_direct_imports;
    list<time_t>      mtimes = ext.m_direct_imports_mod_time;
    lean_assert(length(mods) == length(mtimes));
    while (mods && mtimes) {
        module_name const & mname = head(mods);
        std::string fname;
        try {
            fname = find_file(base, mname.get_k(), mname.get_name(), {".olean"});
        } catch (exception &) {
            return true; // direct import doesn't even exist anymore
        }
        struct stat st;
        if (stat(fname.c_str(), &st) != 0)
            return true; // failed to read stats
        if (st.st_mtime != head(mtimes))
            return true; // mod time has changed
        mods   = tail(mods);
        mtimes = tail(mtimes);
    }
    return false;
}

static char const * g_olean_end_file = "EndFile";
static char const * g_olean_header   = "oleanfile";

serializer & operator<<(serializer & s, module_name const & n) {
    if (n.is_relative())
        s << true << *n.get_k() << n.get_name();
    else
        s << false << n.get_name();
    return s;
}

module_name read_module_name(deserializer & d) {
    if (d.read_bool()) {
        unsigned k; name n;
        d >> k >> n;
        return module_name(k, n);
    } else {
        name n;
        d >> n;
        return module_name(n);
    }
}

void export_module(std::ostream & out, environment const & env) {
    module_ext const & ext = get_extension(env);
    buffer<module_name> imports;
    buffer<writer const *> writers;
    to_buffer(ext.m_direct_imports, imports);
    std::reverse(imports.begin(), imports.end());
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
static std::string * g_hits      = nullptr;

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

static environment export_decl(environment const & env, declaration const & d) {
    name n = d.get_name();
    return add(env, *g_decl_key, [=](environment const & env, serializer & s) {
            s << env.get(n);
        });
}

environment add(environment const & env, certified_declaration const & d) {
    environment new_env = env.add(d);
    declaration _d = d.get_declaration();
    if (!check_computable(new_env, _d.get_name()))
        new_env = mark_noncomputable(new_env, _d.get_name());
    return export_decl(update_module_defs(new_env, _d), _d);
}

environment add(environment const & env, declaration const & d) {
    environment new_env = env.add(d);
    if (!check_computable(new_env, d.get_name()))
        new_env = mark_noncomputable(new_env, d.get_name());
    return export_decl(update_module_defs(new_env, d), d);
}

bool is_definition(environment const & env, name const & n) {
    module_ext const & ext = get_extension(env);
    return ext.m_module_defs.contains(n);
}

environment declare_quotient(environment const & env) {
    environment new_env = ::lean::declare_quotient(env);
    return add(new_env, *g_quotient, [=](environment const &, serializer &) {});
}

static void quotient_reader(deserializer &, shared_environment & senv,
                            std::function<void(asynch_update_fn const &)>  &,
                            std::function<void(delayed_update_fn const &)> &) {
    senv.update([&](environment const & env) {
            return ::lean::declare_quotient(env);
        });
}

environment declare_hits(environment const & env) {
    environment new_env = ::lean::declare_hits(env);
    return add(new_env, *g_hits, [=](environment const &, serializer &) {});
}

static void hits_reader(deserializer &, shared_environment & senv,
                        std::function<void(asynch_update_fn const &)>  &,
                        std::function<void(delayed_update_fn const &)> &) {
    senv.update([&](environment const & env) {
            return ::lean::declare_hits(env);
        });
}

environment add_inductive(environment                  env,
                          level_param_names const &    level_params,
                          unsigned                     num_params,
                          list<inductive::inductive_decl> const & decls) {
    environment new_env = inductive::add_inductive(env, level_params, num_params, decls);
    module_ext ext = get_extension(env);
    ext.m_module_decls = cons(inductive::inductive_decl_name(head(decls)), ext.m_module_decls);
    new_env = update(new_env, ext);
    return add(new_env, *g_inductive, [=](environment const &, serializer & s) {
            s << inductive_decls(level_params, num_params, decls);
        });
}

static void inductive_reader(deserializer & d, shared_environment & senv,
                             std::function<void(asynch_update_fn const &)>  &,
                             std::function<void(delayed_update_fn const &)> &) {
    inductive_decls ds = read_inductive_decls(d);
    senv.update([&](environment const & env) {
            return inductive::add_inductive(env, std::get<0>(ds), std::get<1>(ds), std::get<2>(ds));
        });
}

environment add_inductive(environment const & env, name const & ind_name, level_param_names const & level_params,
                          unsigned num_params, expr const & type, list<inductive::intro_rule> const & intro_rules) {
    return add_inductive(env, level_params, num_params, to_list(inductive::inductive_decl(ind_name, type, intro_rules)));
}
} // end of namespace module

struct import_modules_fn {
    typedef std::tuple<unsigned, unsigned, delayed_update_fn> delayed_update;
    shared_environment             m_senv;
    unsigned                       m_num_threads;
    bool                           m_keep_proofs;
    io_state                       m_ios;
    mutex                          m_asynch_mutex;
    condition_variable             m_asynch_cv;
    std::vector<asynch_update_fn>  m_asynch_tasks;
    mutex                          m_delayed_mutex;
    std::vector<delayed_update>    m_delayed_tasks;
    atomic<unsigned>               m_next_module_idx;
    atomic<unsigned>               m_import_counter; // number of modules to be processed
    atomic<bool>                   m_all_modules_imported;

    struct module_info {
        std::string                               m_fname;
        atomic<unsigned>                          m_counter; // number of dependencies to be processed
        unsigned                                  m_module_idx;
        std::vector<std::shared_ptr<module_info>> m_dependents;
        std::vector<char>                         m_obj_code;
        module_info():m_counter(0), m_module_idx(0) {}
    };
    typedef std::shared_ptr<module_info> module_info_ptr;
    name_map<module_info_ptr> m_module_info;
    name_set                  m_visited; // contains visited files in the current call
    name_set                  m_imported; // contains all imported files, even ones from previous calls

    import_modules_fn(environment const & env, unsigned num_threads, bool keep_proofs, io_state const & ios):
        m_senv(env), m_num_threads(num_threads), m_keep_proofs(keep_proofs), m_ios(ios),
        m_next_module_idx(1), m_import_counter(0), m_all_modules_imported(false) {
        module_ext const & ext = get_extension(env);
        m_imported = ext.m_imported;
        if (m_num_threads == 0)
            m_num_threads = 1;
#if !defined(LEAN_MULTI_THREAD)
        if (m_num_threads > 1)
            m_num_threads = 1;
#endif
        if (env.trust_lvl() > LEAN_BELIEVER_TRUST_LEVEL) {
            // it doesn't payoff to use multiple threads if we will not type check anything
            m_num_threads = 1;
        }
    }

    module_info_ptr load_module_file(std::string const & base, module_name const & mname) {
        std::string fname = find_file(base, mname.get_k(), mname.get_name(), {".olean"});
        auto it    = m_module_info.find(fname);
        if (it)
            return *it;
        if (m_imported.contains(fname)) // file was imported in previous call
            return nullptr;
        if (m_visited.contains(fname))
            throw exception(sstream() << "circular dependency detected at '" << fname << "'");
        m_visited.insert(fname);
        m_imported.insert(fname);
        std::ifstream in(fname, std::ifstream::binary);
        if (!in.good())
            throw exception(sstream() << "failed to open file '" << fname << "'");
        try {
            deserializer d1(in);
            std::string header;
            d1 >> header;
            if (header != g_olean_header)
                throw exception(sstream() << "file '" << fname << "' does not seem to be a valid object Lean file, invalid header");
            unsigned major, minor, patch, claimed_hash;
            d1 >> major >> minor >> patch >> claimed_hash;
            // Enforce version?

            unsigned num_imports  = d1.read_unsigned();
            buffer<module_name> imports;
            for (unsigned i = 0; i < num_imports; i++)
                imports.push_back(read_module_name(d1));

            unsigned code_size    = d1.read_unsigned();
            std::vector<char> code(code_size);
            for (unsigned i = 0; i < code_size; i++)
                code[i] = d1.read_char();

            unsigned computed_hash = hash(code_size, [&](unsigned i) { return code[i]; });
            if (claimed_hash != computed_hash)
                throw exception(sstream() << "file '" << fname << "' has been corrupted, checksum mismatch");

            module_info_ptr r = std::make_shared<module_info>();
            r->m_fname        = fname;
            r->m_counter      = 0;
            r->m_module_idx   = 0;
            m_import_counter++;
            std::string new_base = dirname(fname.c_str());
            std::swap(r->m_obj_code, code);
            bool has_dependency = false;
            for (auto i : imports) {
                if (auto d = load_module_file(new_base, i)) {
                    r->m_counter++;
                    d->m_dependents.push_back(r);
                    has_dependency = true;
                }
            }
            m_module_info.insert(fname, r);
            r->m_module_idx = m_next_module_idx++;

            if (!has_dependency)
                add_import_module_task(r);
            return r;
        } catch (corrupted_stream_exception&) {
            throw corrupted_file_exception(fname);
        }
    }

    void add_asynch_task(asynch_update_fn const & f) {
        {
            lock_guard<mutex> l(m_asynch_mutex);
            m_asynch_tasks.push_back(f);
        }
        m_asynch_cv.notify_one();
    }

    void add_import_module_task(module_info_ptr const & r) {
        add_asynch_task([=](shared_environment &) { import_module(r); });
    }

    declaration theorem2axiom(declaration const & decl) {
        lean_assert(decl.is_theorem());
        return mk_axiom(decl.get_name(), decl.get_univ_params(), decl.get_type());
    }

    void import_decl(deserializer & d) {
        declaration decl = read_declaration(d);
        environment env  = m_senv.env();
        decl = unfold_untrusted_macros(env, decl);
        if (decl.get_name() == get_sorry_name() && has_sorry(env))
            return;
        if (env.trust_lvl() > LEAN_BELIEVER_TRUST_LEVEL) {
            if (!m_keep_proofs && decl.is_theorem())
                m_senv.add(theorem2axiom(decl));
            else
                m_senv.add(decl);
        } else if (LEAN_ASYNCH_IMPORT_THEOREM && decl.is_theorem()) {
            // First, we add the theorem as an axiom, and create an asychronous task for
            // checking the actual theorem, and replace the axiom with the actual theorem.
            certified_declaration tmp_c = check(env, theorem2axiom(decl));
            m_senv.add(tmp_c);
            add_asynch_task([=](shared_environment & m_senv) {
                    certified_declaration c = check(env, decl);
                    if (m_keep_proofs)
                        m_senv.replace(c);
                });
        } else {
            if (!m_keep_proofs && decl.is_theorem()) {
                // check theorem, but add an axiom
                check(env, decl);
                m_senv.add(check(env, theorem2axiom(decl)));
            } else {
                certified_declaration c = check(env, decl);
                m_senv.add(c);
            }
        }
    }

    void import_universe(deserializer & d) {
        name const l = read_name(d);
        m_senv.update([=](environment const & env) { return env.add_universe(l); });
    }

    void import_module(module_info_ptr const & r) {
        std::string s(r->m_obj_code.data(), r->m_obj_code.size());
        std::istringstream in(s, std::ios_base::binary);
        deserializer d(in);
        unsigned obj_counter = 0;
        std::function<void(asynch_update_fn const &)> add_asynch_update([&](asynch_update_fn const & f) {
                add_asynch_task(f);
            });
        std::function<void(delayed_update_fn const &)> add_delayed_update([&](delayed_update_fn const & f) {
                lock_guard<mutex> lk(m_delayed_mutex);
                m_delayed_tasks.push_back(std::make_tuple(r->m_module_idx, obj_counter, f));
            });
        while (true) {
            check_interrupted();
            std::string k;
            d >> k;
            if (k == g_olean_end_file) {
                break;
            } else if (k == *g_decl_key) {
                import_decl(d);
            } else if (k == *g_glvl_key) {
                import_universe(d);
            } else {
                object_readers & readers = get_object_readers();
                auto it = readers.find(k);
                if (it == readers.end())
                    throw exception(sstream() << "file '" << r->m_fname << "' has been corrupted, unknown object");
                it->second(d, m_senv, add_asynch_update, add_delayed_update);
            }
            obj_counter++;
        }
        if (atomic_fetch_sub_explicit(&m_import_counter, 1u, memory_order_release) == 1u) {
            atomic_thread_fence(memory_order_acquire);
            m_all_modules_imported = true;
            m_asynch_cv.notify_all();
        }
        // Module was successfully imported, we should notify descendents.
        for (module_info_ptr const & d : r->m_dependents) {
            if (atomic_fetch_sub_explicit(&(d->m_counter), 1u, memory_order_release) == 1u) {
                atomic_thread_fence(memory_order_acquire);
                // all d's dependencies have been processed
                add_import_module_task(d);
            }
        }
    }

    optional<asynch_update_fn> next_task() {
        while (true) {
            check_interrupted();
            unique_lock<mutex> lk(m_asynch_mutex);
            if (!m_asynch_tasks.empty()) {
                asynch_update_fn r = m_asynch_tasks.back();
                m_asynch_tasks.pop_back();
                return optional<asynch_update_fn>(r);
            } else if (m_all_modules_imported) {
                return optional<asynch_update_fn>();
            } else {
                m_asynch_cv.wait(lk);
            }
        }
    }

    void process_asynch_tasks() {
        if (m_asynch_tasks.empty())
            return;
        std::vector<std::unique_ptr<interruptible_thread>> extra_threads;
        std::vector<std::unique_ptr<throwable>> thread_exceptions(m_num_threads - 1);
        atomic<int> failed_thread_idx(-1); // >= 0 if error
        for (unsigned i = 0; i < m_num_threads - 1; i++) {
            extra_threads.push_back(std::unique_ptr<interruptible_thread>(new interruptible_thread([=, &thread_exceptions, &failed_thread_idx]() {
                            try {
                                while (auto t = next_task()) {
                                    (*t)(m_senv);
                                }
                                m_asynch_cv.notify_all();
                            } catch (throwable & ex) {
                                thread_exceptions[i].reset(ex.clone());
                                failed_thread_idx = i;
                            } catch (...) {
                                thread_exceptions[i].reset(new exception("module import thread failed for unknown reasons"));
                                failed_thread_idx = i;
                            }
                        })));
        }
        try {
            while (auto t = next_task()) {
                (*t)(m_senv);
                int idx = failed_thread_idx;
                if (idx >= 0)
                    thread_exceptions[idx]->rethrow();
            }
            m_asynch_cv.notify_all();
            for (auto & th : extra_threads)
                th->join();
        } catch (...) {
            for (auto & th : extra_threads)
                th->request_interrupt();
            for (auto & th : extra_threads)
                th->join();
            throw;
        }
    }

    environment process_delayed_tasks() {
        environment env = m_senv.env();
        // Sort delayed tasks using lexicographical order on (module-idx, obj-idx).
        // obj-idx is the object's position in the module.
        std::sort(m_delayed_tasks.begin(), m_delayed_tasks.end(),
                  [](delayed_update const & u1, delayed_update const & u2) {
                      if (std::get<0>(u1) != std::get<0>(u2))
                          return std::get<0>(u1) < std::get<0>(u2);
                      else
                          return std::get<1>(u1) < std::get<1>(u2);
                  });
        for (auto const & d : m_delayed_tasks) {
            env = std::get<2>(d)(env, m_ios);
        }
        return env;
    }

    void store_direct_imports(std::string const & base, unsigned num_modules, module_name const * modules) {
        m_senv.update([&](environment const & env) -> environment {
                module_ext ext = get_extension(env);
                ext.m_base     = base;
                for (unsigned i = 0; i < num_modules; i++) {
                    module_name const & mname = modules[i];
                    std::string fname = find_file(base, mname.get_k(), mname.get_name(), {".olean"});
                    if (!m_imported.contains(fname)) {
                        ext.m_direct_imports = cons(mname, ext.m_direct_imports);
                        struct stat st;
                        if (stat(fname.c_str(), &st) != 0)
                            throw exception(sstream() << "failed to access stats of file '" << fname << "'");
                        ext.m_direct_imports_mod_time = cons(st.st_mtime, ext.m_direct_imports_mod_time);
                    }
                }
                return update(env, ext);
            });
    }

    environment operator()(std::string const & base, unsigned num_modules, module_name const * modules) {
        store_direct_imports(base, num_modules, modules);
        for (unsigned i = 0; i < num_modules; i++)
            load_module_file(base, modules[i]);
        process_asynch_tasks();
        environment env = process_delayed_tasks();
        module_ext ext = get_extension(env);
        ext.m_imported = m_imported;
        return update(env, ext);
    }
};

environment import_modules(environment const & env, std::string const & base, unsigned num_modules, module_name const * modules,
                           unsigned num_threads, bool keep_proofs, io_state const & ios) {
    return import_modules_fn(env, num_threads, keep_proofs, ios)(base, num_modules, modules);
}

environment import_module(environment const & env, std::string const & base, module_name const & module,
                          unsigned num_threads, bool keep_proofs, io_state const & ios) {
    return import_modules(env, base, 1, &module, num_threads, keep_proofs, ios);
}

void initialize_module() {
    g_ext            = new module_ext_reg();
    g_object_readers = new object_readers();
    g_glvl_key       = new std::string("glvl");
    g_decl_key       = new std::string("decl");
    g_inductive      = new std::string("ind");
    g_quotient       = new std::string("quot");
    g_hits           = new std::string("hits");
    register_module_object_reader(*g_inductive, module::inductive_reader);
    register_module_object_reader(*g_quotient, module::quotient_reader);
    register_module_object_reader(*g_hits, module::hits_reader);
}

void finalize_module() {
    delete g_inductive;
    delete g_quotient;
    delete g_hits;
    delete g_decl_key;
    delete g_glvl_key;
    delete g_object_readers;
    delete g_ext;
}
}
