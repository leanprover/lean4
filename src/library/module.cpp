/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
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
#include "util/hash.h"
#include "util/thread.h"
#include "util/lean_path.h"
#include "util/sstream.h"
#include "util/buffer.h"
#include "util/interrupt.h"
#include "util/name_map.h"
#include "kernel/type_checker.h"
#include "library/module.h"
#include "library/kernel_serializer.h"
#include "version.h"

#ifndef LEAN_ASYNCH_IMPORT_THEOREM
#define LEAN_ASYNCH_IMPORT_THEOREM false
#endif

namespace lean {
typedef std::pair<std::string, std::function<void(serializer &)>> writer;

struct module_ext : public environment_extension {
    list<name>   m_direct_imports;
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

static char const * g_olean_end_file = "EndFile";
static char const * g_olean_header   = "oleanfile";

void export_module(std::ostream & out, environment const & env) {
    module_ext const & ext = get_extension(env);
    buffer<name> imports;
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
        p->second(s1);
    }
    s1 << g_olean_end_file;

    serializer s2(out);
    std::string r = out1.str();
    unsigned h    = hash(r.size(), [&](unsigned i) { return r[i]; });
    s2 << g_olean_header << LEAN_VERSION_MAJOR << LEAN_VERSION_MINOR;
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

static std::string g_glvl_key("glvl");
static std::string g_decl_key("decl");

namespace module {
environment add(environment const & env, std::string const & k, std::function<void(serializer &)> const & wr) {
    module_ext ext = get_extension(env);
    ext.m_writers  = list<writer>(writer(k, wr), ext.m_writers);
    return update(env, ext);
}

environment add_universe(environment const & env, name const & l) {
    environment new_env = env.add_universe(l);
    return add(new_env, g_glvl_key, [=](serializer & s) { s << l; });
}

environment add(environment const & env, certified_declaration const & d) {
    environment new_env = env.add(d);
    declaration _d = d.get_declaration();
    return add(new_env, g_decl_key, [=](serializer & s) { s << _d; });
}

environment add(environment const & env, declaration const & d) {
    environment new_env = env.add(d);
    return add(new_env, g_decl_key, [=](serializer & s) { s << d; });
}

static std::string g_inductive("ind");

environment add_inductive(environment                  env,
                          level_param_names const &    level_params,
                          unsigned                     num_params,
                          list<inductive::inductive_decl> const & decls) {
    environment new_env = inductive::add_inductive(env, level_params, num_params, decls);
    return add(new_env, g_inductive, [=](serializer & s) {
            s << inductive_decls(level_params, num_params, decls);
        });
}

static void inductive_reader(deserializer & d, module_idx, shared_environment & senv,
                             std::function<void(asynch_update_fn const &)>  &,
                             std::function<void(delayed_update_fn const &)> &) {
    inductive_decls ds = read_inductive_decls(d);
    senv.update([&](environment const & env) {
            return inductive::add_inductive(env, std::get<0>(ds), std::get<1>(ds), std::get<2>(ds));
        });
}

environment add_inductive(environment const & env, name const & ind_name, level_param_names const & level_params,
                          unsigned num_params, expr const & type, list<inductive::intro_rule> const & intro_rules) {
    return add_inductive(env, level_params, num_params, list<inductive::inductive_decl>(inductive::inductive_decl(ind_name, type, intro_rules)));
}

static register_module_object_reader_fn g_reg_ind_reader(g_inductive, inductive_reader);
} // end of namespace module

struct import_modules_fn {
    typedef std::tuple<module_idx, unsigned, delayed_update_fn> delayed_update;
    shared_environment             m_senv;
    unsigned                       m_num_threads;
    bool                           m_keep_proofs;
    io_state                       m_ios;
    mutex                          m_asynch_mutex;
    condition_variable             m_asynch_cv;
    std::vector<asynch_update_fn>  m_asynch_tasks;
    mutex                          m_delayed_mutex;
    std::vector<delayed_update>    m_delayed_tasks;
    atomic<unsigned>               m_import_counter; // number of modules to be processed
    atomic<bool>                   m_all_modules_imported;

    struct module_info {
        name                                      m_name;
        std::string                               m_fname;
        atomic<unsigned>                          m_counter; // number of dependencies to be processed
        unsigned                                  m_module_idx;
        std::vector<std::shared_ptr<module_info>> m_dependents;
        std::vector<char>                         m_obj_code;
        module_info():m_counter(0), m_module_idx(0) {}
    };
    typedef std::shared_ptr<module_info> module_info_ptr;
    name_map<module_info_ptr> m_module_info;

    import_modules_fn(environment const & env, unsigned num_threads, bool keep_proofs, io_state const & ios):
        m_senv(env), m_num_threads(num_threads), m_keep_proofs(keep_proofs), m_ios(ios),
        m_import_counter(0), m_all_modules_imported(false) {
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

    module_info_ptr load_module_file(name const & mname) {
        auto it = m_module_info.find(mname);
        if (it)
            return *it;
        std::string fname = find_file(mname, {".olean"});
        std::ifstream in(fname, std::ifstream::binary);
        if (!in.good())
            throw exception(sstream() << "failed to open file '" << fname << "'");
        deserializer d1(in);
        std::string header;
        d1 >> header;
        if (header != g_olean_header)
            throw exception(sstream() << "file '" << fname << "' does not seem to be a valid object Lean file, invalid header");
        unsigned major, minor, claimed_hash;
        d1 >> major >> minor >> claimed_hash;
        // Enforce version?

        unsigned num_imports  = d1.read_unsigned();
        buffer<name> imports;
        for (unsigned i = 0; i < num_imports; i++)
            imports.push_back(read_name(d1));

        unsigned code_size    = d1.read_unsigned();
        std::vector<char> code(code_size);
        for (unsigned i = 0; i < code_size; i++)
            code[i] = d1.read_char();

        unsigned computed_hash = hash(code_size, [&](unsigned i) { return code[i]; });
        if (claimed_hash != computed_hash)
            throw exception(sstream() << "file '" << fname << "' has been corrupted, checksum mismatch");

        module_info_ptr r = std::make_shared<module_info>();
        r->m_name         = mname;
        r->m_fname        = fname;
        r->m_counter      = imports.size();
        r->m_module_idx   = m_import_counter+1; // importate modules have idx > 0, we reserve idx 0 for new module
        lean_assert(r->m_module_idx != g_main_module_idx);
        m_import_counter++;
        std::swap(r->m_obj_code, code);
        m_module_info.insert(mname, r);

        for (auto i : imports) {
            auto d = load_module_file(i);
            d->m_dependents.push_back(r);
        }

        if (imports.empty())
            add_import_module_task(r);

        return r;
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

    void import_decl(deserializer & d, module_idx midx) {
        declaration decl = read_declaration(d, midx);
        lean_assert(!decl.is_definition() || decl.get_module_idx() == midx);
        environment env  = m_senv.env();
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
            } else if (k == g_decl_key) {
                import_decl(d, r->m_module_idx);
            } else if (k == g_glvl_key) {
                import_universe(d);
            } else {
                object_readers & readers = get_object_readers();
                auto it = readers.find(k);
                if (it == readers.end())
                    throw exception(sstream() << "file '" << r->m_fname << "' has been corrupted, unknown object");
                it->second(d, r->m_module_idx, m_senv, add_asynch_update, add_delayed_update);
            }
            obj_counter++;
        }
        if (atomic_fetch_sub_explicit(&m_import_counter, 1u, memory_order_relaxed) == 1u) {
            m_all_modules_imported = true;
            m_asynch_cv.notify_all();
        }
        // Module was successfully imported, we should notify descendents.
        for (module_info_ptr const & d : r->m_dependents) {
            if (atomic_fetch_sub_explicit(&(d->m_counter), 1u, memory_order_relaxed) == 1u) {
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
        std::vector<std::unique_ptr<exception>> thread_exceptions(m_num_threads - 1);
        atomic<int> failed_thread_idx(-1); // >= 0 if error
        for (unsigned i = 0; i < m_num_threads - 1; i++) {
            extra_threads.push_back(std::unique_ptr<interruptible_thread>(new interruptible_thread([=, &thread_exceptions, &failed_thread_idx]() {
                            try {
                                while (auto t = next_task()) {
                                    (*t)(m_senv);
                                }
                                m_asynch_cv.notify_all();
                            } catch (exception & ex) {
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

    void store_direct_imports(unsigned num_modules, name const * modules) {
        m_senv.update([&](environment const & env) -> environment {
                module_ext ext = get_extension(env);
                for (unsigned i = 0; i < num_modules; i++)
                    ext.m_direct_imports = list<name>(modules[i], ext.m_direct_imports);
                return update(env, ext);
            });
    }

    environment operator()(unsigned num_modules, name const * modules) {
        store_direct_imports(num_modules, modules);
        for (unsigned i = 0; i < num_modules; i++)
            load_module_file(modules[i]);
        process_asynch_tasks();
        return process_delayed_tasks();
    }
};

environment import_modules(environment const & env, unsigned num_modules, name const * modules,
                           unsigned num_threads, bool keep_proofs, io_state const & ios) {
    return import_modules_fn(env, num_threads, keep_proofs, ios)(num_modules, modules);
}

environment import_module(environment const & env, name const & module,
                          unsigned num_threads, bool keep_proofs, io_state const & ios) {
    return import_modules(env, 1, &module, num_threads, keep_proofs, ios);
}
}
