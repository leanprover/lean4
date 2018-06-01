/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <fstream>
#include "runtime/sstream.h"
#include "util/init_module.h"
#include "util/test.h"
#include "util/sexpr/init_module.h"
#include "kernel/init_module.h"
#include "kernel/inductive/inductive.h"
#include "kernel/standard_kernel.h"
#include "kernel/for_each_fn.h"
#include "checker/text_import.h"
#include "checker/simple_pp.h"

#if defined(LEAN_EMSCRIPTEN)
#include <emscripten.h>
#endif

using namespace lean;  // NOLINT

struct checker_print_fn {
    std::ostream & m_out;
    environment m_env;
    lowlevel_notations m_notations;
    std::unordered_set<name, name_hash> m_already_printed;

    checker_print_fn(std::ostream & out, environment const & env, lowlevel_notations const & nots) :
        m_out(out), m_env(env), m_notations(nots) {}

    format pp(expr const & e) {
        return simple_pp(m_env, e, m_notations);
    }

    void print_decl(declaration const & d) {
        format fn = compose_many({simple_pp(d.get_name()), space(), format(":"), space(), pp(d.get_type())});

        if (d.is_definition() && !d.is_theorem()) {
            m_out << compose_many({format("def"), space(), fn, space(), format(":="), line(), pp(d.get_value()), line()});
        } else {
            format cmd(d.is_theorem() ? "theorem" : (d.is_axiom() ? "axiom" : "constant"));
            m_out << compose_many({cmd, space(), fn, line()});
        }
    }

    void print_axioms(declaration const & decl) {
        print_axioms(decl.get_type());
        if (decl.is_definition()) print_axioms(decl.get_value());
    }

    void print_axioms(expr const & ex) {
        for_each(ex, [&] (expr const & e, unsigned) {
            if (is_constant(e) && !m_already_printed.count(const_name(e))) {
                auto decl = m_env.get(const_name(e));
                m_already_printed.insert(decl.get_name());
                print_axioms(decl);
                if (decl.is_constant_assumption() && !m_env.is_builtin(decl.get_name()))
                    print_decl(decl);
            }
            return true;
        });
    }

    void handle_cmdline_args(buffer<name> const & ns) {
        for (auto & n : ns) print_axioms(m_env.get(n));
        for (auto & n : ns) print_decl(m_env.get(n));
    }
};

int main(int argc, char ** argv) {
#if defined(LEAN_EMSCRIPTEN)
    EM_ASM(
        try {
            // emscripten cannot mount all of / in the vfs,
            // we can only mount subdirectories...
            FS.mount(NODEFS, { root: '/home' }, '/home');
            FS.mkdir('/root');
            FS.mount(NODEFS, { root: '/root' }, '/root');

            FS.chdir(process.cwd());
        } catch (e) {
            console.log(e);
        });
#endif

    if (argc < 2) {
        std::cout << "usage: leanchecker export.out lemma_to_print" << std::endl;
        return 1;
    }

    struct initer {
        initer() {
            save_stack_info();
            initialize_util_module();
            initialize_sexpr_module();
            initialize_kernel_module();
            initialize_inductive_module();
        }
        ~initer() {
            finalize_inductive_module();
            finalize_kernel_module();
            finalize_sexpr_module();
            finalize_util_module();
        }
    } initer;

    set_print_fn([] (std::ostream & out, expr const & e) {
        try {
            out << simple_pp(environment(), e, lowlevel_notations());
        } catch (throwable & e) {
            out << "!!!" << e.what() << "!!!";
        }
    });

    try {
        std::ifstream in(argv[1]);
        if (!in) throw exception(sstream() << "file not found: " << argv[1]);

        unsigned trust_lvl = 0;
        auto env = mk_environment(trust_lvl);
        lowlevel_notations notations;
        import_from_text(in, env, notations);

        buffer<name> to_print;
        for (int i = 2; i < argc; i++)
            to_print.push_back(string_to_name(argv[i]));

        checker_print_fn(std::cout, env, notations).handle_cmdline_args(to_print);

        unsigned num_decls = 0;
        env.for_each_declaration([&] (declaration const &) { num_decls++; });
        std::cout << "checked " << num_decls << " declarations" << std::endl;

        return 0;
    } catch (throwable & ex) {
        std::cerr << ex.what() << std::endl;
        return 1;
    } catch (std::exception & ex) {
        std::cerr << ex.what() << std::endl;
        return 1;
    }
}
