/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/for_each_fn.h"
#include "library/attribute_manager.h"
#include "library/kernel_serializer.h"
#include "library/trace.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/module.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_list.h"
#include "library/equations_compiler/util.h"
#include "library/tactic/eqn_lemmas.h"
#include "library/tactic/tactic_state.h"

namespace lean {
struct eqn_lemmas_ext : public environment_extension {
    name_map<list<simp_lemma>> m_lemmas;
    name_set                   m_has_simple_eqn_lemma;
    eqn_lemmas_ext() {}
};

struct eqn_lemmas_ext_reg {
    unsigned m_ext_id;
    eqn_lemmas_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<eqn_lemmas_ext>()); }
};

static eqn_lemmas_ext_reg * g_ext = nullptr;

static eqn_lemmas_ext const & get_extension(environment const & env) {
    return static_cast<eqn_lemmas_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, eqn_lemmas_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<eqn_lemmas_ext>(ext));
}

environment add_eqn_lemma_core(environment const & env, name const & eqn_lemma) {
    type_context_old ctx(env, transparency_mode::None);
    simp_lemmas lemmas = add(ctx, simp_lemmas(), eqn_lemma, LEAN_DEFAULT_PRIORITY);
    optional<simp_lemma> new_lemma;
    lemmas.for_each([&](name const & r, simp_lemma const & sl) {
            if (r != get_eq_name())
                throw exception("invalid equation lemma, it must produce an equality");
            if (new_lemma)
                throw exception("invalid equality lemma, lemma produced more than one equation lemma");
            else
                new_lemma = sl;
        });
    if (!new_lemma)
        throw exception("invalid equation lemma, unexpected form");
    expr const & fn = get_app_fn(new_lemma->get_lhs());
    if (!is_constant(fn))
        throw exception("invalid equality lemma, invalid lhs");
    name const & fn_name = const_name(fn);
    eqn_lemmas_ext ext = get_extension(env);
    if (list<simp_lemma> const * l = ext.m_lemmas.find(fn_name))
        ext.m_lemmas.insert(fn_name, cons(*new_lemma, *l));
    else
        ext.m_lemmas.insert(fn_name, to_list(*new_lemma));
    return update(env, ext);
}

struct eqn_lemmas_modification : public modification {
    LEAN_MODIFICATION("EqnL")

    name m_lemma;

    eqn_lemmas_modification() {}
    eqn_lemmas_modification(name const & lemma) : m_lemma(lemma) {}

    void perform(environment & env) const override {
        env = add_eqn_lemma_core(env, m_lemma);
    }

    void serialize(serializer & s) const override {
        s << m_lemma;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<eqn_lemmas_modification>(read_name(d));
    }
};

environment add_eqn_lemma(environment const & env, name const & eqn_lemma) {
    return module::add_and_perform(env, std::make_shared<eqn_lemmas_modification>(eqn_lemma));
}

void get_eqn_lemmas_for(environment const & env, name const & cname, bool refl_only, buffer<simp_lemma> & result) {
    eqn_lemmas_ext const & ext = get_extension(env);
    if (auto lemmas = ext.m_lemmas.find(cname)) {
        for (simp_lemma const & sl : *lemmas) {
            if (!refl_only || sl.is_refl())
                result.push_back(sl);
        }
    }
}

void get_eqn_lemmas_for(environment const & env, name const & cname, buffer<name> & result) {
    buffer<simp_lemma> lemmas;
    get_eqn_lemmas_for(env, cname, false, lemmas);
    for (simp_lemma const & s : lemmas)
        result.push_back(s.get_id());
}

void get_ext_eqn_lemmas_for(environment const & env, name const & cname, buffer<name> & result) {
    name_set visited;
    unsigned i = result.size();
    get_eqn_lemmas_for(env, cname, result);
    for (; i < result.size(); i++) {
        expr type = env.get(result[i]).get_type();
        for_each(type, [&](expr const & e, unsigned) {
                if (is_constant(e)) {
                    name const & n = const_name(e);
                    if (n != cname && is_prefix_of(cname, n) && !visited.contains(n) && is_internal_name(n)) {
                        get_eqn_lemmas_for(env, n, result);
                        visited.insert(n);
                    }
                }
                return true;
            });
    }
}

vm_obj tactic_get_eqn_lemmas_for(vm_obj const & all, vm_obj const & n, vm_obj const & s) {
    buffer<name> result;
    if (to_bool(all)) {
        get_ext_eqn_lemmas_for(tactic::to_state(s).env(), to_name(n), result);
    } else {
        get_eqn_lemmas_for(tactic::to_state(s).env(), to_name(n), result);
    }
    return tactic::mk_success(to_obj(result), tactic::to_state(s));
}

bool has_eqn_lemmas(environment const & env, name const & cname) {
    eqn_lemmas_ext const & ext = get_extension(env);
    return ext.m_lemmas.contains(cname);
}

environment mark_has_simple_eqn_lemma_core(environment const & env, name const & decl_name) {
    eqn_lemmas_ext ext = get_extension(env);
    lean_assert(ext.m_lemmas.contains(decl_name) && length(*ext.m_lemmas.find(decl_name)) == 1);
    ext.m_has_simple_eqn_lemma.insert(decl_name);
    return update(env, ext);
}

struct mark_has_simple_eqn_lemma_modification : public modification {
    LEAN_MODIFICATION("SEqnL")

    name m_decl_name;

    mark_has_simple_eqn_lemma_modification() {}
    mark_has_simple_eqn_lemma_modification(name const & decl_name) : m_decl_name(decl_name) {}

    void perform(environment & env) const override {
        env = mark_has_simple_eqn_lemma_core(env, m_decl_name);
    }

    void serialize(serializer & s) const override {
        s << m_decl_name;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<mark_has_simple_eqn_lemma_modification>(read_name(d));
    }
};

environment mark_has_simple_eqn_lemma(environment const & env, name const & decl_name) {
    return module::add_and_perform(env, std::make_shared<mark_has_simple_eqn_lemma_modification>(decl_name));
}

bool has_simple_eqn_lemma(environment const & env, name const & cname) {
    eqn_lemmas_ext const & ext = get_extension(env);
    return ext.m_has_simple_eqn_lemma.contains(cname);
}

void initialize_eqn_lemmas() {
    g_ext            = new eqn_lemmas_ext_reg();
    eqn_lemmas_modification::init();
    mark_has_simple_eqn_lemma_modification::init();
    DECLARE_VM_BUILTIN(name({"tactic", "get_eqn_lemmas_for"}), tactic_get_eqn_lemmas_for);
}

void finalize_eqn_lemmas() {
    eqn_lemmas_modification::finalize();
    mark_has_simple_eqn_lemma_modification::finalize();
    delete g_ext;
}
}
