/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <memory>
#include <string>
#include "runtime/sstream.h"
#include "util/name_hash_map.h"
#include "library/annotation.h"

namespace lean {
static name * g_annotation = nullptr;

kvmap mk_annotation_kvmap(name const & k) {
    return set_name(kvmap(), *g_annotation, k);
}

typedef name_hash_map<kvmap> annotation_maps;
static annotation_maps * g_annotation_maps = nullptr;

void register_annotation(name const & kind) {
    lean_assert(g_annotation_maps->find(kind) == g_annotation_maps->end());
    g_annotation_maps->insert(mk_pair(kind, mk_annotation_kvmap(kind)));
}

optional<expr> is_annotation(expr const & e) {
    expr e2 = e;
    if (is_mdata(e2) && get_name(mdata_data(e2), *g_annotation))
        return some_expr(e2);
    else
        return none_expr();
}

name get_annotation_kind(expr const & e) {
    auto o = is_annotation(e);
    lean_assert(o);
    return *get_name(mdata_data(*o), *g_annotation);
}

bool is_annotation(expr const & e, name const & kind) {
    auto o = is_annotation(e);
    return o && get_annotation_kind(*o) == kind;
}

expr const & get_annotation_arg(expr const & e) {
    auto o = is_annotation(e);
    lean_assert(o);
    return mdata_expr(*o);
}

expr mk_annotation(name const & kind, expr const & e) {
    auto it = g_annotation_maps->find(kind);
    if (it != g_annotation_maps->end()) {
        expr r = mk_mdata(it->second, e);
        lean_assert(is_annotation(r));
        lean_assert(get_annotation_kind(r) == kind);
        return r;
    } else {
        throw exception(sstream() << "unknown annotation kind '" << kind << "'");
    }
}

bool is_nested_annotation(expr const & e, name const & kind) {
    expr const * it = &e;
    while (is_annotation(*it)) {
        if (get_annotation_kind(*it) == kind)
            return true;
        it = &get_annotation_arg(*it);
    }
    return false;
}

expr const & get_nested_annotation_arg(expr const & e) {
    expr const * it = &e;
    while (is_annotation(*it))
        it = &get_annotation_arg(*it);
    return *it;
}

expr copy_annotations(expr const & from, expr const & to) {
    buffer<expr> trace;
    expr const * it = &from;
    while (is_annotation(*it)) {
        trace.push_back(*it);
        it = &get_annotation_arg(*it);
    }
    expr r     = to;
    unsigned i = trace.size();
    while (i > 0) {
        --i;
        r = mk_annotation(get_annotation_kind(trace[i]), r);
    }
    return r;
}

static name * g_have       = nullptr;
static name * g_show       = nullptr;
static name * g_suffices   = nullptr;
static name * g_checkpoint = nullptr;

expr mk_have_annotation(expr const & e) { return mk_annotation(*g_have, e); }
expr mk_show_annotation(expr const & e) { return mk_annotation(*g_show, e); }
expr mk_suffices_annotation(expr const & e) { return mk_annotation(*g_suffices, e); }
expr mk_checkpoint_annotation(expr const & e) { return mk_annotation(*g_checkpoint, e); }
bool is_have_annotation(expr const & e) { return is_annotation(e, *g_have); }
bool is_show_annotation(expr const & e) { return is_annotation(e, *g_show); }
bool is_suffices_annotation(expr const & e) { return is_annotation(e, *g_suffices); }
bool is_checkpoint_annotation(expr const & e) { return is_annotation(e, *g_checkpoint); }

void initialize_annotation() {
    g_annotation = new name("annotation");
    mark_persistent(g_annotation->raw());
    g_annotation_maps = new annotation_maps();
    g_have            = new name("have");
    mark_persistent(g_have->raw());
    g_show            = new name("show");
    mark_persistent(g_show->raw());
    g_suffices        = new name("suffices");
    mark_persistent(g_suffices->raw());
    g_checkpoint      = new name("checkpoint");
    mark_persistent(g_checkpoint->raw());

    register_annotation(*g_have);
    register_annotation(*g_show);
    register_annotation(*g_suffices);
    register_annotation(*g_checkpoint);
}

void finalize_annotation() {
    delete g_checkpoint;
    delete g_show;
    delete g_have;
    delete g_suffices;
    delete g_annotation;
}
}
