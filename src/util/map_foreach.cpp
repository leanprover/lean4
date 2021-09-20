/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/map_foreach.h"

namespace lean {
/*
inductive RBNode (α : Type u) (β : α → Type v)
| leaf  {}                                                                            : RBNode
| node  (color : Rbcolor) (lchild : RBNode) (key : α) (val : β key) (rchild : RBNode) : RBNode
*/
class rbmap_visitor_fn {
    std::function<void(b_obj_arg, b_obj_arg)> const & m_fn;
    void visit(b_obj_arg m) {
        if (is_scalar(m)) return;
        visit(cnstr_get(m, 0));
        m_fn(cnstr_get(m, 1), cnstr_get(m, 2));
        visit(cnstr_get(m, 3));
    }
public:
    rbmap_visitor_fn(std::function<void(b_obj_arg, b_obj_arg)> const & fn):m_fn(fn) {}
    void operator()(b_obj_arg m) { visit(m); }
};

void rbmap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn) {
    return rbmap_visitor_fn(fn)(m);
}

/*
inductive Entry (α : Type u) (β : Type v) (σ : Type w)
| entry {} (key : α) (val : β) : Entry
| ref   {} (node : σ) : Entry
| null  {} : Entry

inductive Node (α : Type u) (β : Type v) : Type (max u v)
| entries   (es : Array (Entry α β Node)) : Node
| collision (ks : Array α) (vs : Array β) (h : ks.size = vs.size) : Node

structure PersistentHashMap (α : Type u) (β : Type v) :=
(root    : PersistentHashMap.Node α β := PersistentHashMap.Node.entries PersistentHashMap.mkEmptyEntriesArray)
(size    : Nat                        := 0)
*/

class phashmap_visitor_fn {
    std::function<void(b_obj_arg, b_obj_arg)> const & m_fn;

    void visit_entry(b_obj_arg e) {
        switch (lean_obj_tag(e)) {
        case 0: /* | entry {} (key : α) (val : β) : Entry */
            m_fn(lean_ctor_get(e, 0), lean_ctor_get(e, 1));
            return;
        case 1: /* | ref   {} (node : σ) : Entry */
            visit_node(lean_ctor_get(e, 0));
            return;
        default: /* null */
            return;
        }
    }

    void visit_collision_node(b_obj_arg ks, b_obj_arg vs) {
        lean_assert(lean_array_size(ks) == lean_array_size(vs));
        size_t sz = lean_array_size(ks);
        for (size_t i = 0; i < sz; i++) {
            m_fn(lean_array_get_core(ks, i), lean_array_get_core(vs, i));
        }
    }

    void visit_entries(b_obj_arg es) {
        size_t sz = lean_array_size(es);
        for (size_t i = 0; i < sz; i++) {
            visit_entry(lean_array_get_core(es, i));
        }
    }

    void visit_node(b_obj_arg n) {
        if (lean_ptr_tag(n) == 0) {
            visit_entries(lean_ctor_get(n, 0));
        } else {
            visit_collision_node(lean_ctor_get(n, 0), lean_ctor_get(n, 1));
        }
    }

public:
    phashmap_visitor_fn(std::function<void(b_obj_arg, b_obj_arg)> const & fn):m_fn(fn) {}
    void operator()(b_obj_arg m) { visit_node(lean_ctor_get(m, 0)); }
};

void phashmap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn) {
    return phashmap_visitor_fn(fn)(m);
}

/*
inductive AssocList (α : Type u) (β : Type v)
| nil {} : AssocList
| cons (key : α) (value : β) (tail : AssocList) : AssocList

def HashMapBucket (α : Type u) (β : Type v) :=
{ b : Array (AssocList α β) // b.size > 0 }

structure HashMapImp (α : Type u) (β : Type v) :=
(size       : Nat)
(buckets    : HashMapBucket α β)
*/
class hashmap_visitor_fn {
    std::function<void(b_obj_arg, b_obj_arg)> const & m_fn;
    void visit_assoc_list(b_obj_arg lst) {
        while (!is_scalar(lst)) {
            m_fn(cnstr_get(lst, 0), cnstr_get(lst, 1));
            lst = cnstr_get(lst, 2);
        }
    }

    void visit_buckets(b_obj_arg bs) {
        usize sz = array_size(bs);
        for (usize i = 0; i < sz; i++) {
            visit_assoc_list(array_get(bs, i));
        }
    }
public:
    hashmap_visitor_fn(std::function<void(b_obj_arg, b_obj_arg)> const & fn):m_fn(fn) {}
    void operator()(b_obj_arg m) {
        visit_buckets(cnstr_get(m, 1));
    }
};

void hashmap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn) {
    return hashmap_visitor_fn(fn)(m);
}

/*
structure SMap (α : Type u) (β : Type v) [HasBeq α] [Hashable α] :=
(stage₁ : Bool         := true)
(map₁   : HashMap α β  := {})
(map₂   : PHashMap α β := {})
*/
void smap_foreach(b_obj_arg m, std::function<void(b_obj_arg, b_obj_arg)> const & fn) {
    hashmap_foreach(cnstr_get(m, 0), fn);
    phashmap_foreach(cnstr_get(m, 1), fn);
}

extern "C" LEAN_EXPORT obj_res lean_smap_foreach_test(b_obj_arg m) {
    smap_foreach(m, [](b_obj_arg k, b_obj_arg v) {
            std::cout << ">> " << unbox(k) << " |-> " << unbox(v) << "\n";
        });
    return box(0);
}
}
