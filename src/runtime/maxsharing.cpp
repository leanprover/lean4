/*
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/object.h"
#include "runtime/hash.h"

namespace lean {

extern "C" uint8 lean_maxsharing_eq(b_obj_arg o1, b_obj_arg o2) {
    lean_assert(!lean_is_scalar(o1));
    lean_assert(!lean_is_scalar(o2));
    size_t sz1 = lean_object_byte_size(o1);
    size_t sz2 = lean_object_byte_size(o2);
    if (sz1 != sz2) return false;
    // compare relevant parts of the header
    if (lean_ptr_tag(o1) != lean_ptr_tag(o2)) return false;
    if (lean_ptr_other(o1) != lean_ptr_other(o2)) return false;
    size_t header_sz = sizeof(lean_object);
    lean_assert(sz1 >= header_sz);
    // compare objects' bodies
    return memcmp(reinterpret_cast<char*>(o1) + header_sz, reinterpret_cast<char*>(o2) + header_sz, sz1 - header_sz) == 0;
}

extern "C" usize lean_maxsharing_hash(b_obj_arg o) {
    lean_assert(!lean_is_scalar(o));
    size_t sz = lean_object_byte_size(o);
    size_t header_sz = sizeof(lean_object);
    // hash relevant parts of the header
    unsigned init = hash(lean_ptr_tag(o), lean_ptr_other(o));
    // hash body
    return hash_str(sz - header_sz, reinterpret_cast<char const *>(o) + header_sz, init);
}

// unsafe def mkObjectMap : Unit → ObjectMap
extern "C" obj_res lean_mk_object_map(obj_arg);
// unsafe def ObjectMap.find? (m : ObjectMap) (k : Object) : Option Object
extern "C" obj_res lean_object_map_find(obj_arg m, obj_arg k);
// unsafe def ObjectMap.insert (m : ObjectMap) (k v : Object) : ObjectMap
extern "C" obj_res lean_object_map_insert(obj_arg m, obj_arg k, obj_arg v);

// unsafe def mkObjectSet : Unit → ObjectSet
extern "C" obj_res lean_mk_object_set(obj_arg);
// unsafe def ObjectSet.find? (s : ObjectSet) (o : Object) : Option Object
extern "C" obj_res lean_object_set_find(obj_arg s, obj_arg o);
// unsafe def ObjectSet.insert (s : ObjectSet) (o : Object) : ObjectSet
extern "C" obj_res lean_object_set_insert(obj_arg s, obj_arg o);

// unsafe def mkObjectPersistentMap : Unit → ObjectPersistentMap
extern "C" obj_res lean_mk_object_pmap(obj_arg);
// unsafe def ObjectPersistentMap.find? (m : ObjectPersistentMap) (k : Object) : Option Object
extern "C" obj_res lean_object_pmap_find(obj_arg m, obj_arg k);
// unsafe def ObjectPersistentMap.insert (m : ObjectPersistentMap) (k v : Object) : ObjectPersistentMap
extern "C" obj_res lean_object_pmap_insert(obj_arg m, obj_arg k, obj_arg v);

// unsafe def mkObjectPersistentSet : Unit → ObjectPersistentSet
extern "C" obj_res lean_mk_object_pset(obj_arg);
// unsafe def ObjectPersistentSet.find? (s : ObjectPersistentSet) (o : Object) : Option Object
extern "C" obj_res lean_object_pset_find(obj_arg s, obj_arg o);
// unsafe def ObjectPersistentSet.insert (s : ObjectPersistentSet) (o : Object) : ObjectPersistentSet
extern "C" obj_res lean_object_pset_insert(obj_arg s, obj_arg o);

static obj_res mk_pair(obj_arg a, obj_arg b) {
    object * r = alloc_cnstr(0, 2, 0);
    lean_ctor_set(r, 0, a);
    lean_ctor_set(r, 1, b);
    // std::cout << "mk_pair " << a << " " << b << std::endl;
    return r;
}

extern "C" obj_res lean_maxsharing_mk_state(obj_arg) {
    return mk_pair(lean_mk_object_map(lean_box(0)), lean_mk_object_set(lean_box(0)));
}

extern "C" obj_res lean_maxsharing_mk_pstate(obj_arg) {
    return mk_pair(lean_mk_object_pmap(lean_box(0)), lean_mk_object_pset(lean_box(0)));
}

class max_sharing_state_core {
protected:
    object * m_map;
    object * m_set;
public:
    max_sharing_state_core(obj_arg s) {
        m_map = lean_ctor_get(s, 0); lean_inc(m_map);
        m_set = lean_ctor_get(s, 1); lean_inc(m_set);
        // std::cout << "max_sharing_state_core " << m_map << " " << m_set << std::endl;
        lean_dec(s);
    }

    ~max_sharing_state_core() {
        lean_dec(m_map);
        lean_dec(m_set);
    }

    obj_res pack(obj_arg a) {
        obj_res r = mk_pair(a, mk_pair(m_map, m_set));
        m_map = lean_box(0);
        m_set = lean_box(0);
        return r;
    }
};

class max_sharing_state : public max_sharing_state_core {
public:
    max_sharing_state(obj_arg s):max_sharing_state_core(s) {}

    obj_res map_find(b_obj_arg k) {
        lean_inc(m_map); lean_inc(k);
        return lean_object_map_find(m_map, k);
    }

    void map_insert(obj_arg k, obj_arg v) {
        m_map = lean_object_map_insert(m_map, k, v);
    }

    obj_res set_find(b_obj_arg o) {
        lean_inc(m_set); lean_inc(o);
        return lean_object_set_find(m_set, o);
    }

    void set_insert(obj_arg o) {
        m_set = lean_object_set_insert(m_set, o);
    }
};

class max_sharing_pstate : public max_sharing_state_core {
public:
    max_sharing_pstate(obj_arg s):max_sharing_state_core(s) {}

    obj_res map_find(b_obj_arg k) {
        lean_inc(m_map); lean_inc(k);
        return lean_object_pmap_find(m_map, k);
    }

    void map_insert(obj_arg k, obj_arg v) {
        m_map = lean_object_pmap_insert(m_map, k, v);
    }

    obj_res set_find(b_obj_arg o) {
        lean_inc(m_set); lean_inc(o);
        return lean_object_pset_find(m_set, o);
    }

    void set_insert(obj_arg o) {
        m_set = lean_object_pset_insert(m_set, o);
    }
};

template<typename state>
class max_sharing_fn {
    state m_state;

    obj_res visit_closure(b_obj_arg a) {
        // TODO
        lean_inc(a);
        return a;
    }

    obj_res visit_array(b_obj_arg a) {
        // TODO
        lean_inc(a);
        return a;
    }

    obj_res visit_sarray(b_obj_arg a) {
        // TODO
        lean_inc(a);
        return a;
    }

    obj_res visit_string(b_obj_arg a) {
        // TODO
        lean_inc(a);
        return a;
    }

    obj_res visit_mpz(b_obj_arg a) {
        // TODO
        lean_inc(a);
        return a;
    }

    obj_res visit_thunk(b_obj_arg a) {
        // TODO
        lean_inc(a);
        return a;
    }

    obj_res visit_ctor(b_obj_arg a) {
        // TODO
        lean_inc(a);
        return a;
    }

    obj_res visit(obj_arg a) {
        if (lean_is_scalar(a)) {
            return a;
        }
        obj_res o = m_state.map_find(a);
        if (o != lean_box(0)) {
            obj_res r = lean_ctor_get(o, 0);
            lean_inc(r);
            lean_dec(o);
            std::cout << "found cached:" << r << "\n";
            return r;
        }
        obj_res r;
        switch (lean_ptr_tag(a)) {
        case LeanClosure:         r = visit_closure(a); break;
        case LeanArray:           r = visit_array(a); break;
        case LeanScalarArray:     r = visit_sarray(a); break;
        case LeanString:          r = visit_string(a); break;
        case LeanMPZ:             r = visit_mpz(a); break;
        case LeanThunk:           r = visit_thunk(a); break;
        case LeanTask:            return a;
        case LeanRef:             return a;
        case LeanExternal:        return a;
        case LeanReserved:        lean_unreachable();
        default:                  r = visit_ctor(a); break;
        }

        obj_res opt_new_r = m_state.set_find(r);
        if (opt_new_r != lean_box(0)) {
            lean_dec(r); // we already have a maximally shared term equivalent to `r`
            r = lean_ctor_get(opt_new_r, 0);
            lean_inc_n(r, 2);
            lean_dec(opt_new_r);
            m_state.map_insert(a, r);
            std::cout << "found shared:" << r << "\n";
            return r;
        }

        lean_inc_n(r, 4);
        m_state.set_insert(r);     // r is a new maximally shared term
        m_state.map_insert(a, r);  // `r` is the maximally shared representation for `a`
        m_state.map_insert(r, r);  // `r` is the maximally shared representation of itself
        std::cout << "new shared:" << r << " " << lean_maxsharing_hash(r) << "\n";
        return r;
    }

public:
    max_sharing_fn(obj_arg s):m_state(s) {
    }

    obj_res operator()(obj_arg a) {
        return m_state.pack(visit(a));
    }
};


// def State.maxSharing {α} (s : State) (a : α) : α × State
extern "C" obj_res lean_state_maxsharing(obj_arg s, obj_arg a) {
    return max_sharing_fn<max_sharing_state>(s)(a);
}

// def PersistentState.maxSharing {α} (s : PersistentState) (a : α) : α × PersistentState
extern "C" obj_res lean_persistent_state_maxsharing(obj_arg s, obj_arg a) {
    return max_sharing_fn<max_sharing_pstate>(s)(a);
}
};
