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
    return memcmp(o1, o2, sz1) == 0;
}

extern "C" usize lean_maxsharing_hash(b_obj_arg o) {
    lean_assert(!lean_is_scalar(o));
    size_t sz = lean_object_byte_size(o);
    return hash_str(sz, reinterpret_cast<char const *>(o), 17);
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
    object * m;
    object * s;
public:
    max_sharing_state_core(obj_arg s) {
        m = lean_ctor_get(s, 0); lean_inc_ref(m);
        s = lean_ctor_get(s, 1); lean_inc_ref(s);
        lean_dec_ref(s);
    }

    ~max_sharing_state_core() {
        lean_dec(m);
        lean_dec(s);
    }

    obj_res pack(obj_arg a) {
        obj_res r = mk_pair(a, mk_pair(m, s));
        m = lean_box(0);
        s = lean_box(0);
        return r;
    }
};

class max_sharing_state : public max_sharing_state_core {
public:
    max_sharing_state(obj_arg s):max_sharing_state_core(s) {}

    obj_res map_find(b_obj_arg k) {
        lean_inc_ref(m); lean_inc_ref(k);
        return lean_object_map_find(m, k);
    }

    void map_insert(obj_arg k, obj_arg v) {
        m = lean_object_map_insert(m, k, v);
    }

    obj_res set_find(b_obj_arg o) {
        lean_inc_ref(s); lean_inc_ref(o);
        return lean_object_set_find(s, o);
    }

    void set_insert(obj_arg o) {
        s = lean_object_set_insert(s, o);
    }
};

class max_sharing_pstate : public max_sharing_state_core {
public:
    max_sharing_pstate(obj_arg s):max_sharing_state_core(s) {}

    obj_res map_find(b_obj_arg k) {
        lean_inc_ref(m); lean_inc_ref(k);
        return lean_object_pmap_find(m, k);
    }

    void map_insert(obj_arg k, obj_arg v) {
        m = lean_object_pmap_insert(m, k, v);
    }

    obj_res set_find(b_obj_arg o) {
        lean_inc_ref(s); lean_inc_ref(o);
        return lean_object_pset_find(s, o);
    }

    void set_insert(obj_arg o) {
        s = lean_object_pset_insert(s, o);
    }
};

template<typename state>
class max_sharing_fn {
    state m_state;

    obj_res visit(obj_arg a) {
        // TODO
        return a;
    }

public:
    max_sharing_fn(obj_arg s):m_state(s) {}

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
