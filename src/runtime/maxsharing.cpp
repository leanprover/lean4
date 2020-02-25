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
    cnstr_set(r, 0, a);
    cnstr_set(r, 1, b);
    return r;
}

extern "C" obj_res lean_maxsharing_mk_state(obj_arg) {
    return mk_pair(lean_mk_object_map(box(0)), lean_mk_object_set(box(0)));
}

extern "C" obj_res lean_maxsharing_mk_pstate(obj_arg) {
    return mk_pair(lean_mk_object_pmap(box(0)), lean_mk_object_pset(box(0)));
}

// def State.maxSharing {α} (s : State) (a : α) : α × State
extern "C" obj_res lean_state_maxsharing(obj_arg s, obj_arg a) {
    // TODO
    return mk_pair(a, s);
}

// def PersistentState.maxSharing {α} (s : PersistentState) (a : α) : α × PersistentState
extern "C" obj_res lean_persistent_state_maxsharing(obj_arg s, obj_arg a) {
    // TODO
    return mk_pair(a, s);
}
};
