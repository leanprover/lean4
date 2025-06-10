/*
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstring>
#include "runtime/sharecommon.h"
#include "runtime/hash.h"

namespace lean {

extern "C" LEAN_EXPORT uint8 lean_sharecommon_eq(b_obj_arg o1, b_obj_arg o2) {
    lean_assert(!lean_is_scalar(o1));
    lean_assert(!lean_is_scalar(o2));
    size_t sz1 = lean_object_data_byte_size(o1);
    size_t sz2 = lean_object_data_byte_size(o2);
    if (sz1 != sz2) return false;
    // compare relevant parts of the header
    uint8_t tag = lean_ptr_tag(o1);
    if (tag != lean_ptr_tag(o2)) return false;
    if (lean_ptr_other(o1) != lean_ptr_other(o2)) return false;
    if (tag == LeanMPZ) {
        return mpz_value(o1) == mpz_value(o2);
    } else {
        size_t header_sz = sizeof(lean_object);
        lean_assert(sz1 >= header_sz);
        // compare objects' bodies
        return memcmp(reinterpret_cast<char*>(o1) + header_sz, reinterpret_cast<char*>(o2) + header_sz, sz1 - header_sz) == 0;
    }
}

extern "C" LEAN_EXPORT uint64_t lean_sharecommon_hash(b_obj_arg o) {
    lean_assert(!lean_is_scalar(o));
    size_t sz = lean_object_data_byte_size(o);
    size_t header_sz = sizeof(lean_object);
    uint8_t tag = lean_ptr_tag(o);
    if (tag == LeanMPZ) {
        return hash(tag, mpz_value(o).hash());
    } else {
        // hash relevant parts of the header
        unsigned init = hash(tag, lean_ptr_other(o));
        // hash body
        return hash_str(sz - header_sz, reinterpret_cast<unsigned char const *>(o) + header_sz, init);
    }
}

static obj_res mk_pair(obj_arg a, obj_arg b) {
    object * r = alloc_cnstr(0, 2, 0);
    lean_ctor_set(r, 0, a);
    lean_ctor_set(r, 1, b);
    // std::cout << "mk_pair " << a << " " << b << std::endl;
    return r;
}

class sharecommon_state {
protected:
    object * m_map_find;
    object * m_map_insert;
    object * m_set_find;
    object * m_set_insert;
    object * m_map;
    object * m_set;
public:
    sharecommon_state(b_obj_arg tc, obj_arg s) {
        m_map_find   = lean_ctor_get(tc, 1);
        m_map_insert = lean_ctor_get(tc, 2);
        m_set_find   = lean_ctor_get(tc, 3);
        m_set_insert = lean_ctor_get(tc, 4);
        m_map = lean_ctor_get(s, 0); lean_inc(m_map);
        m_set = lean_ctor_get(s, 1); lean_inc(m_set);
        // std::cout << "sharecommon_state " << m_map << " " << m_set << std::endl;
        lean_dec(s);
    }

    ~sharecommon_state() {
        lean_dec(m_map);
        lean_dec(m_set);
    }

    obj_res pack(obj_arg a) {
        obj_res r = mk_pair(a, mk_pair(m_map, m_set));
        m_map = lean_box(0);
        m_set = lean_box(0);
        return r;
    }

    obj_res map_find(b_obj_arg k) {
        lean_inc(m_map_find); lean_inc(m_map); lean_inc(k);
        return lean_apply_2(m_map_find, m_map, k);
    }

    void map_insert(obj_arg k, obj_arg v) {
        lean_inc(m_map_insert);
        m_map = lean_apply_3(m_map_insert, m_map, k, v);
    }

    obj_res set_find(b_obj_arg o) {
        lean_inc(m_set_find); lean_inc(m_set); lean_inc(o);
        return lean_apply_2(m_set_find, m_set, o);
    }

    void set_insert(obj_arg o) {
        lean_inc(m_set_insert);
        m_set = lean_apply_2(m_set_insert, m_set, o);
    }
};

class sharecommon_fn {
    sharecommon_state         m_state;
    std::vector<lean_object*> m_children;
    std::vector<lean_object*> m_todo;

    void clear_children() {
        m_children.clear();
    }

    bool push_child(b_obj_arg a) {
        if (lean_is_scalar(a)) {
            m_children.push_back(a);
            return true;
        }
        switch (lean_ptr_tag(a)) {
        case LeanReserved:
            lean_unreachable();
        // We do not maximize sharing for the following kinds of objects
        case LeanThunk:
        case LeanTask:     case LeanRef:
        case LeanExternal: case LeanClosure:
        case LeanPromise:
            m_children.push_back(a);
            return true;
        default:
            break;
        }

        // Check whether we have already maximized sharing for `a`
        obj_res o = m_state.map_find(a);
        if (o != lean_box(0)) {
            obj_res r = lean_ctor_get(o, 0);
            lean_dec(o);
            // The map still has a reference to `r`
            m_children.push_back(r);
            // std::cout << "cached maximized " << r << "\n";
            return true;
        }

        m_todo.push_back(a);
        return false;
    }

    void save(b_obj_arg a, obj_arg new_a) {
        lean_assert(m_todo.size() > 0);
        lean_assert(m_todo.back() == a);
        m_todo.pop_back();
        obj_res opt_new_r = m_state.set_find(new_a);
        if (opt_new_r != lean_box(0)) {
            lean_dec(new_a); // we already have a maximally shared term equivalent to `new_a`
            new_a = lean_ctor_get(opt_new_r, 0);
            lean_inc(new_a);
            lean_dec(opt_new_r);
            lean_inc(a);
            m_state.map_insert(a, new_a);
            // std::cout << "already maximized " << new_a << "\n";
        } else {
            lean_inc(a);
            lean_inc_n(new_a, 3);
            m_state.set_insert(new_a);        // `new_a` is a new maximally shared term
            m_state.map_insert(a, new_a);     // `new_a` is the maximally shared representation for `a`
            m_state.map_insert(new_a, new_a); // `new_a` is the maximally shared representation for itself
            // std::cout << "new maximized " << new_a << "\n";
        }
    }

    void visit_array(b_obj_arg a) {
        clear_children();
        bool missing_children = false;
        size_t sz = array_size(a);
        for (size_t i = 0; i < sz; i++) {
            if (!push_child(lean_array_get_core(a, i))) {
                missing_children = true;
            }
        }
        if (missing_children)
            return;
        lean_array_object * new_a = (lean_array_object*)lean_alloc_array(sz, sz);
        for (size_t i = 0; i < sz; i++) {
            lean_inc(m_children[i]);
            lean_array_set_core((lean_object*)new_a, i, m_children[i]);
        }
        save(a, (lean_object*)new_a);
    }

    void visit_sarray(b_obj_arg a) {
        size_t sz        = lean_sarray_size(a);
        unsigned elem_sz = lean_sarray_elem_size(a);
        lean_sarray_object * new_a = (lean_sarray_object*)lean_alloc_sarray(elem_sz, sz, sz);
        memcpy(new_a->m_data, lean_to_sarray(a)->m_data, elem_sz*sz);
        save(a, (lean_object*)new_a);
    }

    void visit_string(b_obj_arg a) {
        size_t sz     = lean_string_size(a);
        size_t len    = lean_string_len(a);
        lean_string_object * new_a = (lean_string_object*)lean_alloc_string(sz, sz, len);
        lean_set_st_header((lean_object*)new_a, LeanString, 0);
        new_a->m_size     = sz;
        new_a->m_capacity = sz;
        new_a->m_length   = len;
        memcpy(new_a->m_data, lean_to_string(a)->m_data, sz);
        save(a, (lean_object*)new_a);
    }

    void visit_mpz(b_obj_arg a) {
        object * new_a = alloc_mpz(mpz_value(a));
        save(a, new_a);
    }

    void visit_ctor(b_obj_arg a) {
        clear_children();
        unsigned num_objs  = lean_ctor_num_objs(a);
        bool missing_child = false;
        for (unsigned i = 0; i < num_objs; i++) {
            if (!push_child(lean_ctor_get(a, i))) {
                // std::cout << "missing_child " << a << " #" << i << " := " << lean_ctor_get(a, i) << std::endl;
                missing_child = true;
                lean_assert(m_todo.back() == lean_ctor_get(a, i));
            }
        }
        if (missing_child)
            return;
        unsigned tag           = lean_ptr_tag(a);
        unsigned sz            = lean_object_byte_size(a);
        unsigned scalar_offset = sizeof(lean_object) + num_objs*sizeof(void*);
        unsigned scalar_sz     = sz - scalar_offset;
        lean_object * new_a    = lean_alloc_ctor(tag, num_objs, scalar_sz);
        for (unsigned i = 0; i < num_objs; i++) {
            lean_inc(m_children[i]);
            lean_ctor_set(new_a, i, m_children[i]);
        }
        if (scalar_sz > 0) {
            memcpy(reinterpret_cast<char*>(new_a) + scalar_offset, reinterpret_cast<char*>(a) + scalar_offset, scalar_sz);
        }
        save(a, new_a);
    }

public:
    sharecommon_fn(b_obj_arg tc, obj_arg s):m_state(tc, s) {}

    obj_res operator()(obj_arg a) {
        if (push_child(a)) {
            object * r = m_children.back();
            lean_inc(r);
            lean_dec(a);
            return m_state.pack(r);
        }
        while (!m_todo.empty()) {
            b_obj_arg curr = m_todo.back();
            // std::cout << "visiting " << curr << " " << static_cast<unsigned>(lean_ptr_tag(curr)) << "\n";
            switch (lean_ptr_tag(curr)) {
            case LeanClosure:         lean_unreachable();
            case LeanArray:           visit_array(curr); break;
            case LeanScalarArray:     visit_sarray(curr); break;
            case LeanString:          visit_string(curr); break;
            case LeanMPZ:             visit_mpz(curr); break;
            case LeanThunk:           lean_unreachable();
            case LeanTask:            lean_unreachable();
            case LeanPromise:         lean_unreachable();
            case LeanRef:             lean_unreachable();
            case LeanExternal:        lean_unreachable();
            case LeanReserved:        lean_unreachable();
            default:                  visit_ctor(curr); break;
            }
        }

        obj_res o = m_state.map_find(a);
        lean_assert(o != lean_box(0));
        obj_res r = lean_ctor_get(o, 0);
        lean_inc(r);
        lean_dec(o);
        lean_dec(a);
        return m_state.pack(r);
    }
};

// def State.shareCommon {α} {σ : @& StateFactory} (s : State σ) (a : α) : α × State σ
extern "C" LEAN_EXPORT obj_res lean_state_sharecommon(b_obj_arg tc, obj_arg s, obj_arg a) {
    return sharecommon_fn(tc, s)(a);
}


/*
  We do not increment reference counters when inserting Lean objects at `m_cache` and `m_set`.
  This is correct because
  - The domain of `m_cache` contains only sub-objects of `lean_sharecommon_quick` parameter,
    and we know the object referenced by this parameter will remain alive.
  - The range of `m_cache` contains only new objects that have been maxed shared, and these
    objects will be are sub-objects of the object returned by `lean_sharecommon_quick`.
  - `m_set` is like the range of `m_cache`.
*/

lean_object * sharecommon_quick_fn::check_cache(lean_object * a) {
    if (!lean_is_exclusive(a)) {
        // We only check the cache if `a` is a shared object
        auto it = m_cache.find(a);
        if (it != m_cache.end()) {
            // All objects stored in the range of `m_cache` are single threaded.
            lean_assert(lean_is_st(it->second));
            // We increment the reference counter because this object
            // will be returned by `lean_sharecommon_quick` or stored into a new object.
            it->second->m_rc++;
            return it->second;
        }
        if (m_check_set) {
            auto it = m_set.find(a);
            if (it != m_set.end()) {
                lean_object * result = *it;
                lean_assert(lean_is_st(result));
                result->m_rc++;
                return result;
            }
        }
    }
    return nullptr;
}

/*
  `new_a` is a new object that is equal to `a`, but its subobjects are maximally shared.
*/
lean_object * sharecommon_quick_fn::save(lean_object * a, lean_object * new_a) {
    lean_assert(lean_is_st(new_a));
    lean_assert(new_a->m_rc == 1);
    auto it = m_set.find(new_a);
    lean_object * result;
    if (it == m_set.end()) {
        // `new_a` is a new object
        m_set.insert(new_a);
        result = new_a;
    } else {
        // We already have a maximally shared object that is equal to `new_a`
        result = *it;
        DEBUG_CODE({
                if (lean_is_ctor(new_a)) {
                    lean_assert(lean_is_ctor(result));
                    unsigned num_objs = lean_ctor_num_objs(new_a);
                    lean_assert(lean_ctor_num_objs(result) == num_objs);
                    for (unsigned i = 0; i < num_objs; i++) {
                        lean_assert(lean_ctor_get(result, i) == lean_ctor_get(new_a, i));
                    }
                }
            });
        lean_dec_ref(new_a); // delete `new_a`
        // All objects in `m_set` are single threaded.
        lean_assert(lean_is_st(result));
        result->m_rc++;
        lean_assert(result->m_rc > 1);
    }
    if (!lean_is_exclusive(a)) {
        // We only cache the result if `a` is a shared object.
        m_cache.insert(std::make_pair(a, result));
    }
    lean_assert(result == new_a || result->m_rc > 1);
    lean_assert(result != new_a || result->m_rc == 1);
    return result;
}

// `sarray` and `string`
lean_object * sharecommon_quick_fn::visit_terminal(lean_object * a) {
    auto it = m_set.find(a);
    if (it == m_set.end()) {
        m_set.insert(a);
    } else {
        a = *it;
    }
    lean_inc_ref(a);
    return a;
}

lean_object * sharecommon_quick_fn::visit_array(lean_object * a) {
    lean_object * r = check_cache(a);
    if (r != nullptr) { lean_assert(r->m_rc > 1); return r; }

    size_t sz = array_size(a);
    lean_array_object * new_a = (lean_array_object*)lean_alloc_array(sz, sz);
    for (size_t i = 0; i < sz; i++) {
        lean_array_set_core((lean_object*)new_a, i, visit(lean_array_get_core(a, i)));
    }
    return save(a, (lean_object*)new_a);
}

lean_object * sharecommon_quick_fn::visit_ctor(lean_object * a) {
    lean_object * r = check_cache(a);
    if (r != nullptr) { lean_assert(r->m_rc > 1); return r; }
    unsigned num_objs      = lean_ctor_num_objs(a);
    unsigned tag           = lean_ptr_tag(a);
    unsigned sz            = lean_object_byte_size(a);
    unsigned scalar_offset = sizeof(lean_object) + num_objs*sizeof(void*);
    unsigned scalar_sz     = sz - scalar_offset;
    lean_object * new_a    = lean_alloc_ctor(tag, num_objs, scalar_sz);
    for (unsigned i = 0; i < num_objs; i++) {
        lean_ctor_set(new_a, i, visit(lean_ctor_get(a, i)));
    }
    if (scalar_sz > 0) {
        memcpy(reinterpret_cast<char*>(new_a) + scalar_offset, reinterpret_cast<char*>(a) + scalar_offset, scalar_sz);
    }
    return save(a, new_a);
}

/*
**TODO:** We did not implement stack overflow detection.
We claim it is not needed in the current uses of `shareCommon'`.
If this becomes an issue, we can use the following approach to address the issue without
affecting the performance.
- Add an extra `depth` parameter.
- In `operator()`, estimate the maximum depth based on the remaining stack space. See `check_stack`.
- If the limit is reached, simply return `a`.
*/
lean_object * sharecommon_quick_fn::visit(lean_object * a) {
    if (lean_is_scalar(a)) {
        return a;
    }
    switch (lean_ptr_tag(a)) {
    /*
      Similarly to `sharecommon_fn`, we only maximally share arrays, scalar arrays, strings, and
      constructor objects.
    */
    case LeanClosure:         lean_inc_ref(a); return a;
    case LeanThunk:           lean_inc_ref(a); return a;
    case LeanTask:            lean_inc_ref(a); return a;
    case LeanPromise:         lean_inc_ref(a); return a;
    case LeanRef:             lean_inc_ref(a); return a;
    case LeanExternal:        lean_inc_ref(a); return a;
    case LeanReserved:        lean_inc_ref(a); return a;
    case LeanMPZ:             return visit_terminal(a);
    case LeanScalarArray:     return visit_terminal(a);
    case LeanString:          return visit_terminal(a);
    case LeanArray:           return visit_array(a);
    default:                  return visit_ctor(a);
    }
}

// def ShareCommon.shareCommon' (a : A) : A := a
extern "C" LEAN_EXPORT obj_res lean_sharecommon_quick(obj_arg a) {
    return sharecommon_quick_fn()(a);
}

lean_object * sharecommon_persistent_fn::operator()(lean_object * e) {
    lean_object * r = check_cache(e);
    if (r != nullptr)
        return r;
    m_saved.push_back(object_ref(e, true));
    r = visit(e);
    m_saved.push_back(object_ref(r, true));
    return r;
}
};
