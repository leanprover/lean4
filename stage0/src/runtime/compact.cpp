/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_set>
#include <algorithm>
#include <string>
#include <vector>
#include <cstring>
#include <lean/lean.h>
#include "runtime/hash.h"
#include "runtime/compact.h"

#ifndef LEAN_WINDOWS
#include <sys/mman.h>
#endif

#define LEAN_COMPACTOR_INIT_SZ 1024*1024
#define LEAN_MAX_SHARING_TABLE_INITIAL_SIZE 1024*1024

// uncomment to track the number of each kind of object in an .olean file
// #define LEAN_TAG_COUNTERS

namespace lean {

struct max_sharing_key {
    size_t m_offset;
    size_t m_size;
    max_sharing_key(size_t offset, size_t sz):m_offset(offset), m_size(sz) {}
};

struct max_sharing_hash {
    object_compactor * m;
    max_sharing_hash(object_compactor * manager):m(manager) {}
    unsigned operator()(max_sharing_key const & k) const {
        return hash_str(k.m_size, reinterpret_cast<unsigned char const *>(m->m_begin) + k.m_offset, 17);
    }
};

struct max_sharing_eq {
    object_compactor * m;
    max_sharing_eq(object_compactor * manager):m(manager) {}
    bool operator()(max_sharing_key const & k1, max_sharing_key const & k2) const {
        if (k1.m_size != k2.m_size) return false;
        return memcmp(reinterpret_cast<char*>(m->m_begin) + k1.m_offset, reinterpret_cast<char*>(m->m_begin) + k2.m_offset, k1.m_size) == 0;
    }
};


struct object_compactor::max_sharing_table {
    std::unordered_set<max_sharing_key, max_sharing_hash, max_sharing_eq> m_table;
    max_sharing_table(object_compactor * manager):
        m_table(LEAN_MAX_SHARING_TABLE_INITIAL_SIZE, max_sharing_hash(manager), max_sharing_eq(manager)) {
    }
};

object_compactor::object_compactor(void * base_addr):
    m_max_sharing_table(new max_sharing_table(this)),
    m_base_addr(base_addr),
    m_begin(malloc(LEAN_COMPACTOR_INIT_SZ)),
    m_end(m_begin),
    m_capacity(static_cast<char*>(m_begin) + LEAN_COMPACTOR_INIT_SZ) {
}

object_compactor::~object_compactor() {
    free(m_begin);
}

/*
  Remark: g_null_offset must NOT be a valid Lean scalar value (e.g., static_cast<size_t>(-1)).
  Recall that Lean scalar are odd size_t values. So, we use (static_cast<size_t>(-1) - 1) which is an even number.
  In the past we used `static_cast<size_t>(-1)`, and it caused nontermination in the object compactor.
*/
object_offset g_null_offset = reinterpret_cast<object_offset>(static_cast<size_t>(-1) - 1);

void * object_compactor::alloc(size_t sz) {
    size_t rem = sz % sizeof(void*);
    if (rem != 0)
        sz = sz + sizeof(void*) - rem;
    while (static_cast<char*>(m_end) + sz > m_capacity) {
        size_t new_capacity = capacity()*2;
        void * new_begin = malloc(new_capacity);
        memcpy(new_begin, m_begin, size());
        m_end      = static_cast<char*>(new_begin) + size();
        m_capacity = static_cast<char*>(new_begin) + new_capacity;
        free(m_begin);
        m_begin    = new_begin;
    }
    void * r = m_end;
    memset(r, 0, sz);
    m_end = static_cast<char*>(m_end) + sz;
    lean_assert(m_end <= m_capacity);
    return r;
}

void object_compactor::save(object * o, object * new_o) {
    lean_assert(m_begin <= new_o && new_o < m_end);
    m_obj_table.insert(std::make_pair(o, reinterpret_cast<object_offset>(reinterpret_cast<char*>(new_o) - reinterpret_cast<char*>(m_begin) + reinterpret_cast<size_t>(m_base_addr))));
}

void object_compactor::save_max_sharing(object * o, object * new_o, size_t new_o_sz) {
    max_sharing_key k(reinterpret_cast<char*>(new_o) - reinterpret_cast<char*>(m_begin), new_o_sz);
    auto it = m_max_sharing_table->m_table.find(k);
    if (it != m_max_sharing_table->m_table.end()) {
        m_end = new_o;
        new_o = reinterpret_cast<lean_object*>(reinterpret_cast<char*>(m_begin) + it->m_offset);
    } else {
        m_max_sharing_table->m_table.insert(k);
    }
    save(o, new_o);
}

object_offset object_compactor::to_offset(object * o) {
    if (lean_is_scalar(o)) {
        return o;
    } else {
        auto it = m_obj_table.find(o);
        if (it == m_obj_table.end()) {
            m_todo.push_back(o);
            return g_null_offset;
        } else {
            return it->second;
        }
    }
}

object * object_compactor::copy_object(object * o) {
    size_t sz  = lean_object_byte_size(o);
    void * mem = alloc(sz);
    memcpy(mem, o, sz);
    object * r = static_cast<object*>(mem);
    lean_set_non_heap_header(r, sz, lean_ptr_tag(o), lean_ptr_other(o));
    lean_assert(!lean_has_rc(r));
    lean_assert(lean_ptr_tag(r) == lean_ptr_tag(o));
    lean_assert(lean_ptr_other(r) == lean_ptr_other(o));
    lean_assert(lean_object_byte_size(r) == sz);
    return r;
}

void object_compactor::insert_sarray(object * o) {
    size_t sz        = lean_sarray_size(o);
    unsigned elem_sz = lean_sarray_elem_size(o);
    size_t obj_sz = sizeof(lean_sarray_object) + elem_sz*sz;
    lean_sarray_object * new_o = (lean_sarray_object*)alloc(obj_sz);
    lean_set_non_heap_header_for_big((lean_object*)new_o, LeanScalarArray, elem_sz);
    new_o->m_size     = sz;
    new_o->m_capacity = sz;
    memcpy(new_o->m_data, lean_to_sarray(o)->m_data, elem_sz*sz);
    save_max_sharing(o, (lean_object*)new_o, obj_sz);
}

void object_compactor::insert_string(object * o) {
    size_t sz        = lean_string_size(o);
    size_t len       = lean_string_len(o);
    size_t obj_sz = sizeof(lean_string_object) + sz;
    lean_string_object * new_o = (lean_string_object*)alloc(obj_sz);
    lean_set_non_heap_header_for_big((lean_object*)new_o, LeanString, 0);
    new_o->m_size     = sz;
    new_o->m_capacity = sz;
    new_o->m_length   = len;
    memcpy(new_o->m_data, lean_to_string(o)->m_data, sz);
    save_max_sharing(o, (lean_object*)new_o, obj_sz);
}

// #define ShowCtors

bool object_compactor::insert_constructor(object * o) {
    std::vector<object_offset> & offsets = m_tmp;
    bool missing_children = false;
    unsigned num_objs     = lean_ctor_num_objs(o);
    offsets.resize(num_objs);
    unsigned i = num_objs;
    while (i > 0) {
        i--;
        object_offset c = to_offset(cnstr_get(o, i));
        if (c == g_null_offset)
            missing_children = true;
        offsets[i] = c;
    }
    if (missing_children)
        return false;
#ifdef ShowCtors
    if (lean_object_byte_size(o) == sizeof(lean_object) + sizeof(void*)*lean_ctor_num_objs(o)) {
        std::cout << "ctor " << (unsigned)lean_ptr_tag(o);
        for (unsigned i = 0; i < num_objs; i++) {
            std::cout << " " << (size_t)offsets[i];
        }
        std::cout << "\n";
    }
#endif
    object * new_o = copy_object(o);
    for (unsigned i = 0; i < lean_ctor_num_objs(o); i++)
        lean_ctor_set(new_o, i, offsets[i]);
    save_max_sharing(o, new_o, lean_object_byte_size(o));
    return true;
}

bool object_compactor::insert_array(object * o) {
    std::vector<object_offset> & offsets = m_tmp;
    bool missing_children = false;
    size_t sz = array_size(o);
    offsets.resize(sz);
    // std::cout << sz << " array\n";
    size_t i = sz;
    while (i > 0) {
        i--;
        object_offset c = to_offset(array_get(o, i));
        if (c == g_null_offset)
            missing_children = true;
        offsets[i] = c;
    }
    if (missing_children)
        return false;
    size_t obj_sz = sizeof(lean_array_object) + sizeof(void*)*sz;
    lean_array_object * new_o = (lean_array_object*)alloc(obj_sz);
    lean_set_non_heap_header_for_big((lean_object*)new_o, LeanArray, 0);
    new_o->m_size     = sz;
    new_o->m_capacity = sz;
    for (size_t i = 0; i < sz; i++) {
        lean_array_set_core((lean_object*)new_o, i, offsets[i]);
    }
    save_max_sharing(o, (lean_object*)new_o, obj_sz);
    return true;
}

bool object_compactor::insert_thunk(object * o) {
    object * v = lean_thunk_get(o);
    object_offset c = to_offset(v);
    if (c == g_null_offset)
        return false;
    object * r = copy_object(o);
    lean_to_thunk(r)->m_value = c;
    save_max_sharing(o, r, lean_object_byte_size(o));
    return true;
}

bool object_compactor::insert_ref(object * o) {
    object * v = lean_to_ref(o)->m_value;
    object_offset c = to_offset(v);
    if (c == g_null_offset)
        return false;
    object * r = copy_object(o);
    lean_to_ref(r)->m_value = c;
    save_max_sharing(o, r, lean_object_byte_size(o));
    return true;
}

bool object_compactor::insert_task(object * o) {
    object * v = lean_task_get(o);
    object_offset c = to_offset(v);
    if (c == g_null_offset)
        return false;
    object * r = copy_object(o);
    lean_assert(lean_to_task(r)->m_imp == nullptr);
    lean_to_task(r)->m_value = c;
    save_max_sharing(o, r, lean_object_byte_size(o));
    return true;
}

bool object_compactor::insert_promise(object * o) {
    object * t = (object *)lean_to_promise(o)->m_result;
    object_offset c = to_offset(t);
    if (c == g_null_offset)
        return false;
    object * r = copy_object(o);
    lean_to_promise(r)->m_result = (lean_task_object *)c;
    save_max_sharing(o, r, lean_object_byte_size(o));
    return true;
}

void object_compactor::insert_mpz(object * o) {
#ifdef LEAN_USE_GMP
    size_t nlimbs = mpz_size(to_mpz(o)->m_value.m_val);
    size_t data_sz = sizeof(mp_limb_t) * nlimbs;
    size_t sz = sizeof(mpz_object) + data_sz;
    mpz_object * new_o = (mpz_object *)alloc(sz);
    memcpy(new_o, to_mpz(o), sizeof(mpz_object));
    lean_set_non_heap_header((lean_object*)new_o, sz, LeanMPZ, 0);
    __mpz_struct & m = new_o->m_value.m_val[0];
    // we assume the limb array is the only indirection in an `__mpz_struct` and everything else can be bitcopied
    void * data = reinterpret_cast<char*>(new_o) + sizeof(mpz_object);
    memcpy(data, m._mp_d, data_sz);
    m._mp_d = reinterpret_cast<mp_limb_t *>(reinterpret_cast<char *>(data) - reinterpret_cast<char *>(m_begin) + reinterpret_cast<ptrdiff_t>(m_base_addr));
    m._mp_alloc = nlimbs;
    save(o, (lean_object*)new_o);
#else
    size_t data_sz = sizeof(mpn_digit) * to_mpz(o)->m_value.m_size;
    size_t sz      = sizeof(mpz_object) + data_sz;
    mpz_object * new_o = (mpz_object *)alloc(sz);
    memcpy(new_o, to_mpz(o), sizeof(mpz_object));
    lean_set_non_heap_header((lean_object*)new_o, sz, LeanMPZ, 0);
    void * data = reinterpret_cast<char*>(new_o) + sizeof(mpz_object);
    memcpy(data, to_mpz(o)->m_value.m_digits, data_sz);
    new_o->m_value.m_digits = reinterpret_cast<mpn_digit *>(reinterpret_cast<char *>(data) - reinterpret_cast<char *>(m_begin) + reinterpret_cast<ptrdiff_t>(m_base_addr));
    save(o, (lean_object*)new_o);
#endif
}

#ifdef LEAN_TAG_COUNTERS

static size_t g_tag_counters[256];

struct tag_counter_manager {
    static void display_kind(char const * msg, unsigned k) {
        if (g_tag_counters[k] != 0)
            std::cout << msg << " " << g_tag_counters[k] << "\n";
    }

    tag_counter_manager() {
        for (unsigned i = 0; i < 256; i++) g_tag_counters[i] = 0;
    }

    ~tag_counter_manager() {
        display_kind("#closure:  ", LeanClosure);
        display_kind("#array:    ", LeanArray);
        display_kind("#sarray:   ", LeanStructArray);
        display_kind("#scarray:  ", LeanScalarArray);
        display_kind("#string:   ", LeanString);
        display_kind("#mpz:      ", LeanMPZ);
        display_kind("#thunk:    ", LeanThunk);
        display_kind("#task:     ", LeanTask);
        display_kind("#promise:  ", LeanPromise);
        display_kind("#ref:      ", LeanRef);
        display_kind("#external: ", LeanExternal);

        size_t num_ctors = 0;
        for (unsigned i = 0; i <= LeanMaxCtorTag; i++)
            num_ctors += g_tag_counters[i];
        std::cout << "#ctors:     " << num_ctors << "\n";
    }
};

tag_counter_manager g_tag_counter_manager;

#endif

void object_compactor::operator()(object * o) {
    lean_assert(m_todo.empty());
    // allocate for root address, see end of function
    // NOTE: we must store an offset instead of the pointer itself as `m_begin` may have been
    //  reallocated in the meantime
    size_t root_offset =
      static_cast<char *>(alloc(sizeof(object_offset))) - static_cast<char *>(m_begin);
    if (!lean_is_scalar(o)) {
        m_todo.push_back(o);
        while (!m_todo.empty()) {
            object * curr = m_todo.back();
            if (m_obj_table.find(curr) != m_obj_table.end()) {
                m_todo.pop_back();
                continue;
            }
            lean_assert(!lean_is_scalar(curr));
            bool r = true;
#ifdef LEAN_TAG_COUNTERS
            g_tag_counters[lean_ptr_tag(curr)]++;
#endif
            switch (lean_ptr_tag(curr)) {
            case LeanClosure:         lean_internal_panic("closures cannot be compacted. One possible cause of this error is trying to store a function in a persistent environment extension.");
            case LeanArray:           r = insert_array(curr); break;
            case LeanScalarArray:     insert_sarray(curr); break;
            case LeanString:          insert_string(curr); break;
            case LeanMPZ:             insert_mpz(curr); break;
            case LeanThunk:           r = insert_thunk(curr); break;
            case LeanTask:            r = insert_task(curr); break;
            case LeanPromise:         r = insert_promise(curr); break;
            case LeanRef:             r = insert_ref(curr); break;
            case LeanExternal:        lean_internal_panic("external objects cannot be compacted");
            case LeanReserved:        lean_unreachable();
            default:                  r = insert_constructor(curr); break;
            }
            if (r) m_todo.pop_back();
        }
        m_tmp.clear();
    }
    object_offset * root = reinterpret_cast<object_offset *>(static_cast<char *>(m_begin) + root_offset);
    *root = to_offset(o);
}

compacted_region::compacted_region(size_t sz, void * data, void * base_addr, bool is_mmap, std::function<void()> free_data):
    m_base_addr(base_addr),
    m_is_mmap(is_mmap),
    m_free_data(free_data),
    m_begin(data),
    m_next(data),
    m_end(static_cast<char*>(data)+sz) {
}

compacted_region::compacted_region(object_compactor const & c):
    m_begin(malloc(c.size())),
    m_next(m_begin),
    m_end(static_cast<char*>(m_begin) + c.size()) {
    memcpy(m_begin, c.data(), c.size());
}

compacted_region::~compacted_region() {
    m_free_data();
}

inline object * compacted_region::fix_object_ptr(object * o) {
    if (lean_is_scalar(o)) return o;
    return reinterpret_cast<object*>(static_cast<char*>(m_begin) + (reinterpret_cast<size_t>(o) - reinterpret_cast<size_t>(m_base_addr)));
}

inline void compacted_region::move(size_t d) {
    lean_assert(m_next < m_end);
    size_t rem = d % sizeof(void*);
    if (rem != 0)
        d = d + sizeof(void*) - rem;
    m_next = static_cast<char*>(m_next) + d;
}

inline void compacted_region::move(object * o) {
    return move(lean_object_byte_size(o));
}

inline void compacted_region::fix_constructor(object * o) {
    lean_assert(!lean_has_rc(o));
    object ** it  = lean_ctor_obj_cptr(o);
    object ** end = it + lean_ctor_num_objs(o);
    for (; it != end; it++) {
        *it = fix_object_ptr(*it);
    }
    lean_assert(lean_object_byte_size(o) < 4192);
    move(o);
}

inline void compacted_region::fix_array(object * o) {
    object ** it  = lean_array_cptr(o);
    object ** end = it + lean_array_size(o);
    for (; it != end; it++) {
        *it = fix_object_ptr(*it);
    }
    move(o);
}

inline void compacted_region::fix_thunk(object * o) {
    lean_to_thunk(o)->m_value = fix_object_ptr(lean_to_thunk(o)->m_value);
    move(sizeof(lean_thunk_object));
}

inline void compacted_region::fix_ref(object * o) {
    lean_to_ref(o)->m_value = fix_object_ptr(lean_to_ref(o)->m_value);
    move(sizeof(lean_ref_object));
}

inline void compacted_region::fix_task(object * o) {
    lean_to_task(o)->m_value = fix_object_ptr(lean_to_task(o)->m_value);
    move(sizeof(lean_task_object));
}

inline void compacted_region::fix_promise(object * o) {
    lean_to_promise(o)->m_result = (lean_task_object *)fix_object_ptr((lean_object *)lean_to_promise(o)->m_result);
    move(sizeof(lean_promise_object));
}

void compacted_region::fix_mpz(object * o) {
#ifdef LEAN_USE_GMP
    __mpz_struct & m = to_mpz(o)->m_value.m_val[0];
    m._mp_d = reinterpret_cast<mp_limb_t *>(static_cast<char *>(m_begin) + reinterpret_cast<size_t>(m._mp_d) - reinterpret_cast<size_t>(m_base_addr));
    move(sizeof(mpz_object) + sizeof(mp_limb_t) * mpz_size(to_mpz(o)->m_value.m_val));
#else
    to_mpz(o)->m_value.m_digits = reinterpret_cast<mpn_digit*>(reinterpret_cast<char*>(o) + sizeof(mpz_object));
    move(sizeof(mpz_object) + sizeof(mpn_digit) * to_mpz(o)->m_value.m_size);
#endif
}

object * compacted_region::read() {
    if (m_next == m_end)
        return nullptr; /* all objects have been read */

    object * root = fix_object_ptr(*static_cast<object_offset *>(m_next));
    move(sizeof(object_offset));
    if (m_begin == m_base_addr) {
        // no relocations needed
        m_end = m_next;
        return root;
    }
    lean_assert(!m_is_mmap);

    while (m_next < m_end) {
        object * curr = reinterpret_cast<object*>(m_next);
        uint8 tag = lean_ptr_tag(curr);
        if (tag <= LeanMaxCtorTag) {
            fix_constructor(curr);
        } else {
            switch (tag) {
            case LeanClosure:         lean_unreachable();
            case LeanArray:           fix_array(curr); break;
            case LeanScalarArray:     move(lean_sarray_byte_size(curr)); break;
            case LeanString:          move(lean_string_byte_size(curr)); break;
            case LeanMPZ:             fix_mpz(curr); break;
            case LeanThunk:           fix_thunk(curr); break;
            case LeanRef:             fix_ref(curr); break;
            case LeanTask:            fix_task(curr); break;
            case LeanPromise:         fix_promise(curr); break;
            case LeanExternal:        lean_unreachable();
            default:                  lean_unreachable();
            }
        }
    }
    return root;
}

extern "C" LEAN_EXPORT uint8 lean_compacted_region_is_memory_mapped(usize region) {
    return reinterpret_cast<compacted_region *>(region)->is_memory_mapped();
}

extern "C" LEAN_EXPORT obj_res lean_compacted_region_free(usize region, object *) {
    delete reinterpret_cast<compacted_region *>(region);
    return lean_io_result_mk_ok(lean_box(0));
}
}
