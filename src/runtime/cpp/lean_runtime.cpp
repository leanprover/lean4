/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/thread.h"
#include "util/buffer.h"
#include "runtime/cpp/lean_runtime.h"

#define LEAN_NUM_OBJ_FREE_LISTS 32

namespace lean {
class obj_pool {
    void * m_free_list[LEAN_NUM_OBJ_FREE_LISTS];
public:
    obj_pool() {
        for (unsigned i = 0; i < LEAN_NUM_OBJ_FREE_LISTS; i++)
            m_free_list[i] = nullptr;
    }

    ~obj_pool() {
        for (unsigned i = 0; i < LEAN_NUM_OBJ_FREE_LISTS; i++) {
            void * lst = m_free_list[i];
            while (lst != nullptr) {
                void * r = lst;
                lst = *(reinterpret_cast<void **>(r));
                free(r);
            }
        }
    }

    void * allocate(unsigned n) {
        if (n < LEAN_NUM_OBJ_FREE_LISTS && m_free_list[n] != nullptr) {
            void * r = m_free_list[n];
            m_free_list[n] = *(reinterpret_cast<void **>(r));
            return r;
        } else {
            return malloc(sizeof(obj_cell) + sizeof(void*)*n); // NOLINT
        }
    }

    void recycle(void * ptr, unsigned n) {
        if (n < LEAN_NUM_OBJ_FREE_LISTS) {
            *(reinterpret_cast<void**>(ptr)) = m_free_list[n];
            m_free_list[n] = ptr;
        } else {
            free(ptr);
        }
    }
};

LEAN_THREAD_PTR(obj_pool, g_obj_pool);

static void finalize_obj_pool(void * p) {
    obj_pool * pool = reinterpret_cast<obj_pool*>(p);
    delete pool;
    g_obj_pool = nullptr;
}

void * alloc_obj(unsigned n) {
    if (!g_obj_pool) {
        g_obj_pool = new obj_pool();
        register_post_thread_finalizer(finalize_obj_pool, g_obj_pool);
    }
    return g_obj_pool->allocate(n);
}

obj_cell::obj_cell(unsigned cidx, unsigned sz, obj const * fs):
    m_rc(0), m_kind(static_cast<unsigned>(obj_kind::Constructor)), m_size(sz), m_cidx(cidx) {
    static_assert(sizeof(obj_cell) % sizeof(void*) == 0); // make sure the hack used to store obj_cell fields satisfies alignment constraints. // NOLINT
    void ** mem = field_addr();
    for (unsigned i = 0; i < sz; i++, mem++)
        new (mem) obj(fs[i]);
}

obj_cell::obj_cell(void * fn, unsigned arity, unsigned sz, obj const * fs):
    m_rc(0), m_kind(static_cast<unsigned>(obj_kind::Closure)), m_size(sz), m_cidx(arity) {
    void ** mem = field_addr();
    for (unsigned i = 0; i < sz; i++, mem++)
        new (mem) obj(fs[i]);
    *fn_ptr_addr() = fn;
}

void obj_cell::copy_fields(obj_cell const & src) {
    obj const * from = src.field_ptr();
    void ** mem = field_addr();
    for (unsigned i = 0; i < src.m_size; i++, from++, mem++)
        new (mem) obj(*from);
}

obj_cell::obj_cell(obj_cell const & src, obj const & a1):
    m_rc(0), m_kind(static_cast<unsigned>(obj_kind::Closure)), m_size(src.m_size+1), m_cidx(src.m_cidx) {
    copy_fields(src);
    void ** f = field_addr();
    new (f + src.m_size) obj(a1);
}

obj_cell::obj_cell(obj_cell const & src, obj const & a1, obj const & a2):
    m_rc(0), m_kind(static_cast<unsigned>(obj_kind::Closure)), m_size(src.m_size+2), m_cidx(src.m_cidx) {
    copy_fields(src);
    void ** f = field_addr();
    new (f + src.m_size)     obj(a1);
    new (f + src.m_size + 1) obj(a2);
}

obj_cell::obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3):
    m_rc(0), m_kind(static_cast<unsigned>(obj_kind::Closure)), m_size(src.m_size+3), m_cidx(src.m_cidx) {
    copy_fields(src);
    void ** f = field_addr();
    new (f + src.m_size)     obj(a1);
    new (f + src.m_size + 1) obj(a2);
    new (f + src.m_size + 2) obj(a3);
}

obj_cell::obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3, obj const & a4):
    m_rc(0), m_kind(static_cast<unsigned>(obj_kind::Closure)), m_size(src.m_size+4), m_cidx(src.m_cidx) {
    copy_fields(src);
    void ** f = field_addr();
    new (f + src.m_size)     obj(a1);
    new (f + src.m_size + 1) obj(a2);
    new (f + src.m_size + 2) obj(a3);
    new (f + src.m_size + 3) obj(a4);
}

obj_cell::obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5):
    m_rc(0), m_kind(static_cast<unsigned>(obj_kind::Closure)), m_size(src.m_size+5), m_cidx(src.m_cidx) {
    copy_fields(src);
    void ** f = field_addr();
    new (f + src.m_size)     obj(a1);
    new (f + src.m_size + 1) obj(a2);
    new (f + src.m_size + 2) obj(a3);
    new (f + src.m_size + 3) obj(a4);
    new (f + src.m_size + 4) obj(a5);
}

obj_cell::obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5,
                   obj const & a6):
    m_rc(0), m_kind(static_cast<unsigned>(obj_kind::Closure)), m_size(src.m_size+6), m_cidx(src.m_cidx) {
    copy_fields(src);
    void ** f = field_addr();
    new (f + src.m_size)     obj(a1);
    new (f + src.m_size + 1) obj(a2);
    new (f + src.m_size + 2) obj(a3);
    new (f + src.m_size + 3) obj(a4);
    new (f + src.m_size + 4) obj(a5);
    new (f + src.m_size + 5) obj(a6);
}

obj_cell::obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5,
                   obj const & a6, obj const & a7):
    m_rc(0), m_kind(static_cast<unsigned>(obj_kind::Closure)), m_size(src.m_size+7), m_cidx(src.m_cidx) {
    copy_fields(src);
    void ** f = field_addr();
    new (f + src.m_size)     obj(a1);
    new (f + src.m_size + 1) obj(a2);
    new (f + src.m_size + 2) obj(a3);
    new (f + src.m_size + 3) obj(a4);
    new (f + src.m_size + 4) obj(a5);
    new (f + src.m_size + 5) obj(a6);
    new (f + src.m_size + 6) obj(a7);
}

obj_cell::obj_cell(obj_cell const & src, obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5,
                   obj const & a6, obj const & a7, obj const & a8):
    m_rc(0), m_kind(static_cast<unsigned>(obj_kind::Closure)), m_size(src.m_size+8), m_cidx(src.m_cidx) {
    copy_fields(src);
    void ** f = field_addr();
    new (f + src.m_size)     obj(a1);
    new (f + src.m_size + 1) obj(a2);
    new (f + src.m_size + 2) obj(a3);
    new (f + src.m_size + 3) obj(a4);
    new (f + src.m_size + 4) obj(a5);
    new (f + src.m_size + 5) obj(a6);
    new (f + src.m_size + 6) obj(a7);
    new (f + src.m_size + 7) obj(a8);
}

#define DEC_FIELDS(o, todo) {                                   \
void ** f = o->field_addr();                                    \
for (unsigned i = 0; i < o->m_size; i++, f++) {                 \
    obj_cell * c = reinterpret_cast<obj*>(f)->steal_ptr();      \
    if (LEAN_IS_PTR(c) && c->dec_ref_core())                    \
        todo.push_back(c);                                      \
}                                                               \
}

void obj_cell::dealloc() {
    try {
        buffer<obj_cell*> todo;
        todo.push_back(this);
        while (!todo.empty()) {
            obj_cell * it = todo.back();
            unsigned sz   = it->m_size;
            todo.pop_back();
            switch (it->kind()) {
            case obj_kind::Constructor:
                DEC_FIELDS(it, todo);
                it->~obj_cell();
                g_obj_pool->recycle(it, sz);
                break;
            case obj_kind::Closure:
                DEC_FIELDS(it, todo);
                it->~obj_cell();
                g_obj_pool->recycle(it, sz+1);
                break;
            case obj_kind::MPN:
                // TODO(Leo):
                break;
            }
        }
    } catch (std::bad_alloc&) {
        // We need this catch, because push_back may fail when expanding the buffer.
        // In this case, we avoid the crash, and "accept" the memory leak.
    }
}

obj mk_obj(unsigned cidx, unsigned n, obj const * fs) {
    void * mem = alloc_obj(n);
    return obj(new (mem) obj_cell(cidx, n, fs));
}

obj mk_closure_core(void * fn, unsigned arity, unsigned n, obj const * fs) {
    void * mem = alloc_obj(n+1);
    return obj(new (mem) obj_cell(fn, arity, n, fs));
}

static obj mk_closure(obj const & f, obj const & a1) {
    void * mem = alloc_obj(f.size()+1);
    return obj(new (mem) obj_cell(f.data(), a1));
}

static obj mk_closure(obj const & f, obj const & a1, obj const & a2) {
    void * mem = alloc_obj(f.size()+2);
    return obj(new (mem) obj_cell(f.data(), a1, a2));
}

static obj mk_closure(obj const & f, obj const & a1, obj const & a2, obj const & a3) {
    void * mem = alloc_obj(f.size()+3);
    return obj(new (mem) obj_cell(f.data(), a1, a2, a3));
}

static obj mk_closure(obj const & f, obj const & a1, obj const & a2, obj const & a3, obj const & a4) {
    void * mem = alloc_obj(f.size()+4);
    return obj(new (mem) obj_cell(f.data(), a1, a2, a3, a4));
}

static obj mk_closure(obj const & f, obj const & a1, obj const & a2, obj const & a3, obj const & a4,
                      obj const & a5) {
    void * mem = alloc_obj(f.size()+5);
    return obj(new (mem) obj_cell(f.data(), a1, a2, a3, a4, a5));
}

static obj mk_closure(obj const & f, obj const & a1, obj const & a2, obj const & a3, obj const & a4,
                      obj const & a5, obj const & a6) {
    void * mem = alloc_obj(f.size()+6);
    return obj(new (mem) obj_cell(f.data(), a1, a2, a3, a4, a5, a6));
}

static obj mk_closure(obj const & f, obj const & a1, obj const & a2, obj const & a3, obj const & a4,
                      obj const & a5, obj const & a6, obj const & a7) {
    void * mem = alloc_obj(f.size()+7);
    return obj(new (mem) obj_cell(f.data(), a1, a2, a3, a4, a5, a6, a7));
}

static obj mk_closure(obj const & f, obj const & a1, obj const & a2, obj const & a3, obj const & a4,
                      obj const & a5, obj const & a6, obj const & a7, obj const & a8) {
    void * mem = alloc_obj(f.size()+8);
    return obj(new (mem) obj_cell(f.data(), a1, a2, a3, a4, a5, a6, a7, a8));
}

typedef obj (*fn1)(obj const &);
typedef obj (*fn2)(obj const &, obj const &);
typedef obj (*fn3)(obj const &, obj const &, obj const &);
typedef obj (*fn4)(obj const &, obj const &, obj const &, obj const &);
typedef obj (*fn5)(obj const &, obj const &, obj const &, obj const &, obj const &);
typedef obj (*fn6)(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &);
typedef obj (*fn7)(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                   obj const &);
typedef obj (*fn8)(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                   obj const &, obj const &);
typedef obj (*fn9)(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                   obj const &, obj const &, obj const &);
typedef obj (*fn10)(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                    obj const &, obj const &, obj const &, obj const &);
typedef obj (*fn11)(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                    obj const &, obj const &, obj const &, obj const &, obj const &);
typedef obj (*fn12)(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                    obj const &, obj const &, obj const &, obj const &, obj const &, obj const &);
typedef obj (*fn13)(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                    obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                    obj const &);
typedef obj (*fn14)(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                    obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                    obj const &, obj const &);
typedef obj (*fn15)(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                    obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                    obj const &, obj const &, obj const &);
typedef obj (*fn16)(obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                    obj const &, obj const &, obj const &, obj const &, obj const &, obj const &,
                    obj const &, obj const &, obj const &, obj const &);
typedef obj (*fnN)(unsigned, obj const *);

inline fn1 to_fn1(obj const & o) { return reinterpret_cast<fn1>(o.fn_ptr()); }
inline fn2 to_fn2(obj const & o) { return reinterpret_cast<fn2>(o.fn_ptr()); }
inline fn3 to_fn3(obj const & o) { return reinterpret_cast<fn3>(o.fn_ptr()); }
inline fn4 to_fn4(obj const & o) { return reinterpret_cast<fn4>(o.fn_ptr()); }
inline fn5 to_fn5(obj const & o) { return reinterpret_cast<fn5>(o.fn_ptr()); }
inline fn6 to_fn6(obj const & o) { return reinterpret_cast<fn6>(o.fn_ptr()); }
inline fn7 to_fn7(obj const & o) { return reinterpret_cast<fn7>(o.fn_ptr()); }
inline fn8 to_fn8(obj const & o) { return reinterpret_cast<fn8>(o.fn_ptr()); }
inline fnN to_fnN(obj const & o) { return reinterpret_cast<fnN>(o.fn_ptr()); }

#define FN1 to_fn1(*this)
#define FN2 to_fn2(*this)
#define FN3 to_fn3(*this)
#define FN4 to_fn4(*this)
#define FN5 to_fn5(*this)
#define FN6 to_fn6(*this)
#define FN7 to_fn7(*this)
#define FN8 to_fn8(*this)
#define FNN to_fnN(*this)

obj obj::apply() const {
    unsigned ar = arity();
    if (ar == size()) {
        switch (ar) {
        case 1:  return FN1(fld(0));
        case 2:  return FN2(fld(0), fld(1));
        case 3:  return FN3(fld(0), fld(1), fld(2));
        case 4:  return FN4(fld(0), fld(1), fld(2), fld(3));
        case 5:  return FN5(fld(0), fld(1), fld(2), fld(3), fld(4));
        case 6:  return FN6(fld(0), fld(1), fld(2), fld(3), fld(4), fld(5));
        case 7:  return FN7(fld(0), fld(1), fld(2), fld(3), fld(4), fld(5), fld(6));
        case 8:  return FN8(fld(0), fld(1), fld(2), fld(3), fld(4), fld(5), fld(6), fld(7));
        default: return FNN(ar, m_data->field_ptr());
        }
    } else {
        return *this;
    }
}

obj obj::apply(obj const & a1) const {
    unsigned ar = arity();
    if (ar == size() + 1) {
        switch (ar) {
        case 1:  return FN1(a1);
        case 2:  return FN2(fld(0), a1);
        case 3:  return FN3(fld(0), fld(1), a1);
        case 4:  return FN4(fld(0), fld(1), fld(2), a1);
        case 5:  return FN5(fld(0), fld(1), fld(2), fld(3), a1);
        case 6:  return FN6(fld(0), fld(1), fld(2), fld(3), fld(4), a1);
        case 7:  return FN7(fld(0), fld(1), fld(2), fld(3), fld(4), fld(5), a1);
        case 8:  return FN8(fld(0), fld(1), fld(2), fld(3), fld(4), fld(5), fld(6), a1);
        default: return mk_closure(*this, a1).apply();
        }
    } else {
        return mk_closure(*this, a1);
    }
}

obj obj::apply(obj const & a1, obj const & a2) const {
    unsigned ar = arity();
    if (ar == size() + 2) {
        switch (ar) {
        case 2:  return FN2(a1, a2);
        case 3:  return FN3(fld(0), a1, a2);
        case 4:  return FN4(fld(0), fld(1), a1, a2);
        case 5:  return FN5(fld(0), fld(1), fld(2), a1, a2);
        case 6:  return FN6(fld(0), fld(1), fld(2), fld(3), a1, a2);
        case 7:  return FN7(fld(0), fld(1), fld(2), fld(3), fld(4), a1, a2);
        case 8:  return FN8(fld(0), fld(1), fld(2), fld(3), fld(4), fld(5), a1, a2);
        default: return mk_closure(*this, a1, a2).apply();
        }
    } else {
        return mk_closure(*this, a1, a2);
    }
}

obj obj::apply(obj const & a1, obj const & a2, obj const & a3) const {
    unsigned ar = arity();
    if (ar == size() + 3) {
        switch (ar) {
        case 3:  return FN3(a1, a2, a3);
        case 4:  return FN4(fld(0), a1, a2, a3);
        case 5:  return FN5(fld(0), fld(1), a1, a2, a3);
        case 6:  return FN6(fld(0), fld(1), fld(2), a1, a2, a3);
        case 7:  return FN7(fld(0), fld(1), fld(2), fld(3), a1, a2, a3);
        case 8:  return FN8(fld(0), fld(1), fld(2), fld(3), fld(4), a1, a2, a3);
        default: return mk_closure(*this, a1, a2, a3).apply();
        }
    } else {
        return mk_closure(*this, a1, a2, a3);
    }
}

obj obj::apply(obj const & a1, obj const & a2, obj const & a3, obj const & a4) const {
    unsigned ar = arity();
    if (ar == size() + 4) {
        switch (ar) {
        case 4:  return FN4(a1, a2, a3, a4);
        case 5:  return FN5(fld(0), a1, a2, a3, a4);
        case 6:  return FN6(fld(0), fld(1), a1, a2, a3, a4);
        case 7:  return FN7(fld(0), fld(1), fld(2), a1, a2, a3, a4);
        case 8:  return FN8(fld(0), fld(1), fld(2), fld(3), a1, a2, a3, a4);
        default: return mk_closure(*this, a1, a2, a3, a4).apply();
        }
    } else {
        return mk_closure(*this, a1, a2, a3, a4);
    }
}

obj obj::apply(obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5) const {
    unsigned ar = arity();
    if (ar == size() + 5) {
        switch (ar) {
        case 5:  return FN5(a1, a2, a3, a4, a5);
        case 6:  return FN6(fld(0), a1, a2, a3, a4, a5);
        case 7:  return FN7(fld(0), fld(1), a1, a2, a3, a4, a5);
        case 8:  return FN8(fld(0), fld(1), fld(2), a1, a2, a3, a4, a5);
        default: return mk_closure(*this, a1, a2, a3, a4, a5).apply();
        }
    } else {
        return mk_closure(*this, a1, a2, a3, a4, a5);
    }
}

obj obj::apply(obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5, obj const & a6) const {
    unsigned ar = arity();
    if (ar == size() + 6) {
        switch (ar) {
        case 6:  return FN6(a1, a2, a3, a4, a5, a6);
        case 7:  return FN7(fld(0), a1, a2, a3, a4, a5, a6);
        case 8:  return FN8(fld(0), fld(1), a1, a2, a3, a4, a5, a6);
        default: return mk_closure(*this, a1, a2, a3, a4, a5, a6).apply();
        }
    } else {
        return mk_closure(*this, a1, a2, a3, a4, a5, a6);
    }
}

obj obj::apply(obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5, obj const & a6,
               obj const & a7) const {
    unsigned ar = arity();
    if (ar == size() + 7) {
        switch (ar) {
        case 7:  return FN7(a1, a2, a3, a4, a5, a6, a7);
        case 8:  return FN8(fld(0), a1, a2, a3, a4, a5, a6, a7);
        default: return mk_closure(*this, a1, a2, a3, a4, a5, a6, a7).apply();
        }
    } else {
        return mk_closure(*this, a1, a2, a3, a4, a5, a6, a7);
    }
}

obj obj::apply(obj const & a1, obj const & a2, obj const & a3, obj const & a4, obj const & a5, obj const & a6,
               obj const & a7, obj const & a8) const {
    unsigned ar = arity();
    if (ar == size() + 8) {
        switch (ar) {
        case 8:  return FN8(a1, a2, a3, a4, a5, a6, a7, a8);
        default: return mk_closure(*this, a1, a2, a3, a4, a5, a6, a7, a8).apply();
        }
    } else {
        return mk_closure(*this, a1, a2, a3, a4, a5, a6, a7, a8);
    }
}
}
