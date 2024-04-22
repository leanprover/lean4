/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <lean/lean.h>
#include "runtime/thread.h"
#include "runtime/debug.h"
#include "runtime/alloc.h"

#ifdef LEAN_RUNTIME_STATS
#define LEAN_RUNTIME_STAT_CODE(c) c
#else
#define LEAN_RUNTIME_STAT_CODE(c)
#endif

#if defined(__GNUC__) || defined(__clang__)
#define LEAN_NOINLINE __attribute__((noinline))
#else
#define LEAN_NOINLINE
#endif

#define LEAN_PAGE_SIZE             8192        // 8 Kb
#define LEAN_SEGMENT_SIZE          8*1024*1024 // 8 Mb
#define LEAN_NUM_SLOTS             (LEAN_MAX_SMALL_OBJECT_SIZE / LEAN_OBJECT_SIZE_DELTA)
#define LEAN_MAX_TO_EXPORT_OBJS    1024

LEAN_CASSERT(LEAN_PAGE_SIZE > LEAN_MAX_SMALL_OBJECT_SIZE);
LEAN_CASSERT(LEAN_SEGMENT_SIZE > LEAN_PAGE_SIZE);

namespace lean {

#ifdef LEAN_SMALL_ALLOCATOR

namespace allocator {
#ifdef LEAN_RUNTIME_STATS
static atomic<uint64> g_num_alloc(0);
static atomic<uint64> g_num_small_alloc(0);
static atomic<uint64> g_num_dealloc(0);
static atomic<uint64> g_num_small_dealloc(0);
static atomic<uint64> g_num_segments(0);
static atomic<uint64> g_num_pages(0);
static atomic<uint64> g_num_exports(0);
static atomic<uint64> g_num_recycled_pages(0);
struct alloc_stats {
    ~alloc_stats() {
        std::cerr << "num. alloc.:         " << g_num_alloc << "\n";
        std::cerr << "num. small alloc.:   " << g_num_small_alloc << "\n";
        std::cerr << "num. dealloc.:       " << g_num_dealloc << "\n";
        std::cerr << "num. small dealloc.: " << g_num_small_dealloc << "\n";
        std::cerr << "num. segments:       " << g_num_segments << "\n";
        std::cerr << "num. pages:          " << g_num_pages << "\n";
        std::cerr << "num. recycled pages: " << g_num_recycled_pages << "\n";
        std::cerr << "num. exports:        " << g_num_exports << "\n";
    }
};
static alloc_stats g_alloc_stats;
#endif

struct heap;
struct page;
struct page_header {
    atomic<heap *>   m_heap;
    page *           m_next;
    page *           m_prev;
    void *           m_free_list;
    unsigned         m_obj_size;
    unsigned         m_max_free;
    unsigned         m_num_free;
    unsigned         m_slot_idx;
    bool             m_in_page_free_list;
};

struct page {
    page_header m_header;
    char        m_data[LEAN_PAGE_SIZE - sizeof(page_header)];
    page * get_next() const { return m_header.m_next; }
    page * get_prev() const { return m_header.m_prev; }
    void set_next(page * n) { m_header.m_next = n; }
    void set_prev(page * p) { m_header.m_prev = p; }
    void set_heap(heap * h) { m_header.m_heap = h; }
    heap * get_heap() { return m_header.m_heap; }
    bool has_many_free() const { return m_header.m_num_free > m_header.m_max_free / 4; }
    bool in_page_free_list() const { return m_header.m_in_page_free_list; }
    unsigned get_slot_idx() const { return m_header.m_slot_idx; }
    void push_free_obj(void * o);
};

inline char * align_ptr(char * p, size_t a) {
    return reinterpret_cast<char*>(lean_align(reinterpret_cast<size_t>(p), a));
}

struct segment {
    segment *    m_next{nullptr};
    char *       m_next_page_mem;
    char         m_data[LEAN_SEGMENT_SIZE];

    char * get_first_page_mem() {
        lean_assert(align_ptr(m_data, LEAN_PAGE_SIZE) >= m_data);
        lean_assert(align_ptr(m_data, LEAN_PAGE_SIZE) > reinterpret_cast<char*>(this));
        return align_ptr(m_data, LEAN_PAGE_SIZE);
    }

    segment() {
        m_next_page_mem = get_first_page_mem();
    }

    bool is_full() const {
        return m_next_page_mem + LEAN_PAGE_SIZE > m_data + LEAN_SEGMENT_SIZE;
    }
};

struct heap {
    segment * m_curr_segment{nullptr};
    heap *    m_next_orphan{nullptr};
    page *    m_curr_page[LEAN_NUM_SLOTS];
    page *    m_page_free_list[LEAN_NUM_SLOTS];
    /* Objects that must be sent to other heaps. */
    void *    m_to_export_list{nullptr};
    unsigned  m_to_export_list_size{0};
    mutex     m_mutex; /* for the following fields */
    /* The following list contains object by this heap that were deallocated
       by other heaps. */
    void *    m_to_import_list{nullptr};
    uint64_t  m_heartbeat{0}; /* Counter for implementing "deterministic timeouts". It is currently the number of small allocations */
    void import_objs();
    void export_objs();
    void alloc_segment();
};

struct heap_manager {
    /* The mutex protects the list of orphan segments. */
    mutex             m_mutex;
    heap *            m_orphans{nullptr};

    void push_orphan(heap * h) {
        /* TODO(Leo): avoid mutex */
        lock_guard<mutex> lock(m_mutex);
        h->m_next_orphan = m_orphans;
        m_orphans = h;
    }

    heap * pop_orphan() {
        /* TODO(Leo): avoid mutex */
        lock_guard<mutex> lock(m_mutex);
        if (m_orphans) {
            heap * h = m_orphans;
            m_orphans = h->m_next_orphan;
            return h;
        } else {
            return nullptr;
        }
    }
};

static inline page * get_page_of(void * o) {
    return reinterpret_cast<page*>((reinterpret_cast<size_t>(o)/LEAN_PAGE_SIZE)*LEAN_PAGE_SIZE);
}

LEAN_THREAD_GLOBAL_PTR(page *, g_curr_pages);
LEAN_THREAD_PTR(heap, g_heap);
static heap_manager * g_heap_manager = nullptr;

inline void set_next_obj(void * obj, void * next) {
    *reinterpret_cast<void**>(obj) = next;
}

inline void * get_next_obj(void * obj) {
    return *reinterpret_cast<void**>(obj);
}

static inline void page_list_insert(page * & head, page * new_head) {
    if (head)
        head->set_prev(new_head);
    new_head->set_next(head);
    head = new_head;
}

static inline void page_list_remove(page * & head, page * to_remove) {
    if (head == to_remove) {
        /* First element */
        head = to_remove->get_next();
    }
    page * prev = to_remove->get_prev();
    lean_assert(prev);
    if (page * next = to_remove->get_next()) {
        prev->set_next(next);
        next->set_prev(prev);
    } else {
        /* Last element */
        prev->set_next(nullptr);
    }
}

static inline page * page_list_pop(page * & head) {
    lean_assert(head);
    page * r = head;
    head = head->get_next();
    return r;
}

void page::push_free_obj(void * o) {
    lean_assert(get_page_of(o) == this);
    set_next_obj(o, m_header.m_free_list);
    m_header.m_free_list = o;
    m_header.m_num_free++;
    if (!in_page_free_list() && has_many_free()) {
        heap * h = get_heap();
        unsigned slot_idx = m_header.m_slot_idx;
        if (this != h->m_curr_page[slot_idx]) {
            LEAN_RUNTIME_STAT_CODE(g_num_recycled_pages++);
            m_header.m_in_page_free_list = true;
            page_list_remove(h->m_curr_page[slot_idx], this);
            page_list_insert(h->m_page_free_list[slot_idx], this);
        }
    }
}

void heap::import_objs() {
    void * to_import = nullptr;
    {   // TODO(Leo): avoid mutex using compare and swap
        lock_guard<mutex> lock(m_mutex);
        to_import = m_to_import_list;
        m_to_import_list = nullptr;
    }
    while (to_import) {
        page * p = get_page_of(to_import);
        void * n = get_next_obj(to_import);
        p->push_free_obj(to_import);
        to_import = n;
    }
}

struct export_entry {
    heap * m_heap;
    void * m_head;
    void * m_tail;
};

void heap::export_objs() {
    std::vector<export_entry> to_export;
    void * o = m_to_export_list;
    while (o != nullptr) {
        void * n   = get_next_obj(o);
        heap * h   = get_page_of(o)->get_heap();
        bool found = false;
        for (export_entry & e : to_export) {
            if (e.m_heap == h) {
                set_next_obj(o, e.m_head);
                e.m_head = o;
                found = true;
                break;
            }
        }
        if (!found) {
            set_next_obj(o, nullptr);
            to_export.push_back(export_entry{h, o, o});
        }
        o = n;
    }
    m_to_export_list      = nullptr;
    m_to_export_list_size = 0;
    for (export_entry const & e : to_export) {
        unique_lock<mutex> lock(e.m_heap->m_mutex);
        set_next_obj(e.m_tail, e.m_heap->m_to_import_list);
        e.m_heap->m_to_import_list = e.m_head;
    }
}

void heap::alloc_segment() {
    LEAN_RUNTIME_STAT_CODE(g_num_segments++);
    segment * s = new segment();
    s->m_next   = m_curr_segment;
    m_curr_segment = s;
}

static page * alloc_page(heap * h, unsigned obj_size) {
    lean_assert(lean_align(obj_size, LEAN_OBJECT_SIZE_DELTA) == obj_size);
    segment * s = h->m_curr_segment;
    LEAN_RUNTIME_STAT_CODE(g_num_pages++);
    page * p    = new (s->m_next_page_mem) page();
    s->m_next_page_mem += LEAN_PAGE_SIZE;
    if (s->is_full()) {
        /* s is full, we need to allocate a new one. */
        h->alloc_segment();
    }
    unsigned slot_idx        = lean_get_slot_idx(obj_size);
    p->m_header.m_heap       = h;
    page_list_insert(h->m_curr_page[slot_idx], p);
    p->m_header.m_slot_idx   = slot_idx;
    p->m_header.m_obj_size   = obj_size;
    char * curr_free         = p->m_data;
    set_next_obj(curr_free, nullptr);
    char * end               = p->m_data + (LEAN_PAGE_SIZE - sizeof(page_header));
    unsigned num_free        = 1;
    char * next_free         = curr_free + obj_size;
    while (true) {
        if (next_free + obj_size > end)
            break; /* next object doesn't fit */
        lean_assert(get_page_of(curr_free) == p);
        set_next_obj(next_free, curr_free);
        curr_free = next_free;
        next_free = next_free + obj_size;
        num_free++;
    }
#ifdef LEAN_DEBUG
            void * it  = curr_free;
            unsigned n = 0;
            while (it != nullptr) {
                it = get_next_obj(it);
                n++;
            }
            lean_assert(n == num_free);
#endif
    p->m_header.m_free_list  = curr_free;
    p->m_header.m_max_free   = num_free;
    p->m_header.m_num_free   = num_free;
    p->m_header.m_in_page_free_list = false;
    return p;
}

static void finalize_heap(void * _h) {
    heap * h = static_cast<heap*>(_h);
    h->export_objs();
    h->import_objs();
    g_heap_manager->push_orphan(h);
}

LEAN_NOINLINE
static void init_heap(bool main) {
    lean_assert(g_heap == nullptr);
    if (heap * h = g_heap_manager->pop_orphan()) {
        /* reuse orphan heap */
        g_heap = h;
    } else {
        g_heap = new heap();
        g_curr_pages = g_heap->m_curr_page;
        for (unsigned i = 0; i < LEAN_NUM_SLOTS; i++) {
            g_heap->m_curr_page[i] = nullptr;
            g_heap->m_page_free_list[i] = nullptr;
        }
        g_heap->alloc_segment();
        unsigned obj_size = LEAN_OBJECT_SIZE_DELTA;
        for (unsigned i = 0; i < LEAN_NUM_SLOTS; i++) {
            if (g_heap->m_curr_page[i] == nullptr) {
                alloc_page(g_heap, obj_size);
            }
            obj_size += LEAN_OBJECT_SIZE_DELTA;
        }
    }
    if (!main)
        register_thread_finalizer(finalize_heap, g_heap);
}
}
using namespace allocator; // NOLINT

void init_thread_heap() {
    init_heap(false);
}

LEAN_NOINLINE
void * lean_alloc_small_cold(unsigned sz, unsigned slot_idx, page * p) {
    if (g_heap->m_page_free_list[slot_idx] == nullptr) {
        g_heap->import_objs();
        lean_assert(g_heap->m_curr_page[slot_idx] == p);
        /* g_heap->import_objs() may add objects to p->m_header.m_free_list */
        if (p->m_header.m_free_list == nullptr)
            p = alloc_page(g_heap, sz);
    } else {
        p = page_list_pop(g_heap->m_page_free_list[slot_idx]);
        p->m_header.m_in_page_free_list = false;
        page_list_insert(g_heap->m_curr_page[slot_idx], p);
    }
    void * r = p->m_header.m_free_list;
    lean_assert(r);
    p->m_header.m_free_list = get_next_obj(r);
    p->m_header.m_num_free--;
    lean_assert(get_page_of(r) == p);
    return r;
}

extern "C" LEAN_EXPORT void * lean_alloc_small(unsigned sz, unsigned slot_idx) {
    page * p = g_heap->m_curr_page[slot_idx];
    g_heap->m_heartbeat++;
    void * r = p->m_header.m_free_list;
    if (LEAN_UNLIKELY(r == nullptr)) {
        return lean_alloc_small_cold(sz, slot_idx, p);
    }
    p->m_header.m_free_list = get_next_obj(r);
    p->m_header.m_num_free--;
    lean_assert(get_page_of(r) == p);
    return r;
}

void * alloc(size_t sz) {
    sz = lean_align(sz, LEAN_OBJECT_SIZE_DELTA);
    LEAN_RUNTIME_STAT_CODE(g_num_alloc++);
    if (LEAN_UNLIKELY(sz > LEAN_MAX_SMALL_OBJECT_SIZE)) {
        void * r = malloc(sz);
        if (r == nullptr) lean_internal_panic_out_of_memory();
        return r;
    }
    lean_assert(g_heap);
    LEAN_RUNTIME_STAT_CODE(g_num_small_alloc++);
    unsigned slot_idx = lean_get_slot_idx(sz);
    return lean_alloc_small(sz, slot_idx);
}

LEAN_NOINLINE
static void dealloc_small_core_cold(void * o) {
    set_next_obj(o, g_heap->m_to_export_list);
    g_heap->m_to_export_list = o;
    g_heap->m_to_export_list_size++;
    if (g_heap->m_to_export_list_size > LEAN_MAX_TO_EXPORT_OBJS) {
        LEAN_RUNTIME_STAT_CODE(g_num_exports++);
        g_heap->export_objs();
    }
}

static inline void dealloc_small_core(void * o) {
    LEAN_RUNTIME_STAT_CODE(g_num_small_dealloc++);
    if (LEAN_UNLIKELY(g_heap == nullptr)) {
        init_heap(false);
    }
    lean_assert(g_heap);
    page * p = get_page_of(o);
    if (LEAN_LIKELY(p->get_heap() == g_heap)) {
        p->push_free_obj(o);
    } else {
        dealloc_small_core_cold(o);
    }
}

void dealloc(void * o, size_t sz) {
    LEAN_RUNTIME_STAT_CODE(g_num_dealloc++);
    sz = lean_align(sz, LEAN_OBJECT_SIZE_DELTA);
    if (LEAN_UNLIKELY(sz > LEAN_MAX_SMALL_OBJECT_SIZE)) {
        return free(o);
    }
    dealloc_small_core(o);
}

extern "C" LEAN_EXPORT void lean_free_small(void * o) {
    dealloc_small_core(o);
}

extern "C" LEAN_EXPORT unsigned lean_small_mem_size(void * o) {
    page * p = get_page_of(o);
    return p->m_header.m_obj_size;
}

#endif

void initialize_alloc() {
#ifdef LEAN_SMALL_ALLOCATOR
    g_heap_manager = new heap_manager();
    init_heap(true);
#endif
}

void finalize_alloc() {
}

#ifndef LEAN_SMALL_ALLOCATOR
LEAN_THREAD_VALUE(uint64_t, g_heartbeat, 0);
#endif

/* Helper function for increasing heartbeat even when LEAN_SMALL_ALLOCATOR is not defined */
extern "C" LEAN_EXPORT void lean_inc_heartbeat() {
#ifdef LEAN_SMALL_ALLOCATOR
    if (g_heap)
        g_heap->m_heartbeat++;
#else
    g_heartbeat++;
#endif
}

uint64_t get_num_heartbeats() {
#ifdef LEAN_SMALL_ALLOCATOR
    if (g_heap)
        return g_heap->m_heartbeat;
    else
        return 0;
#else
    return g_heartbeat;
#endif
}

}
