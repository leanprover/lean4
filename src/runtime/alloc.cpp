/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "runtime/thread.h"
#include "runtime/debug.h"
#include "runtime/compiler_hints.h"
#include "runtime/object.h"
#include "runtime/alloc.h"

#define LEAN_SEGMENT_SIZE          8*1024*1024 // 8 Mb
#define LEAN_NUM_SLOTS             (LEAN_MAX_SMALL_OBJECT_SIZE / LEAN_OBJECT_SIZE_DELTA)
#define LEAN_MAX_TO_EXPORT_OBJS    1024

namespace lean {
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

    void move_to_heap(heap *);
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

void segment::move_to_heap(heap * h) {
    /* "Move" pages in `s` to this heap */
    page * it  = reinterpret_cast<page*>(get_first_page_mem());
    page * end = reinterpret_cast<page*>(m_next_page_mem);
    for (; it != end; ++it) {
        page & p    = *it;
        p.set_heap(h);
        unsigned slot_idx = p.get_slot_idx();
        if (p.in_page_free_list()) {
            page_list_insert(h->m_page_free_list[slot_idx], &p);
        } else {
            page_list_insert(h->m_curr_page[slot_idx], &p);
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
        lean_assert(h != this);
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
    if (heap * h = g_heap_manager->pop_orphan()) {
        lean_assert(h->m_curr_segment);
        segment * s = h->m_curr_segment;
        h->m_curr_segment = s->m_next;
        s->move_to_heap(this);
        h->import_objs();
        if (h->m_curr_segment != nullptr) {
            g_heap_manager->push_orphan(h);
        } else {
            delete h;
        }
        s->m_next      = m_curr_segment;
        m_curr_segment = s;
    } else {
        LEAN_RUNTIME_STAT_CODE(g_num_segments++);
        segment * s = new segment();
        s->m_next   = m_curr_segment;
        m_curr_segment = s;
    }
}

static page * alloc_page(heap * h, unsigned obj_size) {
    lean_assert(align(obj_size, LEAN_OBJECT_SIZE_DELTA) == obj_size);
    segment * s = h->m_curr_segment;
    LEAN_RUNTIME_STAT_CODE(g_num_pages++);
    page * p    = new (s->m_next_page_mem) page();
    s->m_next_page_mem += LEAN_PAGE_SIZE;
    if (s->m_next_page_mem + LEAN_PAGE_SIZE > s->m_data + LEAN_SEGMENT_SIZE) {
        /* s is full, we need to allocate a new one. */
        h->alloc_segment();
    }
    unsigned slot_idx        = get_slot_idx(obj_size);
    p->m_header.m_heap       = h;
    page_list_insert(h->m_curr_page[slot_idx], p);
    p->m_header.m_slot_idx   = slot_idx;
    char * curr_free         = p->m_data;
    set_next_obj(curr_free, nullptr);
    char * end               = p->m_data + LEAN_PAGE_SIZE - sizeof(page_header);
    unsigned num_free        = 1;
    char * next_free         = curr_free + obj_size;
    while (true) {
        if (next_free + obj_size > end)
            break; /* next object doesn't fit */
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

static void init_heap(bool main) {
    lean_assert(g_heap == nullptr);
    g_heap = new heap();
    g_curr_pages = g_heap->m_curr_page;
    g_heap->alloc_segment();
    unsigned obj_size = LEAN_OBJECT_SIZE_DELTA;
    for (unsigned i = 0; i < LEAN_NUM_SLOTS; i++) {
        g_heap->m_curr_page[i] = nullptr;
        alloc_page(g_heap, obj_size);
        g_heap->m_page_free_list[i] = nullptr;
        obj_size += LEAN_OBJECT_SIZE_DELTA;
    }
    if (!main)
        register_thread_finalizer(finalize_heap, g_heap);
}
}
using namespace allocator;

void init_thread_heap() {
    init_heap(false);
}

void * alloc(size_t sz) {
    sz = align(sz, LEAN_OBJECT_SIZE_DELTA);
    LEAN_RUNTIME_STAT_CODE(g_num_alloc++);
    if (LEAN_UNLIKELY(sz > LEAN_MAX_SMALL_OBJECT_SIZE)) {
        void * r = malloc(sz);
        if (r == nullptr) throw std::bad_alloc();
        return r;
    }
    lean_assert(g_heap);
    LEAN_RUNTIME_STAT_CODE(g_num_small_alloc++);
    unsigned slot_idx = get_slot_idx(sz);
    page * p = g_heap->m_curr_page[slot_idx];
    void * r = p->m_header.m_free_list;
    if (LEAN_UNLIKELY(r == nullptr)) {
        if (g_heap->m_page_free_list[slot_idx] == nullptr) {
            g_heap->import_objs();
            p = alloc_page(g_heap, sz);
        } else {
            p = page_list_pop(g_heap->m_page_free_list[slot_idx]);
            p->m_header.m_in_page_free_list = false;
            page_list_insert(g_heap->m_curr_page[slot_idx], p);
        }
        r = p->m_header.m_free_list;
        lean_assert(r);
    }
    p->m_header.m_free_list = get_next_obj(r);
    p->m_header.m_num_free--;
    return r;
}

void dealloc(void * o, size_t sz) {
    LEAN_RUNTIME_STAT_CODE(g_num_dealloc++);
    sz = align(sz, LEAN_OBJECT_SIZE_DELTA);
    if (LEAN_UNLIKELY(sz > LEAN_MAX_SMALL_OBJECT_SIZE)) {
        return free(o);
    }
    LEAN_RUNTIME_STAT_CODE(g_num_small_dealloc++);
    if (LEAN_UNLIKELY(g_heap == nullptr)) {
        init_heap(false);
    }
    lean_assert(g_heap);
    page * p = get_page_of(o);
    if (LEAN_LIKELY(p->get_heap() == g_heap)) {
        p->push_free_obj(o);
    } else {
        set_next_obj(o, g_heap->m_to_export_list);
        g_heap->m_to_export_list = o;
        g_heap->m_to_export_list_size++;
        if (g_heap->m_to_export_list_size > LEAN_MAX_TO_EXPORT_OBJS) {
            LEAN_RUNTIME_STAT_CODE(g_num_exports++);
            g_heap->export_objs();
        }
    }
}

void * alloc_small_slow(size_t sz, unsigned slot_idx) {
    page * p = g_heap->m_curr_page[slot_idx];
    if (g_heap->m_page_free_list[slot_idx] == nullptr) {
        g_heap->import_objs();
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
    return r;
}

void * big_alloc(size_t sz) {
    void * r = malloc(sz);
    if (r == nullptr) throw std::bad_alloc();
    return r;
}

void initialize_alloc() {
#ifdef LEAN_SMALL_ALLOCATOR
    g_heap_manager = new heap_manager();
    init_heap(true);
#endif
}

void finalize_alloc() {
}
}
