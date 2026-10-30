/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
*/
#include <atomic>
#include <lean/lean.h>
#include "runtime/alloc.h"

namespace lean {
/*
Caches for imported-constant lookups.

The `ImportedConsts` of an environment are immutable per import set, so lookup results (including
misses) can be cached. If the environment may be freed (`leakEnv` is false), `finalizeImport` gives
each of its `ImportedConsts` a cache of its own in the `cache?` field, which is freed together with
it. All other lookups, e.g. in leaked environments or ones loaded from header snapshots, use a
process-global cache.

Slots hold immutable entries behind a single atomic pointer each, so lookups are lock-free; races
merely lose an insertion. Entries pin their key and value, so hits perform no reference counting on
the root and key (pointer comparison and read-only name comparison only). Entries of the global
cache are never freed and additionally pin their root, in case it is freeable (see `entry::m_root`).
The value is marked multi-threaded, as reader threads take references to it. Freeing an owned cache
releases the keys and values of its entries; this happens before `Environment.freeRegions` frees the
regions they may point into.

The cache uses open addressing with a short probe window and never replaces an entry: a replaced
entry would have to be leaked (it may still be read concurrently), and colliding hot keys would
then leak one entry per alternation, without bound. Instead, a miss inserts into the first empty
slot of the window, or not at all if the window is full.

The table doubles once half its slots are filled, so its size tracks the working set of distinct
names actually looked up: with a fixed size and more such names than slots, sweep-style workloads
(e.g. per-declaration linting at mathlib scale) would fill the probe windows, leaving most names
uncached and degrading their lookups to full tree walks. Growth migrates the existing entries (they
are immutable, so old and new table can share them) and publishes the new table via an atomic
pointer; old tables are kept until the cache is freed as concurrent readers may still probe them,
with total overhead below the final table's size thanks to geometric growth. Insertions racing with
a swap go to the old table and are merely lost.
*/

extern "C" lean_object * lean_imported_consts_find_entry_core(lean_obj_arg root, lean_obj_arg n);
extern "C" lean_object * lean_imported_extra_consts_find_entry_core(lean_obj_arg root, lean_obj_arg n);

namespace {
struct entry {
    // `entry_hash(m_root, m_key)`, stored so that migration need not read the key
    uint64_t m_hash;
    // the `ImportedConsts` looked up in, compared by address; not pinned in an owned cache, whose
    // entries it owns. The global cache mostly serves ones that are never freed, such as those of
    // leaked environments, but also e.g. results of `modifyAt` on a freeable environment, so it
    // pins them: otherwise, once dropped, their address could be reused by another
    // `ImportedConsts`.
    lean_object * m_root;
    // the name looked up, pinned; in a global-cache entry whose `m_root` was dropped, it may point
    // into regions freed since by `Environment.freeRegions`, so it is only compared once `m_root`
    // matched, which such a pinned `m_root` never does for a live `ImportedConsts`
    lean_object * m_key;
    // the cached `Option` result object
    lean_object * m_val;
    // next entry inserted into the same cache, for freeing
    entry * m_next;
};

constexpr size_t global_initial_num_slots = 1 << 18;
constexpr size_t view_initial_num_slots = 1 << 16;
constexpr size_t max_num_slots = 1 << 26;
constexpr size_t probe_window = 8;

struct table {
    // power of two
    size_t m_num_slots;
    std::atomic<entry *> * m_slots;
    // successful insertions into `m_slots`; slightly underestimates occupancy when a swap loses
    // migrated-over entries, which only delays the next doubling
    std::atomic<size_t> m_num_entries;
    // claimed by the one thread that migrates and replaces this table
    std::atomic<bool> m_growing;
    // the table this one replaced, for freeing
    table * m_prev;
};

struct cache {
    std::atomic<table *> m_table;
    // all entries inserted into some table of an owned cache
    std::atomic<entry *> m_entries;
};

std::atomic<entry *> g_global_slots[global_initial_num_slots];
table g_global_table = { global_initial_num_slots, g_global_slots, {0}, {false}, nullptr };
cache g_global_cache = { {&g_global_table}, {nullptr} };

uint64_t entry_hash(lean_object * root, lean_object * key) {
    return lean_name_hash(key) ^ (reinterpret_cast<uintptr_t>(root) >> 4);
}

/* Inserts `e`, taken from the table being replaced, into the first empty slot of its probe window
   in `t`, or drops it if the window is full. Entries of a table are pairwise distinct, so no
   comparison is needed. Returns whether `e` was inserted. */
bool migrate_entry(table * t, entry * e) {
    size_t slot = static_cast<size_t>(e->m_hash) & (t->m_num_slots - 1);
    for (size_t i = 0; i < probe_window; i++) {
        size_t s = (slot + i) & (t->m_num_slots - 1);
        entry * expected = nullptr;
        if (t->m_slots[s].compare_exchange_strong(expected, e))
            return true;
    }
    return false;
}

/* Doubles `t` if it is still the current table of `c`, migrating its entries. */
void grow(cache & c, table * t) {
    if (t->m_num_slots >= max_num_slots || c.m_table.load() != t)
        return;
    if (t->m_growing.exchange(true))
        return;
    size_t num_slots = 2 * t->m_num_slots;
    table * nt = new table{num_slots, new std::atomic<entry *>[num_slots](), {0}, {false}, t};
    size_t migrated = 0;
    for (size_t i = 0; i < t->m_num_slots; i++) {
        // a concurrent insertion into an already-visited slot is lost with the old table
        if (entry * e = t->m_slots[i].load())
            if (migrate_entry(nt, e))
                migrated++;
    }
    nt->m_num_entries.store(migrated);
    // only this thread swaps `t` out, so the exchange cannot fail
    c.m_table.store(nt);
}

void cache_finalize(void * p) {
    cache * c = static_cast<cache *>(p);
    // no concurrent readers remain, as they would hold a reference to the owning `ImportedConsts`
    entry * e = c->m_entries.load();
    while (e) {
        entry * next = e->m_next;
        lean_dec(e->m_key);
        lean_dec(e->m_val);
        delete e;
        e = next;
    }
    table * t = c->m_table.load();
    while (t) {
        table * prev = t->m_prev;
        delete[] t->m_slots;
        delete t;
        t = prev;
    }
    delete c;
}

void cache_foreach(void *, b_lean_obj_arg) {
    // entries hold only multi-threaded keys and values (see `find_cached_in`), so marking need not
    // visit them
}

lean_external_class * get_cache_class() {
    static lean_external_class * cls = lean_register_external_class(cache_finalize, cache_foreach);
    return cls;
}
}

/* The module index stored in a lookup result `Option (α × Nat)`, plus one, or zero for `none`. */
static inline lean_object * mod_idx_of(b_lean_obj_arg r) {
    if (lean_is_scalar(r))
        return lean_box(0);
    return lean_box(lean_unbox(lean_ctor_get(lean_ctor_get(r, 0), 1)) + 1);
}

template <bool owned>
static lean_obj_res find_cached_miss(cache & c, table * t, uint64_t h, size_t empty,
        b_lean_obj_arg root, b_lean_obj_arg n, lean_object * (*core)(lean_obj_arg, lean_obj_arg));

/* Specialized per `owned` and inlined into `find_cached`: a shared out-of-line copy measurably slows
   down the hot path. With `idx_only`, returns `mod_idx_of` the result instead, so that hits need no
   reference counting. */
template <bool owned, bool idx_only>
static inline __attribute__((always_inline)) lean_obj_res find_cached_in(cache & c,
        b_lean_obj_arg root, b_lean_obj_arg n, lean_object * (*core)(lean_obj_arg, lean_obj_arg)) {
    table * t = c.m_table.load();
    uint64_t h = entry_hash(root, n);
    size_t slot = static_cast<size_t>(h) & (t->m_num_slots - 1);
    size_t empty = t->m_num_slots;
    for (size_t i = 0; i < probe_window; i++) {
        size_t s = (slot + i) & (t->m_num_slots - 1);
        entry * e = t->m_slots[s].load();
        if (!e) {
            empty = s;
            // entries are only inserted at the window's first empty slot, so stop searching
            break;
        }
        if (e->m_root == root && lean_name_eq(e->m_key, n)) {
            if (idx_only)
                return mod_idx_of(e->m_val);
            // the value is pinned by the entry and multi-threaded
            lean_inc(e->m_val);
            return e->m_val;
        }
    }
    lean_object * r = find_cached_miss<owned>(c, t, h, empty, root, n, core);
    if (idx_only) {
        lean_object * i = mod_idx_of(r);
        lean_dec(r);
        return i;
    }
    return r;
}

template <bool owned>
static lean_obj_res find_cached_miss(cache & c, table * t, uint64_t h, size_t empty,
        b_lean_obj_arg root, b_lean_obj_arg n, lean_object * (*core)(lean_obj_arg, lean_obj_arg)) {
    lean_inc(root); lean_inc(n);
    // Whether a lookup misses depends on other threads using the same cache, so the miss path must
    // not count toward the heartbeats of the current thread.
    uint64_t heartbeats = get_num_heartbeats();
    lean_object * r = core(root, n);
    set_heartbeats(heartbeats);
    // Marked even when it is not cached, so that the result is never exclusive: whether it is
    // cached depends on other threads, and an exclusive result would let the caller save
    // allocations, making heartbeats nondeterministic.
    lean_mark_mt(r);
    if (empty == t->m_num_slots)
        return r;
    // Pin the key, and the root unless it owns the cache; hits only compare them. An owned cache
    // releases its keys from whichever thread frees it, so they must be multi-threaded.
    if (!owned)
        lean_inc(root);
    else
        lean_mark_mt(n);
    lean_inc(n);
    entry * ne = new entry{h, root, n, r, nullptr};
    entry * expected = nullptr;
    if (!t->m_slots[empty].compare_exchange_strong(expected, ne)) {
        // lost an insertion race; drop the new entry rather than probing on
        if (!owned)
            lean_dec(root);
        lean_dec(n);
        delete ne;
        return r;
    }
    if (owned) {
        entry * head = c.m_entries.load();
        do {
            ne->m_next = head;
        } while (!c.m_entries.compare_exchange_weak(head, ne));
    }
    lean_inc(r);
    if (2 * (t->m_num_entries.fetch_add(1) + 1) >= t->m_num_slots)
        grow(c, t);
    return r;
}

template <bool idx_only>
static lean_obj_res find_cached(b_lean_obj_arg opt, b_lean_obj_arg root, b_lean_obj_arg n,
        lean_object * (*core)(lean_obj_arg, lean_obj_arg)) {
    if (!lean_is_scalar(opt)) {
        cache * c = static_cast<cache *>(lean_get_external_data(lean_ctor_get(opt, 0)));
        return find_cached_in<true, idx_only>(*c, root, n, core);
    }
    return find_cached_in<false, idx_only>(g_global_cache, root, n, core);
}

/* ImportedConsts.findConstEntryCachedImpl (cache? : @& Option LookupCache)
     (t : @& ImportedConsts ConstantInfo) (n : @& Name) : Option (ConstantInfo × Nat) */
extern "C" LEAN_EXPORT lean_obj_res lean_imported_consts_find_entry_cached(
        b_lean_obj_arg cache, b_lean_obj_arg root, b_lean_obj_arg n) {
    return find_cached<false>(cache, root, n, lean_imported_consts_find_entry_core);
}

/* ImportedConsts.findExtraEntryCachedImpl (cache? : @& Option LookupCache)
     (t : @& ImportedConsts Unit) (n : @& Name) : Option (Unit × Nat) */
extern "C" LEAN_EXPORT lean_obj_res lean_imported_extra_consts_find_entry_cached(
        b_lean_obj_arg cache, b_lean_obj_arg root, b_lean_obj_arg n) {
    return find_cached<false>(cache, root, n, lean_imported_extra_consts_find_entry_core);
}

extern "C" LEAN_EXPORT lean_obj_res lean_imported_consts_find_mod_idx_cached(
        b_lean_obj_arg cache, b_lean_obj_arg root, b_lean_obj_arg n) {
    return find_cached<true>(cache, root, n, lean_imported_consts_find_entry_core);
}

extern "C" LEAN_EXPORT lean_obj_res lean_imported_extra_consts_find_mod_idx_cached(
        b_lean_obj_arg cache, b_lean_obj_arg root, b_lean_obj_arg n) {
    return find_cached<true>(cache, root, n, lean_imported_extra_consts_find_entry_core);
}

/* LookupCache.new : BaseIO LookupCache */
extern "C" LEAN_EXPORT lean_obj_res lean_imported_consts_cache_new() {
    size_t num_slots = view_initial_num_slots;
    table * t = new table{num_slots, new std::atomic<entry *>[num_slots](), {0}, {false}, nullptr};
    cache * c = new cache{{t}, {nullptr}};
    return lean_alloc_external(get_cache_class(), c);
}
}
