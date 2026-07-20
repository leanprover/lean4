/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
*/
#include <atomic>
#include <lean/lean.h>

namespace lean {
/*
Process-global cache for imported-constant lookups.

The imported-constants views of an environment are immutable per import set, so lookup results
(including misses) can be cached. Slots hold immutable entries behind a single atomic pointer each,
so lookups are lock-free; races merely lose an insertion. Entries pin their root, key, and value
with references that are never dropped, so hits perform no reference counting on the root and key
(pointer comparison and read-only name comparison only) and cache entries can never be revived
after a free. The value is marked multi-threaded so that reader threads can take references to it
atomically. `lean_mark_persistent` must NOT be used here: it plain-writes reference counts while
other elaboration threads concurrently update them atomically, corrupting shared object graphs.

The cache uses open addressing with a short probe window and never replaces an entry: a replaced
entry would have to be leaked (it may still be read concurrently), and colliding hot keys would
then leak one entry per alternation, without bound. Instead, a miss inserts into the first empty
slot of the window, or not at all if the window is full.

The table doubles once half its slots are filled, so its size tracks the working set of distinct
names actually looked up: with more such names than slots, sweep-style workloads (e.g.
per-declaration linting at mathlib scale) displace each other's entries and degrade every lookup
to a full tree walk. Growth migrates the existing entries (they are immutable and never freed, so
old and new table can share them) and publishes the new table via an atomic pointer; old tables
are leaked as concurrent readers may still probe them, with total leakage below the final table's
size thanks to geometric growth. Insertions racing with a swap go to the old table and are merely
lost.
*/

extern "C" void lean_mark_persistent_unshared(lean_object * o);
extern "C" lean_object * lean_imported_consts_find_entry_core(lean_obj_arg root, lean_obj_arg n);
extern "C" lean_object * lean_imported_extra_consts_find_entry_core(lean_obj_arg root, lean_obj_arg n);

namespace {
struct entry {
    lean_object * m_root;
    lean_object * m_key;
    // the cached `Option` result object
    lean_object * m_val;
};

constexpr size_t initial_num_slots = 1 << 18;
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
};

std::atomic<entry *> g_initial_slots[initial_num_slots];
table g_initial_table = { initial_num_slots, g_initial_slots, {0}, {false} };
std::atomic<table *> g_table{&g_initial_table};

uint64_t entry_hash(entry * e) {
    return lean_name_hash(e->m_key) ^ (reinterpret_cast<uintptr_t>(e->m_root) >> 4);
}

/* Inserts `e` into the first empty slot of its probe window, or drops it if the window is full or
   already contains an entry. Returns whether `e` was inserted. */
bool insert_entry(table * t, entry * e) {
    size_t slot = static_cast<size_t>(entry_hash(e)) & (t->m_num_slots - 1);
    for (size_t i = 0; i < probe_window; i++) {
        size_t s = (slot + i) & (t->m_num_slots - 1);
        entry * expected = nullptr;
        if (t->m_slots[s].compare_exchange_strong(expected, e, std::memory_order_release,
                std::memory_order_acquire))
            return true;
        if (expected->m_root == e->m_root && lean_name_eq(expected->m_key, e->m_key))
            return false;
    }
    return false;
}

/* Doubles `t` if it is still the current table, migrating its entries. */
void grow(table * t) {
    if (t->m_num_slots >= max_num_slots || g_table.load(std::memory_order_acquire) != t)
        return;
    if (t->m_growing.exchange(true, std::memory_order_acq_rel))
        return;
    size_t num_slots = 2 * t->m_num_slots;
    table * nt = new table{num_slots, new std::atomic<entry *>[num_slots](), {0}, {false}};
    size_t migrated = 0;
    for (size_t i = 0; i < t->m_num_slots; i++) {
        // a concurrent insertion into an already-visited slot is lost with the old table
        if (entry * e = t->m_slots[i].load(std::memory_order_acquire))
            if (insert_entry(nt, e))
                migrated++;
    }
    nt->m_num_entries.store(migrated, std::memory_order_relaxed);
    // only this thread swaps `t` out, so the exchange cannot fail
    g_table.store(nt, std::memory_order_release);
}
}

static lean_obj_res find_cached(b_lean_obj_arg root, b_lean_obj_arg n,
        lean_object * (*core)(lean_obj_arg, lean_obj_arg)) {
    table * t = g_table.load(std::memory_order_acquire);
    uint64_t h = lean_name_hash(n) ^ (reinterpret_cast<uintptr_t>(root) >> 4);
    size_t slot = static_cast<size_t>(h) & (t->m_num_slots - 1);
    size_t empty = t->m_num_slots;
    for (size_t i = 0; i < probe_window; i++) {
        size_t s = (slot + i) & (t->m_num_slots - 1);
        entry * e = t->m_slots[s].load(std::memory_order_acquire);
        if (!e) {
            empty = s;
            // entries are only inserted at the window's first empty slot, so stop searching
            break;
        }
        if (e->m_root == root && lean_name_eq(e->m_key, n)) {
            // atomic: the value is multi-threaded and pinned by the entry
            lean_inc(e->m_val);
            return e->m_val;
        }
    }
    lean_inc(root); lean_inc(n);
    lean_object * r = core(root, n);
    if (empty == t->m_num_slots)
        return r;
    // The value is handed to and `inc`ed by arbitrary reader threads; marking it persistent keeps
    // hits free of atomic RC and of coherence traffic on hot values. The unshared variant only
    // writes thread-owned counts, so it is race-free where plain `lean_mark_persistent` is not.
    lean_mark_persistent_unshared(r);
    // pin root and key; hits only compare them, so they need no special marking
    lean_inc(root);
    lean_inc(n);
    entry * ne = new entry{root, n, r};
    entry * expected = nullptr;
    if (!t->m_slots[empty].compare_exchange_strong(expected, ne, std::memory_order_release,
            std::memory_order_relaxed)) {
        // lost an insertion race; drop the new entry rather than probing on
        lean_dec(root); lean_dec(n);
        delete ne;
        return r;
    }
    lean_inc(r);
    if (2 * (t->m_num_entries.fetch_add(1, std::memory_order_relaxed) + 1) >= t->m_num_slots)
        grow(t);
    return r;
}

extern "C" LEAN_EXPORT lean_obj_res lean_imported_consts_find_entry_cached(b_lean_obj_arg root, b_lean_obj_arg n) {
    return find_cached(root, n, lean_imported_consts_find_entry_core);
}

extern "C" LEAN_EXPORT lean_obj_res lean_imported_extra_consts_find_entry_cached(b_lean_obj_arg root, b_lean_obj_arg n) {
    return find_cached(root, n, lean_imported_extra_consts_find_entry_core);
}

extern "C" LEAN_EXPORT lean_obj_res lean_imported_consts_cache_reset(lean_object * /* w */) {
    table * t = g_table.load(std::memory_order_acquire);
    for (size_t i = 0; i < t->m_num_slots; i++) {
        // entries (and their pins) are leaked: concurrent readers may still dereference them
        t->m_slots[i].store(nullptr, std::memory_order_release);
    }
    // occupancy is only ever an estimate; a racing insert after the reset merely re-adds one
    t->m_num_entries.store(0, std::memory_order_relaxed);
    return lean_io_result_mk_ok(lean_box(0));
}
}
