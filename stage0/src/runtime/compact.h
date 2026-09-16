/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include <string>
#include <vector>
#include "runtime/object.h"
#include "util/alloc.h"

namespace lean {
typedef lean_object * object_offset;

class region_reader;

/** Information about a loaded library, used for closure function pointer relocation. */
struct lib_info {
    size_t base_addr;
    // Loader-reported identity, used as an opaque key to match a saved library against a
    // currently-loaded one
    std::string id;
};

/** Builds the sorted table of all currently loaded libraries. */
LEAN_EXPORT std::vector<lib_info> get_loaded_libs();

/** A lightweight, non-owning view of a compacted region's address range, used as a cross-region
    pointer-relocation dependency. The owning buffer is managed on the Lean side (`CompactedRegion`),
    not here. `begin`/`size` give the physical data range; `base_addr` is the logical base its
    pointers are relative to. */
struct region_view {
    void * begin;
    size_t size;
    void * base_addr;
};

class LEAN_EXPORT object_compactor {
    struct max_sharing_table;
    friend struct max_sharing_hash;
    friend struct max_sharing_eq;
    lean::unordered_map<object*, object_offset, std::hash<object*>, std::equal_to<object*>> m_obj_table;
    std::unique_ptr<max_sharing_table> m_max_sharing_table;
    // Scratch stack of child offsets, to avoid repeated stack allocs during recursion
    std::vector<object_offset> m_tmp;
    // Dependency regions sorted by `begin` address for binary search in `to_offset`
    std::vector<region_view> m_dep_regions;
    // Sorted table of loaded libraries for closure function pointer mapping
    std::vector<lib_info> m_libs;
    // Buffer-relative byte offsets of every compacted closure's `m_fun` field
    std::vector<size_t> m_closure_offsets;
    bool m_allow_closures = false;
    // On-disk base address used for `mmap`ing compacted regions without relocations
    // References within the compacted region are rewritten by subtracting `m_begin` and adding `m_base_addr`
    // In the simplest case `base_addr == nullptr`, we get region-relative pointers
    void * m_base_addr;
    void * m_begin;
    void * m_end;
    void * m_capacity;
    size_t capacity() const { return static_cast<char*>(m_capacity) - static_cast<char*>(m_begin); }
    object_offset save(object * o, object * new_o);
    object_offset save_max_sharing(object * o, object * new_o, size_t new_o_sz);
    object_offset to_offset(object * o);
    // Compacts a not-yet-seen heap object (and, recursively, its children),
    // returning its offset. Dispatches on the object's tag.
    object_offset compact(object * o);
    void insert_terminator(object * o);
    object * copy_object(object * o, size_t sz = 0);
    object_offset insert_constructor(object * o);
    object_offset insert_array(object * o);
    object_offset insert_sarray(object * o);
    object_offset insert_string(object * o);
    object_offset insert_thunk(object * o);
    object_offset insert_task(object * o);
    object_offset insert_promise(object * o);
    object_offset insert_ref(object * o);
    object_offset insert_mpz(object * o);
    object_offset insert_closure(object * o);
public:
    object_compactor(void * base_addr = nullptr, std::vector<region_view> dep_regions = {},
                     bool allow_closures = false);
    object_compactor(object_compactor const &) = delete;
    object_compactor(object_compactor &&) = delete;
    ~object_compactor();
    object_compactor operator=(object_compactor const &) = delete;
    object_compactor operator=(object_compactor &&) = delete;
    void operator()(object * o);
    size_t size() const { return static_cast<char*>(m_end) - static_cast<char*>(m_begin); }
    void const * data() const { return m_begin; }
    // Allocate `sz` bytes of zeroed memory.
    void * alloc(size_t sz);
    void const * base_addr() const { return m_base_addr; }
    /** Returns the distinct loaded libraries that contain a compacted closure's `m_fun` pointer
        — the subset of loaded libraries needed to relocate this region's closures on load.
        Throws if a closure's fn pointer lies in no loaded library. */
    std::vector<lib_info> used_libs() const;
    /** Buffer-relative offsets of all closure `m_fun` fields compacted so far. */
    std::vector<size_t> & closure_offsets() { return m_closure_offsets; }
};

// A transient, non-owning read context: it walks a just-mapped buffer to fix up its pointers
// (`read`), then is discarded. The buffer itself is owned by the Lean `CompactedRegion` and freed
// via `lean_compacted_region_free`, not here, so this class holds no finalizer.
class LEAN_EXPORT region_reader {
    size_t m_size;
    // see `object_compactor::m_base_addr`
    void * m_base_addr;
    void * m_begin;
    void * m_next;
    void * m_end;
    // Path of the file this region was loaded from (empty when constructed in-memory rather
    // than read from disk). Lets snapshot save re-derive its dep paths from `env.header.regions`.
    std::string m_fname;
    // Dependency regions for cross-region pointer fixup
    std::vector<region_view> m_dep_regions;
    // Sorted (old_base, delta) pairs for closure function pointer relocation
    std::vector<std::pair<size_t, ptrdiff_t>> m_lib_relocs;
    // Data-relative byte offsets of every closure's `m_fun` field. Used to patch fn
    // pointers on load without scanning the compacted region. Empty if no closures.
    std::vector<size_t> m_closure_offsets;
    void sort_and_validate_dep_regions();
    void move(size_t d);
    void move(object * o);
    object * fix_object_ptr(object * o);
    void fix_constructor(object * o);
    void fix_array(object * o);
    void fix_thunk(object * o);
    void fix_ref(object * o);
    void fix_task(object * o);
    void fix_promise(object * o);
    void fix_mpz(object * o);
    void fix_closure(object * o);
public:
    /* Creates a read context over the given just-mapped buffer. Does not take ownership of the
       buffer; see the class comment. */
    region_reader(size_t sz, void * data, void * base_addr,
                  std::vector<region_view> dep_regions = {},
                  std::vector<std::pair<size_t, ptrdiff_t>> lib_relocs = {},
                  std::vector<size_t> closure_offsets = {});
    region_reader(region_reader const &) = delete;
    region_reader(region_reader &&) = delete;
    region_reader operator=(region_reader const &) = delete;
    region_reader operator=(region_reader &&) = delete;
    object * read();
};
}
