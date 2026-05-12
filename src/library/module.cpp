/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Gabriel Ebner, Sebastian Ullrich

.olean serialization and deserialization.
*/
#include <unordered_map>
#include <vector>
#include <utility>
#include <string>
#include <sstream>
#include <fstream>
#include <algorithm>
#include <sys/stat.h>
#include <cerrno>
#include <cstring>
#include "runtime/thread.h"
#include "runtime/interrupt.h"
#include "runtime/sstream.h"
#include "runtime/hash.h"
#include "runtime/io.h"
#include "runtime/compact.h"
#include "runtime/buffer.h"
#include "runtime/array_ref.h"
#include "runtime/option_ref.h"
#include "util/io.h"
#include "util/name_map.h"
#include "library/module.h"
#include "library/constants.h"
#include "library/time_task.h"
#include "library/util.h"
#include "githash.h"

#ifdef LEAN_WINDOWS
#include <windows.h>
#include <io.h>
#include <fcntl.h>
#else
#include <sys/mman.h>
#include <unistd.h>
#include <fcntl.h>
#endif

// `MAP_FIXED_NOREPLACE` turns out to improve mmap hits in the snapshot use case but is exclusive to
// Linux 4.17+ and glibc 2.28+; as this is not a core use case and older kernels will silently
// ignore the flag, we simply define it conditionally.
#if defined(__linux__) && !defined(MAP_FIXED_NOREPLACE)
#define MAP_FIXED_NOREPLACE 0x100000
#endif

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#include <sanitizer/lsan_interface.h>
#endif
#endif

namespace lean {

namespace {
/** Read up to `n` bytes from `fd` into `buf`, handling `EINTR`. */
ssize_t readn(int fd, void * buf, size_t n) {
    size_t bytes_read_total = 0;
    while (bytes_read_total < n) {
        ssize_t bytes_read = read(fd, static_cast<char*>(buf) + bytes_read_total, n - bytes_read_total);
        if (bytes_read < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        if (bytes_read == 0) {
            break;
        }
        bytes_read_total += bytes_read;
    }
    return bytes_read_total;
}
}

/** Trivial RAII wrapper for file descriptors so we don't have to worry about `close` management. */
class file_descriptor {
private:
    int m_fd;
public:
    explicit file_descriptor(int fd) : m_fd(fd) {}

    // It should not be copyable
    file_descriptor(const file_descriptor&) = delete;
    file_descriptor& operator=(const file_descriptor&) = delete;

    file_descriptor(file_descriptor&& other) noexcept : m_fd(other.m_fd) {
        other.m_fd = -1;
    }

    ~file_descriptor() {
        if (m_fd != -1) {
            close(m_fd);
        }
    }

    int get() const { return m_fd; }
    operator bool() const { return m_fd != -1; }
};

/** On-disk format of a .olean file. */
struct olean_header {
    // 5 bytes: magic number
    char marker[5] = {'o', 'l', 'e', 'a', 'n'};
    // 1 byte: version, incremented on structural changes to header
    uint8_t version = 2;
    // 1 byte of flags:
    // * bit 0: whether persisted bignums use GMP or Lean-native encoding
    // * bit 1-7: reserved
    uint8_t flags =
#ifdef LEAN_USE_GMP
        0b1;
#else
        0b0;
#endif
    // 33 bytes: Lean version string, padded with '\0' to the right
    // e.g. "4.12.0-nightly-2024-10-18". Other suffixes after the version
    // triple currently in use are `-rcN` for some `N` and `-pre` for any
    // other non-release commit. Not necessarily null-terminated.
    char lean_version[33];
    // 81b008650766442a0dfa9faa796e4588c9d7d3a1
    // 40 bytes: build githash, padded with `\0` to the right
    char githash[40];
    // address at which the beginning of the file (including header) is attempted to be mmapped
    size_t base_addr;
    // payload, a serialize Lean object graph; `size_t` has same alignment requirements as Lean objects
    size_t data[];
};
// make sure we don't have any padding bytes, which also ensures `data` is properly aligned
static_assert(sizeof(olean_header) == 5 + 1 + 1 + 33 + 40 + sizeof(size_t), "olean_header must be packed");


// Compactor external object: wraps a live `object_compactor` for incremental compaction.
// Keeping the full compactor alive preserves both the `obj_table` (pointer-identity dedup)
// and the `max_sharing_table` (structural dedup) across sequential `lean_compacted_region_save`
// calls so that objects shared between parts are emitted exactly once.

static lean_external_class * g_compactor_class = nullptr;

static void compactor_finalizer(void * data) {
    delete static_cast<object_compactor *>(data);
}

static void compactor_foreach(void *, b_lean_obj_arg) {
    // no Lean object references to trace
}

static void ensure_compactor_class() {
    if (!g_compactor_class) {
        g_compactor_class = lean_register_external_class(compactor_finalizer, compactor_foreach);
    }
}

static lean_object * mk_compactor(void * base_addr, std::vector<compacted_region *> dep_regions) {
    ensure_compactor_class();
    return lean_alloc_external(g_compactor_class,
        new object_compactor(base_addr, std::move(dep_regions)));
}

static object_compactor * to_compactor(lean_object * o) {
    return static_cast<object_compactor *>(lean_get_external_data(o));
}

// Extract `compacted_region *` pointers from an `Array CompactedRegion`.
static std::vector<compacted_region *> extract_dep_regions(b_obj_arg odep_regions) {
    std::vector<compacted_region *> result;
    size_t n = lean_array_size(odep_regions);
    result.reserve(n);
    for (size_t i = 0; i < n; i++) {
        result.push_back(reinterpret_cast<compacted_region *>(
            lean_unbox_usize(lean_array_get_core(odep_regions, i))));
    }
    return result;
}

extern "C" LEAN_EXPORT object * lean_compacted_region_save(b_obj_arg ofname, b_obj_arg mod, b_obj_arg odata,
                                                           b_obj_arg odep_regions, obj_arg oprev, object *) {
    // `mmap` addresses must be page-aligned. The default (non-huge) page size on x86-64 is 4KB;
    // `MapViewOfFileEx` addresses must be aligned to the "memory allocation granularity" (64KB).
    const size_t ALIGN = 1LL<<16;

    option_ref<object_ref> prev(oprev);
    object_ref cs_obj;
    if (prev) {
        cs_obj = prev.get_val();
    } else {
        // Derive a base address that is uniformly distributed but deterministic, and should most
        // likely work for `mmap` on all interesting platforms.
        // NOTE: an overlapping/non-compatible base address does not prevent the module from being
        // imported, merely from using `mmap` for that.
        // Start with a hash of the module name. While our string hash is a dubious 32-bit
        // algorithm, the mixing of multiple `Name` parts seems to result in a nicely distributed
        // 64-bit output.
        size_t base_addr = name(mod, true).hash();
        // x86-64 user space is currently limited to the lower 47 bits
        // (https://en.wikipedia.org/wiki/X86-64#Virtual_address_space_details).
        // On Linux at least, the stack grows down from ~0x7fff... followed by shared libraries,
        // so reserve a bit of space for them (0x7fff...-0x7f00... = 1TB).
        base_addr = base_addr % 0x7f0000000000;
        base_addr = base_addr & ~(ALIGN - 1);
        std::vector<compacted_region *> dep_regions = extract_dep_regions(odep_regions);
        cs_obj = object_ref(mk_compactor(reinterpret_cast<void *>(base_addr), std::move(dep_regions)));
    }

    object_compactor & compactor = *to_compactor(cs_obj.raw());

    char const * olean_fn = lean_string_cstr(ofname);
    // We first write to a temp file and then move it to the correct path (possibly deleting an
    // older file) so that we neither expose partially-written files nor modify possibly
    // memory-mapped files.
#ifdef LEAN_WINDOWS
    uint32_t pid = GetCurrentProcessId();
#else
    uint32_t pid = getpid();
#endif
    std::string olean_tmp_fn = std::string(olean_fn) + ".tmp." + std::to_string(pid);

    try {
        std::ofstream out(olean_tmp_fn, std::ios_base::binary);

        if (compactor.size() % ALIGN != 0) {
            compactor.alloc(ALIGN - (compactor.size() % ALIGN));
        }
        size_t file_offset = compactor.size();

        // Reserve space in the compactor buffer for the header so subsequent objects'
        // `base_addr`-relative offsets land in the right spot. The header is written directly
        // to `out` below; these reserved bytes are never read back.
        compactor.alloc(sizeof(olean_header));
        olean_header header = {};
        header.base_addr = reinterpret_cast<size_t>(compactor.base_addr()) + file_offset;
        strncpy(header.lean_version, get_short_version_string().c_str(), sizeof(header.lean_version));
        strncpy(header.githash, LEAN_GITHASH, sizeof(header.githash));
        out.write(reinterpret_cast<char *>(&header), sizeof(header));

        compactor(odata);

        if (out.fail()) {
            throw exception((sstream() << "failed to create file '" << olean_fn << "'").str());
        }
        out.write(static_cast<char const *>(compactor.data()) + file_offset + sizeof(olean_header),
                  compactor.size() - file_offset - sizeof(olean_header));
        out.close();
    } catch (exception & ex) {
        std::remove(olean_tmp_fn.c_str());
        return io_result_mk_error((sstream() << "failed to write '" << olean_fn << "': " << ex.what()).str());
    }

    while (std::rename(olean_tmp_fn.c_str(), olean_fn) != 0) {
#ifdef LEAN_WINDOWS
        if (errno == EEXIST) {
            // Memory-mapped files can be deleted starting with Windows 10 using "POSIX semantics".
            HANDLE h_olean_fn = CreateFile(olean_fn, GENERIC_READ | DELETE, FILE_SHARE_READ | FILE_SHARE_DELETE, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
            if (h_olean_fn == INVALID_HANDLE_VALUE) {
                return io_result_mk_error((sstream() << "failed to open '" << olean_fn << "': " << GetLastError()).str());
            }
            FILE_DISPOSITION_INFO_EX fdi = { FILE_DISPOSITION_FLAG_DELETE | FILE_DISPOSITION_FLAG_POSIX_SEMANTICS };
            if (SetFileInformationByHandle(h_olean_fn, static_cast<FILE_INFO_BY_HANDLE_CLASS>(21) /* FileDispositionInfoEx */, &fdi, sizeof(fdi)) != 0) {
                lean_always_assert(CloseHandle(h_olean_fn));
                continue;
            } else {
                return io_result_mk_error((sstream() << "failed to delete '" << olean_fn << "': " << GetLastError()).str());
            }
        }
#endif
        return io_result_mk_error((sstream() << "failed to write '" << olean_fn << "': " << errno << " " << strerror(errno)).str());
    }

    return io_result_mk_ok(cs_obj.steal());
}

// Implements `Lean.CompactedRegion.read`. Loads a compacted region from disk. `odep_regions`
// carries `CompactedRegion`s whose address ranges must be known to resolve cross-region pointers
// in this file. Returns `(α × CompactedRegion)`, where `α` is the type the Lean caller asks the
// root to be interpreted as — the C side does no type checking and the caller is responsible for
// using a type compatible with what was saved (see `CompactedRegion.read`).
extern "C" LEAN_EXPORT object * lean_compacted_region_read(b_obj_arg ofname, b_obj_arg odep_regions, object *) {
    std::string olean_fn(lean_string_cstr(ofname));
    std::vector<compacted_region *> dep_regions = extract_dep_regions(odep_regions);
    try {
#ifdef LEAN_WINDOWS
        HANDLE h_file = CreateFile(olean_fn.c_str(), GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_DELETE, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
        if (h_file == INVALID_HANDLE_VALUE) {
            return io_result_mk_error((sstream() << "failed to open file '" << olean_fn << "': " << GetLastError()).str());
        }
        int raw_fd = _open_osfhandle((intptr_t)h_file, _O_RDONLY);
        if (raw_fd == -1) {
            CloseHandle(h_file);
            return io_result_mk_error((sstream() << "failed to convert handle to fd for '" << olean_fn << "'").str());
        }
        file_descriptor fd(raw_fd);
#else
        file_descriptor fd(open(olean_fn.c_str(), O_RDONLY));
        if (!fd) {
            return io_result_mk_error((sstream() << "failed to open file '" << olean_fn << "': " << strerror(errno)).str());
        }
#endif

        struct stat st;
        if (fstat(fd.get(), &st) == -1) {
            return io_result_mk_error((sstream() << "failed to stat file '" << olean_fn << "': " << strerror(errno)).str());
        }
        size_t size = st.st_size;

        olean_header default_header = {};
        olean_header header;
        ssize_t read_size = readn(fd.get(), &header, sizeof(header));
        if (read_size < 0) {
            return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "': " << strerror(errno)).str());
        }
        if (read_size != sizeof(header)
            || memcmp(header.marker, default_header.marker, sizeof(header.marker)) != 0) {
            return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "', invalid header").str());
        }
        if (header.version != default_header.version || header.flags != default_header.flags
#ifdef LEAN_CHECK_OLEAN_VERSION
            || strncmp(header.githash, LEAN_GITHASH, sizeof(header.githash)) != 0
#endif
        ) {
            return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "', incompatible header").str());
        }
        char * base_addr = reinterpret_cast<char *>(header.base_addr);

        char * buffer = nullptr;
        bool is_mmap = false;
        std::function<void()> free_data;

        // Map file COW-writable. The fallback walk in `compacted_region::read()` writes
        // fixed pointers back into the region's memory when any dep region didn't land at its
        // saved `base_addr`, so the mapping must be writable. Unwritten pages remain shared
        // with the page cache under `MAP_PRIVATE` regardless of protection, so `PROT_WRITE`
        // is free when no fixup happens.
#ifdef LEAN_MMAP
#ifdef LEAN_WINDOWS
        HANDLE h_map = CreateFileMapping(h_file, NULL, PAGE_WRITECOPY, 0, 0, NULL);
        if (h_map != NULL) {
            // `FILE_MAP_COPY` already implies read+copy-on-write; OR'ing with `FILE_MAP_READ`
            // silently degrades the mapping to read-only and turns the fix-up walk's pointer
            // writes into access violations.
            buffer = static_cast<char *>(MapViewOfFileEx(h_map, FILE_MAP_COPY, 0, 0, 0, base_addr));
            lean_always_assert(CloseHandle(h_map));
            if (buffer && buffer == base_addr) {
                is_mmap = true;
                free_data = [=]() { lean_always_assert(UnmapViewOfFile(base_addr)); };
            } else if (buffer) {
                lean_always_assert(UnmapViewOfFile(buffer));
                buffer = nullptr;
            }
        }
#else
        // On Linux 4.17+ kernels, `MAP_FIXED_NOREPLACE` makes the kernel atomically reject the
        // mapping if `base_addr` is already taken; older kernels silently ignore the bit. macOS
        // doesn't expose the flag at all (see top-of-file fallback). The post-check + cleanup
        // `munmap` handles every "did not land at `base_addr`" case uniformly.
        int mmap_flags = MAP_PRIVATE
#ifdef MAP_FIXED_NOREPLACE
            | MAP_FIXED_NOREPLACE
#endif
            ;
        buffer = static_cast<char *>(mmap(base_addr, size, PROT_READ | PROT_WRITE,
            mmap_flags, fd.get(), 0));
        if (buffer != MAP_FAILED && buffer == base_addr) {
            is_mmap = true;
            free_data = [=]() { lean_always_assert(munmap(buffer, size) == 0); };
        } else {
            if (buffer != MAP_FAILED) munmap(buffer, size);
            buffer = nullptr;
        }
#endif
#endif

        if (!buffer) {
            buffer = static_cast<char *>(malloc(size));
            lseek(fd.get(), 0, SEEK_SET);
            ssize_t r = readn(fd.get(), buffer, size);
            if (r < 0 || r != static_cast<ssize_t>(size)) {
                free(buffer);
                return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "'").str());
            }
            char * buf = buffer;
            size_t sz = size;
            free_data = [=]() { free_sized(buf, sz); };
        }

        compacted_region * region = new compacted_region(
            size - sizeof(olean_header), buffer + sizeof(olean_header),
            base_addr + sizeof(olean_header), is_mmap, free_data,
            std::move(dep_regions));
#if defined(__has_feature)
#if __has_feature(address_sanitizer)
        __lsan_ignore_object(region);
#endif
#endif
        object * mod = region->read();
        object * pair = alloc_cnstr(0, 2, 0);
        cnstr_set(pair, 0, mod);
        cnstr_set(pair, 1, box_size_t(reinterpret_cast<size_t>(region)));
        return io_result_mk_ok(pair);
    } catch (exception & ex) {
        return io_result_mk_error((sstream() << "failed to read '" << olean_fn << "': " << ex.what()).str());
    }
}

}
