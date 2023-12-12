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
#include "runtime/thread.h"
#include "runtime/interrupt.h"
#include "runtime/sstream.h"
#include "runtime/hash.h"
#include "runtime/io.h"
#include "runtime/compact.h"
#include "runtime/buffer.h"
#include "util/io.h"
#include "util/name_map.h"
#include "library/module.h"
#include "library/constants.h"
#include "library/time_task.h"
#include "library/util.h"
#include "githash.h"

#ifdef LEAN_WINDOWS
#include <windows.h>
#else
#include <sys/mman.h>
#include <unistd.h>
#include <fcntl.h>
#endif

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#include <sanitizer/lsan_interface.h>
#endif
#endif

namespace lean {

/** On-disk format of a .olean file. */
struct olean_header {
    // 5 bytes: magic number
    char marker[5] = {'o', 'l', 'e', 'a', 'n'};
    // 1 byte: version, currently always `1`
    uint8_t version = 1;
    // 42 bytes: build githash, padded with `\0` to the right
    char githash[42];
    // address at which the beginning of the file (including header) is attempted to be mmapped
    size_t base_addr;
    // payload, a serialize Lean object graph; `size_t` has same alignment requirements as Lean objects
    size_t data[];
};
// make sure we don't have any padding bytes, which also ensures `data` is properly aligned
static_assert(sizeof(olean_header) == 5 + 1 + 42 + sizeof(size_t), "olean_header must be packed");

extern "C" LEAN_EXPORT object * lean_save_module_data(b_obj_arg fname, b_obj_arg mod, b_obj_arg mdata, object *) {
    std::string olean_fn(string_cstr(fname));
    // we first write to a temp file and then move it to the correct path (possibly deleting an older file)
    // so that we neither expose partially-written files nor modify possibly memory-mapped files
    std::string olean_tmp_fn = olean_fn + ".tmp";
    try {
        std::ofstream out(olean_tmp_fn, std::ios_base::binary);
        if (out.fail()) {
            return io_result_mk_error((sstream() << "failed to create file '" << olean_fn << "'").str());
        }

        // Derive a base address that is uniformly distributed by deterministic, and should most likely
        // work for `mmap` on all interesting platforms
        // NOTE: an overlapping/non-compatible base address does not prevent the module from being imported,
        // merely from using `mmap` for that

        // Let's start with a hash of the module name. Note that while our string hash is a dubious 32-bit
        // algorithm, the mixing of multiple `Name` parts seems to result in a nicely distributed 64-bit
        // output
        size_t base_addr = name(mod, true).hash();
        // x86-64 user space is currently limited to the lower 47 bits
        // https://en.wikipedia.org/wiki/X86-64#Virtual_address_space_details
        // On Linux at least, the stack grows down from ~0x7fff... followed by shared libraries, so reserve
        // a bit of space for them (0x7fff...-0x7f00... = 1TB)
        base_addr = base_addr % 0x7f0000000000;
        // `mmap` addresses must be page-aligned. The default (non-huge) page size on x86-64 is 4KB.
        // `MapViewOfFileEx` addresses must be aligned to the "memory allocation granularity", which is 64KB.
        base_addr = base_addr & ~((1LL<<16) - 1);

        object_compactor compactor(reinterpret_cast<void *>(base_addr + offsetof(olean_header, data)));
        compactor(mdata);

        // see/sync with file format description above
        olean_header header = {};
        header.base_addr = base_addr;
        strncpy(header.githash, LEAN_GITHASH, sizeof(header.githash));
        out.write(reinterpret_cast<char *>(&header), sizeof(header));
        out.write(static_cast<char const *>(compactor.data()), compactor.size());
        out.close();
        while (std::rename(olean_tmp_fn.c_str(), olean_fn.c_str()) != 0) {
#ifdef LEAN_WINDOWS
            if (errno == EEXIST) {
                // Memory-mapped files can be deleted starting with Windows 10 using "POSIX semantics"
                HANDLE h_olean_fn = CreateFile(olean_fn.c_str(), GENERIC_READ | DELETE, FILE_SHARE_READ | FILE_SHARE_DELETE, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
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
        return io_result_mk_ok(box(0));
    } catch (exception & ex) {
        return io_result_mk_error((sstream() << "failed to write '" << olean_fn << "': " << ex.what()).str());
    }
}

extern "C" LEAN_EXPORT object * lean_read_module_data(object * fname, object *) {
    std::string olean_fn(string_cstr(fname));
    try {
        std::ifstream in(olean_fn, std::ios_base::binary);
        if (in.fail()) {
            return io_result_mk_error((sstream() << "failed to open file '" << olean_fn << "'").str());
        }
        /* Get file size */
        in.seekg(0, in.end);
        size_t size = in.tellg();
        in.seekg(0);

        olean_header default_header = {};
        olean_header header;
        if (!in.read(reinterpret_cast<char *>(&header), sizeof(header))) {
            return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "', invalid header").str());
        }
        if (memcmp(header.marker, default_header.marker, sizeof(header.marker)) != 0
            || header.version != default_header.version
#ifdef LEAN_CHECK_OLEAN_VERSION
            || strncmp(header.githash, LEAN_GITHASH, sizeof(header.githash)) != 0
#endif
        ) {
            return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "', invalid header").str());
        }
        char * base_addr = reinterpret_cast<char *>(header.base_addr);
        char * buffer = nullptr;
        bool is_mmap = false;
        std::function<void()> free_data;
#ifdef LEAN_WINDOWS
        // `FILE_SHARE_DELETE` is necessary to allow the file to (be marked to) be deleted while in use
        HANDLE h_olean_fn = CreateFile(olean_fn.c_str(), GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_DELETE, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
        if (h_olean_fn == INVALID_HANDLE_VALUE) {
            return io_result_mk_error((sstream() << "failed to open '" << olean_fn << "': " << GetLastError()).str());
        }
        HANDLE h_map = CreateFileMapping(h_olean_fn, NULL, PAGE_READONLY, 0, 0, NULL);
        if (h_olean_fn == NULL) {
            return io_result_mk_error((sstream() << "failed to map '" << olean_fn << "': " << GetLastError()).str());
        }
        buffer = static_cast<char *>(MapViewOfFileEx(h_map, FILE_MAP_READ, 0, 0, 0, base_addr));
        free_data = [=]() {
            if (buffer) {
                lean_always_assert(UnmapViewOfFile(base_addr));
            }
            lean_always_assert(CloseHandle(h_map));
            lean_always_assert(CloseHandle(h_olean_fn));
        };
#else
        int fd = open(olean_fn.c_str(), O_RDONLY);
        if (fd == -1) {
            return io_result_mk_error((sstream() << "failed to open '" << olean_fn << "': " << strerror(errno)).str());
        }
#ifdef LEAN_MMAP
        buffer = static_cast<char *>(mmap(base_addr, size, PROT_READ, MAP_PRIVATE, fd, 0));
#endif
        close(fd);
        free_data = [=]() {
            if (buffer != MAP_FAILED) {
                lean_always_assert(munmap(buffer, size) == 0);
            }
        };
#endif
        if (buffer && buffer == base_addr) {
            buffer += sizeof(olean_header);
            is_mmap = true;
        } else {
#ifdef LEAN_MMAP
            free_data();
#endif
            buffer = static_cast<char *>(malloc(size - sizeof(olean_header)));
            free_data = [=]() {
                free(buffer);
            };
            in.read(buffer, size - sizeof(olean_header));
            if (!in) {
                return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "'").str());
            }
        }
        in.close();

        compacted_region * region =
          new compacted_region(size - sizeof(olean_header), buffer, base_addr + sizeof(olean_header), is_mmap, free_data);
#if defined(__has_feature)
#if __has_feature(address_sanitizer)
        // do not report as leak
        __lsan_ignore_object(region);
#endif
#endif
        object * mod = region->read();
        object * mod_region = alloc_cnstr(0, 2, 0);
        cnstr_set(mod_region, 0, mod);
        cnstr_set(mod_region, 1, box_size_t(reinterpret_cast<size_t>(region)));
        return io_result_mk_ok(mod_region);
    } catch (exception & ex) {
        return io_result_mk_error((sstream() << "failed to read '" << olean_fn << "': " << ex.what()).str());
    }
}

/*
@[export lean.write_module_core]
def writeModule (env : Environment) (fname : String) : IO Unit := */
extern "C" object * lean_write_module(object * env, object * fname, object *);

void write_module(environment const & env, std::string const & olean_fn) {
    consume_io_result(lean_write_module(env.to_obj_arg(), mk_string(olean_fn), io_mk_world()));
}
}
