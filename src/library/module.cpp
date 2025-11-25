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
#include "runtime/array_ref.h"
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

extern "C" LEAN_EXPORT object * lean_save_module_data_parts(b_obj_arg mod, b_obj_arg oparts, object *) {
#ifdef LEAN_WINDOWS
    uint32_t pid = GetCurrentProcessId();
#else
    uint32_t pid = getpid();
#endif
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
    const size_t ALIGN = 1LL<<16;
    base_addr = base_addr & ~(ALIGN - 1);

    object_compactor compactor(reinterpret_cast<void *>(base_addr));

    array_ref<pair_ref<string_ref, object_ref>> parts(oparts, true);
    std::vector<std::string> tmp_fnames;
    for (auto const & part : parts) {
        std::string olean_fn = part.fst().to_std_string();
        try {
            // we first write to a temp file and then move it to the correct path (possibly deleting an older file)
            // so that we neither expose partially-written files nor modify possibly memory-mapped files
            std::string olean_tmp_fn = olean_fn + ".tmp." + std::to_string(pid);
            tmp_fnames.push_back(olean_tmp_fn);

            std::ofstream out(olean_tmp_fn, std::ios_base::binary);

            if (compactor.size() % ALIGN != 0) {
                compactor.alloc(ALIGN - (compactor.size() % ALIGN));
            }
            size_t file_offset = compactor.size();

            compactor.alloc(sizeof(olean_header));
            olean_header header = {};
            // see/sync with file format description above
            header.base_addr = base_addr + file_offset;
            strncpy(header.lean_version, get_short_version_string().c_str(), sizeof(header.lean_version));
            strncpy(header.githash, LEAN_GITHASH, sizeof(header.githash));
            out.write(reinterpret_cast<char *>(&header), sizeof(header));

            compactor(part.snd().raw());

            if (out.fail()) {
                throw exception((sstream() << "failed to create file '" << olean_fn << "'").str());
            }
            out.write(static_cast<char const *>(compactor.data()) + file_offset + sizeof(olean_header), compactor.size() - file_offset - sizeof(olean_header));
            out.close();
        } catch (exception & ex) {
            return io_result_mk_error((sstream() << "failed to write '" << olean_fn << "': " << ex.what()).str());
        }
    }

    for (unsigned i = 0; i < parts.size(); i++) {
        std::string olean_fn = parts[i].fst().to_std_string();
        while (std::rename(tmp_fnames[i].c_str(), olean_fn.c_str()) != 0) {
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
    }
    return io_result_mk_ok(box(0));
}

struct module_file {
    std::string m_fname;
    std::ifstream m_in;
    char * m_base_addr;
    size_t m_size;
    char * m_buffer;
    std::function<void()> m_free_data;
};

extern "C" LEAN_EXPORT object * lean_read_module_data_parts(b_obj_arg ofnames, object *) {
    array_ref<string_ref> fnames(ofnames, true);

    // first read in all headers
    std::vector<module_file> files;
    for (auto const & fname : fnames) {
        std::string olean_fn = fname.to_std_string();
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
            if (!in.read(reinterpret_cast<char *>(&header), sizeof(header))
                || memcmp(header.marker, default_header.marker, sizeof(header.marker)) != 0) {
                return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "', invalid header").str());
            }
            in.seekg(0);
            if (header.version != default_header.version || header.flags != default_header.flags
#ifdef LEAN_CHECK_OLEAN_VERSION
                || strncmp(header.githash, LEAN_GITHASH, sizeof(header.githash)) != 0
#endif
            ) {
                return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "', incompatible header").str());
            }
            char * base_addr = reinterpret_cast<char *>(header.base_addr);
            files.push_back({olean_fn, std::move(in), base_addr, size, nullptr, nullptr});
        } catch (exception & ex) {
            return io_result_mk_error((sstream() << "failed to read '" << olean_fn << "': " << ex.what()).str());
        }
    }

#ifndef LEAN_MMAP
    bool is_mmap = false;
#else
    // now try mmapping *all* files
    bool is_mmap = true;
    for (auto & file : files) {
        std::string const & olean_fn = file.m_fname;
        char * base_addr = file.m_base_addr;
        try {
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
            char * buffer = static_cast<char *>(MapViewOfFileEx(h_map, FILE_MAP_READ, 0, 0, 0, base_addr));
            lean_always_assert(CloseHandle(h_map));
            lean_always_assert(CloseHandle(h_olean_fn));
            if (!buffer) {
                is_mmap = false;
                break;
            }
            file.m_free_data = [=]() {
                lean_always_assert(UnmapViewOfFile(base_addr));
            };
#else
            int fd = open(olean_fn.c_str(), O_RDONLY);
            if (fd == -1) {
                return io_result_mk_error((sstream() << "failed to open '" << olean_fn << "': " << strerror(errno)).str());
            }
            char * buffer = static_cast<char *>(mmap(base_addr, file.m_size, PROT_READ, MAP_PRIVATE, fd, 0));
            if (buffer == MAP_FAILED) {
                is_mmap = false;
                break;
            }
            close(fd);
            size_t size = file.m_size;
            file.m_free_data = [=]() {
                lean_always_assert(munmap(buffer, size) == 0);
            };
#endif
            if (buffer == base_addr) {
                file.m_buffer = buffer;
            } else {
                is_mmap = false;
                break;
            }
        } catch (exception & ex) {
            return io_result_mk_error((sstream() << "failed to read '" << olean_fn << "': " << ex.what()).str());
        }
    }
#endif

    // if *any* file failed to mmap, read all of them into a single big allocation so that offsets
    // between them are unchanged
    if (!is_mmap) {
        for (auto & file : files) {
            if (file.m_free_data) {
                file.m_free_data();
                file.m_free_data = {};
            }
        }

        size_t big_size = files[files.size()-1].m_base_addr + files[files.size()-1].m_size - files[0].m_base_addr;
        char * big_buffer = static_cast<char *>(malloc(big_size));
        for (auto & file : files) {
            std::string const & olean_fn = file.m_fname;
            try {
                file.m_buffer = big_buffer + (file.m_base_addr - files[0].m_base_addr);
                file.m_in.read(file.m_buffer, file.m_size);
                if (!file.m_in) {
                    return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "'").str());
                }
                file.m_in.close();
            } catch (exception & ex) {
                return io_result_mk_error((sstream() << "failed to read '" << olean_fn << "': " << ex.what()).str());
            }
        }
        files[0].m_free_data = [=]() {
            free_sized(big_buffer, big_size);
        };
    }

    std::vector<object_ref> res;
    for (auto & file : files) {
        compacted_region * region =
        new compacted_region(file.m_size - sizeof(olean_header), file.m_buffer + sizeof(olean_header), static_cast<char *>(file.m_base_addr) + sizeof(olean_header), is_mmap, file.m_free_data);
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

        res.push_back(object_ref(mod_region));
    }
    return io_result_mk_ok(to_array(res));
}
}
