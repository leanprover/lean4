/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Gabriel Ebner, Sebastian Ullrich
*/
#include <unordered_map>
#include <vector>
#include <utility>
#include <string>
#include <sstream>
#include <fstream>
#include <algorithm>
#include <sys/stat.h>
#include <lean/thread.h>
#include <lean/interrupt.h>
#include <lean/sstream.h>
#include <lean/hash.h>
#include <lean/io.h>
#include <lean/compact.h>
#include "util/io.h"
#include "util/buffer.h"
#include "util/name_map.h"
#include "util/file_lock.h"
#include "library/module.h"
#include "library/constants.h"
#include "library/time_task.h"
#include "library/util.h"

#ifndef LEAN_WINDOWS
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
// manually padded to multiple of word size, see `initialize_module`
static char const * g_olean_header   = "oleanfile!!!!!!!";

extern "C" object * lean_save_module_data(b_obj_arg fname, b_obj_arg mod, b_obj_arg mdata, object *) {
    std::string olean_fn(string_cstr(fname));
    try {
        exclusive_file_lock output_lock(olean_fn);
        std::ofstream out(olean_fn, std::ios_base::binary);
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
        base_addr = base_addr & ((1LL<<47) - 1);
        // `mmap` addresses must be page-aligned. The default (non-huge) page size on x86-64 is 4KB.
        base_addr = base_addr & ~((1LL<<12) - 1);

        object_compactor compactor(reinterpret_cast<void *>(base_addr + strlen(g_olean_header) + sizeof(base_addr)));
        compactor(mdata);
        out.write(g_olean_header, strlen(g_olean_header));
        out.write(reinterpret_cast<char *>(&base_addr), sizeof(base_addr));
        out.write(static_cast<char const *>(compactor.data()), compactor.size());
        out.close();
        return io_result_mk_ok(box(0));
    } catch (exception & ex) {
        return io_result_mk_error((sstream() << "failed to write '" << olean_fn << "': " << ex.what()).str());
    }
}

extern "C" object * lean_read_module_data(object * fname, object *) {
    std::string olean_fn(string_cstr(fname));
    try {
        shared_file_lock olean_lock(olean_fn);
        std::ifstream in(olean_fn, std::ios_base::binary);
        if (in.fail()) {
            return io_result_mk_error((sstream() << "failed to open file '" << olean_fn << "'").str());
        }
        /* Get file size */
        in.seekg(0, in.end);
        size_t size = in.tellg();
        in.seekg(0);
        size_t header_size = strlen(g_olean_header);
        if (size < header_size) {
            return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "', invalid header").str());
        }
        char * header = new char[header_size];
        in.read(header, header_size);
        if (strncmp(header, g_olean_header, header_size) != 0) {
            return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "', invalid header").str());
        }
        delete[] header;
        char * base_addr;
        in.read(reinterpret_cast<char *>(&base_addr), sizeof(base_addr));
        header_size += sizeof(base_addr);
        char * buffer = nullptr;
        bool is_mmap = false;
#ifndef LEAN_WINDOWS
        int fd = open(olean_fn.c_str(), O_RDONLY);
        if (fd == -1) {
            return io_result_mk_error((sstream() << "failed to open '" << olean_fn << "': " << strerror(errno)).str());
        }
        buffer = static_cast<char *>(mmap(base_addr, size, PROT_READ, MAP_PRIVATE, fd, 0));
        close(fd);
        if (buffer == base_addr) {
            buffer += header_size;
            is_mmap = true;
        } else {
            if (munmap(buffer, size)) {
                return io_result_mk_error((sstream() << "munmap() failed: " << strerror(errno)).str());
            }
            buffer = nullptr;
        }
#endif
        if (!buffer) {
            // use `malloc` here as expected by `compacted_region`
            buffer = static_cast<char *>(malloc(size - header_size));
            in.read(buffer, size - header_size);
            if (!in) {
                return io_result_mk_error((sstream() << "failed to read file '" << olean_fn << "'").str());
            }
        }
        in.close();

        compacted_region * region = new compacted_region(size - header_size, buffer, base_addr + header_size, is_mmap ? base_addr : 0);
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
