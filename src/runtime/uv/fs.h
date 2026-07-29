/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

static lean_external_class * g_uv_file_external_class = NULL;
static lean_external_class * g_uv_dir_external_class = NULL;
void initialize_libuv_fs();

#ifndef LEAN_EMSCRIPTEN
using namespace std;

// Structure for managing a single open file. `m_file` becomes -1 once the descriptor is closed, and
// `m_busy` marks an operation as in flight, so that reads never race a concurrent close.
typedef struct {
    uv_file    m_file;   // LibUV file descriptor.
    uv_mutex_t m_mutex;  // Guards `m_file` and `m_busy`.
    bool       m_busy;   // Flag indicating an operation currently holds the descriptor.
} lean_uv_file_object;

// Structure for managing a single open directory stream, tracked exactly like `lean_uv_file_object`
// except that a closed stream is marked by a null `m_dir`.
typedef struct {
    uv_dir_t*  m_dir;    // LibUV directory stream.
    uv_mutex_t m_mutex;  // Guards `m_dir` and `m_busy`.
    bool       m_busy;   // Flag indicating an operation currently holds the stream.
} lean_uv_dir_object;

// =======================================
// File object manipulation functions.
static inline lean_object* lean_uv_file_new(lean_uv_file_object* f) { return lean_alloc_external(g_uv_file_external_class, f); }
static inline lean_uv_file_object* lean_to_uv_file(lean_object* o) { return (lean_uv_file_object*)(lean_get_external_data(o)); }

// =======================================
// Directory object manipulation functions.
static inline lean_object* lean_uv_dir_new(lean_uv_dir_object* d) { return lean_alloc_external(g_uv_dir_external_class, d); }
static inline lean_uv_dir_object* lean_to_uv_dir(lean_object* o) { return (lean_uv_dir_object*)(lean_get_external_data(o)); }
#endif

// =======================================
// Filesystem operations
//
// Each wraps the corresponding libuv `uv_fs_*` request run with no callback, so the call blocks until
// the request completes. Open files are identified by the opaque `File` external object.

extern "C" LEAN_EXPORT uint32_t lean_uv_fs_open_flags(uint8_t read, uint8_t write, uint8_t append, uint8_t truncate, uint8_t create, uint8_t create_new);
extern "C" LEAN_EXPORT uint32_t lean_uv_fs_access_flags(uint8_t read, uint8_t write, uint8_t execution);
extern "C" LEAN_EXPORT uint8_t lean_uv_fs_file_type_of_mode(uint64_t mode);
extern "C" LEAN_EXPORT uint8_t lean_uv_fs_file_type_of_dirent(uint8_t type);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_open(b_obj_arg path, uint32_t flags, uint32_t mode);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_close(b_obj_arg file);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_read(b_obj_arg file, size_t len, int64_t offset, obj_arg buf);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_write(b_obj_arg file, b_obj_arg data, int64_t offset);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fsync(b_obj_arg file);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fdatasync(b_obj_arg file);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_ftruncate(b_obj_arg file, uint64_t len);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fstat(b_obj_arg file);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fchmod(b_obj_arg file, uint32_t mode);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fchown(b_obj_arg file, uint32_t uid, uint32_t gid);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_futime(b_obj_arg file, double atime, double mtime);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_sendfile(b_obj_arg out_file, b_obj_arg in_file, int64_t in_offset, size_t length);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lock(b_obj_arg file, uint8_t exclusive);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_trylock(b_obj_arg file, uint8_t exclusive);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_unlock(b_obj_arg file);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_copyfile(b_obj_arg src, b_obj_arg dst, uint32_t flags);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_unlink(b_obj_arg path);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_rename(b_obj_arg src, b_obj_arg dst);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_link(b_obj_arg path, b_obj_arg link);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_symlink(b_obj_arg target, b_obj_arg path, uint32_t flags);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_readlink(b_obj_arg path);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_chmod(b_obj_arg path, uint32_t mode);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_chown(b_obj_arg path, uint32_t uid, uint32_t gid);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lchown(b_obj_arg path, uint32_t uid, uint32_t gid);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_utime(b_obj_arg path, double atime, double mtime);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lutime(b_obj_arg path, double atime, double mtime);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_stat(b_obj_arg path);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lstat(b_obj_arg path);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_statfs(b_obj_arg path);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_access(b_obj_arg path, uint32_t mode);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_mkstemp(b_obj_arg tmpl);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_mkdtemp(b_obj_arg tmpl);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_mkdir(b_obj_arg path, uint32_t mode);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_rmdir(b_obj_arg path);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_opendir(b_obj_arg path);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_closedir(b_obj_arg dir);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_readdir(b_obj_arg dir);

}
