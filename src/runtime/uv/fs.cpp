/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sofia Rodrigues
*/
#include "runtime/uv/fs.h"
#include "runtime/sstream.h"
#include <cstdlib>
#include <cstring>
#include <cerrno>
#include <sys/stat.h>

#ifdef LEAN_WINDOWS
#include <windows.h>
#else
#include <sys/file.h>
#include <unistd.h>
#endif

// `uv_fs_access` takes its mode as a combination of `F_OK`, `R_OK`, `W_OK` and `X_OK`, which POSIX
// declares in `<unistd.h>`. Windows has no such header; libuv reads the same bits out of the mode it
// is handed and only honours `W_OK`, so the fallbacks below are the values POSIX fixes and MSVC's
// `_access` documents.
#ifndef F_OK
#define F_OK 0
#endif
#ifndef R_OK
#define R_OK 4
#endif
#ifndef W_OK
#define W_OK 2
#endif
#ifndef X_OK
#define X_OK 1
#endif

// MSVC's `<sys/stat.h>` ships the `_S_IF*` constants but almost none of the `S_IS*` macros, and has
// no bits at all for symlinks, block devices or sockets — libuv reports those entries as `unknown`.
#ifdef _MSC_VER
#ifndef S_ISREG
#define S_ISREG(mode) (((mode) & _S_IFMT) == _S_IFREG)
#endif
#ifndef S_ISDIR
#define S_ISDIR(mode) (((mode) & _S_IFMT) == _S_IFDIR)
#endif
#ifndef S_ISCHR
#define S_ISCHR(mode) (((mode) & _S_IFMT) == _S_IFCHR)
#endif
#ifndef S_ISFIFO
#define S_ISFIFO(mode) (((mode) & _S_IFMT) == _S_IFIFO)
#endif
#endif

namespace lean {

// Constructors of `Std.FS.FileType`. Every one is nullary, so Lean represents the type as a bare
// constructor tag rather than an object, and returning the tag builds the value directly. Their
// order has to match the declaration.
enum file_type : uint8_t {
    FILE_TYPE_FILE = 0,
    FILE_TYPE_DIR = 1,
    FILE_TYPE_SYMLINK = 2,
    FILE_TYPE_BLOCK_DEVICE = 3,
    FILE_TYPE_CHAR_DEVICE = 4,
    FILE_TYPE_FIFO = 5,
    FILE_TYPE_SOCKET = 6,
    FILE_TYPE_UNKNOWN = 7,
};

extern "C" LEAN_EXPORT uint8_t lean_uv_fs_file_type_of_mode(uint64_t mode) {
    if (S_ISREG(mode)) return FILE_TYPE_FILE;
    if (S_ISDIR(mode)) return FILE_TYPE_DIR;
    if (S_ISCHR(mode)) return FILE_TYPE_CHAR_DEVICE;
    if (S_ISFIFO(mode)) return FILE_TYPE_FIFO;
#ifdef S_ISLNK
    if (S_ISLNK(mode)) return FILE_TYPE_SYMLINK;
#endif
#ifdef S_ISBLK
    if (S_ISBLK(mode)) return FILE_TYPE_BLOCK_DEVICE;
#endif
#ifdef S_ISSOCK
    if (S_ISSOCK(mode)) return FILE_TYPE_SOCKET;
#endif
    return FILE_TYPE_UNKNOWN;
}

extern "C" LEAN_EXPORT uint32_t lean_uv_fs_access_flags(uint8_t read, uint8_t write, uint8_t execution) {
    int mode = F_OK;
    if (read) mode |= R_OK;
    if (write) mode |= W_OK;
    if (execution) mode |= X_OK;
    return static_cast<uint32_t>(mode);
}

#ifndef LEAN_EMSCRIPTEN

static void lean_uv_file_finalizer(void* ptr) {
    lean_uv_file_object* f = (lean_uv_file_object*)ptr;
    if (f->m_file != -1) {
        uv_fs_t req;
        uv_fs_close(nullptr, &req, f->m_file, nullptr);
        uv_fs_req_cleanup(&req);
    }
    uv_mutex_destroy(&f->m_mutex);
    free(f);
}

static void lean_uv_dir_finalizer(void* ptr) {
    lean_uv_dir_object* d = (lean_uv_dir_object*)ptr;
    if (d->m_dir != nullptr) {
        uv_fs_t req;
        uv_fs_closedir(nullptr, &req, d->m_dir, nullptr);
        uv_fs_req_cleanup(&req);
    }
    uv_mutex_destroy(&d->m_mutex);
    free(d);
}

// Neither external object holds owned `lean_object*` fields, so there is nothing for the `foreach`
// callback (used for cycle collection) to visit.
static void lean_uv_fs_foreach(void*, lean_object*) {}

void initialize_libuv_fs() {
    g_uv_file_external_class = lean_register_external_class(lean_uv_file_finalizer, lean_uv_fs_foreach);
    g_uv_dir_external_class = lean_register_external_class(lean_uv_dir_finalizer, lean_uv_fs_foreach);
}

static lean_object* lean_uv_file_of_fd(uv_file fd) {
    lean_uv_file_object* f = (lean_uv_file_object*)malloc(sizeof(lean_uv_file_object));

    if (f == nullptr) {
        uv_fs_t req;
        uv_fs_close(nullptr, &req, fd, nullptr);
        uv_fs_req_cleanup(&req);
        return nullptr;
    }

    f->m_file = fd;
    uv_mutex_init(&f->m_mutex);
    f->m_busy = false;

    lean_object* obj = lean_uv_file_new(f);
    lean_mark_mt(obj);
    return obj;
}

static lean_object* lean_uv_dir_of_raw(uv_dir_t* dir) {
    lean_uv_dir_object* d = (lean_uv_dir_object*)malloc(sizeof(lean_uv_dir_object));

    if (d == nullptr) {
        uv_fs_t req;
        uv_fs_closedir(nullptr, &req, dir, nullptr);
        uv_fs_req_cleanup(&req);
        return nullptr;
    }

    d->m_dir = dir;
    uv_mutex_init(&d->m_mutex);
    d->m_busy = false;

    lean_object* obj = lean_uv_dir_new(d);
    lean_mark_mt(obj);
    return obj;
}

static int lean_uv_file_claim(lean_uv_file_object* f, uv_file* out_fd) {
    uv_mutex_lock(&f->m_mutex);
    if (f->m_file == -1) { uv_mutex_unlock(&f->m_mutex); return UV_EBADF; }
    if (f->m_busy) { uv_mutex_unlock(&f->m_mutex); return UV_EALREADY; }
    f->m_busy = true;
    *out_fd = f->m_file;
    uv_mutex_unlock(&f->m_mutex);
    return 0;
}

static int lean_uv_file_claim_close(lean_uv_file_object* f, uv_file* out_fd) {
    uv_mutex_lock(&f->m_mutex);
    if (f->m_file == -1) { uv_mutex_unlock(&f->m_mutex); return UV_EBADF; }
    if (f->m_busy) { uv_mutex_unlock(&f->m_mutex); return UV_EALREADY; }
    f->m_busy = true;
    *out_fd = f->m_file;
    f->m_file = -1;
    uv_mutex_unlock(&f->m_mutex);
    return 0;
}

static void lean_uv_file_release(lean_uv_file_object* f) {
    uv_mutex_lock(&f->m_mutex);
    f->m_busy = false;
    uv_mutex_unlock(&f->m_mutex);
}

static int lean_uv_dir_claim(lean_uv_dir_object* d, uv_dir_t** out_dir) {
    uv_mutex_lock(&d->m_mutex);
    if (d->m_dir == nullptr) { uv_mutex_unlock(&d->m_mutex); return UV_EBADF; }
    if (d->m_busy) { uv_mutex_unlock(&d->m_mutex); return UV_EALREADY; }
    d->m_busy = true;
    *out_dir = d->m_dir;
    uv_mutex_unlock(&d->m_mutex);
    return 0;
}

static int lean_uv_dir_claim_close(lean_uv_dir_object* d, uv_dir_t** out_dir) {
    uv_mutex_lock(&d->m_mutex);
    if (d->m_dir == nullptr) { uv_mutex_unlock(&d->m_mutex); return UV_EBADF; }
    if (d->m_busy) { uv_mutex_unlock(&d->m_mutex); return UV_EALREADY; }
    d->m_busy = true;
    *out_dir = d->m_dir;
    d->m_dir = nullptr;
    uv_mutex_unlock(&d->m_mutex);
    return 0;
}

static void lean_uv_dir_release(lean_uv_dir_object* d) {
    uv_mutex_lock(&d->m_mutex);
    d->m_busy = false;
    uv_mutex_unlock(&d->m_mutex);
}

template<typename Body>
static lean_obj_res fs_with_fd(b_obj_arg file, Body body) {
    lean_uv_file_object* f = lean_to_uv_file(file);
    uv_file fd;

    int claim = lean_uv_file_claim(f, &fd);

    if (claim < 0) return lean_io_result_mk_error(lean_decode_uv_error(claim, nullptr));

    lean_obj_res res = body(fd);

    lean_uv_file_release(f);

    return res;
}

static lean_obj_res fs_result(lean_object* value) {
    return value == nullptr
        ? lean_io_result_mk_error(decode_io_error(ENOMEM, nullptr))
        : lean_io_result_mk_ok(value);
}

template<typename Submit, typename Finish>
static lean_obj_res fs_file_op(b_obj_arg file, Submit submit, Finish finish) {
    return fs_with_fd(file, [&](uv_file fd) {
        uv_fs_t req;
        int result = submit(&req, fd);
        lean_obj_res res = result < 0
            ? lean_io_result_mk_error(lean_decode_uv_error(result, nullptr))
            : fs_result(finish(&req, result));
        uv_fs_req_cleanup(&req);
        return res;
    });
}

template<typename Submit, typename Finish>
static lean_obj_res fs_path_op(b_obj_arg path, Submit submit, Finish finish) {
    const char* path_cstr = lean_string_cstr(path);
    if (strlen(path_cstr) != lean_string_size(path) - 1) return mk_embedded_nul_error(path);

    uv_fs_t req;
    int result = submit(&req, path_cstr);
    lean_obj_res res;
    if (result < 0) {
        lean_inc(path);
        res = lean_io_result_mk_error(lean_decode_uv_error(result, path));
    } else {
        res = fs_result(finish(&req, result));
    }
    uv_fs_req_cleanup(&req);
    return res;
}

template<typename Submit>
static lean_obj_res fs_path2_op(b_obj_arg first, b_obj_arg second, Submit submit) {
    const char* first_cstr = lean_string_cstr(first);
    if (strlen(first_cstr) != lean_string_size(first) - 1) return mk_embedded_nul_error(first);
    const char* second_cstr = lean_string_cstr(second);
    if (strlen(second_cstr) != lean_string_size(second) - 1) return mk_embedded_nul_error(second);

    uv_fs_t req;
    int result = submit(&req, first_cstr, second_cstr);
    uv_fs_req_cleanup(&req);
    if (result < 0) return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    return lean_io_result_mk_ok(lean_box(0));
}

static lean_object* fs_unit(uv_fs_t*, int) { return lean_box(0); }
static lean_object* fs_usize(uv_fs_t*, int result) { return lean_box_usize((size_t)result); }

static lean_object* fs_timespec(uv_timespec_t const& ts) {
    lean_object* o = lean_alloc_ctor(0, 0, 16);
    lean_ctor_set_uint64(o, 0, (uint64_t)(int64_t)ts.tv_sec);
    lean_ctor_set_uint64(o, 8, (uint64_t)(int64_t)ts.tv_nsec);
    return o;
}

static lean_object* fs_stat(uv_fs_t* req, int) {
    uv_stat_t const& st = req->statbuf;
    lean_object* o = lean_alloc_ctor(0, 4, 96);
    lean_ctor_set(o, 0, fs_timespec(st.st_atim));
    lean_ctor_set(o, 1, fs_timespec(st.st_mtim));
    lean_ctor_set(o, 2, fs_timespec(st.st_ctim));
    lean_ctor_set(o, 3, fs_timespec(st.st_birthtim));
    lean_ctor_set_uint64(o, 32 + 0 * 8, st.st_dev);
    lean_ctor_set_uint64(o, 32 + 1 * 8, st.st_mode);
    lean_ctor_set_uint64(o, 32 + 2 * 8, st.st_nlink);
    lean_ctor_set_uint64(o, 32 + 3 * 8, st.st_uid);
    lean_ctor_set_uint64(o, 32 + 4 * 8, st.st_gid);
    lean_ctor_set_uint64(o, 32 + 5 * 8, st.st_rdev);
    lean_ctor_set_uint64(o, 32 + 6 * 8, st.st_ino);
    lean_ctor_set_uint64(o, 32 + 7 * 8, st.st_size);
    lean_ctor_set_uint64(o, 32 + 8 * 8, st.st_blksize);
    lean_ctor_set_uint64(o, 32 + 9 * 8, st.st_blocks);
    lean_ctor_set_uint64(o, 32 + 10 * 8, st.st_flags);
    lean_ctor_set_uint64(o, 32 + 11 * 8, st.st_gen);
    return o;
}

static lean_object* fs_statfs(uv_fs_t* req, int) {
    uv_statfs_t const& s = *(uv_statfs_t*)req->ptr;
    lean_object* o = lean_alloc_ctor(0, 0, 56);
    lean_ctor_set_uint64(o, 0 * 8, s.f_type);
    lean_ctor_set_uint64(o, 1 * 8, s.f_bsize);
    lean_ctor_set_uint64(o, 2 * 8, s.f_blocks);
    lean_ctor_set_uint64(o, 3 * 8, s.f_bfree);
    lean_ctor_set_uint64(o, 4 * 8, s.f_bavail);
    lean_ctor_set_uint64(o, 5 * 8, s.f_files);
    lean_ctor_set_uint64(o, 6 * 8, s.f_ffree);
    return o;
}

extern "C" LEAN_EXPORT uint32_t lean_uv_fs_open_flags(uint8_t read, uint8_t write, uint8_t append, uint8_t truncate, uint8_t create, uint8_t create_new) {
    int flags = 0;

    if (write && read) {
        flags |= UV_FS_O_RDWR;
    } else if (write) {
        flags |= UV_FS_O_WRONLY;
    } else {
        flags |= UV_FS_O_RDONLY;
    }

    if (append) flags |= UV_FS_O_APPEND;
    if (truncate) flags |= UV_FS_O_TRUNC;
    if (create || create_new) flags |= UV_FS_O_CREAT;
    if (create_new) flags |= UV_FS_O_EXCL;

    return static_cast<uint32_t>(flags);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_open(b_obj_arg path, uint32_t flags, uint32_t mode) {
    return fs_path_op(path,
        [=](uv_fs_t* req, const char* path_cstr) {
            int fd = uv_fs_open(nullptr, req, path_cstr, (int)flags, (int)mode, nullptr);
            if (fd < 0) return fd;

            // Opening a directory read-only succeeds on POSIX and only later reads fail with
            // `EISDIR`. Checking the descriptor rather than the path leaves no TOCTOU window.
            uv_fs_t stat_req;
            int stat_result = uv_fs_fstat(nullptr, &stat_req, fd, nullptr);
            bool regular = stat_result >= 0 && S_ISREG(stat_req.statbuf.st_mode);
            uv_fs_req_cleanup(&stat_req);

            if (regular) return fd;

            uv_fs_t close_req;
            uv_fs_close(nullptr, &close_req, fd, nullptr);
            uv_fs_req_cleanup(&close_req);

            return stat_result < 0 ? stat_result : UV_EISDIR;
        },
        [](uv_fs_t*, int fd) { return lean_uv_file_of_fd((uv_file)fd); });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_close(b_obj_arg file) {
    lean_uv_file_object* f = lean_to_uv_file(file);
    uv_file fd;
    int claim = lean_uv_file_claim_close(f, &fd);
    if (claim < 0) return lean_io_result_mk_error(lean_decode_uv_error(claim, nullptr));

    uv_fs_t req;
    int result = uv_fs_close(nullptr, &req, fd, nullptr);
    uv_fs_req_cleanup(&req);
    if (result < 0) return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_mkstemp(b_obj_arg tmpl) {
    return fs_path_op(tmpl,
        [](uv_fs_t* req, const char* tmpl_cstr) { return uv_fs_mkstemp(nullptr, req, tmpl_cstr, nullptr); },
        [](uv_fs_t* req, int fd) -> lean_object* {
            // `req->path` is the template with its trailing `XXXXXX` filled in, i.e. the created file.
            lean_object* path = lean_mk_string(req->path);
            lean_object* file = lean_uv_file_of_fd((uv_file)fd);

            if (file == nullptr) {
                lean_dec(path);
                return (lean_object*)nullptr;
            }

            lean_object* pair = lean_alloc_ctor(0, 2, 0);
            lean_ctor_set(pair, 0, file);
            lean_ctor_set(pair, 1, path);
            return pair;
        });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_read(b_obj_arg file, size_t len, int64_t offset, obj_arg buf) {
    lean_uv_file_object* f = lean_to_uv_file(file);
    uv_file fd;
    int claim = lean_uv_file_claim(f, &fd);
    if (claim < 0) { lean_dec(buf); return lean_io_result_mk_error(lean_decode_uv_error(claim, nullptr)); }

    // Append the new bytes after whatever `buf` already holds, reusing its storage when it is uniquely
    // owned and large enough. `arr` stays null if the resulting size is not representable.
    size_t existing = lean_sarray_size(buf);
    lean_object* arr = nullptr;
    if (!lean_usize_add_would_overflow(existing, len)) {
        size_t needed = existing + len;
        if (lean_is_exclusive(buf) && lean_sarray_capacity(buf) >= needed) {
            arr = buf;
        } else if (!lean_alloc_sarray_would_overflow(1, needed)) {
            arr = lean_alloc_sarray(1, existing, needed);
            memcpy(lean_sarray_cptr(arr), lean_sarray_cptr(buf), existing);
            lean_dec(buf);
        }
    }
    if (arr == nullptr) {
        lean_dec(buf);
        lean_uv_file_release(f);
        return lean_io_result_mk_error(decode_io_error(ENOMEM, nullptr));
    }

    uv_buf_t uvbuf = uv_buf_init((char*)lean_sarray_cptr(arr) + existing, len);
    uv_fs_t req;
    int result = uv_fs_read(nullptr, &req, fd, &uvbuf, 1, offset, nullptr);
    uv_fs_req_cleanup(&req);
    lean_uv_file_release(f);

    if (result < 0) {
        lean_dec(arr);
        return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    }
    lean_sarray_set_size(arr, existing + (size_t)result);
    return lean_io_result_mk_ok(arr);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_write(b_obj_arg file, b_obj_arg data, int64_t offset) {
    return fs_file_op(file,
        [=](uv_fs_t* req, uv_file fd) {
            uv_buf_t uvbuf = uv_buf_init((char*)lean_sarray_cptr(data), lean_sarray_size(data));
            return uv_fs_write(nullptr, req, fd, &uvbuf, 1, offset, nullptr);
        },
        fs_usize);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_sendfile(b_obj_arg out_file, b_obj_arg in_file, int64_t in_offset, size_t length) {
    return fs_with_fd(out_file, [=](uv_file out_fd) {
        return fs_file_op(in_file,
            [=](uv_fs_t* req, uv_file in_fd) { return uv_fs_sendfile(nullptr, req, out_fd, in_fd, in_offset, length, nullptr); },
            fs_usize);
    });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fsync(b_obj_arg file) {
    return fs_file_op(file,
        [](uv_fs_t* req, uv_file fd) { return uv_fs_fsync(nullptr, req, fd, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fdatasync(b_obj_arg file) {
    return fs_file_op(file,
        [](uv_fs_t* req, uv_file fd) { return uv_fs_fdatasync(nullptr, req, fd, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_ftruncate(b_obj_arg file, uint64_t len) {
    return fs_file_op(file,
        [=](uv_fs_t* req, uv_file fd) { return uv_fs_ftruncate(nullptr, req, fd, (int64_t)len, nullptr); },
        fs_unit);
}

// =======================================
// Metadata on an open descriptor.

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fstat(b_obj_arg file) {
    return fs_file_op(file,
        [](uv_fs_t* req, uv_file fd) { return uv_fs_fstat(nullptr, req, fd, nullptr); },
        fs_stat);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fchmod(b_obj_arg file, uint32_t mode) {
    return fs_file_op(file,
        [=](uv_fs_t* req, uv_file fd) { return uv_fs_fchmod(nullptr, req, fd, (int)mode, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fchown(b_obj_arg file, uint32_t uid, uint32_t gid) {
    return fs_file_op(file,
        [=](uv_fs_t* req, uv_file fd) { return uv_fs_fchown(nullptr, req, fd, (uv_uid_t)uid, (uv_gid_t)gid, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_futime(b_obj_arg file, double atime, double mtime) {
    return fs_file_op(file,
        [=](uv_fs_t* req, uv_file fd) { return uv_fs_futime(nullptr, req, fd, atime, mtime, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lock(b_obj_arg file, uint8_t exclusive) {
    return fs_with_fd(file, [=](uv_file fd) -> lean_obj_res {
#ifdef LEAN_WINDOWS
        OVERLAPPED o = {0};
        if (LockFileEx((HANDLE)uv_get_osfhandle(fd), exclusive ? LOCKFILE_EXCLUSIVE_LOCK : 0, 0, MAXDWORD, MAXDWORD, &o) == 0)
            return lean_io_result_mk_error(mk_string((sstream() << "LockFileEx failed with code " << GetLastError()).str()));
#else
        if (flock(fd, exclusive ? LOCK_EX : LOCK_SH) != 0)
            return lean_io_result_mk_error(decode_io_error(errno, nullptr));
#endif
        return lean_io_result_mk_ok(lean_box(0));
    });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_trylock(b_obj_arg file, uint8_t exclusive) {
    return fs_with_fd(file, [=](uv_file fd) -> lean_obj_res {
#ifdef LEAN_WINDOWS
        OVERLAPPED o = {0};
        DWORD flags = (exclusive ? LOCKFILE_EXCLUSIVE_LOCK : 0) | LOCKFILE_FAIL_IMMEDIATELY;
        if (LockFileEx((HANDLE)uv_get_osfhandle(fd), flags, 0, MAXDWORD, MAXDWORD, &o) != 0)
            return lean_io_result_mk_ok(lean_box(1));
        // Read once: anything in between, including an allocation, may reset the thread's last error.
        DWORD err = GetLastError();
        if (err == ERROR_LOCK_VIOLATION) return lean_io_result_mk_ok(lean_box(0));
        return lean_io_result_mk_error(mk_string((sstream() << "LockFileEx failed with code " << err).str()));
#else
        if (flock(fd, (exclusive ? LOCK_EX : LOCK_SH) | LOCK_NB) == 0) return lean_io_result_mk_ok(lean_box(1));
        if (errno == EWOULDBLOCK) return lean_io_result_mk_ok(lean_box(0));
        return lean_io_result_mk_error(decode_io_error(errno, nullptr));
#endif
    });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_unlock(b_obj_arg file) {
    return fs_with_fd(file, [](uv_file fd) -> lean_obj_res {
#ifdef LEAN_WINDOWS
        OVERLAPPED o = {0};
        if (UnlockFileEx((HANDLE)uv_get_osfhandle(fd), 0, MAXDWORD, MAXDWORD, &o) == 0) {
            DWORD err = GetLastError();
            if (err != ERROR_NOT_LOCKED)
                return lean_io_result_mk_error(mk_string((sstream() << "UnlockFileEx failed with code " << err).str()));
        }
#else
        if (flock(fd, LOCK_UN) != 0)
            return lean_io_result_mk_error(decode_io_error(errno, nullptr));
#endif
        return lean_io_result_mk_ok(lean_box(0));
    });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_unlink(b_obj_arg path) {
    return fs_path_op(path,
        [](uv_fs_t* req, const char* path_cstr) { return uv_fs_unlink(nullptr, req, path_cstr, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_copyfile(b_obj_arg src, b_obj_arg dst, uint32_t flags) {
    return fs_path2_op(src, dst,
        [=](uv_fs_t* req, const char* src_cstr, const char* dst_cstr) { return uv_fs_copyfile(nullptr, req, src_cstr, dst_cstr, (int)flags, nullptr); });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_rename(b_obj_arg src, b_obj_arg dst) {
    return fs_path2_op(src, dst,
        [](uv_fs_t* req, const char* src_cstr, const char* dst_cstr) { return uv_fs_rename(nullptr, req, src_cstr, dst_cstr, nullptr); });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_link(b_obj_arg path, b_obj_arg link) {
    return fs_path2_op(path, link,
        [](uv_fs_t* req, const char* path_cstr, const char* link_cstr) { return uv_fs_link(nullptr, req, path_cstr, link_cstr, nullptr); });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_symlink(b_obj_arg target, b_obj_arg path, uint32_t flags) {
    return fs_path2_op(target, path,
        [=](uv_fs_t* req, const char* target_cstr, const char* path_cstr) { return uv_fs_symlink(nullptr, req, target_cstr, path_cstr, (int)flags, nullptr); });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_readlink(b_obj_arg path) {
    return fs_path_op(path,
        [](uv_fs_t* req, const char* path_cstr) { return uv_fs_readlink(nullptr, req, path_cstr, nullptr); },
        [](uv_fs_t* req, int) { return lean_mk_string((const char*)req->ptr); });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_chmod(b_obj_arg path, uint32_t mode) {
    return fs_path_op(path,
        [=](uv_fs_t* req, const char* path_cstr) { return uv_fs_chmod(nullptr, req, path_cstr, (int)mode, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_chown(b_obj_arg path, uint32_t uid, uint32_t gid) {
    return fs_path_op(path,
        [=](uv_fs_t* req, const char* path_cstr) { return uv_fs_chown(nullptr, req, path_cstr, (uv_uid_t)uid, (uv_gid_t)gid, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lchown(b_obj_arg path, uint32_t uid, uint32_t gid) {
    return fs_path_op(path,
        [=](uv_fs_t* req, const char* path_cstr) { return uv_fs_lchown(nullptr, req, path_cstr, (uv_uid_t)uid, (uv_gid_t)gid, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_utime(b_obj_arg path, double atime, double mtime) {
    return fs_path_op(path,
        [=](uv_fs_t* req, const char* path_cstr) { return uv_fs_utime(nullptr, req, path_cstr, atime, mtime, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lutime(b_obj_arg path, double atime, double mtime) {
    return fs_path_op(path,
        [=](uv_fs_t* req, const char* path_cstr) { return uv_fs_lutime(nullptr, req, path_cstr, atime, mtime, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_stat(b_obj_arg path) {
    return fs_path_op(path,
        [](uv_fs_t* req, const char* path_cstr) { return uv_fs_stat(nullptr, req, path_cstr, nullptr); },
        fs_stat);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lstat(b_obj_arg path) {
    return fs_path_op(path,
        [](uv_fs_t* req, const char* path_cstr) { return uv_fs_lstat(nullptr, req, path_cstr, nullptr); },
        fs_stat);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_statfs(b_obj_arg path) {
    return fs_path_op(path,
        [](uv_fs_t* req, const char* path_cstr) { return uv_fs_statfs(nullptr, req, path_cstr, nullptr); },
        fs_statfs);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_access(b_obj_arg path, uint32_t mode) {
    const char* path_cstr = lean_string_cstr(path);

    if (strlen(path_cstr) != lean_string_size(path) - 1) {
        return mk_embedded_nul_error(path);
    }

    uv_fs_t req;
    int result = uv_fs_access(nullptr, &req, path_cstr, (int)mode, nullptr);
    uv_fs_req_cleanup(&req);
    return lean_io_result_mk_ok(lean_box(result == 0 ? 1 : 0));
}

// =======================================
// Directories.

extern "C" LEAN_EXPORT uint8_t lean_uv_fs_file_type_of_dirent(uint8_t type) {
    switch ((uv_dirent_type_t)type) {
        case UV_DIRENT_FILE: return FILE_TYPE_FILE;
        case UV_DIRENT_DIR: return FILE_TYPE_DIR;
        case UV_DIRENT_LINK: return FILE_TYPE_SYMLINK;
        case UV_DIRENT_BLOCK: return FILE_TYPE_BLOCK_DEVICE;
        case UV_DIRENT_CHAR: return FILE_TYPE_CHAR_DEVICE;
        case UV_DIRENT_FIFO: return FILE_TYPE_FIFO;
        case UV_DIRENT_SOCKET: return FILE_TYPE_SOCKET;
        default: return FILE_TYPE_UNKNOWN;
    }
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_mkdir(b_obj_arg path, uint32_t mode) {
    return fs_path_op(path,
        [=](uv_fs_t* req, const char* path_cstr) { return uv_fs_mkdir(nullptr, req, path_cstr, (int)mode, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_rmdir(b_obj_arg path) {
    return fs_path_op(path,
        [](uv_fs_t* req, const char* path_cstr) { return uv_fs_rmdir(nullptr, req, path_cstr, nullptr); },
        fs_unit);
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_mkdtemp(b_obj_arg tmpl) {
    return fs_path_op(tmpl,
        // `req->path` is the template with its trailing `XXXXXX` filled in, i.e. the created directory.
        [](uv_fs_t* req, const char* tmpl_cstr) { return uv_fs_mkdtemp(nullptr, req, tmpl_cstr, nullptr); },
        [](uv_fs_t* req, int) { return lean_mk_string(req->path); });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_opendir(b_obj_arg path) {
    return fs_path_op(path,
        [](uv_fs_t* req, const char* path_cstr) { return uv_fs_opendir(nullptr, req, path_cstr, nullptr); },
        // `uv_fs_req_cleanup` deliberately leaves an `opendir` request's `ptr` alone, so the stream
        // outlives the request that produced it.
        [](uv_fs_t* req, int) { return lean_uv_dir_of_raw((uv_dir_t*)req->ptr); });
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_closedir(b_obj_arg dir) {
    lean_uv_dir_object* d = lean_to_uv_dir(dir);
    uv_dir_t* raw;
    int claim = lean_uv_dir_claim_close(d, &raw);
    if (claim < 0) return lean_io_result_mk_error(lean_decode_uv_error(claim, nullptr));

    uv_fs_t req;
    int result = uv_fs_closedir(nullptr, &req, raw, nullptr);
    uv_fs_req_cleanup(&req);
    if (result < 0) return lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    return lean_io_result_mk_ok(lean_box(0));
}

extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_readdir(b_obj_arg dir) {
    lean_uv_dir_object* d = lean_to_uv_dir(dir);
    uv_dir_t* raw;
    int claim = lean_uv_dir_claim(d, &raw);
    if (claim < 0) return lean_io_result_mk_error(lean_decode_uv_error(claim, nullptr));

    // `uv_fs_readdir` fills entries the caller hands it through the stream itself; one at a time
    // keeps the entry on the stack and the ownership question with libuv.
    uv_dirent_t ent;
    raw->dirents = &ent;
    raw->nentries = 1;

    uv_fs_t req;
    int result = uv_fs_readdir(nullptr, &req, raw, nullptr);

    lean_obj_res res;
    if (result < 0) {
        res = lean_io_result_mk_error(lean_decode_uv_error(result, nullptr));
    } else if (result == 0) {
        res = lean_io_result_mk_ok(mk_option_none());
    } else {
        // `ent.name` is owned by the request, so it has to be copied before the cleanup below.
        lean_object* o = lean_alloc_ctor(0, 1, 1);
        lean_ctor_set(o, 0, lean_mk_string(ent.name));
        lean_ctor_set_uint8(o, sizeof(void*), (uint8_t)ent.type);
        res = lean_io_result_mk_ok(mk_option_some(o));
    }

    uv_fs_req_cleanup(&req);
    lean_uv_dir_release(d);
    return res;
}

#else

#define LEAN_UV_FS_NO_LIBUV \
    lean_always_assert(false && ("Please build a version of Lean4 with libuv to invoke this."))

void initialize_libuv_fs() {}

extern "C" LEAN_EXPORT uint32_t lean_uv_fs_open_flags(uint8_t read, uint8_t write, uint8_t append, uint8_t truncate, uint8_t create, uint8_t create_new) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_open(b_obj_arg path, uint32_t flags, uint32_t mode) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_close(b_obj_arg file) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_read(b_obj_arg file, size_t len, int64_t offset, obj_arg buf) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_write(b_obj_arg file, b_obj_arg data, int64_t offset) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fsync(b_obj_arg file) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fdatasync(b_obj_arg file) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_ftruncate(b_obj_arg file, uint64_t len) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fstat(b_obj_arg file) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fchmod(b_obj_arg file, uint32_t mode) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_fchown(b_obj_arg file, uint32_t uid, uint32_t gid) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_futime(b_obj_arg file, double atime, double mtime) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_sendfile(b_obj_arg out_file, b_obj_arg in_file, int64_t in_offset, size_t length) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lock(b_obj_arg file, uint8_t exclusive) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_trylock(b_obj_arg file, uint8_t exclusive) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_unlock(b_obj_arg file) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_copyfile(b_obj_arg src, b_obj_arg dst, uint32_t flags) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_unlink(b_obj_arg path) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_rename(b_obj_arg src, b_obj_arg dst) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_link(b_obj_arg path, b_obj_arg link) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_symlink(b_obj_arg target, b_obj_arg path, uint32_t flags) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_readlink(b_obj_arg path) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_chmod(b_obj_arg path, uint32_t mode) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_chown(b_obj_arg path, uint32_t uid, uint32_t gid) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lchown(b_obj_arg path, uint32_t uid, uint32_t gid) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_utime(b_obj_arg path, double atime, double mtime) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lutime(b_obj_arg path, double atime, double mtime) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_stat(b_obj_arg path) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_lstat(b_obj_arg path) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_statfs(b_obj_arg path) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_access(b_obj_arg path, uint32_t mode) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_mkstemp(b_obj_arg tmpl) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT uint8_t lean_uv_fs_file_type_of_dirent(uint8_t type) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_mkdtemp(b_obj_arg tmpl) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_mkdir(b_obj_arg path, uint32_t mode) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_rmdir(b_obj_arg path) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_opendir(b_obj_arg path) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_closedir(b_obj_arg dir) { LEAN_UV_FS_NO_LIBUV; }
extern "C" LEAN_EXPORT lean_obj_res lean_uv_fs_readdir(b_obj_arg dir) { LEAN_UV_FS_NO_LIBUV; }

#endif

}
