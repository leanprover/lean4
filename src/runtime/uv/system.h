#pragma once
#include <lean/lean.h>
#include "runtime/uv/event_loop.h"

namespace lean {

#ifndef LEAN_EMSCRIPTEN
using namespace std;
#include <uv.h>
#endif

// =======================================
// System information functions

extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_process_title(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_set_process_title(b_obj_arg title, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_uptime(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getpid(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getppid(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_cpu_info(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_cwd(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_chdir(b_obj_arg path, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_homedir(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_tmpdir(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_passwd(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_group(uint64_t gid, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_environ(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getenv(b_obj_arg name, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_setenv(b_obj_arg name, b_obj_arg value, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_unsetenv(b_obj_arg name, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_gethostname(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getpriority(uint64_t pid, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_setpriority(uint64_t pid, int64_t priority, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_uname(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_hrtime(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_random(uint64_t size, obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_getrusage(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_exepath(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_free_memory(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_total_memory(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_constrained_memory(obj_arg /* w */);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_available_memory(obj_arg /* w */);

}
