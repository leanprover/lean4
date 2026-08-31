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

extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_process_title();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_set_process_title(b_obj_arg title);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_uptime();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getpid();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getppid();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_cpu_info();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_cwd();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_chdir(b_obj_arg path);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_homedir();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_tmpdir();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_passwd();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_group(uint64_t gid);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_environ();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getenv(b_obj_arg name);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_setenv(b_obj_arg name, b_obj_arg value);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_unsetenv(b_obj_arg name);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_gethostname();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_getpriority(uint64_t pid);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_setpriority(uint64_t pid, int64_t priority);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_uname();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_hrtime();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_random(uint64_t size);
extern "C" LEAN_EXPORT lean_obj_res lean_uv_getrusage();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_exepath();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_free_memory();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_total_memory();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_constrained_memory();
extern "C" LEAN_EXPORT lean_obj_res lean_uv_get_available_memory();

}
