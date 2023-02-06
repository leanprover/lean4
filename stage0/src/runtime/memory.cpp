/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <new>
#include <cstdlib>
#include <iostream>
#include "runtime/exception.h"
#include "runtime/memory.h"
#include "runtime/thread.h"

#ifndef LEAN_CHECK_MEM_THRESHOLD
#define LEAN_CHECK_MEM_THRESHOLD 200
#endif

#if defined(HAS_JEMALLOC)
#include <jemalloc/jemalloc.h>

namespace lean {

size_t get_peak_rss() {
    // refresh stats
    uint64_t epoch;
    mallctl("epoch", NULL, NULL, &epoch, sizeof(epoch));

    size_t allocated;
    size_t sz = sizeof(size_t);
    if (mallctl("stats.allocated", &allocated, &sz, NULL, 0) == 0) {
        return allocated;
    } else {
        return 0;
    }
}

size_t get_current_rss() {
    return get_peak_rss();
}

}
#elif defined(LEAN_WINDOWS)
/* ----------------------------------------------------
   Windows version for get_peak_rss and get_current_rss
   --------------------------------------------------- */
#include <windows.h>
#include <psapi.h>

namespace lean {
size_t get_peak_rss() {
    PROCESS_MEMORY_COUNTERS info;
    GetProcessMemoryInfo(GetCurrentProcess(), &info, sizeof(info));
    return static_cast<size_t>(info.PeakWorkingSetSize);
}

size_t get_current_rss() {
    PROCESS_MEMORY_COUNTERS info;
    GetProcessMemoryInfo(GetCurrentProcess(), &info, sizeof(info));
    return static_cast<size_t>(info.WorkingSetSize);
}
}
/* ----------------------------------------------------
   End of Windows version
   --------------------------------------------------- */
#else
/* ----------------------------------------------------
   Linux/OSX version for get_peak_rss and get_current_rss
   --------------------------------------------------- */
#include <unistd.h>
#include <sys/resource.h>

#if defined(__APPLE__)
#include <mach/mach.h>
#endif

namespace lean {
size_t get_peak_rss() {
    struct rusage rusage;
    getrusage(RUSAGE_SELF, &rusage);
#if defined(__APPLE__)
    return static_cast<size_t>(rusage.ru_maxrss);
#else
    return static_cast<size_t>(rusage.ru_maxrss) * static_cast<size_t>(1024);
#endif
}

size_t get_current_rss() {
#if defined(__APPLE__)
    struct mach_task_basic_info info;
    mach_msg_type_number_t infoCount = MACH_TASK_BASIC_INFO_COUNT;
    if (task_info(mach_task_self(), MACH_TASK_BASIC_INFO, reinterpret_cast<task_info_t>(&info), &infoCount) != KERN_SUCCESS)
        return static_cast<size_t>(0);
    return static_cast<size_t>(info.resident_size);
#else
    long rss  = 0;
    FILE * fp = nullptr;
    if ((fp = fopen("/proc/self/statm", "r")) == nullptr)
        return static_cast<size_t>(0L);
    if (fscanf(fp, "%*s%ld", &rss ) != 1) {
        fclose(fp);
        return static_cast<size_t>(0);
    }
    fclose(fp);
    return static_cast<size_t>(rss) * static_cast<size_t>(sysconf(_SC_PAGESIZE));
#endif
}
}
/* ----------------------------------------------------
   End of Linux/OSX version
   --------------------------------------------------- */
#endif

namespace lean {
static size_t g_max_memory = 0;
LEAN_THREAD_VALUE(size_t, g_counter, 0);

void set_max_memory(size_t max) {
    g_max_memory = max;
}

void set_max_memory_megabyte(unsigned max) {
    size_t m = max;
    m *= 1024 * 1024;
    set_max_memory(m);
}

// separate definition to allow breakpoint in debugger
void throw_memory_exception(char const * component_name) {
    throw memory_exception(component_name);
}

void check_memory(char const * component_name) {
    if (g_max_memory == 0) return;
    g_counter++;
    if (g_counter >= LEAN_CHECK_MEM_THRESHOLD) {
        g_counter = 0;
        // We try first get_peak_rss because it is much faster
        // than get_current_rss on Linux.
        size_t r = get_peak_rss();
        if (r > 0 && r < g_max_memory) return;
        r = get_current_rss();
        if (r == 0 || r < g_max_memory) return;
        throw_memory_exception(component_name);
    }
}

size_t get_allocated_memory() {
    return get_current_rss();
}
}
