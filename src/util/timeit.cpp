/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "util/timeit.h"
#include <iomanip>
#include <unistd.h>
#include "runtime/debug.h"

#ifdef __linux
#include <linux/perf_event.h>
#include <sys/ioctl.h>
#include <asm/unistd.h>
#include <string.h>
#endif

namespace lean {

// file descriptor for reading instruction counts, if available
static int perf_fd = -1;

static double instructions_per_second = 8924929271.7;

static std::chrono::steady_clock::time_point now() {
    if (perf_fd == -1) {
        return std::chrono::steady_clock::now();
    } else {
        long long start;
        read(perf_fd, &start, sizeof(start));
        return std::chrono::steady_clock::time_point(
            std::chrono::duration_cast<std::chrono::steady_clock::duration>(
                std::chrono::duration<double>(start / instructions_per_second)));
    }
}

xtimeit::xtimeit(second_duration threshold, std::function<void(second_duration)> const & fn): // NOLINT
    m_threshold(threshold), m_fn(fn) {
    m_start = now();
}

second_duration xtimeit::get_elapsed_inclusive() const {
    return second_duration(now() - m_start);
}

std::ostream & operator<<(std::ostream & out, display_profiling_time const & time) {
    out << std::setprecision(3);
    if (time.m_time < second_duration(1)) {
        out << std::chrono::duration<double, std::milli>(time.m_time).count() << "ms";
    } else {
        out << time.m_time.count() << "s";
    }
    return out;
}

#ifdef __linux
// from `man 2 perf_event_open`
static long perf_event_open(struct perf_event_attr * hw_event, pid_t pid, int cpu, int group_fd,
        unsigned long flags) {
    int ret;

    ret = syscall(__NR_perf_event_open, hw_event, pid, cpu, group_fd, flags);
    return ret;
}
#endif

void initialize_timeit() {
#ifdef __linux
    // from `man 2 perf_event_open`
    struct perf_event_attr pe;
    memset(&pe, 0, sizeof(pe));
    pe.type = PERF_TYPE_HARDWARE;
    pe.size = sizeof(pe);
    pe.config = PERF_COUNT_HW_INSTRUCTIONS;
    pe.disabled = 1;
    pe.exclude_kernel = 1;
    pe.exclude_hv = 1;
    perf_fd = perf_event_open(&pe, 0, -1, -1, 0);
    if (perf_fd != -1) {
        lean_always_assert(ioctl(perf_fd, PERF_EVENT_IOC_RESET, 0) == 0);
        lean_always_assert(ioctl(perf_fd, PERF_EVENT_IOC_ENABLE, 0) == 0);
    }
#endif
}

void finalize_timeit() {
    if (perf_fd != -1)
        close(perf_fd);
}

}
