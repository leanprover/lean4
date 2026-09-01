/*
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich

Print a nicer error message on stack overflow.
Port of the corresponding Rust code (see links below).
*/
#ifdef LEAN_WINDOWS
#include <windows.h>
#else
#include <csignal>
#include <pthread.h>
#include <unistd.h>
#endif
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <lean/lean.h>
#include <initializer_list>
#include "runtime/stack_overflow.h"
#include "runtime/thread.h"

namespace lean {
// stack guard of the main thread
static stack_guard * g_stack_guard;

#ifdef LEAN_WINDOWS
// https://github.com/rust-lang/rust/blob/master/src/libstd/sys/windows/stack_overflow.rs

LONG WINAPI stack_overflow_handler(struct _EXCEPTION_POINTERS * info) {
    if (info->ExceptionRecord->ExceptionCode == EXCEPTION_STACK_OVERFLOW) {
        fprintf(stderr, "\nStack overflow detected. Aborting.\n");
        abort();
    } else {
        return EXCEPTION_CONTINUE_SEARCH;
    }
}

stack_guard::stack_guard() {
    // reserve some stack space for the handler
    ULONG sz = 0x5000;
    SetThreadStackGuarantee(&sz);
}

stack_guard::~stack_guard() {}
#else
// Install a segfault signal handler and abort with custom message if address is within stack guard.
// https://github.com/rust-lang/rust/blob/master/library/std/src/sys/pal/unix/stack_overflow.rs


#ifndef __APPLE__
// Lowest address of the current thread's stack, captured by `stack_guard`. Null on threads the
// runtime did not create; those have no alternate signal stack either.
static LEAN_THREAD_LOCAL char * g_stackaddr = nullptr;
#endif
// close enough; the actual guard might be bigger, but it's unlikely a Lean function will have stack frames that big
static size_t g_guardsize;

// https://github.com/rust-lang/rust/blob/7c8dbd969dd0ef2af6d8bab9e03ba7ce6cac41a2/src/libstd/sys/unix/thread.rs#L293
static void capture_stack_bounds() {
#ifndef __APPLE__
    pthread_attr_t attr;
    if (pthread_attr_init(&attr) != 0) return;
    char * stackaddr;
    size_t stacksize;
    if (pthread_getattr_np(pthread_self(), &attr) == 0 &&
        pthread_attr_getstack(&attr, reinterpret_cast<void **>(&stackaddr), &stacksize) == 0)
        g_stackaddr = stackaddr;
    pthread_attr_destroy(&attr);
#endif
}

// Must be async-signal-safe: on glibc `pthread_getattr_np` allocates, and the interrupted frame may
// hold the allocator lock.
bool is_within_stack_guard(void * addr) {
    char * stackaddr;
#ifdef __APPLE__
    // does not allocate, unlike Mach-O `thread_local` on first access
    stackaddr = static_cast<char *>(pthread_get_stackaddr_np(pthread_self())) - pthread_get_stacksize_np(pthread_self());
#else
    stackaddr = g_stackaddr;
    if (stackaddr == nullptr) return false;
#endif
    // the stack guard is *below* the stack
    return stackaddr - g_guardsize <= addr && addr < stackaddr;
}

extern "C" LEAN_EXPORT void segv_handler(int signum, siginfo_t * info, void *) {
    if (is_within_stack_guard(info->si_addr)) {
        char const msg[] = "\nStack overflow detected. Aborting.\n";
        write(STDERR_FILENO, msg, sizeof(msg) - 1);
        abort();
    } else {
        // reset signal handler and return; see comments in Rust code
        struct sigaction action;
        memset(&action, 0, sizeof(struct sigaction));
        action.sa_handler = SIG_DFL;
        sigaction(signum, &action, nullptr);
    }
}

stack_guard::stack_guard() {
    capture_stack_bounds();
    m_signal_stack.ss_sp = malloc(SIGSTKSZ);
    if (m_signal_stack.ss_sp == nullptr) return;
    m_signal_stack.ss_size = SIGSTKSZ;
    m_signal_stack.ss_flags = 0;
    sigaltstack(&m_signal_stack, nullptr);
}

stack_guard::~stack_guard() {
    if (!m_signal_stack.ss_sp) return;
    m_signal_stack.ss_flags = SS_DISABLE;
    sigaltstack(&m_signal_stack, nullptr);
    free(m_signal_stack.ss_sp);
}
#endif

void initialize_stack_overflow() {
#ifndef LEAN_WINDOWS
    g_guardsize = static_cast<size_t>(sysconf(_SC_PAGESIZE));
#endif
    g_stack_guard = new stack_guard();
#ifdef LEAN_WINDOWS
    AddVectoredExceptionHandler(0, stack_overflow_handler);
#else
    for (auto signum : {SIGSEGV, SIGBUS}) {
        struct sigaction action;
        memset(&action, 0, sizeof(struct sigaction));
        sigaction(signum, nullptr, &action);
        // Configure our signal handler if one is not already set.
        if (action.sa_handler == SIG_DFL) {
            action.sa_flags = SA_SIGINFO | SA_ONSTACK;
            action.sa_sigaction = segv_handler;
            sigaction(signum, &action, nullptr);
        }
    }
#endif
}

void finalize_stack_overflow() {
    delete g_stack_guard;
}
}
