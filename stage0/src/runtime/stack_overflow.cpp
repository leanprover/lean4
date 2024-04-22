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
#include "runtime/stack_overflow.h"

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
// https://github.com/rust-lang/rust/blob/master/src/libstd/sys/unix/stack_overflow.rs


// https://github.com/rust-lang/rust/blob/7c8dbd969dd0ef2af6d8bab9e03ba7ce6cac41a2/src/libstd/sys/unix/thread.rs#L293
bool is_within_stack_guard(void * addr) {
    char * stackaddr;
#ifdef __APPLE__
    stackaddr = static_cast<char *>(pthread_get_stackaddr_np(pthread_self())) - pthread_get_stacksize_np(pthread_self());
#else
    pthread_attr_t attr;
    if (pthread_attr_init(&attr) != 0) return false;
    pthread_getattr_np(pthread_self(), &attr);
    size_t stacksize;
    pthread_attr_getstack(&attr, reinterpret_cast<void **>(&stackaddr), &stacksize);
    pthread_attr_destroy(&attr);
#endif
    // close enough; the actual guard might be bigger, but it's unlikely a Lean function will have stack frames that big
    size_t guardsize = static_cast<size_t>(sysconf(_SC_PAGESIZE));
    // the stack guard is *below* the stack
    return stackaddr - guardsize <= addr && addr < stackaddr;
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
    g_stack_guard = new stack_guard();
#ifdef LEAN_WINDOWS
    AddVectoredExceptionHandler(0, stack_overflow_handler);
#else
    struct sigaction action;
    memset(&action, 0, sizeof(struct sigaction));
    action.sa_flags = SA_SIGINFO | SA_ONSTACK;
    action.sa_sigaction = segv_handler;
    sigaction(SIGSEGV, &action, nullptr);
#endif
}

void finalize_stack_overflow() {
    delete g_stack_guard;
}
}
