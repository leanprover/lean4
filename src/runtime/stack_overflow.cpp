/*
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich

Install a segfault signal handler and abort with custom message if address is within stack guard.
Inspired by https://github.com/rust-lang/rust/blob/master/src/libstd/sys/unix/stack_overflow.rs
*/
#if !defined(LEAN_WINDOWS) && !defined(__APPLE__)
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <pthread.h>
#include <unistd.h>

namespace lean {
// signal stack of the main thread
static stack_t g_signal_stack;

// https://github.com/rust-lang/rust/blob/7c8dbd969dd0ef2af6d8bab9e03ba7ce6cac41a2/src/libstd/sys/unix/thread.rs#L293
bool is_within_stack_guard(void * addr) {
    pthread_attr_t attr;
    if (pthread_attr_init(&attr) != 0) return false;
    pthread_getattr_np(pthread_self(), &attr);
    void * stackaddr;
    size_t stacksize, guardsize;
    pthread_attr_getstack(&attr, &stackaddr, &stacksize);
    pthread_attr_getguardsize(&attr, &guardsize);
    pthread_attr_destroy(&attr);
    if (guardsize == 0) {
        // probably the main thread, make an educated guess
        // https://github.com/rust-lang/rust/blob/7c8dbd969dd0ef2af6d8bab9e03ba7ce6cac41a2/src/libstd/sys/unix/thread.rs#L343-L347
        guardsize = static_cast<size_t>(sysconf(_SC_PAGESIZE));
    }
    // the stack guard is *below* the stack
    return stackaddr > addr && addr >= static_cast<char *>(stackaddr) - guardsize;
}

extern "C" void segv_handler(int signum, siginfo_t * info, void *) {
    if (is_within_stack_guard(info->si_addr)) {
        fprintf(stderr, "\nStack overflow detected. Aborting.\n");
        abort();
    } else {
        // reset signal handler and return; see comments in Rust code
        struct sigaction action;
        memset(&action, 0, sizeof(struct sigaction));
        action.sa_handler = SIG_DFL;
        sigaction(signum, &action, nullptr);
    }
}

// We need a separate signal stack since we can't use the overflowed stack
void setup_signal_stack(stack_t & stack) {
    stack.ss_sp = malloc(SIGSTKSZ);
    if (stack.ss_sp == nullptr) return;
    stack.ss_size = SIGSTKSZ;
    stack.ss_flags = 0;
    sigaltstack(&stack, nullptr);
}

void free_signal_stack(stack_t & stack) {
    if (!stack.ss_sp) {
        return;
    }
    stack.ss_flags = SS_DISABLE;
    sigaltstack(&stack, nullptr);
    free(stack.ss_sp);
}

void initialize_stack_overflow() {
    setup_signal_stack(g_signal_stack);
    struct sigaction action;
    memset(&action, 0, sizeof(struct sigaction));
    action.sa_flags = SA_SIGINFO | SA_ONSTACK;
    action.sa_sigaction = segv_handler;
    sigaction(SIGSEGV, &action, nullptr);
}

void finalize_stack_overflow() {
    free_signal_stack(g_signal_stack);
}
}
#else
namespace lean {
void initialize_stack_overflow() {}
void finalize_stack_overflow() {}
}
#endif
