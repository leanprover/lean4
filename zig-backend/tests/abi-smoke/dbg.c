#include <lean/lean.h>

#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define CHECK(cond)                                                                 \
    do {                                                                            \
        if (!(cond)) {                                                              \
            fprintf(stderr, "FAIL:%s:%d: %s\n", __FILE__, __LINE__, #cond);         \
            return 1;                                                               \
        }                                                                           \
    } while (0)

void lean_initialize_runtime_module(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);

static lean_object *return_trace_result(lean_object *unit) {
    if (unit != lean_box(0)) {
        fprintf(stderr, "FAIL:%s:%d: unit != lean_box(0)\n", __FILE__, __LINE__);
        abort();
    }
    return lean_box(42);
}

int main(void) {
    lean_initialize_runtime_module();
    lean_initialize_thread();

    char path[] = "/tmp/lean-dbg-XXXXXX";
    char output[256];
    int fd = mkstemp(path);
    CHECK(fd >= 0);
    CHECK(unlink(path) == 0);

    int stderr_copy = dup(STDERR_FILENO);
    CHECK(stderr_copy >= 0);
    CHECK(fflush(stderr) == 0);
    CHECK(dup2(fd, STDERR_FILENO) >= 0);

    lean_object *trace_result = lean_dbg_trace(
        lean_mk_string("hello-dbg"),
        lean_alloc_closure((void *)return_trace_result, 1, 0));

    CHECK(fflush(stderr) == 0);
    CHECK(dup2(stderr_copy, STDERR_FILENO) >= 0);
    CHECK(close(stderr_copy) == 0);

    CHECK(lseek(fd, 0, SEEK_SET) >= 0);
    ssize_t read_count = read(fd, output, sizeof(output) - 1);
    CHECK(read_count >= 0);
    output[read_count] = '\0';
    CHECK(close(fd) == 0);

    CHECK(trace_result == lean_box(42));
    CHECK(strstr(output, "hello-dbg") != NULL);
    lean_finalize_thread();
    return 0;
}
