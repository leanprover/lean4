#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

int main(void) {
    int pipefd[2];
    assert(pipe(pipefd) == 0);

    pid_t pid = fork();
    assert(pid >= 0);

    if (pid == 0) {
        assert(dup2(pipefd[1], STDERR_FILENO) >= 0);
        close(pipefd[0]);
        close(pipefd[1]);

        lean_initialize_runtime_module();
        lean_initialize_thread();

        lean_object * message = lean_mk_string("show-error-payload");
        lean_object * error = lean_mk_io_user_error(message);
        lean_object * result = lean_io_result_mk_error(error);
        lean_io_result_show_error(result);
        lean_dec_ref(result);

        lean_finalize_thread();
        _exit(23);
    }

    close(pipefd[1]);

    char buffer[256];
    ssize_t total = 0;
    while (total < (ssize_t)(sizeof(buffer) - 1)) {
        ssize_t read_now = read(pipefd[0], buffer + total, sizeof(buffer) - 1 - (size_t)total);
        assert(read_now >= 0);
        if (read_now == 0) break;
        total += read_now;
    }
    buffer[total] = '\0';
    close(pipefd[0]);

    int status = 0;
    assert(waitpid(pid, &status, 0) == pid);
    assert(WIFEXITED(status));
    assert(WEXITSTATUS(status) == 23);
    assert(strstr(buffer, "show-error-payload") != NULL);
    return 0;
}
