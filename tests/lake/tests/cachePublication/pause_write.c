/* Pause a real native cache copy after flushing only its first half. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int link(const char *source, const char *target) {
    const char *copy_source = getenv("TEST_COPY_SOURCE");
    const char *prefix = getenv("TEST_WRITE_PREFIX");
    if (copy_source && prefix && strcmp(source, copy_source) == 0 &&
        strncmp(target, prefix, strlen(prefix)) == 0) {
        errno = EXDEV;
        return -1;
    }
    int (*native_link)(const char *, const char *) = dlsym(RTLD_NEXT, "link");
    return native_link(source, target);
}

size_t fwrite(const void *data, size_t size, size_t count, FILE *stream) {
    size_t (*native_write)(const void *, size_t, size_t, FILE *) = dlsym(RTLD_NEXT, "fwrite");
    const char *prefix = getenv("TEST_WRITE_PREFIX");
    const char *directory = getenv("TEST_WRITE_PAUSE_DIR");
    char descriptor[64], path[4096], executable[4096];
    snprintf(descriptor, sizeof(descriptor), "/proc/self/fd/%d", fileno(stream));
    ssize_t length = readlink(descriptor, path, sizeof(path) - 1);
    ssize_t exe_length = readlink("/proc/self/exe", executable, sizeof(executable) - 1);
    if (length >= 0) path[length] = 0;
    if (exe_length >= 0) executable[exe_length] = 0;
    /* curl stages the primary download; this hook targets Lake's subsequent copies. */
    if (prefix && directory && length >= 0 && exe_length >= 0 &&
        !strstr(executable, "curl") && strncmp(path, prefix, strlen(prefix)) == 0 &&
        size == 1 && count > 1) {
        char marker[4096], release[4096];
        snprintf(marker, sizeof(marker), "%s/paused", directory);
        snprintf(release, sizeof(release), "%s/release", directory);
        int fd = open(marker, O_WRONLY | O_CREAT | O_EXCL, 0600);
        if (fd >= 0) {
            size_t first = native_write(data, 1, count / 2, stream);
            fflush(stream);
            ssize_t written = write(fd, path, strlen(path));
            close(fd);
            if (written >= 0) {
                while (access(release, F_OK) != 0) usleep(1000);
            }
            return first + native_write((const char *)data + first, 1, count - first, stream);
        }
    }
    return native_write(data, size, count, stream);
}
