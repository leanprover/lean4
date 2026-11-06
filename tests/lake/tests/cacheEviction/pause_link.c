/* Deterministically remove a cached artifact after lookup but before restoration. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <fcntl.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int link(const char *source, const char *target) {
    int (*native_link)(const char *, const char *) = dlsym(RTLD_NEXT, "link");
    const char *prefix = getenv("TEST_CACHE_PREFIX");
    const char *directory = getenv("TEST_LINK_PAUSE_DIR");
    const char *extension = getenv("TEST_ARTIFACT_EXTENSION");
    if (!extension) extension = ".olean";
    if (prefix && getenv("TEST_RESTORE_WRITE_FAIL") &&
        strncmp(source, prefix, strlen(prefix)) == 0 && strstr(source, extension)) {
        errno = EXDEV;
        return -1;
    }
    if (prefix && directory && strncmp(source, prefix, strlen(prefix)) == 0 &&
        strstr(source, extension) && strstr(target, extension)) {
        char marker[4096], release[4096];
        snprintf(marker, sizeof(marker), "%s/source", directory);
        snprintf(release, sizeof(release), "%s/release", directory);
        int descriptor = open(marker, O_WRONLY | O_CREAT | O_EXCL, 0600);
        if (descriptor >= 0) {
            write(descriptor, source, strlen(source));
            close(descriptor);
            while (access(release, F_OK) != 0) usleep(1000);
        }
    }
    return native_link(source, target);
}

size_t fwrite(const void *data, size_t size, size_t count, FILE *stream) {
    size_t (*native_write)(const void *, size_t, size_t, FILE *) = dlsym(RTLD_NEXT, "fwrite");
    const char *marker = getenv("TEST_RESTORE_WRITE_FAIL");
    const char *prefix = getenv("TEST_WRITE_TARGET_PREFIX");
    char descriptor[64], path[4096];
    snprintf(descriptor, sizeof(descriptor), "/proc/self/fd/%d", fileno(stream));
    ssize_t length = readlink(descriptor, path, sizeof(path) - 1);
    if (length >= 0) path[length] = 0;
    if (marker && prefix && length >= 0 && strncmp(path, prefix, strlen(prefix)) == 0 &&
        strstr(path, ".a") && size == 1 && count > 1) {
        int fd = open(marker, O_WRONLY | O_CREAT | O_EXCL, 0600);
        if (fd >= 0) {
            close(fd);
            size_t first = native_write(data, 1, count / 2, stream);
            fflush(stream);
            errno = ENOSPC;
            return first;
        }
    }
    return native_write(data, size, count, stream);
}
