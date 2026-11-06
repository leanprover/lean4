/* Deterministically remove a cached artifact after lookup but before restoration. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int link(const char *source, const char *target) {
    int (*native_link)(const char *, const char *) = dlsym(RTLD_NEXT, "link");
    const char *prefix = getenv("TEST_CACHE_PREFIX");
    const char *directory = getenv("TEST_LINK_PAUSE_DIR");
    if (prefix && directory && strncmp(source, prefix, strlen(prefix)) == 0 &&
        strstr(source, ".olean") && strstr(target, ".olean")) {
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
