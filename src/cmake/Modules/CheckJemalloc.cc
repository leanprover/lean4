#include <stdio.h>
#include <string.h>
#include <jemalloc/jemalloc.h>

int main() {
    printf("%d.%d.%d", JEMALLOC_VERSION_MAJOR, JEMALLOC_VERSION_MINOR, JEMALLOC_VERSION_BUGFIX);
    return 0;
}
