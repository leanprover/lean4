#!/usr/bin/env python3

import argparse
import glob
import os
import sys


def evict(patterns: list[str]) -> None:
    evicted = 0
    for pattern in patterns:
        for path in glob.glob(pattern, recursive=True):
            if not os.path.isfile(path):
                continue
            fd = os.open(path, os.O_RDONLY)
            try:
                os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED)
            finally:
                os.close(fd)
            evicted += 1
    if evicted == 0:
        sys.exit(f"error: evicted no files, globs matched nothing: {patterns}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Evict files from the page cache.")
    parser.add_argument(
        "globs",
        nargs="+",
        metavar="GLOB",
        help="glob patterns to evict (`**` is recursive)",
    )
    args = parser.parse_args()
    evict(args.globs)
