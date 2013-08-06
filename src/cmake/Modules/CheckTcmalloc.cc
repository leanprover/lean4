/** -*- C++ -*-
 * Copyright (C) 2009  Luke Lu (llu@hypertable.org)
 *
 * This file is part of Hypertable.
 *
 * Hypertable is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * Hypertable is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Hypertable. If not, see <http://www.gnu.org/licenses/>
 */

#include <stdio.h>
#include <string.h>
#include <google/tcmalloc.h>

int main() {
    int major, minor;
    const char *patch;
    const char *version = tc_version(&major, &minor, &patch);

    if (major != TC_VERSION_MAJOR || minor != TC_VERSION_MINOR ||
        strcmp(patch, TC_VERSION_PATCH)) {
        fprintf(stderr, "Tcmalloc header/library mismatch:\n "
                "header: %s\nlibrary: %s\n", TC_VERSION_STRING, version);
        return 1;
    }
    printf("%d.%d%s", major, minor, patch);
    return 0;
}
