# Copyright (c) 2018 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Simon Hudon, Sebastian Ullrich

import sys
import os
import re

for x in sys.stdin:
  # HACK: rewrite Windows path to mingw path
  x = re.sub(r"^(\w):", lambda m: "/" + m[1].lower(), x).replace('\\', '/').strip()
  print(os.path.relpath(x))
