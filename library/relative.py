# Copyright (c) 2018 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Simon Hudon

import sys
import os

for x in sys.stdin:
  print(os.path.relpath(x))
