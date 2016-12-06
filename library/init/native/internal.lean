/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.meta.expr
import init.meta.format

-- builtin stuff
meta constant native.is_internal_cnstr : expr → option unsigned
meta constant native.is_internal_cases : expr → option unsigned
meta constant native.is_internal_proj : expr → option unsigned
meta constant native.get_nat_value : expr → option nat
meta constant native.dump_format : string → format → nat
