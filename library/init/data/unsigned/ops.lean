/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.unsigned.basic init.data.fin.ops

namespace unsigned
def of_nat (n : nat) : unsigned := fin.of_nat n
instance : has_zero unsigned := ⟨fin.of_nat 0⟩
instance : has_one unsigned  := ⟨fin.of_nat 1⟩
instance : has_add unsigned  := ⟨fin.add⟩
instance : has_sub unsigned  := ⟨fin.sub⟩
instance : has_mul unsigned  := ⟨fin.mul⟩
instance : has_mod unsigned  := ⟨fin.mod⟩
instance : has_div unsigned  := ⟨fin.div⟩
instance : has_lt unsigned   := ⟨fin.lt⟩
instance : has_le unsigned   := ⟨fin.le⟩
end unsigned
