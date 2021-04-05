namespace Foo
namespace Bla

theorem ex1 {a b : Nat} (h : a ≤ b) : a + a ≤ b + b :=
  sorry

theorem ex2 {a b : Nat} (h : a ≤ b) : a + 2 ≤ b + 2 :=
  sorry

theorem ex3 {a b c d : Nat} (h : a ≤ b) (h : c ≤ d) : a + c ≤ b + d :=
  sorry

theorem ax1 {a b : Nat} (h : a ≤ b) : a - a ≤ b - b :=
  sorry

end Bla
end Foo

theorem tst1 (h : a ≤ b) : a + 2 ≤ b + 2 :=
  Foo.Bla.
        --^ textDocument/completion
#print ""

open Foo in
theorem tst2 (h : a ≤ b) : a + 2 ≤ b + 2 :=
  Bla.
    --^ textDocument/completion
#print ""

theorem tst3 (h : a ≤ b) : a + 2 ≤ b + 2 :=
  let aux := Foo.Bla.  -- we don't have the expected type here
                   --^ textDocument/completion
  aux

#print ""

theorem tst4 (h : a ≤ b) : a + 2 ≤ b + 2 :=
  let aux := Foo.Bla.e  -- we don't have the expected type here
                    --^ textDocument/completion
  aux
