def simpleFun {_ : Type} (a b : Nat) : Nat → Nat → Nat := sorry

#check simpleFun  -- Full signature help expected
              --^ textDocument/signatureHelp

#check simpleFun  -- Full signature help expected
               --^ textDocument/signatureHelp

#check simpleFun 0  -- Shortened signature help expected (implicit is skipped)
                 --^ textDocument/signatureHelp

#check simpleFun 0 0  -- Shortened signature help without ∀ expected
                   --^ textDocument/signatureHelp

#check simpleFun 0 0 0  -- Shortened signature help without ∀ expected
                     --^ textDocument/signatureHelp

#check simpleFun 0 0 0 0  -- No signature help expected
                       --^ textDocument/signatureHelp

#check simpleFun 0 0 0 0  -- No signature help expected
                    --^ textDocument/signatureHelp

#check simpleFun -- No signature help expected in end-of-line comment
               --^ textDocument/signatureHelp

#check simpleFun <|  -- Full signature help expected
                  --^ textDocument/signatureHelp

#check simpleFun 0 0 0 <|  -- Shortened signature help expected
                        --^ textDocument/signatureHelp

#check simpleFun 0 <| simpleFun  -- Full signature help expected
                              --^ textDocument/signatureHelp

#check simpleFun $  -- Full signature help expected
                 --^ textDocument/signatureHelp

#check simpleFun 0 0 0 $  -- Shortened signature help expected
                       --^ textDocument/signatureHelp

#check simpleFun 0 $ simpleFun  -- Full signature help expected
                             --^ textDocument/signatureHelp

#check simpleFun ( )  -- No signature help expected
                --^ textDocument/signatureHelp

#check @simpleFun  -- Full signature help expected
                --^ textDocument/signatureHelp

#check @simpleFun _  -- Shortened signature help expected (implicit is not skipped)
                  --^ textDocument/signatureHelp

#check simpleFun (b := 0)  -- Shortened signature help without `b` expected
                        --^ textDocument/signatureHelp

#check (simpleFun 0)  -- Shortened signature help expected
                   --^ textDocument/signatureHelp

#check (simpleFun 0) 0  -- Shortened signature help expected
                     --^ textDocument/signatureHelp

def simpleProp (x y : Nat) : x = y → x = y := sorry

#check simpleProp  -- Full signature help with `∀` expected
                --^ textDocument/signatureHelp

#check simpleProp 0  -- Shortened signature help with `∀` expected
                  --^ textDocument/signatureHelp

#check simpleProp 0 0  -- Shortened signature help with remaining implication expected
                    --^ textDocument/signatureHelp

#check simpleProp 0 0 sorry  -- No signature help expected
                          --^ textDocument/signatureHelp

def complexFun (f : Nat → Nat → Nat → Nat → Nat) (x : Nat) : Nat := sorry

#check complexFun simpleFun  -- Shortened signature help of `complexFun` expected
                          --^ textDocument/signatureHelp

#check complexFun simpleFun 0  -- No signature help expected
                            --^ textDocument/signatureHelp

#check complexFun (simpleFun  ) -- Signature help of `simpleFun` expected
                           --^ textDocument/signatureHelp

def complexFun' (x : Nat) (f : Nat → Nat → Nat → Nat → Nat) : Nat := sorry

#check complexFun' 0  -- Shortened signature help of `complexFun'` expected
                   --^ textDocument/signatureHelp

#check complexFun' 0 simpleFun  -- No signature help expected
                             --^ textDocument/signatureHelp

structure SomeStructure where
  fieldFun (x : Nat) : Nat → Nat

def SomeStructure.dotFun (s : SomeStructure) (x : Nat) : Nat := sorry

def SomeStructure.dotIdFun (x : Nat) : SomeStructure := sorry

variable (s : SomeStructure) (s' : Nat → SomeStructure)

#check s.fieldFun  -- Full signature help expected
                --^ textDocument/signatureHelp

#check s.fieldFun 0  -- Shortened signature help expected
                  --^ textDocument/signatureHelp

#check s.fieldFun 0 0  -- No signature help expected
                    --^ textDocument/signatureHelp

#check (s' 0).fieldFun  -- Full signature help expected
                     --^ textDocument/signatureHelp

#check (s' 0).fieldFun 0  -- Shortened signature help expected
                       --^ textDocument/signatureHelp

#check s.dotFun  -- Full signature help expected
              --^ textDocument/signatureHelp

#check s.dotFun 0  -- No signature help expected
                --^ textDocument/signatureHelp

#check (s' 0).dotFun  -- Full signature help expected
                   --^ textDocument/signatureHelp

#check (s' 0).dotFun 0  -- No signature help expected
                     --^ textDocument/signatureHelp

#check s |>.fieldFun  -- Full signature help expected
                   --^ textDocument/signatureHelp

#check s |>.fieldFun 0  -- Shortened signature help expected
                     --^ textDocument/signatureHelp

#check s |>.fieldFun 0 0  -- No signature help expected
                       --^ textDocument/signatureHelp

#check s' 0 |>.fieldFun  -- Full signature help expected
                      --^ textDocument/signatureHelp

#check s' 0 |>.fieldFun 0  -- Shortened signature help expected
                        --^ textDocument/signatureHelp

example : SomeStructure := .dotIdFun  -- Full signature help expected
                                   --^ textDocument/signatureHelp


example : SomeStructure := .dotIdFun 0  -- No signature help expected
                                     --^ textDocument/signatureHelp
