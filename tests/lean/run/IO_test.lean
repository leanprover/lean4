prelude
import Init.System.IO
import Init.Data.List.Control

open IO.FS

instance : HasRepr UInt8 := ⟨ toString ⟩

def check_eq {α} [HasBeq α] [HasRepr α] (tag : String) (expected actual : α) : IO Unit :=
unless (expected == actual) $ throw $ IO.userError $
  "assertion failure \"" ++ tag ++
    "\":\n  expected: " ++ repr expected ++
       "\n  actual:   " ++ repr actual

def test : IO Unit := do
let xs : ByteArray := ⟨#[1,2,3,4]⟩;
let fn := "foo.txt";
withFile fn Mode.write $ fun h => do
{ h.write xs;
  h.write xs;
  pure () };
ys ← withFile "foo.txt" Mode.read $ fun h => h.read 10;
check_eq "1" (xs.toList ++ xs.toList) ys.toList;
withFile fn Mode.append $ fun h => do
{ h.write ⟨#[5,6,7,8]⟩;
  pure () };
withFile "foo.txt" Mode.read $ fun h => do
  { ys ← h.read 10;
    check_eq "2" [1,2,3,4,1,2,3,4,5,6] ys.toList;
    ys ← h.read 2;
    check_eq "3" [7,8] ys.toList;
    b ← h.isEof;
    unless (!b)
      (throw $ IO.userError $ "wrong (4): ");
    ys ← h.read 2;
    check_eq "5" [] ys.toList;
    b ← h.isEof;
    unless b
      (throw $ IO.userError $ "wrong (6): ") };
pure ()

#eval test

def test2 : IO Unit := do
let fn2 := "foo2.txt";
let xs₀ : String := "⟨[₂,α]⟩";
let xs₁ := "⟨[6,8,@]⟩";
let xs₂ := "/* Handle.getLine : Handle → IO Unit                     */" ++
           "/*   The line returned by `lean_io_prim_handle_get_line` */" ++
           "/*   is truncated at the first \'\\0\' character and the    */" ++
           "/*   rest of the line is discarded.                      */";
    -- multi-buffer line
withFile fn2 Mode.write $ fun h => pure ();

withFile fn2 Mode.write $ fun h => do
{ h.putStr xs₀;
  h.putStrLn xs₀;
  h.putStrLn xs₂;
  h.putStrLn xs₁;
  pure () };
ys ← withFile fn2 Mode.read $ fun h => h.getLine;
check_eq "1" (xs₀ ++ xs₀ ++ "\n") ys;
withFile fn2 Mode.append $ fun h => do
{ h.putStrLn xs₁;
  pure () };
ys ← withFile fn2 Mode.read $ fun h => do
  { ys ← (List.iota 5).mapM $ fun i => do
    { ln ← h.getLine;
      -- IO.println ∘ repr $ ln;
      b  ← h.isEof;
      unless (i == 1 || !b) (throw $ IO.userError "isEof");
      pure ln };
    b ← h.isEof;
    unless b (throw $ IO.userError "not isEof");
    pure ys };
let rs := [xs₀ ++ xs₀ ++ "\n", xs₂ ++ "\n", xs₁ ++ "\n", xs₁ ++ "\n", ""];
check_eq "2" rs ys;
ys ← IO.readFile fn2;
check_eq "3" (String.join rs) ys;
pure ()

#eval test2
