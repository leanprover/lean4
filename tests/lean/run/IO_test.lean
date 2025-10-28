prelude
import Init.System.IO
import Init.Data.List.Control
import Init.Data.ToString


open IO.FS

#eval createDirAll "io_test"

def check_eq {α} [BEq α] [Repr α] (tag : String) (expected actual : α) : IO Unit :=
unless (expected == actual) do
  throw $ IO.userError $
    s!"assertion failure \"{tag}\":\n  expected: {repr expected}\n  actual:   {repr actual}"

def mkEmptyFile (file : System.FilePath) : IO Unit :=
  writeFile file ""

def removeFileIfExists (file : System.FilePath) : IO Unit :=
  try removeFile file catch
    | .noFileOrDirectory .. => pure ()
    | e => throw e

def test : IO Unit := do
let xs : ByteArray := ⟨#[1,2,3,4]⟩;
let fn := "io_test/foo.txt";
withFile fn Mode.write fun h => do
  h.write xs;
  h.write xs;
  pure ();
let ys ← withFile "io_test/foo.txt" Mode.read $ fun h => h.read 10;
check_eq "1" (xs.toList ++ xs.toList) ys.toList;
withFile fn Mode.append fun h => do
  h.write ⟨#[5,6,7,8]⟩;
  pure ();
withFile "io_test/foo.txt" Mode.read fun h => do
    let ys ← h.read 10
    check_eq "2" [1,2,3,4,1,2,3,4,5,6] ys.toList
    let ys ← h.read 2
    check_eq "3" [7,8] ys.toList
    let ys ← h.read 2
    check_eq "5" [] ys.toList
pure ()

#guard_msgs in
#eval test

def test2 : IO Unit := do
let fn1 := "bar2.txt";
let fn2 := "io_test/foo2.txt";
let xs₀ : String := "⟨[₂,α]⟩";
let xs₁ := "⟨[6,8,@]⟩";
let xs₂ := "/* Handle.getLine : Handle → IO Unit                     */" ++
           "/*   The line returned by `lean_io_prim_handle_get_line` */" ++
           "/*   is truncated at the first \'\\0\' character and the    */" ++
           "/*   rest of the line is discarded.                      */";
    -- multi-buffer line
withFile fn1 Mode.write $ fun _h => pure ();

withFile fn1 Mode.write $ fun h => do
  h.putStr xs₀
  h.putStrLn xs₀
  h.putStrLn xs₂
  h.putStrLn xs₁
withFile fn2 Mode.write $ fun h => h.putStr "overwritten"
rename fn1 fn2
let ys ← withFile fn2 Mode.read $ fun h => h.getLine;
IO.println ys;
check_eq "1" (xs₀ ++ xs₀ ++ "\n") ys;
IO.println ys;
withFile fn2 Mode.append $ fun h => do
{ h.putStrLn xs₁;
  pure () };
let ys ← withFile fn2 Mode.read $ fun h => do
  { let ys ← (List.range 4).mapM $ fun i => do
    { let ln ← h.getLine;
      IO.println i;
      IO.println ∘ repr $ ln;
      pure ln };
    pure ys };
IO.println ys;
let rs := [xs₀ ++ xs₀ ++ "\n", xs₂ ++ "\n", xs₁ ++ "\n", xs₁ ++ "\n"];
check_eq "2" rs ys;
let ys ← readFile fn2;
check_eq "3" (String.join rs) ys;
pure ()

/--
info: ⟨[₂,α]⟩⟨[₂,α]⟩

⟨[₂,α]⟩⟨[₂,α]⟩

0
"⟨[₂,α]⟩⟨[₂,α]⟩\n"
1
"/* Handle.getLine : Handle → IO Unit                     *//*   The line returned by `lean_io_prim_handle_get_line` *//*   is truncated at the first '\\0' character and the    *//*   rest of the line is discarded.                      */\n"
2
"⟨[6,8,@]⟩\n"
3
"⟨[6,8,@]⟩\n"
[⟨[₂,α]⟩⟨[₂,α]⟩
, /* Handle.getLine : Handle → IO Unit                     *//*   The line returned by `lean_io_prim_handle_get_line` *//*   is truncated at the first '\0' character and the    *//*   rest of the line is discarded.                      */
, ⟨[6,8,@]⟩
, ⟨[6,8,@]⟩
]
-/
#guard_msgs in
#eval test2

def test3 : IO Unit := do
let fn3 := "io_test/foo3.txt"
let xs₀ := "abc"
let xs₁ := ""
let xs₂ := "hello"
let xs₃ := "world"
withFile fn3 Mode.write $ fun _h => do {
  pure ()
}
let ys ← lines fn3
IO.println $ repr ys
check_eq "1" ys #[]
withFile fn3 Mode.write $ fun h => do
  h.putStrLn xs₀
  h.putStrLn xs₁
  h.putStrLn xs₂
  h.putStrLn xs₃
let ys ← lines fn3
IO.println $ repr ys
check_eq "2" ys #[xs₀, xs₁, xs₂, xs₃]
pure ()

/--
info: #[]
#["abc", "", "hello", "world"]
-/
#guard_msgs in
#eval test3

def test4 : IO Unit := do
let fn4 := "io_test/foo4.txt"
withFile fn4 Mode.write fun _h => do pure ();
let ys ← withFile fn4 Mode.read $ fun h => h.read 1;
check_eq "1" [] ys.toList
let ys ← withFile fn4 Mode.read $ fun h => h.read 1;
check_eq "2" [] ys.toList

#guard_msgs in
#eval test4

/-! `removeDirAll` should remove all contents but not follow symlinks. -/

def testRemoveDirAll : IO Unit := do
  createDirAll "io_test/dir/sub"
  createDirAll "io_test/symlink_target"
  writeFile "io_test/dir/file" ""
  writeFile "io_test/dir/sub/file" ""
  unless System.Platform.isWindows do
    let _ ← IO.Process.run { cmd := "ln", args := #["-s", "../symlink_target", "io_test/dir/symlink"] }
  removeDirAll "io_test/dir"
  assert! !(← System.FilePath.pathExists "io_test/dir")
  unless System.Platform.isWindows do
    assert! (← System.FilePath.pathExists "io_test/symlink_target")

#eval testRemoveDirAll

def testHardLink : IO Unit := do
  let fn := "io_test/hardLinkTarget.txt"
  let contents := "foo"
  writeFile fn contents
  let linkFn := "io_test/hardLink.txt"
  if (← System.FilePath.pathExists linkFn) then
    removeFile linkFn
  hardLink fn linkFn
  removeFile fn
  assert! !(← System.FilePath.pathExists fn)
  assert! (← System.FilePath.pathExists linkFn)
  let linkContents ← readFile linkFn
  check_eq "1" contents linkContents

#guard_msgs in
#eval testHardLink

/-
`walkDir` with `followLinks := false` yields a subset of entries obtained by `walkDir` which
follows symlinks.
-/

def testWalkDir : IO Unit := do
  let fn := "g.txt"
  let symlink := "io_test/walkdir/dir/symlink"
  createDirAll "io_test/walkdir/dir"
  createDirAll "io_test/walkdir/symlink_target"
  mkEmptyFile "io_test/walkdir/dir/f.txt"
  mkEmptyFile s!"io_test/walkdir/symlink_target/{fn}"
  removeFileIfExists symlink

  unless System.Platform.isWindows do
    let _ ← IO.Process.run { cmd := "ln", args := #["-s", "../../symlink_target", symlink] }
    let noSymlinks <- System.FilePath.walkDir "io_test/walkdir/dir" (followLinks := false)
    let withSymlinks <- System.FilePath.walkDir "io_test/walkdir/dir" (followLinks := true)
    check_eq "1" (withSymlinks.filter (fun s => !(s.toString.endsWith fn))) noSymlinks

#guard_msgs in
#eval testWalkDir

/-
`walkDir` with `followLinks := false` does not throw an exception when encountering a dangling
symlink. When the dangling symlink is followed, `IO.Error.noFileOrDirectory` exception is thrown.
-/

def testWalkDirDanglingSymlink : IO Unit := do
  let symlink := "io_test/walkdir_dangling_symlink/symlink"
  let nonexistentTarget := "nonexistent-target"
  createDirAll "io_test/walkdir_dangling_symlink"
  removeFileIfExists symlink

  unless System.Platform.isWindows do
    assert! !(← System.FilePath.pathExists nonexistentTarget)
    let _ ← IO.Process.run { cmd := "ln", args := #["-s", nonexistentTarget, symlink] }
    let noSymlinks <- System.FilePath.walkDir  "io_test/walkdir_dangling_symlink" (followLinks := false)
    /- symbolic link was recorded in the array, but not followed -/
    check_eq "1" noSymlinks.size 1

    match <- (System.FilePath.walkDir  "io_test/walkdir_dangling_symlink" (followLinks := true)).toBaseIO with
    | .error (.noFileOrDirectory ..) => pure ()
    | _ => assert! false

#guard_msgs in
#eval testWalkDirDanglingSymlink
