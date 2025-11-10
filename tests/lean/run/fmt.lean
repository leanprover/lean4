import Lean.Data.Fmt.Basic

open Lean.Fmt

def traditional : Doc :=
  .join #[
    .text "function append(first,second,third){",
    .indent 4 (
      let f : Doc := .text "first +"
      let s : Doc := .text "second +"
      let t : Doc := .text "third"
      .join #[
        .nl,
        .text "return ",
        .maybeFlattened (.indent 4 (.join #[f, .nl, s, .nl, t]))]
    ),
    .nl,
    .text "}"
  ]

def test (d : Doc) (width : Nat) (pre : String := "") : IO Unit := do
  IO.println ""
  let r := pre ++ (format? d width (offset := pre.length) |>.getD "")
  IO.println r

/--
info:
function append(first,second,third){
    return first +
        second +
        third
}
-/
#guard_msgs in
#eval test traditional 22

/--
info:
function append(first,second,third){
    return first + second + third
}
-/
#guard_msgs in
#eval test traditional 36

inductive SExpr where
  | leaf (v : String)
  | node (cs : List SExpr)

instance : Coe String SExpr where
  coe v := .leaf v

partial def SExpr.pretty (s : SExpr) : Doc :=
  match s with
  | .leaf v => .text v
  | .node [] => .text "()"
  | .node (f :: args) =>
    let fp := f.pretty
    let argsp := args.toArray.map pretty
    .oneOf #[
      .join #[
        .text "(",
        .align (.joinUsing .hardNl (#[fp] ++ argsp)),
        .text ")"
      ],
      .join #[
        .text "(",
        .align fp,
        .text " ",
        .align (.joinUsing .hardNl argsp),
        .text ")"
      ],
      .flatten (
        .join #[
          .text "(",
          .align (.joinUsing (.text " ") (#[fp] ++ argsp)),
          .text ")"
        ]
      )
    ]

partial def SExpr.pretty' (s : SExpr) : Doc :=
  match s with
  | .leaf v => .text v
  | .node [] => .text "()"
  | .node (f :: args) =>
    let fp := f.pretty
    let argsp := args.toArray.map pretty
    .oneOf #[
      .join #[
        .text "(",
        .align (.joinUsing .hardNl (#[fp] ++ argsp)),
        .text ")"
      ],
      .join #[
        .text "(",
        .align fp,
        .text " ",
        .align (.joinUsing .hardNl argsp),
        .text ")"
      ],
      .join #[
        .text "(",
        .align (.joinUsing (.text " ") (#[fp] ++ argsp)),
        .text ")"
      ]
    ]

def testSExpr (e : SExpr) (width : Nat) (pre : String := "") : IO Unit := do
  test e.pretty width pre

def testSExpr' (e : SExpr) (width : Nat) : IO Unit := do
  test e.pretty' width

def sExpr1 : SExpr :=
  .node ["+", .node ["foo", "1", "2"], .node ["bar", "2", "3"], .node ["baz", "3", "4"]]

/--
info:
(+ (foo 1 2)
   (bar 2 3)
   (baz 3 4))
-/
#guard_msgs in
#eval testSExpr sExpr1 31

/--
info:
(+ (foo 1 2) (bar 2 3) (baz 3
                            4))
-/
#guard_msgs in
#eval testSExpr' sExpr1 31

def sExpr2 : SExpr := .node ["+", "123", "456", "789"]


/--
info:
(+ 123 456 789)
-/
#guard_msgs in
#eval testSExpr sExpr2 15

/--
info:
(+ 123
   456
   789)
-/
#guard_msgs in
#eval testSExpr sExpr2 14

/--
info:
(+
 123
 456
 789)
-/
#guard_msgs in
#eval testSExpr sExpr2 5

/--
info:
(+
 123
 456
 789)
-/
#guard_msgs in
#eval testSExpr sExpr2 0

def sExpr3 : SExpr :=
  .node ["a", "b", "c", "d"]

def sExpr4 : SExpr :=
  .node [sExpr3, sExpr3, sExpr3, sExpr3]

def sExpr5 : SExpr :=
  .node [.node ["abcde", sExpr4], .node ["abcdefgh", sExpr4]]

def pre1 := "hello: "

/--
info:
hello: ((abcde ((a b c d)
                (a b c d)
                (a b c d)
                (a b c d)))
        (abcdefgh
         ((a b c d)
          (a b c d)
          (a b c d)
          (a b c d))))
-/
#guard_msgs in
#eval testSExpr sExpr5 (20 + pre1.length) pre1

/--
info:
abc
def
-/
#guard_msgs in
#eval test (.indent 4 (.reset (.joinUsing .hardNl #[.text "abc", .text "def"]))) 80

/--
info:
abc
    def
-/
#guard_msgs in
#eval test (.indent 4 (.joinUsing .hardNl #[.text "abc", .text "def"])) 80

/--
info:
something
-/
#guard_msgs in
#eval test (.either (.joinUsing .hardNl #[.text "abc", .text "def"]) (.text "something")) 80

/-- info: none -/
#guard_msgs in
#eval format? .failure 80

def concated (n : Nat) : Doc :=
  if n = 0 then
    .text ""
  else
    .concat (concated (n - 1)) (.text "line")

/--
info:
linelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelineline
-/
#guard_msgs in
#eval test (concated 100) 100
