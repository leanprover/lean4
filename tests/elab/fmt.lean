import Lean.Fmt.Core.Formatter

/-!
Tests the renderings chosen by the core of the auto-formatter for various documents.
-/

open Lean.Fmt

-- Optimality cutoff width used by all tests in this file.
abbrev cutoff := 200

def traditional : Doc τ :=
  .join #[
    .text "function append(first,second,third){",
    .indented 4 true (
      let f : Doc τ := .text "first +"
      let s : Doc τ := .text "second +"
      let t : Doc τ := .text "third"
      .join #[
        .nl,
        .text "return ",
        .maybeFlattened (.indented 4 true (.join #[f, .nl, s, .nl, t]))]
    ),
    .nl,
    .text "}"
  ]

def test (width : Nat) (d : Doc (DefaultCost width cutoff)) (pre : String := "") : IO Unit := do
  IO.println ""
  let r? := format? width cutoff d (taintedResolution := true) (offset := pre.length)
  IO.println (pre ++ (r?.toOption.map (·.rendering) |>.getD ""))

/--
info:
function append(first,second,third){
    return first +
        second +
        third
}
-/
#guard_msgs in
#eval test 22 traditional

/--
info:
function append(first,second,third){
    return first + second + third
}
-/
#guard_msgs in
#eval test 36 traditional

inductive SExpr where
  | leaf (v : String)
  | node (cs : List SExpr)

instance : Coe String SExpr where
  coe v := .leaf v

partial def SExpr.pretty (s : SExpr) : Doc τ :=
  match s with
  | .leaf v => .text v
  | .node [] => .text "()"
  | .node (f :: args) =>
    let fp := f.pretty
    let argsp := args.toArray.map pretty
    .oneOf #[
      .join #[
        .text "(",
        .aligned (.joinUsing .hardNl (#[fp] ++ argsp)),
        .text ")"
      ],
      .join #[
        .text "(",
        .aligned fp,
        .text " ",
        .aligned (.joinUsing .hardNl argsp),
        .text ")"
      ],
      .flattened (
        .join #[
          .text "(",
          .aligned (.joinUsing (.text " ") (#[fp] ++ argsp)),
          .text ")"
        ]
      )
    ]

partial def SExpr.pretty' (s : SExpr) : Doc τ :=
  match s with
  | .leaf v => .text v
  | .node [] => .text "()"
  | .node (f :: args) =>
    let fp := f.pretty'
    let argsp := args.toArray.map pretty'
    .oneOf #[
      .join #[
        .text "(",
        .aligned (.joinUsing .hardNl (#[fp] ++ argsp)),
        .text ")"
      ],
      .join #[
        .text "(",
        .aligned fp,
        .text " ",
        .aligned (.joinUsing .hardNl argsp),
        .text ")"
      ],
      .join #[
        .text "(",
        .aligned (.joinUsing (.text " ") (#[fp] ++ argsp)),
        .text ")"
      ]
    ]

partial def SExpr.pretty'' (s : SExpr) : Doc τ :=
  match s with
  | .leaf v => .text v
  | .node [] => .text "()"
  | .node (f :: args) =>
    let fp := f.pretty''
    let argsp := args.toArray.map pretty''
    .oneOf #[
      .join #[
        .text "(",
        .nested (.joinUsing .hardNl (#[fp] ++ argsp)),
        .text ")"
      ],
      .flattened (
        .join #[
          .text "(",
          .nested (.joinUsing (.text " ") (#[fp] ++ argsp)),
          .text ")"
        ]
      )
    ]

def testSExpr (width : Nat) (e : SExpr) (pre : String := "") : IO Unit := do
  test width e.pretty pre

def testSExpr' (width : Nat) (e : SExpr) : IO Unit := do
  test width e.pretty'

def testSExpr'' (width : Nat) (e : SExpr) (pre : String := "") : IO Unit := do
  test width e.pretty'' pre

def sExpr1 : SExpr :=
  .node ["+", .node ["foo", "1", "2"], .node ["bar", "2", "3"], .node ["baz", "3", "4"]]

/--
info:
(+ (foo 1 2)
   (bar 2 3)
   (baz 3 4))
-/
#guard_msgs in
#eval testSExpr 31 sExpr1

/--
info:
(+ (foo 1 2) (bar 2 3) (baz 3
                            4))
-/
#guard_msgs in
#eval testSExpr' 31 sExpr1

def sExpr2 : SExpr := .node ["+", "123", "456", "789"]


/--
info:
(+ 123 456 789)
-/
#guard_msgs in
#eval testSExpr 15 sExpr2

/--
info:
(+ 123
   456
   789)
-/
#guard_msgs in
#eval testSExpr 14 sExpr2

/--
info:
(+
 123
 456
 789)
-/
#guard_msgs in
#eval testSExpr 5 sExpr2

/--
info:
(+
 123
 456
 789)
-/
#guard_msgs in
#eval testSExpr 0 sExpr2

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
#eval testSExpr (20 + pre1.length) sExpr5 pre1

/--
info:
hello: ((abcde
  ((a b c d)
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
#eval testSExpr'' (20 + pre1.length) sExpr5 pre1

/--
info:
abc
def
-/
#guard_msgs in
#eval test 80
  (.indented 4 true (.unindented false (.joinUsing .hardNl #[.text "abc", .text "def"])))

/--
info:
abc
    def
-/
#guard_msgs in
#eval test 80 (.indented 4 true (.joinUsing .hardNl #[.text "abc", .text "def"]))

/--
info:
something
-/
#guard_msgs in
#eval test 80 (.either (.joinUsing .hardNl #[.text "abc", .text "def"]) (.text "something"))

/-- info: none -/
#guard_msgs in
#eval format? 80 cutoff .failure (taintedResolution := true) |>.toOption.map (·.rendering)

def concated (n : Nat) : Doc τ :=
  if n = 0 then
    .text ""
  else
    .append (concated (n - 1)) (.text "line")

/--
info:
linelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelinelineline
-/
#guard_msgs in
#eval test 100 (concated 100)

/-!
`final` and its dual `initial`.
-/

/--
info:
cccc
-/
#guard_msgs in
#eval test 80 (.either (.append (.final (.text "a")) (.text "b")) (.text "cccc"))

/--
info:
ba
-/
#guard_msgs in
#eval test 80 (.append (.text "b") (.final (.text "a")))

/--
info:
a
b
-/
#guard_msgs in
#eval test 80 (.join #[.final (.text "a"), .hardNl, .text "b"])

/--
info:
a
-/
#guard_msgs in
#eval test 80 (.append (.final (.text "a")) .empty)

/-- info: none -/
#guard_msgs in
#eval format? 80 cutoff (.append (.final (.text "a")) (.text "b")) (taintedResolution := true)
  |>.toOption.map (·.rendering)

/--
info:
cccc
-/
#guard_msgs in
#eval test 80 (.either (.append (.text "b") (.initial (.text "a"))) (.text "cccc"))

/--
info:
ab
-/
#guard_msgs in
#eval test 80 (.append (.initial (.text "a")) (.text "b"))

/--
info:
b
a
-/
#guard_msgs in
#eval test 80 (.join #[.text "b", .hardNl, .initial (.text "a")])

/--
info:
a
-/
#guard_msgs in
#eval test 80 (.append .empty (.initial (.text "a")))

-- The start of the document is treated as the start of a line, even at a non-zero offset.
/--
info:
hello: a
-/
#guard_msgs in
#eval test 80 (.initial (.text "a")) "hello: "

/-- info: none -/
#guard_msgs in
#eval format? 80 cutoff (.append (.text "b") (.initial (.text "a"))) (taintedResolution := true)
  |>.toOption.map (·.rendering)

-- Fullness propagates through empty text nodes in both directions.
/--
info:
cccc
-/
#guard_msgs in
#eval test 80
  (.either (.join #[.text "b", .empty, .empty, .initial (.text "a")]) (.text "cccc"))

/--
info:
cccc
-/
#guard_msgs in
#eval test 80
  (.either (.join #[.final (.text "a"), .empty, .empty, .text "b"]) (.text "cccc"))

-- The formatter picks the alternative that moves an `initial` node to a fresh line.
/--
info:
x
y
-/
#guard_msgs in
#eval test 80
  (.append (.text "x") (.oneOf #[.initial (.text "y"), .append .hardNl (.initial (.text "y"))]))

-- A node that is both `initial` and `final` is placed on a line of its own.
/--
info:
x
y
z
-/
#guard_msgs in
#eval test 80 (.join #[
  .text "x",
  .oneOf #[.empty, .hardNl],
  .initial (.final (.text "y")),
  .oneOf #[.empty, .hardNl],
  .text "z"
])

-- Nested `initial` nodes impose no additional constraints.
/--
info:
b
ac
-/
#guard_msgs in
#eval test 80 (.join #[.text "b", .hardNl, .initial (.initial (.text "a")), .text "c"])

-- Flattening a newline in front of an `initial` node is rejected, since it would place text
-- before the `initial` node.
/--
info:
b
a
-/
#guard_msgs in
#eval test 80 (.maybeFlattened (.join #[.text "b", .nl, .initial (.text "a")]))

/--
info:
a b
-/
#guard_msgs in
#eval test 80 (.maybeFlattened (.join #[.initial (.text "a"), .nl, .text "b"]))

/-!
`fillUsingSpaceWithSoftBoundaries`.

These tests compare line breaks, so they must not normalize whitespace.
-/

def fillFlat (dss : Array (Array (Doc (DefaultCost w cutoff)))) : Doc (DefaultCost w cutoff) :=
  .fillUsingSpace dss.flatten

def fillSoft (dss : Array (Array (Doc (DefaultCost w cutoff)))) : Doc (DefaultCost w cutoff) :=
  .fillUsingSpaceWithSoftBoundaries (.ofHeightFallbackPenalty 1) dss

def abcd : Array (Array (Doc (DefaultCost w cutoff))) :=
  #[#[.text "a", .text "b"], #[.text "c", .text "d"]]

-- A soft boundary is not broken when breaking it would add a line.
/--
info:
a b c d
-/
#guard_msgs (whitespace := exact) in
#eval test 80 (fillSoft abcd)

/--
info:
a b c d
-/
#guard_msgs (whitespace := exact) in
#eval test 80 (fillFlat abcd)

-- Without soft boundaries, the fill is greedy and the second group is split across both lines.
/--
info:
a b c
d
-/
#guard_msgs (whitespace := exact) in
#eval test 5 (fillFlat abcd)

-- The soft boundary between the two groups is broken instead, which yields the same amount of
-- lines.
/--
info:
a b
c d
-/
#guard_msgs (whitespace := exact) in
#eval test 5 (fillSoft abcd)

-- Empty groups do not introduce a soft boundary.
/--
info:
a b
c d
-/
#guard_msgs (whitespace := exact) in
#eval test 5 (fillSoft #[#[], #[.text "a", .text "b"], #[], #[.text "c", .text "d"], #[]])

-- Groups of differing sizes.
/--
info:
a
b c d e
-/
#guard_msgs (whitespace := exact) in
#eval test 7 (fillSoft #[#[.text "a"], #[.text "b", .text "c", .text "d", .text "e"]])

-- The soft boundary stays unbroken because breaking it would add a line.
/--
info:
a b c d e
-/
#guard_msgs (whitespace := exact) in
#eval test 9 (fillSoft #[#[.text "a"], #[.text "b", .text "c", .text "d", .text "e"]])

-- Both soft boundaries are broken, since three lines are needed either way.
/--
info:
aaa
bbb bbb
ccc ccc
-/
#guard_msgs (whitespace := exact) in
#eval test 8 (fillSoft #[
  #[.text "aaa"],
  #[.text "bbb", .text "bbb"],
  #[.text "ccc", .text "ccc"]
])

/--
info:
aaa bbb
bbb ccc
ccc
-/
#guard_msgs (whitespace := exact) in
#eval test 8 (fillFlat #[
  #[.text "aaa"],
  #[.text "bbb", .text "bbb"],
  #[.text "ccc", .text "ccc"]
])

-- Fewer lines always win over broken soft boundaries.
/--
info:
aa bb bb
cc cc cc
-/
#guard_msgs (whitespace := exact) in
#eval test 8 (fillSoft #[
  #[.text "aa"],
  #[.text "bb", .text "bb"],
  #[.text "cc", .text "cc", .text "cc"]
])

-- A group is still split when its documents do not fit on a single line.
/--
info:
aaaa
bbbb
bbbb
-/
#guard_msgs (whitespace := exact) in
#eval test 4 (fillSoft #[#[.text "aaaa"], #[.text "bbbb", .text "bbbb"]])

-- A document that cannot be flattened is surrounded by newlines, just like in `fillUsingSpace`.
/--
info:
a
b
c
d
-/
#guard_msgs (whitespace := exact) in
#eval test 80 (fillSoft #[
  #[.text "a", .join #[.text "b", .hardNl, .text "c"]],
  #[.text "d"]
])

-- Flattening the whole document collapses every soft boundary to a space.
/--
info:
a b c d
-/
#guard_msgs (whitespace := exact) in
#eval test 5 (.flattened (fillSoft abcd))

/--
info:
a
-/
#guard_msgs (whitespace := exact) in
#eval test 80 (fillSoft #[#[], #[.text "a"]])

/-- info: -/
#guard_msgs (whitespace := exact) in
#eval test 80 (fillSoft #[])

/-! ## Guaranteed failure -/

-- Guaranteed failure composes through inner nodes, so the formatter prunes failing alternatives
-- before resolving them.
#guard (Doc.either .failure .failure : Doc Unit).isFailure (.mk false false false false)
#guard !(Doc.either .failure (.text "a") : Doc Unit).isFailure (.mk false false false false)
#guard (Doc.append (.text "a") .failure : Doc Unit).isFailure (.mk false false false false)
-- `initial` cannot follow a non-empty `text` on the same line, whatever the fullness state of the
-- position between them.
#guard (Doc.append (.text "a") (.initial (.text "b")) : Doc Unit).isFailure
  (.mk false false false false)
-- `final` fails if the line is not full after it, and otherwise if its inner document fails.
#guard (Doc.final (.text "a") : Doc Unit).isFailure (.mk false false false false)
#guard !(Doc.final (.text "a") : Doc Unit).isFailure (.mk false true false false)
#guard (Doc.final .failure : Doc Unit).isFailure (.mk false true false false)

/-! ## `guarded` -/

def atColumn0 : Assertion where
  id := `atColumn0
  assertion columnPos _ _ := columnPos == 0

-- A guard-free alternative that never fails makes the failure of an `either` independent of the
-- resolution context. A guard-free alternative that can fail does not.
#guard !(Doc.either (.guarded atColumn0 (.text "x")) (.text "y") : Doc Unit).hasContextDependentFailure
  (.mk false false false false)
#guard (Doc.either (.guarded atColumn0 (.text "x")) .failure : Doc Unit).hasContextDependentFailure
  (.mk false false false false)
-- Where the document below `guarded` fails whether the assertion holds or not, failure does not
-- depend on the resolution context.
#guard !(Doc.either (.guarded atColumn0 (.text "x")) (.text "y") : Doc Unit).hasContextDependentFailure
  (.mk true false false false)

-- In the following documents, the shared document `g` is first resolved at a column position where
-- the assertion fails and then at column 0, where it holds. The first failure must not prune `g`
-- at column 0.

def sharedGuard : Doc τ :=
  let g : Doc τ := .guarded atColumn0 (.text "x")
  .either (.append (.text "aaa") g) g

/--
info:
x
-/
#guard_msgs (whitespace := exact) in
#eval test 80 sharedGuard

-- The guard-free alternative of `g` always fails.
def sharedGuardWithFailingAlternative : Doc τ :=
  let g : Doc τ := .either (.guarded atColumn0 (.text "x")) .failure
  .either (.append (.text "aaa") g) g

/--
info:
x
-/
#guard_msgs (whitespace := exact) in
#eval test 80 sharedGuardWithFailingAlternative

def sharedGuardInAppend : Doc τ :=
  let g : Doc τ := .append (.text "") (.guarded atColumn0 (.text "x"))
  .either (.append (.text "aaa") g) g

/--
info:
x
-/
#guard_msgs (whitespace := exact) in
#eval test 80 sharedGuardInAppend

def sharedGuardInFinal : Doc τ :=
  let g : Doc τ := .final (.guarded atColumn0 (.text "x"))
  .either (.append (.text "aaa") g) g

/--
info:
x
-/
#guard_msgs (whitespace := exact) in
#eval test 80 sharedGuardInFinal

-- `g` is first resolved at column 3 at the start of a line, where `initial` holds.
def sharedGuardInInitial : Doc τ :=
  let g : Doc τ := .initial (.guarded atColumn0 (.text "x"))
  .either (.indented 3 true (.append .hardNl g)) g

/--
info:
x
-/
#guard_msgs (whitespace := exact) in
#eval test 80 sharedGuardInInitial

-- Both measures of the first document are followed by a tainted resolution of the guarded document,
-- since its indentation exceeds the optimality cutoff width. The assertion only holds after the
-- second measure, so merging both resolutions must keep the second one.
def taintedGuard : Doc τ :=
  .append
    (.either (.text "aaaa") (.append (.text "b") .hardNl))
    (.indented (cutoff + 50) true (.guarded atColumn0 (.text "x")))

/--
info:
b
x
-/
#guard_msgs (whitespace := exact) in
#eval test 80 taintedGuard
