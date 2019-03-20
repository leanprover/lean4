/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.level init.lean.kvmap

namespace lean

inductive literal
| natVal (val : nat)
| strVal (val : string)

inductive binderInfo
| default | implicit | strictImplicit | instImplicit | auxDecl

/-
TODO(Leo): fix the `mvar` constructor.
In Lean3 (and Lean4), we have two kinds of metavariables: regular and temporary.
The type of regular metavariables is stored in the metavarContext.
The type of temporary metavariables is stored in the metavar itself. This decision is legacy from Lean2.
Moreover, the `name` in temporary metavariables are supposed to be (small) numerals. So,
we can store their assignment as an array. Actually, it is a numeral with a hidden unique prefix.
The decision of storing the type of the tmp metavar is also debatable.
For example, we can avoid this by have another array with their types.
For regular metavariables, the `expr` field is a dummy value.

We should have two different constructors:
`| mvar : name → expr` for regular metavariables
and
`| tmvar : usize → expr` for temporary metavariables
The `usize` makes it clear that we can use arrays to store tmp metavar assignments and their types.
-/
inductive expr
| bvar  : nat → expr                                -- bound variables
| fvar  : name → expr                               -- free variables
| mvar  : name → expr → expr                        -- (temporary) meta variables
| sort  : level → expr                              -- Sort
| const : name → list level → expr                  -- constants
| app   : expr → expr → expr                        -- application
| lam   : name → binderInfo → expr → expr → expr   -- lambda abstraction
| pi    : name → binderInfo → expr → expr → expr   -- Pi
| elet  : name → expr → expr → expr → expr          -- let expressions
| lit   : literal → expr                            -- literals
| mdata : kvmap → expr → expr                       -- metadata
| proj  : name → nat → expr → expr                  -- projection

instance exprIsInhabited : inhabited expr :=
⟨expr.sort level.zero⟩

attribute [extern "leanExprMkBvar"]   expr.bvar
attribute [extern "leanExprMkFvar"]   expr.fvar
attribute [extern "leanExprMkMvar"]   expr.mvar
attribute [extern "leanExprMkSort"]   expr.sort
attribute [extern "leanExprMkConst"]  expr.const
attribute [extern "leanExprMkApp"]    expr.app
attribute [extern "leanExprMkLambda"] expr.lam
attribute [extern "leanExprMkPi"]     expr.pi
attribute [extern "leanExprMkLet"]    expr.elet
attribute [extern "leanExprMkLit"]    expr.lit
attribute [extern "leanExprMkMdata"]  expr.mdata
attribute [extern "leanExprMkProj"]   expr.proj

namespace expr
def mkApp (fn : expr) (args : list expr) : expr :=
args.foldl expr.app fn

def mkCapp (fn : name) (args : list expr) : expr :=
mkApp (expr.const fn []) args

@[extern "leanExprHash"]
constant hash (n : @& expr) : usize := default usize

@[extern "leanExprDbgToString"]
constant dbgToString (e : @& expr) : string := default string

end expr

def getAppFn : expr → expr
| (expr.app f a) := getAppFn f
| e              := e

def mkBinApp (f a b : expr) :=
expr.app (expr.app f a) b

def mkDecIsTrue (pred proof : expr) :=
mkBinApp (expr.const `decidable.isTrue []) pred proof

def mkDecIsFalse (pred proof : expr) :=
mkBinApp (expr.const `decidable.isFalse []) pred proof

end lean
