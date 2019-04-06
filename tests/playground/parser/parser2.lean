import init.lean.name
open Lean

/-
We need the following compiler improvement for this experiment:

- The cases-merging optimization does not work when scrutinee is a constant.
  We need more tests for cases-merging.
-/
def ParserCache := Nat -- TODO
def Syntax      := String -- TODO

structure ParserData :=
(stxStack : Array Syntax) (pos : String.Pos) (cache : ParserCache) (errorMsg : Option String)

@[inline] def ParserData.hasError (d : ParserData) : Bool :=
d.errorMsg != none

@[inline] def ParserData.stackSize (d : ParserData) : Nat :=
d.stxStack.size

@[inline] def Array.shrink {α : Type} (a : Array α) (sz : Nat) : Array α :=
a -- TODO

@[inline] def ParserData.restore : ParserData → Nat → ParserData
| ⟨stack, pos, cache, _⟩ sz := ⟨stack.shrink sz, pos, cache, none⟩

def ParserFn := String → ParserData → ParserData

def ParserConfig        := List String -- TODO
def CommandParserConfig := List String -- TODO

structure TokenConfig :=
(val : String) (lbp : Nat := 0)

structure ParserInfo :=
(updateTokens : NameSet → NameSet  := λ m, m)
(firstToken   : Option TokenConfig := none)

@[inline] def ParserFn.eps : ParserFn :=
λ s d, d

@[inline] def andthenFn (p q : ParserFn) : ParserFn :=
λ s d,
  let d := p s d in
  if d.hasError then d else q s d

@[noinline] def andthenInfo (p q : ParserInfo) : ParserInfo :=
{ updateTokens := q.updateTokens ∘ p.updateTokens,
  firstToken   := p.firstToken }

@[inline] def orelseFn (p q : ParserFn) : ParserFn :=
λ s d,
  let iniPos := d.pos in
  let iniSz  := d.stackSize in
  let d      := p s d in
  if d.hasError && d.pos == iniPos then q s (d.restore iniSz) else d

@[noinline] def orelseInfo (p q : ParserInfo) : ParserInfo :=
{ updateTokens := q.updateTokens ∘ p.updateTokens,
  firstToken   := none }

def ParserData.resetPos : ParserData → String.Pos → ParserData
| ⟨stack, _, cache, errorMsg⟩ pos := ⟨stack, pos, cache, errorMsg⟩

@[inline] def tryFn (p : ParserFn) : ParserFn :=
λ s d,
  let iniPos := d.pos in
  let d := p s d in
  if d.hasError then d.resetPos iniPos else d

@[noinline] def tryInfo (p : ParserInfo) : ParserInfo :=
{ updateTokens := p.updateTokens,
  firstToken   := none }

instance : Inhabited ParserFn :=
⟨λ s, id⟩

structure AbsParser (ρ : Type) :=
(info : Thunk ParserInfo) (fn : ρ)

abbrev Parser := AbsParser ParserFn

class ParserFnLift (ρ : Type) :=
(lift {} : ParserFn → ρ)
(map     : (ParserFn → ParserFn) → ρ → ρ)
(map₂    : (ParserFn → ParserFn → ParserFn) → ρ → ρ → ρ)

instance parserLiftInhabited {ρ : Type} [ParserFnLift ρ] : Inhabited ρ :=
⟨ParserFnLift.lift (default _)⟩

instance : ParserFnLift ParserFn :=
{ lift := λ p, p,
  map  := λ m p, m p,
  map₂ := λ m p1 p2, m p1 p2 }

@[inline]
def liftParser {ρ : Type} [ParserFnLift ρ] (info : Thunk ParserInfo) (fn : ParserFn) : AbsParser ρ :=
{ info := info, fn := ParserFnLift.lift fn }

@[inline]
def mapParser {ρ : Type} [ParserFnLift ρ] (infoFn : ParserInfo → ParserInfo) (pFn : ParserFn → ParserFn) : AbsParser ρ → AbsParser ρ :=
λ p, { info := Thunk.mk (λ _, infoFn p.info.get), fn := ParserFnLift.map pFn p.fn }

@[inline]
def mapParser₂ {ρ : Type} [ParserFnLift ρ] (infoFn : ParserInfo → ParserInfo → ParserInfo) (pFn : ParserFn → ParserFn → ParserFn)
               : AbsParser ρ → AbsParser ρ → AbsParser ρ :=
λ p q, { info := Thunk.mk (λ _, infoFn p.info.get q.info.get), fn := ParserFnLift.map₂ pFn p.fn q.fn }

def EnvParserFn (α : Type) (ρ : Type) :=
α → ρ

def RecParserFn (α ρ : Type) :=
EnvParserFn (α → ρ) ρ

instance (α ρ : Type) [ParserFnLift ρ] : ParserFnLift (EnvParserFn α ρ) :=
{ lift    := λ p a, ParserFnLift.lift p,
  map     := λ m p a, ParserFnLift.map m (p a),
  map₂    := λ m p1 p2 a, ParserFnLift.map₂ m (p1 a) (p2 a) }

instance (α ρ : Type) [ParserFnLift ρ] : ParserFnLift (RecParserFn α ρ) :=
inferInstanceAs (ParserFnLift (EnvParserFn (α → ρ) ρ))

namespace RecParserFn
variables {α ρ : Type}

@[inline] def recurse (a : α) : RecParserFn α ρ :=
λ p, p a

@[inline] def run [ParserFnLift ρ] (x : RecParserFn α ρ) (rec : α → RecParserFn α ρ) : ρ :=
x (fix (λ f a, rec a f))

end RecParserFn

@[noinline] def tokenFn (s : String) : ParserFn :=
λ s d, d

@[noinline] def tokenInfo (s : String) : ParserInfo :=
{ updateTokens := λ m, m.insert (mkSimpleName s),
  firstToken   := some { val := s } }

@[inline] def token {ρ : Type} [ParserFnLift ρ] (s : String) : AbsParser ρ :=
liftParser (tokenInfo s) (tokenFn s)

@[inline] def andthen {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ → AbsParser ρ :=
mapParser₂ andthenInfo andthenFn

@[inline] def orelse {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ → AbsParser ρ :=
mapParser₂ orelseInfo orelseFn

@[inline] def try {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ :=
mapParser tryInfo tryFn

abbrev BasicParser : Type            := AbsParser (EnvParserFn ParserConfig ParserFn)
abbrev CmdParserFn (ρ : Type) : Type := EnvParserFn ρ (RecParserFn Unit ParserFn)
abbrev TermParserFn : Type           := RecParserFn Nat (CmdParserFn ParserConfig)
abbrev TermParser : Type             := AbsParser TermParserFn
abbrev TrailingTermParser : Type     := AbsParser (EnvParserFn Syntax TermParserFn)
abbrev CommandParser : Type          := AbsParser (CmdParserFn CommandParserConfig)

@[inline] def basicParser2TermParser (p : BasicParser) : TermParser :=
{ info := Thunk.mk (λ _, p.info.get), fn := λ _ cfg _, p.fn cfg }

instance basic2term : HasCoe BasicParser TermParser :=
⟨basicParser2TermParser⟩

local infix ` ; `:10 := _root_.andthen
local infix ` || `:5 := _root_.orelse


def p0 : BasicParser :=
token "foo"; token "boo"

set_option pp.implicit true
set_option pp.binder_types false
set_option trace.compiler.stage1 true
set_option trace.compiler.lcnf true
-- set_option trace.compiler.simp true

def p1 (s : String) : TermParser :=
token "hello"; token "world"; token "boo"
||
token s
||
token "opt3"; token "boo"

@[noinline] def p1_info (s : String) : ParserInfo := {}
@[noinline] def p1_fn   (s : String) : TermParserFn   := default _

@[inline] def p1_aux (s : String) : TermParser :=
{ info := Thunk.mk (λ _, p1_info s), fn := p1_fn s }

def p2 (s : String) : TermParser :=
-- token "boo"; p1; p1; p0
p1_aux "hello"; p0; p1_aux s

def p4 (s : String) : CommandParser :=
token s; token "boo"
