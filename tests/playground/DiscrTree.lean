import Lean.Format
open Lean

def List.insert {α} [BEq α] (as : List α) (a : α) : List α :=
if as.contains a then as else a::as

inductive Term
| var : Nat → Term
| app : String → Array Term → Term

instance : Inhabited Term := ⟨Term.var 0⟩

inductive Key
| var : Key
| sym : String → Nat → Key

instance : Inhabited Key := ⟨Key.var⟩

def Key.beq : Key → Key → Bool
| Key.var,       Key.var       => true
| Key.sym k₁ a₁, Key.sym k₂ a₂ => k₁ == k₂ && a₁ == a₂
| _,             _             => false

instance : BEq Key := ⟨Key.beq⟩

def Key.lt : Key → Key → Bool
| Key.var,       Key.var       => false
| Key.var,       _             => true
| Key.sym k₁ a₁, Key.sym k₂ a₂ => k₁ < k₂ || (k₁ == k₂ && a₁ < a₂)
| _,             _             => false

instance : Less Key := ⟨fun k₁ k₂ => k₁.lt k₂⟩

def Key.format : Key → Format
| Key.var     => "*"
| Key.sym k a => if a > 0 then k ++ "." ++ fmt a else k

instance : HasFormat Key := ⟨Key.format⟩

def Term.key : Term → Key
| Term.var _    => Key.var
| Term.app f as => Key.sym f as.size

def Term.args : Term → Array Term
| Term.var _    => #[]
| Term.app f as => as

-- TODO: root should be a persistent hash map
inductive Trie (α : Type)
| node (vals : List α) (children : Array (Key × Trie)) : Trie

namespace Trie

def empty {α} : Trie α :=
node [] #[]

instance {α} : Inhabited (Trie α) := ⟨empty⟩

partial def appendTodoAux (as : Array Term) : Nat → Array Term → Array Term
| 0,   todo => todo
| i+1, todo => appendTodoAux i (todo.push (as.get! i))

def appendTodo (todo : Array Term) (as : Array Term) : Array Term :=
appendTodoAux as as.size todo

partial def createNodes {α} (v : α) : Array Term → Trie α
| todo =>
  if todo.isEmpty then node [v] #[]
  else
    let t    := todo.back;
    let todo := todo.pop;
    node [] #[(t.key, createNodes (appendTodo todo t.args))]

partial def insertAux {α} [BEq α] (v : α) : Array Term → Trie α → Trie α
| todo, node vs cs =>
  if todo.isEmpty then node (vs.insert v) cs
  else
    let t    := todo.back;
    let todo := todo.pop;
    let todo := appendTodo todo t.args;
    let k    := t.key;
    node vs $ Id.run $
      cs.binInsertM
        (fun a b => a.1 < b.1)
        (fun ⟨_, s⟩ => (k, insertAux todo s)) -- merge with existing
        (fun _ => (k, createNodes v todo))  -- add new node
        (k, arbitrary _)

def insert {α} [BEq α] (d : Trie α) (k : Term) (v : α) : Trie α :=
let todo : Array Term := Array.mkEmpty 32;
let todo := todo.push k;
insertAux v todo d

partial def format {α} [HasFormat α] : Trie α → Format
| node vs cs => Format.group $ Format.paren $ "node" ++ (if vs.isEmpty then Format.nil else " " ++ fmt vs) ++ Format.join (cs.toList.map $ fun ⟨k, c⟩ => Format.line ++ Format.paren (fmt k ++ " => " ++ format c))

instance {α} [HasFormat α] : HasFormat (Trie α) := ⟨format⟩

@[specialize] partial def foldMatchAux {α β} {m : Type → Type} [Monad m] (f : β → α → m β) : Array Term → Trie α → β → m β
| todo, node vs cs, b =>
  if todo.isEmpty then vs.foldlM f b
  else if cs.isEmpty then pure b
  else
    let t     := todo.back;
    let todo  := todo.pop;
    let first := cs.get! 0;
    let k     := t.key;
    match k with
    | Key.var     => if first.1 == Key.var then foldMatchAux todo first.2 b else pure b
    | Key.sym _ _ => do
      match cs.binSearch (k, arbitrary _) (fun a b => a.1 < b.1) with
      | none   => if first.1 == Key.var then foldMatchAux todo first.2 b else pure b
      | some c => do
        b ← if first.1 == Key.var then foldMatchAux todo first.2 b else pure b;
        let todo := appendTodo todo t.args;
        foldMatchAux todo c.2 b

@[specialize] def foldMatch {α β} {m : Type → Type} [Monad m] (d : Trie α) (k : Term) (f : β → α → m β) (b : β) : m β :=
let todo : Array Term := Array.mkEmpty 32;
let todo := todo.push k;
foldMatchAux f todo d b

/-- Return all (approximate) matches (aka generalizations) of the term `k` -/
def getMatch {α} (d : Trie α) (k : Term) : Array α :=
Id.run $ d.foldMatch k (fun (r : Array α) v => pure $ r.push v) #[]

@[specialize] partial def foldUnifyAux {α β} {m : Type → Type} [Monad m] (f : β → α → m β) : Nat → Array Term → Trie α → β → m β
| skip+1, todo, node vs cs, b =>
  if cs.isEmpty then pure b
  else
    cs.foldlM
      (fun b ⟨k, c⟩ =>
        match k with
        | Key.var     => foldUnifyAux skip todo c b
        | Key.sym _ a => foldUnifyAux (skip + a) todo c b)
      b
| 0, todo, node vs cs, b =>
  if todo.isEmpty then vs.foldlM f b
  else if cs.isEmpty then pure b
  else
    let t     := todo.back;
    let todo  := todo.pop;
    let first := cs.get! 0;
    let k     := t.key;
    match k with
    | Key.var     =>
      cs.foldlM
        (fun b ⟨k, c⟩ =>
           match k with
           | Key.var     => foldUnifyAux 0 todo c b
           | Key.sym _ a => foldUnifyAux a todo c b)
        b
    | Key.sym _ _ => do
      match cs.binSearch (k, arbitrary _) (fun a b => a.1 < b.1) with
      | none   => if first.1 == Key.var then foldUnifyAux 0 todo first.2 b else pure b
      | some c => do
        b ← if first.1 == Key.var then foldUnifyAux 0 todo first.2 b else pure b;
        let todo := appendTodo todo t.args;
        foldUnifyAux 0 todo c.2 b

@[specialize] def foldUnify {α β} {m : Type → Type} [Monad m] (d : Trie α) (k : Term) (f : β → α → m β) (b : β) : m β :=
let todo : Array Term := Array.mkEmpty 32;
let todo := todo.push k;
foldUnifyAux f 0 todo d b

/-- Return all candidate unifiers of the term `k` -/
def getUnify {α} (d : Trie α) (k : Term) : Array α :=
Id.run $ d.foldUnify k (fun (r : Array α) v => pure $ r.push v) #[]

end Trie

def mkApp (s : String) (cs : Array Term) := Term.app s cs
def mkConst (s : String) := Term.app s #[]
def mkVar (i : Nat) := Term.var i

def tst1 : IO Unit :=
let d  := @Trie.empty Nat;
let t  := mkApp "f" #[mkApp "g" #[mkConst "a"], mkApp "g" #[mkConst "b"]];
let d  := d.insert t 10;
let t  := mkApp "f" #[mkApp "h" #[mkConst "a", mkVar 0], mkConst "b"];
let d  := d.insert t 20;
let t  := mkApp "f" #[mkConst "b", mkConst "c", mkConst "d"];
let d  := d.insert t 20;
let d  := (20:Nat).fold
  (fun i (d : Trie Nat) =>
    let t  := mkApp "f" #[mkApp "h" #[mkConst "a", mkVar 0], mkApp "f" #[mkConst ("c" ++ toString i)]];
    d.insert t i)
  d;
let d  := (20:Nat).fold
  (fun i (d : Trie Nat) =>
    let t  := mkApp "f" #[mkApp "g" #[mkConst ("a" ++ toString i)], mkApp "g" #[mkConst "b"]];
    d.insert t i)
  d;
-- let t  := mkApp "g" [mkApp "h" [mkConst "a"]];
-- let d  := d.insert t 10;
IO.println (format d)

#eval tst1

def check (as bs : Array Nat) : IO Unit :=
let as := as.qsort (fun a b => a < b);
let bs := bs.qsort (fun a b => a < b);
unless (as == bs) $ throw $ IO.userError "check failed"

def tst2 : IO Unit :=
do
let d  := @Trie.empty Nat;
let d  := d.insert (mkApp "f" #[mkVar 0, mkConst "a"]) 1;                  -- f * a
let d  := d.insert (mkApp "f" #[mkConst "b", mkVar 0]) 2;                  -- f b *
let d  := d.insert (mkApp "f" #[mkVar 0, mkVar 0]) 3;                      -- f * *
let d  := d.insert (mkApp "f" #[mkVar 0, mkConst "b"]) 4;                  -- f * b
let d  := d.insert (mkApp "f" #[mkApp "h" #[mkVar 0], mkConst "b"]) 5;     -- f (h *) b
let d  := d.insert (mkApp "f" #[mkApp "h" #[mkConst "a"], mkConst "b"]) 6; -- f (h a) b
let d  := d.insert (mkApp "f" #[mkApp "h" #[mkConst "a"], mkVar 1]) 7;     -- f (h a) *
let d  := d.insert (mkApp "f" #[mkApp "h" #[mkConst "a"], mkVar 0]) 8;     -- f (h a) *
let d  := d.insert (mkApp "f" #[mkApp "h" #[mkVar 0], mkApp "h" #[mkConst "b"]]) 9;  -- f (h *) (h b)
let d  := d.insert (mkApp "g" #[mkVar 0, mkConst "a"]) 10;                  -- g * a
let d  := d.insert (mkApp "g" #[mkConst "b", mkVar 0]) 11;                  -- g b *
let d  := d.insert (mkApp "g" #[mkVar 0, mkVar 0]) 12;                      -- g * *
let d  := d.insert (mkApp "g" #[mkApp "h" #[mkConst "a"], mkConst "b"]) 13; -- g (h a) b
let d  := d.insert (mkApp "g" #[mkApp "h" #[mkConst "a"], mkVar 1]) 14;     -- g (h a) *
IO.println (format d);
let vs := d.getMatch (mkApp "f" #[mkApp "h" #[mkConst "a"], mkApp "h" #[mkConst "b"]]); -- f (h a) (h b)
check vs #[3, 7, 8, 9];
let vs := d.getMatch (mkApp "f" #[mkConst "b", mkConst "a"]); -- f a b
check vs #[1, 2, 3];
let vs := d.getMatch (mkApp "g" #[mkConst "b", mkConst "b"]); -- g b b
check vs #[11, 12];
let vs := d.getUnify (mkApp "f" #[mkApp "h" #[mkVar 0], mkApp "h" #[mkVar 0]]); -- f (h *) (h *)
check vs #[3, 7, 8, 9];
let vs := d.getUnify (mkApp "f" #[mkApp "h" #[mkVar 0], mkVar 0]); -- f (h *) *
check vs #[1, 3, 4, 5, 6, 7, 8, 9];
let vs := d.getUnify (mkApp "f" #[mkApp "h" #[mkConst "b"], mkVar 0]); -- f (h b) *
check vs #[1, 3, 4, 5, 9];
let vs := d.getUnify (mkVar 0);                                         -- *
check vs (List.iota 14).toArray;
let vs := d.getUnify (mkApp "g" #[mkVar 0, mkConst "b"]);               -- g * b
check vs #[11, 12, 13, 14];
let vs := d.getUnify (mkApp "g" #[mkApp "h" #[mkVar 0], mkConst "b"]);  -- g (h *) b
check vs #[12, 13, 14];
let vs := d.getUnify (mkApp "g" #[mkApp "h" #[mkConst "b"], mkVar 0]);  -- g (h b) *
check vs #[10, 12];
pure ()

#eval tst2
