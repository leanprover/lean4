/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.ordering.basic init.coe init.data.option.basic init.io

universes u v w w'

inductive color
| Red | Black

inductive node (α : Type u) (β : Type v)
| Leaf  {}                                                                      : node
| Node  (color : color) (lchild : node) (key : α) (val : β) (rchild : node) : node

variables {α : Type u} {β : Type v} {σ : Type w}
open color nat node

@[specialize] def fold (f : Π (k : α), β → σ → σ) : node α β → σ → σ
| Leaf b               := b
| (Node _ l k v r)   b := fold r (f k v (fold l b))

def balance1 : node α β → node α β → node α β
| (Node _ _ kv vv t) (Node _ (Node Red l kx vx r₁) ky vy r₂) := Node Red (Node Black l kx vx r₁) ky vy (Node Black r₂ kv vv t)
| (Node _ _ kv vv t) (Node _ l₁ ky vy (Node Red l₂ kx vx r)) := Node Red (Node Black l₁ ky vy l₂) kx vx (Node Black r kv vv t)
| (Node _ _ kv vv t) (Node _ l  ky vy r)                     := Node Black (Node Red l ky vy r) kv vv t
| _                                                        _ := Leaf

def balance2 : node α β → node α β → node α β
| (Node _ t kv vv _) (Node _ (Node Red l kx₁ vx₁ r₁) ky vy r₂)  := Node Red (Node Black t kv vv l) kx₁ vx₁ (Node Black r₁ ky vy r₂)
| (Node _ t kv vv _) (Node _ l₁ ky vy (Node Red l₂ kx₂ vx₂ r₂)) := Node Red (Node Black t kv vv l₁) ky vy (Node Black l₂ kx₂ vx₂ r₂)
| (Node _ t kv vv _) (Node _ l ky vy r)                         := Node Black t kv vv (Node Red l ky vy r)
| _                                                        _    := Leaf

def is_red : node α β → bool
| (Node Red _ _ _ _) := tt
| _                  := ff

section insert
variables (lt : α → α → Prop) [decidable_rel lt]

@[specialize] def ins : node α β → α → β → node α β
| Leaf                 kx vx := Node Red Leaf kx vx Leaf
| (Node Red a ky vy b) kx vx :=
   (if lt kx ky then Node Red (ins a kx vx) ky vy b
    else if lt ky kx then Node Red a ky vy (ins b kx vx)
    else Node Red a ky vy (ins b kx vx))
| (Node Black a ky vy b) kx vx :=
    if lt kx ky then
      (if is_red a then balance1 (Node Black Leaf ky vy b) (ins a kx vx)
       else Node Black (ins a kx vx) ky vy b)
    else if lt ky kx then
      (if is_red b then balance2 (Node Black a ky vy Leaf) (ins b kx vx)
       else Node Black a ky vy (ins b kx vx))
    else Node Black a kx vx b

def set_black : node α β → node α β
| (Node _ l k v r) := Node Black l k v r
| e                := e

@[specialize] def insert (t : node α β) (k : α) (v : β) : node α β :=
if is_red t then set_black (ins lt t k v)
else ins lt t k v

end insert

def mk_map_aux : nat → node nat bool → node nat bool
| 0 m := m
| (n+1) m := mk_map_aux n (insert (<) m n (n % 10 = 0))

def mk_map (n : nat) :=
mk_map_aux n Leaf

def main (xs : list string) : io uint32 :=
let m := mk_map xs.head.to_nat in
let v := fold (λ (k : nat) (v : bool) (r : nat), if v then r + 1 else r) m 0 in
io.println' (to_string v) *>
pure 0
