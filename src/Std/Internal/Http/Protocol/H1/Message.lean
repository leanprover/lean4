
/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.Http.Data
public import Std.Internal.Http.Internal
public import Std.Internal.Http.Protocol.H1.Parser

public section

namespace Std.Http.Protocol.H1

/--
Direction of message flow in the HTTP connection in relation with requests.
-/
inductive Direction
  /--
  Processing incoming requests.
  -/
  | receiving

  /--
  Processing outgoing requests.
  -/
  | sending

/--
Inverts the direction of the requests.
-/
@[expose]
abbrev Direction.swap : Direction → Direction
  | .receiving => .sending
  | .sending => .receiving

/--
Get the message head type based on direction
-/
@[expose]
def Message.Head : Direction → Type
  | .receiving => Request.Head
  | .sending => Response.Head

def Message.Head.headers (m : Message.Head dir) : Headers :=
  match dir with
  | .receiving => Request.Head.headers m
  | .sending => Response.Head.headers m

def Message.Head.version (m : Message.Head dir) : Version :=
  match dir with
  | .receiving => Request.Head.version m
  | .sending => Response.Head.version m

instance : Repr (Message.Head dir) :=
  match dir with
  | .receiving => inferInstanceAs (Repr Request.Head)
  | .sending => inferInstanceAs (Repr Response.Head)

instance : ToString (Message.Head dir) :=
  match dir with
  | .receiving => inferInstanceAs (ToString Request.Head)
  | .sending => inferInstanceAs (ToString Response.Head)

instance : EmptyCollection (Message.Head dir) where
  emptyCollection :=
    match dir with
    | .receiving => {}
    | .sending => {}
