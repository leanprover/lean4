import Lean.Elab.InfoTree
import Lean.Server.Rpc.Basic
import Lean.Widget.TaggedText

/-! This file defines the widget RPC data types but few functions, since in general the UI may explore
them in a mutually recursive fashion:
msg -> trace -> goal -> expr -> info -> msg (only a subset of ctrs) -> ..
-/

namespace Lean.Widget
open Server

-- TODO: Some of the `WithBlah` types exist mostly because we cannot derive multi-argument RPC wrappers.
-- They will be gone eventually.
structure InfoWithCtx where
  ctx : Elab.ContextInfo
  lctx : LocalContext
  info : Elab.Info
  deriving Inhabited, RpcEncoding with { withRef := true }

/-- Pretty-printed syntax (usually but not necessarily an `Expr`) with embedded `Info`s. -/
abbrev CodeWithInfos := TaggedText (WithRpcRef InfoWithCtx)

def CodeWithInfos.pretty (tt : CodeWithInfos) :=
  tt.stripTags

structure InteractiveGoal where
  hyps      : Array (String × CodeWithInfos)
  type      : CodeWithInfos
  userName? : Option String
  deriving Inhabited, RpcEncoding

namespace InteractiveGoal

def pretty (g : InteractiveGoal) : String :=
  let ret := match g.userName? with
    | some userName => s!"case {userName}\n"
    | none          => ""
  let hyps := g.hyps.map fun (name, tt) => s!"{name} : {tt.stripTags}"
  let ret := ret ++ "\n".intercalate hyps.toList
  ret ++ s!"⊢ {g.type.stripTags}"

end InteractiveGoal

-- TODO
structure LazyTrace where
  contents : String
  deriving Inhabited, FromJson, ToJson

inductive MsgEmbed where
  | expr : CodeWithInfos → MsgEmbed
  | goal : InteractiveGoal → MsgEmbed
  | lazyTrace : LazyTrace → MsgEmbed
  deriving Inhabited

namespace MsgEmbed

-- TODO(WN): `deriving RpcEncoding` for `inductive`
private inductive RpcEncodingPacket where
  | expr : TaggedText Lsp.RpcRef → RpcEncodingPacket
  | goal : Nat → RpcEncodingPacket
  | lazyTrace : LazyTrace → RpcEncodingPacket
  deriving Inhabited, FromJson, ToJson

instance : RpcEncoding MsgEmbed RpcEncodingPacket where
  rpcEncode a := match a with
    | expr t      => return RpcEncodingPacket.expr (← rpcEncode t)
    | goal t      => return RpcEncodingPacket.goal 0
    | lazyTrace t => return RpcEncodingPacket.lazyTrace (← rpcEncode t)

  rpcDecode a := match a with
    | RpcEncodingPacket.expr t      => return expr (← rpcDecode t)
    | RpcEncodingPacket.goal t      => return unreachable!
    | RpcEncodingPacket.lazyTrace t => return lazyTrace (← rpcDecode t)

end MsgEmbed

/-- We embed objects in messages by storing them in the tag of an empty subtree (`text ""`).
In other words, we terminate the `MsgEmbed`-tagged tree at embedded objects and instead
store the pretty-printed embed (which can itself be a `TaggedText`) in the tag. -/
abbrev InteractiveMessage := TaggedText MsgEmbed

namespace InteractiveMessage
open MsgEmbed

def pretty (msg : InteractiveMessage) : String :=
  let tt : TaggedText MsgEmbed := msg.rewrite fun
    | expr tt,     _ => TaggedText.text tt.stripTags
    | goal g,      _ => TaggedText.text g.pretty
    | lazyTrace t, _ => TaggedText.text t.contents
  tt.stripTags

end InteractiveMessage

end Lean.Widget
