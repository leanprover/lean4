import Lean
open Lean
open Lean.Elab
open Lean.Elab.Term

instance : HasMonadLift MetaM MetaIO :=
⟨fun α x ⟨env, opts⟩ => Prod.fst <$> IO.runMeta x env { opts := opts }⟩

private def liftTermElabMSimple {α} (elab : TermElabM α) : MetaM (Except MessageLog α) := do
ctx ← read;
st ← get;
match elab { ctx with fileName := "<delaborator>", fileMap := arbitrary _, cmdPos := 0, currNamespace := Name.anonymous } { st with } with
| EStateM.Result.ok a newS => if !newS.messages.hasErrors then pure (Except.ok a) else pure (Except.error newS.messages)
| EStateM.Result.error (Term.Exception.ex (Exception.error msg)) newS => pure (Except.error $ MessageLog.empty.add msg)
| EStateM.Result.error _ newS => unreachable!

#eval show MetaIO Unit from do
  opts ← MetaIO.getOptions;
  let stx := Unhygienic.run `(id $ @pure (fun _ => Nat) ⟨fun x => 0⟩ _ (id false));
  IO.println $ "syntax input: " ++ stx.reprint.get!;
  Except.ok e ← liftM $ liftTermElabMSimple $ elabTermAndSynthesize stx none
    | throw $ IO.userError "failed to elaborate?";
  IO.println $ "elaboration output: " ++ toString e;
  stx ← liftM $ delab e opts;
  IO.println $ "delaboration output: " ++ stx.reprint.get!;
  Except.error msgs ← liftM $ liftTermElabMSimple $ elabTermAndSynthesize stx none
    | throw $ IO.userError "succeeded to elaborate?";
  IO.println $ "re-elaboration output:";
  msgs.forM IO.println;
  let posOpts : OptionsPerPos := {};
  let posOpts := msgs.toList.foldl (fun (posOpts : OptionsPerPos) msg =>
    let opts := KVMap.empty.insert `pp.explicit true;
    posOpts.insert msg.pos.column opts) posOpts;
  stx ← liftM $ delab e opts posOpts;
  IO.println $ "delaboration output after applying pp.explicit to error locations: " ++ stx.reprint.get!;
  Except.ok e' ← liftM $ liftTermElabMSimple $ elabTermAndSynthesize stx none
    | throw $ IO.userError "failed to elaborate?";
  IO.println $ "new re-elaboration output: " ++ toString e';
  condM (liftM (Meta.isDefEq e e'))
    (IO.println "terms are defeq!")
    (throw $ IO.userError "terms are not defeq?");
  pure ()
