/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Lean.Data.Options

namespace Lean

register_builtin_option pp.maxSteps : Nat := {
  defValue := 5000
  group    := "pp"
  descr    := "(pretty printer) maximum number of expressions to visit, after which terms will pretty print as `⋯`"
}
register_builtin_option pp.all : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display coercions, implicit parameters, proof terms, fully qualified names, universe, " ++
              "and disable beta reduction and notations during pretty printing"
}
register_builtin_option pp.notation : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) disable/enable notation (infix, mixfix, postfix operators and unicode characters)"
}
register_builtin_option pp.parens : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) if set to true, notation is wrapped in parentheses regardless of precedence"
}
register_builtin_option pp.unicode.fun : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) disable/enable unicode ↦ notation for functions"
}
register_builtin_option pp.match : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) disable/enable 'match' notation"
}
register_builtin_option pp.sorrySource : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) if true, pretty print 'sorry' with its originating source position, if available"
}
register_builtin_option pp.coercions : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) hide coercion applications"
}
register_builtin_option pp.coercions.types : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display coercion applications with a type ascription"
}
register_builtin_option pp.universes : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display universe"
}
register_builtin_option pp.fullNames : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display fully qualified names"
}
register_builtin_option pp.privateNames : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display internal names assigned to private declarations"
}
register_builtin_option pp.funBinderTypes : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display types of lambda parameters"
}
register_builtin_option pp.piBinderTypes : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) display types of pi parameters"
}
register_builtin_option pp.letVarTypes : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display types of let-bound variables"
}
register_builtin_option pp.natLit : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display raw natural number literals with `nat_lit` prefix"
}
register_builtin_option pp.numericTypes : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display types of numeric literals"
}
register_builtin_option pp.instantiateMVars : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) instantiate mvars before delaborating"
}
register_builtin_option pp.mvars : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) display names of metavariables when true, \
    and otherwise display them as '?_' (for expression metavariables) and as '_' (for universe level metavariables)"
}
register_builtin_option pp.mvars.levels : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) display universe level metavariables as `?u.22` when true, and otherwise display them as '_'. \
    When either 'pp.mvars' or 'pp.mvars.anonymous' is false, this is 'false' as well."
}
register_builtin_option pp.mvars.anonymous : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) display names for auto-generated metavariables such as `?m.22` when true, \
    and otherwise display them as '?_' (for expression metavariables) and as '_' (for universe level metavariables). \
    When 'pp.mvars' is false, this is 'false' as well."
}
register_builtin_option pp.mvars.withType : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display metavariables with a type ascription"
}
register_builtin_option pp.mvars.delayed : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display delayed assigned metavariables when true, otherwise display what they are assigned to"
}
register_builtin_option pp.beta : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) apply beta-reduction when pretty printing"
}
register_builtin_option pp.structureInstances : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) display structure instances using the '{ fieldName := fieldValue, ... }' notation, \
              or using '⟨fieldValue, ... ⟩' if structure is tagged with the '@[pp_using_anonymous_constructor]' attribute"
}
register_builtin_option pp.structureInstances.flatten : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) flatten nested structure instances for parent projections"
}
register_builtin_option pp.fieldNotation : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) use field notation when pretty printing, including for structure projections, unless '@[pp_nodot]' is applied"
}
register_builtin_option pp.fieldNotation.generalized : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) when `pp.fieldNotation` is true, enable using generalized field notation when the argument for field notation is the first explicit argument"
}
register_builtin_option pp.explicit : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display implicit arguments"
}
register_builtin_option pp.structureInstanceTypes : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display type of structure instances"
}
register_builtin_option pp.safeShadowing  : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) allow variable shadowing if there is no collision"
}
register_builtin_option pp.tagAppFns : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) tag all constants that are the function in a function application"
}
register_builtin_option pp.proofs : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display proofs when true, and replace proofs appearing within expressions by `⋯` when false"
}
register_builtin_option pp.proofs.withType : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) when `pp.proofs` is false, adds a type ascription to the omitted proof"
}
register_builtin_option pp.proofs.threshold : Nat := {
  defValue := 0
  group    := "pp"
  descr    := "(pretty printer) when `pp.proofs` is false, controls the complexity of proofs at which they begin being replaced with `⋯`"
}
register_builtin_option pp.instances : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) if set to false, replace inst-implicit arguments to explicit applications with placeholders"
}
register_builtin_option pp.instanceTypes : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) when printing explicit applications, show the types of inst-implicit arguments"
}
register_builtin_option pp.deepTerms : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display deeply nested terms, replacing them with `⋯` if set to false"
}
register_builtin_option pp.deepTerms.threshold : Nat := {
  defValue := 50
  group    := "pp"
  descr    := "(pretty printer) when `pp.deepTerms` is false, the depth at which terms start being replaced with `⋯`"
}
register_builtin_option pp.motives.pi : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) print all motives that return pi types"
}
register_builtin_option pp.motives.nonConst : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) print all motives that are not constant functions"
}
register_builtin_option pp.motives.all : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) print all motives"
}
-- TODO:
/-
register_builtin_option g_pp_locals_full_names : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) show full names of locals"
}
register_builtin_option g_pp_goal_compact : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) try to display goal in a single line when possible"
}
register_builtin_option g_pp_goal_max_hyps : Nat := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) maximum number of hypotheses to be displayed"
}
register_builtin_option g_pp_annotations : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display internal annotations (for debugging purposes only)"
}
register_builtin_option g_pp_compact_let : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) minimal indentation at `let`-declarations"
}
-/

def getPPMaxSteps (o : Options) : Nat := o.get pp.maxSteps.name pp.maxSteps.defValue
def getPPAll (o : Options) : Bool := o.get pp.all.name false
def getPPFunBinderTypes (o : Options) : Bool := o.get pp.funBinderTypes.name (getPPAll o)
def getPPPiBinderTypes (o : Options) : Bool := o.get pp.piBinderTypes.name pp.piBinderTypes.defValue
def getPPLetVarTypes (o : Options) : Bool := o.get pp.letVarTypes.name (getPPAll o)
def getPPNumericTypes (o : Options) : Bool := o.get pp.numericTypes.name pp.numericTypes.defValue
def getPPNatLit (o : Options) : Bool := o.get pp.natLit.name (getPPNumericTypes o && !getPPAll o)
def getPPCoercions (o : Options) : Bool := o.get pp.coercions.name (!getPPAll o)
def getPPCoercionsTypes (o : Options) : Bool := o.get pp.coercions.types.name pp.coercions.types.defValue
def getPPExplicit (o : Options) : Bool := o.get pp.explicit.name (getPPAll o)
def getPPNotation (o : Options) : Bool := o.get pp.notation.name (!getPPAll o)
def getPPParens (o : Options) : Bool := o.get pp.parens.name pp.parens.defValue
def getPPUnicodeFun (o : Options) : Bool := o.get pp.unicode.fun.name false
def getPPMatch (o : Options) : Bool := o.get pp.match.name (!getPPAll o)
def getPPSorrySource (o : Options) : Bool := o.get pp.sorrySource.name pp.sorrySource.defValue
def getPPFieldNotation (o : Options) : Bool := o.get pp.fieldNotation.name (!getPPAll o)
def getPPFieldNotationGeneralized (o : Options) : Bool := o.get pp.fieldNotation.generalized.name pp.fieldNotation.generalized.defValue
def getPPStructureInstances (o : Options) : Bool := o.get pp.structureInstances.name (!getPPAll o)
def getPPStructureInstancesFlatten (o : Options) : Bool := o.get pp.structureInstances.flatten.name pp.structureInstances.flatten.defValue
def getPPStructureInstanceType (o : Options) : Bool := o.get pp.structureInstanceTypes.name (getPPAll o)
def getPPTagAppFns (o : Options) : Bool := o.get pp.tagAppFns.name (getPPAll o)
def getPPUniverses (o : Options) : Bool := o.get pp.universes.name (getPPAll o)
def getPPFullNames (o : Options) : Bool := o.get pp.fullNames.name (getPPAll o)
def getPPPrivateNames (o : Options) : Bool := o.get pp.privateNames.name (getPPAll o)
def getPPInstantiateMVars (o : Options) : Bool := o.get pp.instantiateMVars.name pp.instantiateMVars.defValue
def getPPMVars (o : Options) : Bool := o.get pp.mvars.name pp.mvars.defValue
def getPPMVarsAnonymous (o : Options) : Bool := o.get pp.mvars.anonymous.name (pp.mvars.anonymous.defValue && getPPMVars o)
def getPPMVarsLevels (o : Options) : Bool := o.get pp.mvars.levels.name (pp.mvars.levels.defValue && getPPMVarsAnonymous o)
def getPPMVarsWithType (o : Options) : Bool := o.get pp.mvars.withType.name pp.mvars.withType.defValue
def getPPMVarsDelayed (o : Options) : Bool := o.get pp.mvars.delayed.name (pp.mvars.delayed.defValue || getPPAll o)
def getPPBeta (o : Options) : Bool := o.get pp.beta.name pp.beta.defValue
def getPPSafeShadowing (o : Options) : Bool := o.get pp.safeShadowing.name pp.safeShadowing.defValue
def getPPProofs (o : Options) : Bool := o.get pp.proofs.name (pp.proofs.defValue || getPPAll o)
def getPPProofsWithType (o : Options) : Bool := o.get pp.proofs.withType.name pp.proofs.withType.defValue
def getPPProofsThreshold (o : Options) : Nat := o.get pp.proofs.threshold.name pp.proofs.threshold.defValue
def getPPMotivesPi (o : Options) : Bool := o.get pp.motives.pi.name pp.motives.pi.defValue
def getPPMotivesNonConst (o : Options) : Bool := o.get pp.motives.nonConst.name pp.motives.nonConst.defValue
def getPPMotivesAll (o : Options) : Bool := o.get pp.motives.all.name pp.motives.all.defValue
def getPPInstances (o : Options) : Bool := o.get pp.instances.name pp.instances.defValue
def getPPInstanceTypes (o : Options) : Bool := o.get pp.instanceTypes.name pp.instanceTypes.defValue
def getPPDeepTerms (o : Options) : Bool := o.get pp.deepTerms.name (pp.deepTerms.defValue || getPPAll o)
def getPPDeepTermsThreshold (o : Options) : Nat := o.get pp.deepTerms.threshold.name pp.deepTerms.threshold.defValue

end Lean
