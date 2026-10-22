module

public import Dependency

/-! Local deprecations, including deprecations of upstream argument names and syntax. -/

public section

@[deprecated "old local name" (since := "2000-01-02")]
def ownOld : Nat := 1

deprecated_syntax Dep.upstreamTerm "locally deprecated syntax" (since := "2000-01-02")
attribute [deprecated_arg old new (since := "2000-01-02")] Dep.upstreamFunction

@[deprecated "old local option" (since := "2000-01-02")]
meta register_option ownOldOption : Bool := { defValue := false }
