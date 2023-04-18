import Lean.Linter.Util
import Lean.Elab.Command

namespace Lean.Linter

register_builtin_option linter.suspiciousUnexpanderPatterns : Bool := {
  defValue := true,
  descr := "enable the 'suspicious unexpander patterns' linter"
}

def getLinterSuspiciousUnexpanderPatterns (o : Options) : Bool := getLinterValue linter.suspiciousUnexpanderPatterns o

def suspiciousUnexpanderPatterns : Linter where
  run cmdStx := do
    unless getLinterSuspiciousUnexpanderPatterns (← getOptions) do
      return

    -- check `[app_unexpander _]` defs defined by pattern matching
    let `($[$_:docComment]? @[$[$attrs:attr],*] $(_vis)? def $_ : $_ $[| $pats => $_]*) := cmdStx | return

    unless attrs.any (· matches `(attr| app_unexpander $_)) do
      return

    for pat in pats do
      let patHead ← match pat with
        | `(`($patHead:ident $_args*)) => pure patHead
        | `(`($patHead:ident))         => pure patHead
        | _                            => continue

      logLint linter.suspiciousUnexpanderPatterns patHead
        "Unexpanders should match the function name against an antiquotation `$_` so as to be independent of the specific pretty printing of the name."

builtin_initialize addLinter suspiciousUnexpanderPatterns

end Lean.Linter
