/-- Types implementing this can displayed in HTML, for example as a SVG.
This is non-interactive -- for interactivity, see widgets. -/
-- should suffice for Dynkin
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Dynkin.20diagrams
class ToHtmlFormat (α : Type u) where
  toHtmlFormat : α → String -- TODO HTML
