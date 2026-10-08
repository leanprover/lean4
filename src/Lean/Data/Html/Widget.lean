/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
module

prelude
public import Lean.Data.Html.Basic
import Lean.Data.Html.Printer
import Lean.Widget.UserWidget
meta import Lean.Widget.UserWidget
public import Lean.Message

set_option doc.verso true

public section

namespace Lean.Html

/-- Renders an HTML string. Expects props {lit}`{ html : string }`. -/
@[builtin_widget_module]
def htmlWidget : Widget.Module where
  javascript := "
import { createElement } from 'react'

export default function ({ html }) {
  return createElement('span', {
    style: { display: 'contents' },
    dangerouslySetInnerHTML: { __html: html }
  })
}"

/-- A message that displays the given HTML as a widget,
falling back to the HTML source in plaintext contexts. -/
def toMessageData (h : Html) : MessageData :=
  let s := h.render
  .ofWidget {
    id := ``htmlWidget
    javascriptHash := htmlWidget.javascriptHash
    props := return json% { html: $(s) }
  } s

instance : ToMessageData Html := ⟨toMessageData⟩

end Lean.Html
