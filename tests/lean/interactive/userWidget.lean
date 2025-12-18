import Lean
open Lean

@[widget_module]
def helloWidget : Widget.Module where
  javascript := "
    import * as React from 'react';
    export default function(props) {
      const name = props.name || 'world'
      return React.createElement('p', {}, name + '!')
    }"

#widget helloWidget
  --^ widgets

structure HelloWidgetProps where
  name? : Option String := none
  deriving Server.RpcEncodable

#widget helloWidget with { name? := "lean" : HelloWidgetProps }
  --^ widgets

show_panel_widgets [helloWidget with { name? := "global" : HelloWidgetProps }]

section
show_panel_widgets [local helloWidget with { name? := "local" : HelloWidgetProps }]
--^ widgets
end

namespace Foo
show_panel_widgets [scoped helloWidget with { name? := "scoped" : HelloWidgetProps }]
end Foo

open scoped Foo
--^ widgets

show_panel_widgets [-helloWidget]
--^ widgets
