# The user-widgets system

Proving is an inherently interactive task. Lots of mathematical objects that we use are visual in nature.
The user-widget system lets users associate React components with the Lean document which are then rendered in the Lean VSCode infoview.

There is nothing about the RPC calls presented here that make the user-widgets system
dependent on JavaScript. However the primary use case is the web-based infoview in VSCode.

## How to write your own user-widgets

You can write your own user-widgets using the `@[widgetSource]` attribute:

```lean
import Lean
open Lean Widget

@[widget]
def widget1 : UserWidgetDefinition := {
  name := "my fancy widget"
  javascript := "
  import * as React from 'react';
  export default function (props) {
    return React.createElement('p', {}, 'hello')
  }"
}
```

This JavaScript text must include `import * as React from "react"` in the imports and may not use JSX.
The default export of the sourcetext must be a React component whose props are an RPC encoding.
The React component may accept a props argument whose value will be determined for each particular widget instance (below).
Widget sources may import the `@lean4/infoview` package ([todo] publish on NPM) in order to use
components such as `InteractiveMessage` to display `MessageData` interactively.

## Using Lake to build your widgets

For larger projects, you can use Lake to create files that will be used as `widgetSource`.
To learn how to do this, please view the readme of the [WidgetsMinimal sample](https://github.com/leanprover/lean4-samples/tree/main/WidgetsMinimal) ([todo] merge sample).
