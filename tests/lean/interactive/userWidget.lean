import Lean
open Lean Widget

@[widget]
def widget1 : UserWidgetDefinition := {
  name := "my fancy widget"
  javascript:= "
  import * as React from 'react';
  export default function (props) {
    return React.createElement('p', {}, 'hello')
  }"
}

#widget widget1 (Json.mkObj [])
  --^ widgets
