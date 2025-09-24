-- Hovering on `match` displays the type
example :=
  match true with
  --^ textDocument/hover
  | true => true
  | false => false
