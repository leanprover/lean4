structure Map (α β : Type) where
  map    : Type
  mk     : map
  insert : map → α → β → map
