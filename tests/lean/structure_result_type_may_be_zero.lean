record Fun.{uA uB} (A : Type.{uA}) (B : Type.{uB}) : Type.{imax uA uB} := (item : Π(a : A), B)
