open nat
section
  parameter (X : Type)
  definition A {n : ℕ} : Type := X
  definition B : Type := X
  variable {n : ℕ}
  #check @A n
  #check _root_.A nat
  #check _root_.A (X × B)
  #check @_root_.A (X × B) 10
  #check @_root_.A (_root_.B (@_root_.A X n)) n
  #check @_root_.A (@_root_.B (@_root_.A nat n)) n

  set_option pp.full_names true
  #check A
  #check _root_.A nat
  #check @_root_.A (X × B) 10
  #check @_root_.A (@_root_.B (@_root_.A X n)) n
  #check @_root_.A (@_root_.B (@_root_.A nat n)) n

  set_option pp.full_names false

  set_option pp.implicit true
  #check @A n
  #check @_root_.A nat 10
  #check @_root_.A X n
  set_option pp.full_names true
  #check @_root_.A X n
  #check @_root_.A B n

  set_option pp.full_names false
  #check @_root_.A X n
  #check @_root_.A B n
  #check @_root_.A (@_root_.B (@A n)) n
  #check @_root_.A (@_root_.B (@_root_.A X n)) n
  #check @_root_.A (@_root_.B (@_root_.A nat n)) n
  #check @A n
end
