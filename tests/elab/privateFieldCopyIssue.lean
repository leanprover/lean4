structure A where
  a : Nat
  protected b : Nat
  private c : Nat

structure B where
  a : Nat
  private d : Nat
  protected e : Nat

structure C extends A, B

#print A.b
#print A.c
#print C.d
#print C.e
