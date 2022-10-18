@[specialize] unsafe partial def umapAux {α β : Type} (f : α → β) : Nat → Array NonScalar → Array NonScalar
| i, a =>
  if h : i < a.size then
     let a                := dbgTraceIfShared "array" a;
     let idx : Fin a.size := ⟨i, h⟩;
     let v   : NonScalar  := a.get idx;
     let a                := a.set idx (arbitrary _);
     let newV             := f (unsafeCast v);
     umapAux (i+1) (a.set idx (unsafeCast newV))
  else
     a

@[inline] unsafe partial def umap {α β : Type} (f : α → β) (as : Array α) : Array β :=
unsafeCast (umapAux f 0 (unsafeCast as))

@[implemented_by umap] def map {α β : Type} (f : α → β) (as : Array α) : Array β :=
as.foldl (fun bs a => bs.push (f a)) (Array.mkEmpty as.size)

set_option compiler.extract_closed false
-- set_option trace.compiler.ir.result true

def tst1 : Array String :=
map (fun x => "val: " ++ toString x) #[1, 2, 3]

#eval tst1

def tst2 : Array String :=
let xs := #[1, 2, 3];
map (fun x => "val1: " ++ toString x) xs
++
map (fun x => "val2: " ++ toString x) xs

#eval tst2
