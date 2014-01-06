setoption pp::implicit true.
setoption pp::colors   false.
variable N : Type.

check
fun (a : N) (f : N -> N) (H : f a == a),
let calc1 : f a == a := substp (fun x : N, f a == _) (refl (f a)) H
in  calc1.