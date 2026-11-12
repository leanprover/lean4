class cls12 where (u12 : Unit)
class cls11 extends cls12 where (u11 : Unit)
class cls10 extends cls11 where (u10 : Unit)
class cls9 extends cls10 where (u9 : Unit)
class cls8 extends cls9 where (u8 : Unit)
class cls7 extends cls8 where (u7 : Unit)
class cls6 extends cls7 where (u6 : Unit)
class cls5 extends cls6 where (u5 : Unit)
class cls4 extends cls5 where (u4 : Unit)
class cls3 extends cls4 where (u3 : Unit)
class cls2 extends cls3 where (u2 : Unit)
class cls1 extends cls2 where (u1 : Unit)
class cls0 extends cls1 where (u0 : Unit)

class CommRing (n : semiOutParam Nat) extends cls0 where (ucr : Unit)
class Field (n : semiOutParam Nat) extends CommRing n where (uf : Unit)
class DVR (n : semiOutParam Nat) [CommRing n] where (udvr : Unit)

instance [c : CommRing n] : CommRing n.succ := { ucr := c.u12 }
instance [Field n] : DVR n.succ := ⟨()⟩

example [CommRing 0] : DVR 1 := by infer_instance -- should fail fast, instead hits maxHeartbeats
