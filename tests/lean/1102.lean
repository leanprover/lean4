class cls12 := (u12 : Unit)
class cls11 extends cls12 := (u11 : Unit)
class cls10 extends cls11 := (u10 : Unit)
class cls9 extends cls10 := (u9 : Unit)
class cls8 extends cls9 := (u8 : Unit)
class cls7 extends cls8 := (u7 : Unit)
class cls6 extends cls7 := (u6 : Unit)
class cls5 extends cls6 := (u5 : Unit)
class cls4 extends cls5 := (u4 : Unit)
class cls3 extends cls4 := (u3 : Unit)
class cls2 extends cls3 := (u2 : Unit)
class cls1 extends cls2 := (u1 : Unit)
class cls0 extends cls1 := (u0 : Unit)

class CommRing (n : Nat) extends cls0 := (ucr : Unit)
class Field (n) extends CommRing n := (uf : Unit)
class DVR (n) [CommRing n] := (udvr : Unit)

instance [c : CommRing n] : CommRing n.succ := { ucr := c.u12 }
instance [Field n] : DVR n.succ := ⟨()⟩

example [CommRing 0] : DVR 1 := by infer_instance -- should fail fast, instead hits maxHeartbeats
