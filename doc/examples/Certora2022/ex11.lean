/- Structures -/

structure Point where
  x : Int := 0
  y : Int := 0
  deriving Repr

#eval Point.x (Point.mk 10 20)
-- 10

#eval { x := 10, y := 20 : Point }

def p : Point := { y := 20 }

#eval p.x
#eval p.y
#eval { p with x := 5 }
-- { x := 5, y := 20 }

structure Point3D extends Point where
  z : Int

