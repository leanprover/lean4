universes l1 l2 l3
constants (f : Π (X Y U : Type) (x1 x2 : X) (y1 y2 : Y) (Hx : x1 = x2) (Hy : y1 = y2), U)
constants (X : Type.{l1}) (Y : Type.{l2}) (U : Type.{l3})
constants (x1 x2 : X) (y1 y2 : Y) (Hx1 Hx2 : x1 = x2) (Hy1 Hy2 : y1 = y2)

#abstract_expr 0 f X Y U
#abstract_expr 0 f X Y U x1
#abstract_expr 0 f X Y U x1 x2
#abstract_expr 0 f X Y U x1 x2 y1
#abstract_expr 0 f X Y U x1 x2 y1 y2
#abstract_expr 0 f X Y U x1 x2 y1 y2 Hx1
#abstract_expr 0 f X Y U x1 x2 y1 y2 Hx1 Hy1
#abstract_expr 0 f X Y U x1 x2 y1 y2 Hx2 Hy2

#abstract_expr 1 (f X Y U x1 x2 y1 y2), (f X Y U x1 x2 y1 y2 Hx2 Hy2)
#abstract_expr 1 (f X Y U x1 x2 y1 y2 Hx1 Hy1), (f X Y U x1 x2 y1 y2)

#abstract_expr 1 (f X Y U x1 x2 y1 y2 Hx1), (f X Y U x1 x2 y1 y2 Hx2)
#abstract_expr 1 (f X Y U x1 x2 y1 y2 Hx1 Hy1), (f X Y U x1 x2 y1 y2 Hx2 Hy2)
