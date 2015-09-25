import homotopy.circle
open circle

definition f (x : S¹) : bool := circle.rec_on x _ _
