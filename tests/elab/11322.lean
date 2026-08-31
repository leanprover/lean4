/-!
This is a regression test for https://github.com/leanprover/lean4/issues/11322
-/

abbrev Prop1 (U : Type) := U -> Prop

structure Object where
    type : Type
    isAllowedProp1 : Prop1 type -> Prop

abbrev Object.prop1 (U : Object) := Subtype U.isAllowedProp1

structure Hom (A B : Object) where
    mapType : A.type -> B.type
    mapProp1 : A.prop1 -> B.prop1
    mapProp1_valid (p : A.prop1) (x : A.type) : (mapProp1 p).val (mapType x) = p.val x

def Hom.mapType' {U V : Object} (h : Hom U V) : U.type -> V.type := h.mapType
