abbrev Value := BitVec 32

def Env := String → Value

namespace Env

def set (x : String) (v : Value) (ρ : Env) : Env :=
  fun y => if x = y then v else ρ y

def get (x : String) (ρ : Env) : Value :=
  ρ x

def init (i : Value) : Env := fun _ => i

end Env

@[simp] theorem Env.get_init : (Env.init v).get x = v := by rfl

@[simp] theorem Env.get_set_same {ρ : Env} : (ρ.set x v).get x = v := by
  simp [get, set]

@[simp] theorem Env.get_set_different {ρ : Env} : x ≠ y → (ρ.set x v).get y = ρ.get y := by
  intro; simp [get, set, *]

example : (((Env.init 0).set "x" 1).set "y" 2).get "y" = 2 := by
  simp

example : (((Env.init 0).set "x" 1).set "y" 2).get "x" = 1 := by
  simp

example : (((Env.init 0).set "x" 1).set "y" 2).get "z" = 0 := by
  simp

example : "hello" ≠ "foo" := by
  simp

example : "hello" != "foo" := by
  simp

example : "hello" == "hello" := by
  simp

example : "hello" == "foo" → False := by
  simp

example : "hello" = "foo" → False := by
  simp [-String.reduceEq]
  guard_target =ₛ ¬ "hello" = "foo"
  simp

example : "hello" ≤ "hellz" := by simp
example : "hello" < "hellz" := by simp
example : "hellz" > "hello" := by simp
example : "hellz" ≥ "hello" := by simp
example : "abcd" > "abc" := by simp

example : 'b' > 'a' := by simp
example : 'a' ≥ 'a' := by simp
example : 'a' < 'b' := by simp
example : 'a' ≤ 'a' := by simp
