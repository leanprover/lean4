/-!
Check that the compiler correctly deals with `Float` in various situations.
-/

-- If the output of `trace.Compiler.result` turns out to be too unstable, we'll have to
-- assert this some other way.

set_option trace.Compiler.result true

namespace F

/--
trace: [Compiler.result] size: 1
    def F.f x.1 : UInt64 :=
      let toModel.2 := Float.toModel x.1;
      return toModel.2
[Compiler.result] size: 4
    def F.f._boxed x.1 : obj :=
      let x.10.boxed := unbox x.1;
      dec[ref] x.1;
      let res := F.f x.10.boxed;
      let r := box res;
      return r
-/
#guard_msgs in
def f : Float → UInt64
  | ⟨model⟩ => model.toBits

/--
trace: [Compiler.result] size: 1
    def F.g x.1 : Float :=
      let _x.2 := Float.ofModel x.1;
      return _x.2
[Compiler.result] size: 4
    def F.g._boxed x.1 : obj :=
      let x.4.boxed := unbox x.1;
      dec[ref] x.1;
      let res := F.g x.4.boxed;
      let r := box res;
      return r
-/
#guard_msgs in
def g : Float.Model → Float
  | a => ⟨a⟩

structure Foo where
  foo : Float

/--
trace: [Compiler.result] size: 0
    def F.h x.1 : Float :=
      return x.1
[Compiler.result] size: 4
    def F.h._boxed x.1 : obj :=
      let x.4.boxed := unbox x.1;
      dec[ref] x.1;
      let res := F.h x.4.boxed;
      let r := box res;
      return r
-/
#guard_msgs in
def h : Float → Foo
  | a => ⟨a⟩

end F

namespace F32

/--
trace: [Compiler.result] size: 1
    def F32.f x.1 : UInt32 :=
      let toModel.2 := Float32.toModel x.1;
      return toModel.2
[Compiler.result] size: 4
    def F32.f._boxed x.1 : tobj :=
      let x.10.boxed := unbox x.1;
      dec[ref] x.1;
      let res := F32.f x.10.boxed;
      let r := box res;
      return r
-/
#guard_msgs in
def f : Float32 → UInt32
  | ⟨model⟩ => model.toBits

/--
trace: [Compiler.result] size: 1
    def F32.g x.1 : Float32 :=
      let _x.2 := Float32.ofModel x.1;
      return _x.2
[Compiler.result] size: 4
    def F32.g._boxed x.1 : obj :=
      let x.4.boxed := unbox x.1;
      dec x.1;
      let res := F32.g x.4.boxed;
      let r := box res;
      return r
-/
#guard_msgs in
def g : Float32.Model → Float32
  | a => ⟨a⟩

structure Foo where
  foo : Float32

/--
trace: [Compiler.result] size: 0
    def F32.h x.1 : Float32 :=
      return x.1
[Compiler.result] size: 4
    def F32.h._boxed x.1 : obj :=
      let x.4.boxed := unbox x.1;
      dec[ref] x.1;
      let res := F32.h x.4.boxed;
      let r := box res;
      return r
-/
#guard_msgs in
def h : Float32 → Foo
  | a => ⟨a⟩

end F32
