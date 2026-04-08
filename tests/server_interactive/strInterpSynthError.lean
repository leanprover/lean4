/-!
# String interpolation synthesis diagnostic spans

The spans for type-class synthesis errors in interpolated strings to be localized to the
interpolants at which synthesis failure occurs.
-/

structure Foo where
structure Bar where

def foo := Foo.mk
def bar := Bar.mk

instance : ToString Foo := ⟨fun _ => "foo"⟩

example := s!"a {foo} b {bar} c"
            --^ collectDiagnostics
               --^ collectDiagnostics
                       --^ collectDiagnostics

example := s!"{bar} a"
            --^ collectDiagnostics
             --^ collectDiagnostics
                  --^ collectDiagnostics


example := s!"a {bar}"
            --^ collectDiagnostics
               --^ collectDiagnostics
                  --^ collectDiagnostics
