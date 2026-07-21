/-!
Tests for the `internalModule` linter. The module name `IMLinterTest` matches a test-only entry
in `Lean.Linter.InternalModule.internalModulePrefixes`, so this module is considered internal
and the linter should flag every non-internal declaration in it.
-/

-- warns: a plain declaration is not internal
def leaky := 1

-- warns: "Internal" as a mere substring of a name component is not enough
def myInternalHelper := 2

-- no warning: private declarations are internal
private def privateHelper := 3

-- no warning: the `Lean` namespace is internal
def Lean.pkgTestHelper := 4

-- no warning: `Internal` is a component of the declaration name
def Internal.helper := 5

-- no warning: the `Internal` component may occur anywhere in the name
def Impl.Internal.deepHelper := 6
