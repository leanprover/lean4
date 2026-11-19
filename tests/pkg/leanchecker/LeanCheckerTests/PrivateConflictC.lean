module

prelude
public import Init.Core
import LeanCheckerTests.PrivateConflictA2
import LeanCheckerTests.PrivateConflictB2

public theorem all  : True ∧ True := .intro thm1' thm2'
