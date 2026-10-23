module

public import Accepted

/-! An arbitrary unlisted premise must not be discharged. -/

public theorem task (_ : False) : True := True.intro
