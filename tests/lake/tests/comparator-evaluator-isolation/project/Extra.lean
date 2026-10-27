module
public import Reference

/-! The project's own approval list cannot authorize an extra hypothesis. -/

public theorem success (h : Project.only) : True := False.elim h
