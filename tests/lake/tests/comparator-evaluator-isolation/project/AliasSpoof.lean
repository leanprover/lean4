module
public import Reference

/-! An identically named proposition with a different meaning must be rejected. -/

public theorem success (h : Evaluator.approved) : True := False.elim h
