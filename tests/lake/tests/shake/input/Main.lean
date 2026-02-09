module

public import Lib.A  -- used privately
public import Lib.B  -- unused
public import Lib.CSimp  -- used privately via `[csimp]` replacement

def myValue : Nat := valueA
def myCSimpedValue : Nat := valueC
