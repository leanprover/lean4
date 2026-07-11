module

/-!
Canonical browser UI wire ABI. Run `browser_demo/generate_ui_abi.py` after changing constants.
-/

namespace UiAbi

public def magic : UInt32 := 0x4c554931
public def version : UInt32 := 1
public def headerSize : UInt32 := 32
public def recordSize : UInt32 := 32

namespace Effect
public def createElement : UInt32 := 1
public def createText : UInt32 := 2
public def setText : UInt32 := 3
public def remove : UInt32 := 4
public def setClass : UInt32 := 5
public def setHandler : UInt32 := 6
end Effect

namespace Handler
public def none : UInt32 := 0
public def intro : UInt32 := 1
public def constructor : UInt32 := 2
public def cases : UInt32 := 3
public def undo : UInt32 := 4
public def reset : UInt32 := 5
public def exactBase : UInt32 := 0x100
public def exact (i : UInt32) : UInt32 := exactBase + i
end Handler

end UiAbi
