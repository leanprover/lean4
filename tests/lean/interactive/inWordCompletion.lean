prelude

def gfxabc (x : Nat) := x
def gfxacc (x : Nat) := x
def gfxadc (x : Nat) := x
def gfxbbc (x : Nat) := x
#check gfxabc
         --^ textDocument/completion

def Boo.gfxabc (x : Nat) := x
def Boo.gfxacc (x : Nat) := x
def Boo.gfxadc (x : Nat) := x
def Boo.gfxbbc (x : Nat) := x

#check Boo.gfxabc
             --^ textDocument/completion
