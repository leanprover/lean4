def gfabc (x : Nat) := x
def gfacc (x : Nat) := x
def gfadc (x : Nat) := x
def gfbbc (x : Nat) := x

#check gfabc
        --^ textDocument/completion

def Boo.gfabc (x : Nat) := x
def Boo.gfacc (x : Nat) := x
def Boo.gfadc (x : Nat) := x
def Boo.gfbbc (x : Nat) := x

#check Boo.gfabc
            --^ textDocument/completion
