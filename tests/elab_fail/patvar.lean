-- set_option trace.Elab true
def myId : List α → List α
| List.nil => List.nil

def constNil : List α → List α
| List.nil => List.nil
| List.cons x y => List.nil

def failing1 : List α → List α
| [] => List.nil

def failing2 : List α → List α
| x => List.nil
| foo.bar => List.nil -- "invalid pattern variable"

def myId2 : List α → List α
| foo.bar => foo.bar
