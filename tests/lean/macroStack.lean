new_frontend

def f1 :=
if h:x then 1 else 0

set_option pp.macroStack true
def f2 :=
if h:(x > 0) then 1 else 0
