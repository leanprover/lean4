def foo := 3
def bar := 4

def ex1  (heq : foo = bar) (P : Nat → Prop) (h : P foo)         := heq ▸ h
#check ex1
def ex2  (heq : foo = bar) (P : Nat → Prop) (h : P foo) : P 4   := heq ▸ h -- error
def ex3  (heq : foo = bar) (P : Nat → Prop) (h : P foo) : P bar := heq ▸ h
def ex4  (heq : foo = bar) (P : Nat → Prop) (h : P 3)           := heq ▸ h -- error
def ex5  (heq : foo = bar) (P : Nat → Prop) (h : P 3)   : P 4   := heq ▸ h -- error
def ex6  (heq : foo = bar) (P : Nat → Prop) (h : P 3)   : P bar := heq ▸ h

def ex7  (heq : bar = foo) (P : Nat → Prop) (h : P foo)         := heq ▸ h
#check ex7
def ex8  (heq : bar = foo) (P : Nat → Prop) (h : P foo) : P 4   := heq ▸ h -- error
def ex9  (heq : bar = foo) (P : Nat → Prop) (h : P foo) : P bar := heq ▸ h
def ex10 (heq : bar = foo) (P : Nat → Prop) (h : P 3)           := heq ▸ h -- error
def ex11 (heq : bar = foo) (P : Nat → Prop) (h : P 3)   : P 4   := heq ▸ h -- error
def ex12 (heq : bar = foo) (P : Nat → Prop) (h : P 3)   : P bar := heq ▸ h
