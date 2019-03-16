@[noinline]
def h (x : nat) : uint32 :=
uint32.of_nat x

def f (x y : uint32) : uint32 :=
let a1 : uint32 := 128 * 100 - 100 in
let v  : nat := 10 + x.to_nat in
let a2 : uint32 := x + a1 in
let a3 : uint32 := 10 in
y + a2 + h v + a3

def g : uint32 → uint32 → uint32 | x y :=
if x = 0 then y else g (x-1) (y+2)

def foo : uint8 :=
let x : uint8 := 100 in
x + x + x

def main : io uint32 :=
io.println (to_string (f 10 20)) *>
io.println (to_string (f 0 0)) *>
io.println (to_string (g 3 5)) *>
io.println (to_string (g 0 6)) *>
io.println (to_string foo) *>
pure 0
