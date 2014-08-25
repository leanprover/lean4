import logic
using tactic

theorem T {a b c d : Prop} (H : a) (H : b) (H : c) (H : d) : a
:= by state; assumption