def bndng (α : Type) : Type := string

inductive pterm : Type
| star : pterm -> pterm
| letrec : bndng pterm -> pterm

def weaken : pterm → pterm
| (pterm.star p) := pterm.star (weaken p)
| (pterm.letrec _) := pterm.letrec ""