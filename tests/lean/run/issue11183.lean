inductive extension where
| Ext_M
| Ext_A
| Ext_F
| Ext_D
| Ext_B
| Ext_V
| Ext_S
| Ext_U
| Ext_H
| Ext_Zic64b
| Ext_Zicbom
| Ext_Zicbop
| Ext_Zicboz
| Ext_Zicfilp
| Ext_Zicntr
| Ext_Zicond
| Ext_Zicsr
| Ext_Zifencei
| Ext_Zihintntl
| Ext_Zihintpause
| Ext_Zihpm
| Ext_Zimop
| Ext_Zmmul
| Ext_Zaamo
| Ext_Zabha
| Ext_Zacas
| Ext_Zalrsc
| Ext_Zawrs
| Ext_Za64rs
| Ext_Za128rs
| Ext_Zfa
| Ext_Zfbfmin
| Ext_Zfh
| Ext_Zfhmin
| Ext_Zfinx
| Ext_Zdinx
| Ext_Zca
| Ext_Zcb
| Ext_Zcd
| Ext_Zcf
| Ext_Zcmop
| Ext_C
| Ext_Zba
| Ext_Zbb
| Ext_Zbc
| Ext_Zbkb
| Ext_Zbkc
| Ext_Zbkx
| Ext_Zbs
| Ext_Zknd
| Ext_Zkne
| Ext_Zknh
| Ext_Zkr
| Ext_Zksed
| Ext_Zksh
| Ext_Zkt
| Ext_Zhinx
| Ext_Zhinxmin
| Ext_Zvl32b
| Ext_Zvl64b
| Ext_Zvl128b
| Ext_Zvl256b
| Ext_Zvl512b
| Ext_Zvl1024b
| Ext_Zve32f
| Ext_Zve32x
| Ext_Zve64d
| Ext_Zve64f
| Ext_Zve64x
| Ext_Zvfbfmin
| Ext_Zvfbfwma
| Ext_Zvfh
| Ext_Zvfhmin
| Ext_Zvbb
| Ext_Zvbc
| Ext_Zvkb
| Ext_Zvkg
| Ext_Zvkned
| Ext_Zvknha
| Ext_Zvknhb
| Ext_Zvksed
| Ext_Zvksh
| Ext_Zvkt
| Ext_Zvkn
| Ext_Zvknc
| Ext_Zvkng
| Ext_Zvks
| Ext_Zvksc
| Ext_Zvksg
| Ext_Sscofpmf
| Ext_Sstc
| Ext_Sstvecd
| Ext_Ssu64xl
| Ext_Svbare
| Ext_Sv32
| Ext_Sv39
| Ext_Sv48
| Ext_Sv57
| Ext_Svinval
| Ext_Svnapot
| Ext_Svpbmt
| Ext_Svrsw60t59b
| Ext_Smcntrpmf
deriving BEq, Inhabited, Repr

open extension

inductive Privilege where | User | VirtualUser | Supervisor | VirtualSupervisor | Machine
  deriving BEq, Inhabited, Repr

open Privilege

def hartSupports (_ext : extension) : Bool := false

@[simp]
def currentlyEnabled_measure (ext : extension) : Nat :=
  match ext with
  | Ext_Zicsr => 0
  | Ext_A => 1
  | Ext_B => 1
  | Ext_C => 1
  | Ext_D => 1
  | Ext_F => 1
  | Ext_M => 1
  | Ext_S => 1
  | Ext_Smcntrpmf => 3
  | Ext_Sscofpmf => 3
  | Ext_Svrsw60t59b => 3
  | Ext_Za128rs => 3
  | Ext_Za64rs => 3
  | Ext_Zabha => 3
  | Ext_Zacas => 3
  | Ext_Zcb => 3
  | Ext_Zcd => 3
  | Ext_Zcf => 3
  | Ext_Zcmop => 3
  | Ext_Zfhmin => 3
  | Ext_Zhinx => 3
  | Ext_Zicfilp => 3
  | Ext_Zve32x => 3
  | Ext_H => 4
  | Ext_Zhinxmin => 4
  | Ext_Zvbb => 4
  | Ext_Zve32f => 4
  | Ext_Zve64x => 4
  | Ext_Zvkg => 4
  | Ext_Zvkned => 4
  | Ext_Zvksed => 4
  | Ext_Zvknha => 4
  | Ext_Zvksh => 4
  | Ext_Zvbc => 5
  | Ext_Zve64f => 5
  | Ext_Zvfh => 5
  | Ext_Zvkb => 5
  | Ext_Zvknhb => 5
  | Ext_Zvfbfmin => 5
  | Ext_Zve64d => 6
  | Ext_Zvfhmin => 6
  | Ext_Zvfbfwma => 6
  | Ext_V => 7
  | _ => 2

-- If you delete exactly one line from the following `match`, the compilation will succeed.
mutual
def currentlyEnabled [Monad M] (merge_var : extension) : M Bool := do
  match merge_var with
  | Ext_Zic64b => (pure (hartSupports Ext_Zic64b))
  | Ext_Zkt => (pure (hartSupports Ext_Zkt))
  | Ext_Zvkt => (pure (hartSupports Ext_Zvkt))
  | Ext_Zvkn => (pure (hartSupports Ext_Zvkn))
  | Ext_Zvknc => (pure (hartSupports Ext_Zvknc))
  | Ext_Zvkng => (pure (hartSupports Ext_Zvkng))
  | Ext_Zvks => (pure (hartSupports Ext_Zvks))
  | Ext_Zvksc => (pure (hartSupports Ext_Zvksc))
  | Ext_Zvksg => (pure (hartSupports Ext_Zvksg))
  | Ext_Sstc => (pure (hartSupports Ext_Sstc))
  | Ext_U => (pure (hartSupports Ext_U && (← (currentlyEnabled Ext_Zicsr))))
  | Ext_S => pure false
  | Ext_Ssu64xl => (pure ((hartSupports Ext_Ssu64xl) && (← (currentlyEnabled Ext_S))))
  | Ext_Svbare => (currentlyEnabled Ext_S)
  | Ext_Sv32 => (pure ((hartSupports Ext_Sv32) && (← (currentlyEnabled Ext_S))))
  | Ext_Sv39 => (pure ((hartSupports Ext_Sv39) && (← (currentlyEnabled Ext_S))))
  | Ext_Sv48 => (pure ((hartSupports Ext_Sv48) && (← (currentlyEnabled Ext_S))))
  | Ext_Sv57 => (pure ((hartSupports Ext_Sv57) && (← (currentlyEnabled Ext_S))))
  | Ext_Sstvecd => (pure ((hartSupports Ext_Sstvecd) && (← (currentlyEnabled Ext_S))))
  | Ext_F => pure false
  | Ext_D => pure false
  | Ext_Zfinx => (pure ((hartSupports Ext_Zfinx) && (← (currentlyEnabled Ext_Zicsr))))
  | Ext_Zvl32b => (pure (hartSupports Ext_Zvl32b))
  | Ext_Zvl64b => (pure (hartSupports Ext_Zvl64b))
  | Ext_Zvl128b => (pure (hartSupports Ext_Zvl128b))
  | Ext_Zvl256b => (pure (hartSupports Ext_Zvl256b))
  | Ext_Zvl512b => (pure (hartSupports Ext_Zvl512b))
  | Ext_Zvl1024b => (pure (hartSupports Ext_Zvl1024b))
  | Ext_Zve32x => pure false
  | Ext_Zve32f =>
    (pure ((hartSupports Ext_Zve32f) && ((← (currentlyEnabled Ext_Zve32x)) && (← (currentlyEnabled
              Ext_F)))))
  | Ext_Zve64x =>
    (pure ((hartSupports Ext_Zve64x) && ((← (currentlyEnabled Ext_Zvl64b)) && (← (currentlyEnabled
              Ext_Zve32x)))))
  | Ext_Zve64f =>
    (pure ((hartSupports Ext_Zve64f) && ((← (currentlyEnabled Ext_Zve64x)) && (← (currentlyEnabled
              Ext_Zve32f)))))
  | Ext_Zve64d =>
    (pure ((hartSupports Ext_Zve64d) && ((← (currentlyEnabled Ext_Zve64f)) && (← (currentlyEnabled
              Ext_D)))))
  | Ext_V =>
    (pure ((hartSupports Ext_V)
      && ((← (currentlyEnabled Ext_Zvl128b)) && (← (currentlyEnabled Ext_Zve64d)))))
  | Ext_Zvfh =>
    (pure ((hartSupports Ext_Zvfh) && ((← (currentlyEnabled Ext_Zve32f)) && (← (currentlyEnabled
              Ext_Zfhmin)))))
  | Ext_Zvfhmin =>
    (pure (((hartSupports Ext_Zvfhmin) && (← (currentlyEnabled Ext_Zve32f))) || (← (currentlyEnabled
            Ext_Zvfh))))
  | Ext_Smcntrpmf => (pure ((hartSupports Ext_Smcntrpmf) && (← (currentlyEnabled Ext_Zicntr))))
  | Ext_Zicfilp =>
    (pure ((← (currentlyEnabled Ext_Zicsr))
      && ((hartSupports Ext_Zicfilp)
      && (← (get_xLPE (← return User))))))
  | Ext_Svnapot => (pure false)
  | Ext_Svpbmt => (pure false)
  | Ext_Svrsw60t59b => (pure ((hartSupports Ext_Svrsw60t59b) && (← (currentlyEnabled Ext_Sv39))))
  | Ext_C => (pure ((hartSupports Ext_C)))
  | Ext_Zca =>
    (pure ((hartSupports Ext_Zca) && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))
  | Ext_Zfh => (pure ((hartSupports Ext_Zfh) && (← (currentlyEnabled Ext_F))))
  | Ext_Zfhmin =>
    (pure (((hartSupports Ext_Zfhmin) && (← (currentlyEnabled Ext_F))) || (← (currentlyEnabled Ext_Zfh))))
  | Ext_Zcf =>
    (pure ((hartSupports Ext_Zcf)
      && ((← (currentlyEnabled Ext_F))
      && ((← (currentlyEnabled Ext_Zca))
      && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))))
  | Ext_Zdinx => (pure ((hartSupports Ext_Zdinx)))
  | Ext_Zcd =>
    (pure ((hartSupports Ext_Zcd) && ((← (currentlyEnabled Ext_D)) && ((← (currentlyEnabled
                Ext_Zca)) && ((← (currentlyEnabled Ext_C)) || (not (hartSupports Ext_C)))))))
  | Ext_Zhinx => (pure ((hartSupports Ext_Zhinx) && (← (currentlyEnabled Ext_Zfinx))))
  | Ext_Zhinxmin =>
    (pure (((hartSupports Ext_Zhinxmin) && (← (currentlyEnabled Ext_Zfinx))) || (← (currentlyEnabled
            Ext_Zhinx))))
  | Ext_Zfa => (pure ((hartSupports Ext_Zfa) && (← (currentlyEnabled Ext_F))))
  | Ext_Zknh => (pure (hartSupports Ext_Zknh))
  | Ext_Zkne => (pure (hartSupports Ext_Zkne))
  | Ext_Zknd => (pure (hartSupports Ext_Zknd))
  | Ext_Zksh => (pure (hartSupports Ext_Zksh))
  | Ext_Zksed => (pure (hartSupports Ext_Zksed))
  | Ext_Zkr => (pure (hartSupports Ext_Zkr))
  | Ext_Zbkx => (pure (hartSupports Ext_Zbkx))
  | Ext_Zvbb => (pure ((hartSupports Ext_Zvbb) && (← (currentlyEnabled Ext_Zve32x))))
  | Ext_Zvkb =>
    (pure (((hartSupports Ext_Zvkb) && (← (currentlyEnabled Ext_Zve32x))) || (← (currentlyEnabled
            Ext_Zvbb))))
  | _ => pure false
termination_by currentlyEnabled_measure merge_var
def get_xLPE [Monad M] (p : Privilege) : M Bool := do
  match p with
  | Machine => pure false
  | Supervisor => pure false
  | User => currentlyEnabled Ext_S
  | VirtualSupervisor => pure false
  | VirtualUser => pure false
termination_by 2
end
