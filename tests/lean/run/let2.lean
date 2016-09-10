set_option new_elaborator true
definition b :=
      let a := true ∧ true,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a,
          a := a ∧ a in
       a

check b
