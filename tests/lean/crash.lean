import logic

section
hypothesis P : Prop.

theorem crash
         := assume H : P,
            have H' : ¬ P,
            from H,
            _.

end