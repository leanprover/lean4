import logic

section
hypothesis P : Prop.

definition crash
         := assume H : P,
            have H' : ¬ P,
            from H,
            _.

end
