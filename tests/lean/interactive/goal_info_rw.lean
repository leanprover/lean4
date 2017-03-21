example (p q r : Prop) (h₁ : p = q) (h₂ : q = r) : p = r :=
by rw [h₁,
       --^ "command": "info"
       -h₂,
     --^ "command": "info"
       -h₁
       --^ "command": "info"
    --^ "command": "info"
      ]
    --^ "command": "info"
