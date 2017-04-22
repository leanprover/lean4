open tactic

example : false :=
begin
  simp,
   --^ "command": "info"
  simp ,
    --^ "command": "info"
  simp [ ],
      --^ "command": "info"
  simp [d] ,
        --^ "command": "info"
  get_env
--^ "command": "info"
end
