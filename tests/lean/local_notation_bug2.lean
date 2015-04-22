open nat
section
parameters (b : ℕ)
definition add_b (n : ℕ) := n + b
local postfix `%`:max := add_b
end
eval 5% -- Error, unexpected token
