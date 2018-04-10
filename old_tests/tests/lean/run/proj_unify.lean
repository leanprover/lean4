open tactic

-- Unify  (prod.fst ?m) with (prod.fst (1,2))
example : true :=
by do
  type ← to_expr ``(nat × nat),
  m₁   ← mk_meta_var type,
  t₁   ← mk_app ``prod.fst [m₁],
  t₂   ← to_expr ``(prod.fst (1, 2)),
  unify t₁ t₂,
  constructor

-- Unify (prod.fst (?m, 2)) with (prod.fst (3, 1))
example : true :=
by do
  type ← to_expr ``(nat),
  m₁   ← mk_meta_var type,
  two  ← to_expr ``(2),
  mk   ← mk_app ``prod.mk [m₁, two],
  t₁   ← mk_app ``prod.fst [mk],
  t₂   ← to_expr ``(prod.fst (3, 1)),
  trace t₁, trace t₂,
  unify t₁ t₂,
  four ← to_expr ``(4),
  fail_if_success (unify m₁ four),
  three ← to_expr ``(3),
  unify m₁ three,
  constructor

-- Unify  (prod.fst ?m) with (id (prod.fst (1,2)))
example : true :=
by do
  type ← to_expr ``(nat × nat),
  m₁   ← mk_meta_var type,
  t₁   ← mk_app ``prod.fst [m₁],
  t₂   ← to_expr ``(id (prod.fst (1, 2))),
  unify t₁ t₂,
  constructor

-- Unify  (id (prod.fst ?m)) with (prod.fst (1,2))
example : true :=
by do
  type ← to_expr ``(nat × nat),
  m₁   ← mk_meta_var type,
  s    ← mk_app ``prod.fst [m₁],
  t₁   ← mk_app ``id [s],
  t₂   ← to_expr ``(id (prod.fst (1, 2))),
  unify t₁ t₂,
  constructor

-- Unify (prod.fst (?m, 2)) with (id (prod.fst (3, 1)))
example : true :=
by do
  type ← to_expr ``(nat),
  m₁   ← mk_meta_var type,
  two  ← to_expr ``(2),
  mk   ← mk_app ``prod.mk [m₁, two],
  t₁   ← mk_app ``prod.fst [mk],
  t₂   ← to_expr ``(id (prod.fst (3, 1))),
  trace t₁, trace t₂,
  unify t₁ t₂,
  four ← to_expr ``(4),
  fail_if_success (unify m₁ four),
  three ← to_expr ``(3),
  unify m₁ three,
  constructor
