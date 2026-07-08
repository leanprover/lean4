variable (p q : Prop)
variable (b c d : Bool)
variable (u v w : Prop) [Decidable u] [Decidable v] [Decidable w]

-- Specific regressions found when introducing Boolean normalization
#check_simp (b != !c) = false ~> b ≠ c
#check_simp ¬(u → v ∨ w) ~> u ∧ ¬v ∧ ¬w
#check_simp decide (u ∧ (v → False)) ~> decide u && !decide v
#check_simp decide (cond true b c = true) ~> b
#check_simp decide (ite u b c = true) ~> ite u b c
#check_simp true ≠ (b || c) ~> b = false ∧ c = false
#check_simp ¬((!b = false) ∧ (c = false)) ~> b = true → c = true
#check_simp (((!b) && c) ≠ false) ~> b = false ∧ c = true
#check_simp (cond b false c ≠ false) ~> b = false ∧ c
#check_simp (b && c) = false ~> b → c = false
#check_simp (b && c) ≠   false ~> b ∧ c
#check_simp decide (u → False) ~> !decide u
#check_simp decide (¬u) ~> !decide u
#check_simp (b = true) ≠ (c = false) ~> b = c
#check_simp (b != c) != (false != d) ~> b != (c != d)
#check_simp (b == false) ≠ (c != d) ~> b = (c != d)
#check_simp (b = true) ≠ (c = false) ~> b = c
#check_simp ¬b = !c ~> b = c
#check_simp (b == c) = false ~> ¬(b = c)
#check_simp (true ≠ if u then b else c) ~> (if u then b = false else c = false)
#check_simp (u ∧ v → False) ~> u → v → False
#check_simp (u = (v ≠ w)) ~> (u ↔ ¬(v ↔ w))
#check_simp ((b = false) = (c = false)) ~> b = c
#check_simp True ≠ (c = false) ~> c = true
#check_simp u ∧ u ∧ v ~> u ∧ v
#check_simp b || (b || c) ~> b || c
#check_simp ((b ≠ c) : Bool) ~> !(decide (b = c))
#check_simp ((u ≠ v) : Bool) ~> !((u : Bool) == (v : Bool))
#check_simp decide (u → False) ~> !(decide u)
#check_simp decide (¬u) ~> !u
-- Specific regressions done

-- Round trip isomorphisms
#check_simp (decide (b : Prop)) ~> b
#check_simp ((u : Bool) : Prop) ~> u

/- # not -/

variable [Decidable u]

-- Ground
#check_simp (¬True) ~> False
#check_simp (¬true) ~> False
#check_simp (!True) ~> false
#check_simp (!true) ~> false

#check_simp (¬False) ~> True
#check_simp (!False) ~> true
#check_simp (¬false) ~> True
#check_simp (!false) ~> true

/- # Coercions and not -/

#check_simp ¬p !~>
#check_simp !b !~>

#check_simp (¬u : Prop) !~>
#check_simp (¬u : Bool) ~> !u
#check_simp (!u : Prop) ~> ¬u
#check_simp (!u : Bool) !~>
#check_simp (¬b : Prop) ~> b = false
#check_simp (¬b : Bool) ~> !b
#check_simp (!b : Prop) ~> b = false
#check_simp (!b : Bool) !~>

#check_simp (¬¬u) ~> u

/- # and -/

-- Validate coercions
#check_simp (u ∧  v : Prop) !~>
#check_simp (u ∧  v : Bool) ~> u && v
#check_simp (u && v : Prop) ~> u ∧  v
#check_simp (u && v : Bool) !~>
#check_simp (b ∧  c : Prop) !~>
#check_simp (b ∧  c : Bool) ~> b && c
#check_simp (b && c : Prop) ~> b ∧  c
#check_simp (b && c : Bool) !~>

-- Partial evaluation
#check_simp (True ∧  v : Prop) ~> v
#check_simp (True ∧  v : Bool) ~> (v : Bool)
#check_simp (True && v : Prop) ~> v
#check_simp (True && v : Bool) ~> (v : Bool)
#check_simp (true ∧  c : Prop) ~> (c : Prop)
#check_simp (true ∧  c : Bool) ~> c
#check_simp (true && c : Prop) ~> (c : Prop)
#check_simp (true && c : Bool) ~> c

#check_simp (u ∧  True : Prop) ~> u
#check_simp (u ∧  True : Bool) ~> (u : Bool)
#check_simp (u && True : Prop) ~> u
#check_simp (u && True : Bool) ~> (u : Bool)
#check_simp (b ∧  true : Prop) ~> (b : Prop)
#check_simp (b ∧  true : Bool) ~> b
#check_simp (b && true : Prop) ~> (b : Prop)
#check_simp (b && true : Bool) ~> b

#check_simp (False ∧  v : Prop) ~> False
#check_simp (False ∧  v : Bool) ~> false
#check_simp (False && v : Prop) ~> False
#check_simp (False && v : Bool) ~> false
#check_simp (false ∧  c : Prop) ~> False
#check_simp (false ∧  c : Bool) ~> false
#check_simp (false && c : Prop) ~> False
#check_simp (false && c : Bool) ~> false

#check_simp (u ∧  False : Prop) ~> False
#check_simp (u ∧  False : Bool) ~> false
#check_simp (u && False : Prop) ~> False
#check_simp (u && False : Bool) ~> false
#check_simp (b ∧  false : Prop) ~> False
#check_simp (b ∧  false : Bool) ~> false
#check_simp (b && false : Prop) ~> False
#check_simp (b && false : Bool) ~> false

-- Idempotence
#check_simp (u ∧  u) ~> u
#check_simp (u && u) ~> (u : Bool)
#check_simp (b ∧  b) ~> (b : Prop)
#check_simp (b && b) ~> b

-- Cancellation
#check_simp (u ∧ ¬u)  ~> False
#check_simp (¬u ∧ u)  ~> False
#check_simp (b && ¬b) ~> false
#check_simp (¬b && b) ~> false

-- Check we swap operators, but do apply deMorgan etc
#check_simp ¬(u ∧ v)  ~> u → ¬v
#check_simp decide (¬(u ∧ v))  ~> !u || !v
#check_simp !(u ∧ v)  ~> !u || !v
#check_simp ¬(b ∧ c)  ~> b → c = false
#check_simp !(b ∧ c)  ~> !b || !c
#check_simp ¬(u && v) ~> u → ¬ v
#check_simp ¬(b && c) ~> b = true → c = false
#check_simp !(u && v) ~> !u || !v
#check_simp !(b && c) ~> !b || !c
#check_simp ¬u ∧  ¬v !~>
#check_simp ¬b ∧  ¬c  ~> ((b = false) ∧ (c = false))
#check_simp ¬u && ¬v  ~> (!u && !v)
#check_simp ¬b && ¬c  ~> (!b && !c)

-- Some ternary test cases
#check_simp (u ∧ (v ∧ w) : Prop) !~>
#check_simp (u ∧ (v ∧ w) : Bool) ~> (u && (v && w))
#check_simp ((u ∧ v) ∧ w : Prop) !~>
#check_simp ((u ∧ v) ∧ w : Bool)  ~> ((u && v) && w)
#check_simp (b && (c && d) : Prop) ~> (b ∧ c ∧ d)
#check_simp (b && (c && d) : Bool) !~>
#check_simp ((b && c) && d : Prop)  ~> ((b ∧ c) ∧ d)
#check_simp ((b && c) && d : Bool) !~>

/- # or -/

-- Validate coercions
#check_simp p ∨ q !~>
#check_simp q ∨ p !~>
#check_simp (u ∨ v : Prop) !~>
#check_simp (u ∨ v : Bool)  ~> u || v
#check_simp (u || v : Prop) ~> u ∨  v
#check_simp (u || v : Bool) !~>
#check_simp (b ∨ c : Prop)  !~>
#check_simp (b ∨ c : Bool)  ~> b || c
#check_simp (b || c : Prop) ~> b ∨  c
#check_simp (b || c : Bool) !~>

-- Partial evaluation
#check_simp (True ∨ v : Prop)  ~> True
#check_simp (True ∨ v : Bool)  ~> true
#check_simp (True || v : Prop) ~> True
#check_simp (True || v : Bool) ~> true
#check_simp (true ∨  c : Prop) ~> True
#check_simp (true ∨  c : Bool) ~> true
#check_simp (true || c : Prop) ~> True
#check_simp (true || c : Bool) ~> true

#check_simp (u ∨  True : Prop) ~> True
#check_simp (u ∨  True : Bool) ~> true
#check_simp (u || True : Prop) ~> True
#check_simp (u || True : Bool) ~> true
#check_simp (b ∨  true : Prop) ~> True
#check_simp (b ∨  true : Bool) ~> true
#check_simp (b || true : Prop) ~> True
#check_simp (b || true : Bool) ~> true

#check_simp (False ∨ v : Prop)  ~> v
#check_simp (False ∨ v : Bool)  ~> (v : Bool)
#check_simp (False || v : Prop) ~> v
#check_simp (False || v : Bool) ~> (v : Bool)
#check_simp (false ∨ c : Prop)  ~> (c : Prop)
#check_simp (false ∨ c : Bool)  ~> c
#check_simp (false || c : Prop) ~> (c : Prop)
#check_simp (false || c : Bool) ~> c

#check_simp (u ∨ False : Prop)  ~> u
#check_simp (u ∨ False : Bool)  ~> (u : Bool)
#check_simp (u || False : Prop) ~> u
#check_simp (u || False : Bool) ~> (u : Bool)
#check_simp (b ∨ false : Prop)  ~> (b : Prop)
#check_simp (b ∨ false : Bool)  ~> b
#check_simp (b || false : Prop) ~> (b : Prop)
#check_simp (b || false : Bool) ~> b

-- Idempotence
#check_simp (u ∨ u)  ~> u
#check_simp (u || u) ~> (u : Bool)
#check_simp (b ∨  b) ~> (b : Prop)
#check_simp (b || b) ~> b

-- Complement
-- Note. We may want to revisit this.
--   Decidable excluded middle currently does not simplify.
#check_simp ( u ∨  ¬u) !~>
#check_simp (¬u ∨   u) !~>
#check_simp ( b || ¬b)  ~> true
#check_simp (¬b ||  b)  ~> true

-- Check we swap operators, but do apply deMorgan etc
#check_simp ¬(u ∨ v)  ~> ¬u ∧ ¬v
#check_simp !(u ∨ v)  ~> !u && !v
#check_simp ¬(b ∨ c)  ~> b = false ∧ c =false
#check_simp !(b ∨ c)  ~> !b && !c
#check_simp ¬(u || v) ~> ¬u ∧ ¬v
#check_simp ¬(b || c) ~> b = false ∧ c = false
#check_simp !(u || v) ~> !u && !v
#check_simp !(b || c) ~> !b && !c
#check_simp ¬u ∨  ¬v !~>
#check_simp (¬b) ∨ (¬c)  ~> b = false ∨ c = false
#check_simp ¬u || ¬v  ~> (!u || !v)
#check_simp ¬b || ¬c  ~> (!b || !c)

-- Some ternary test cases
#check_simp (u ∨ (v ∨ w) : Prop) !~>
#check_simp (u ∨ (v ∨ w) : Bool)   ~> (u || (v || w))
#check_simp ((u ∨ v) ∨ w : Prop) !~>
#check_simp ((u ∨ v) ∨ w : Bool)   ~> ((u || v) || w)
#check_simp (b || (c || d) : Prop) ~> (b ∨ c ∨ d)
#check_simp (b || (c || d) : Bool) !~>
#check_simp ((b || c) || d : Prop) ~> ((b ∨ c) ∨ d)
#check_simp ((b || c) || d : Bool) !~>

/- # and/or -/

-- We don't currently do automatic simplification across and/or/not
-- This tests for non-unexpected reductions.

#check_simp p ∧ (p ∨ q) !~>
#check_simp (p ∨ q) ∧ p !~>

#check_simp u ∧ (v ∨ w) !~>
#check_simp u ∨ (v ∧ w) !~>
#check_simp (v ∨ w) ∧ u !~>
#check_simp (v ∧ w) ∨ u !~>
#check_simp b && (c || d) !~>
#check_simp b || (c && d) !~>
#check_simp (c || d) && b !~>
#check_simp (c && d) || b !~>

/- # implication -/

#check_simp (b → c) !~>
#check_simp (u → v) !~>
#check_simp p → q !~>
#check_simp decide (u → ¬v)  ~> !u || !v

/- # iff -/

#check_simp (u = v : Prop) ~> u ↔ v
#check_simp (u = v : Bool) ~> u == v
#check_simp (u ↔ v : Prop) !~>
#check_simp (u ↔ v : Bool) ~> u == v
#check_simp (u == v : Prop) ~> u ↔ v
#check_simp (u == v : Bool) !~>

#check_simp (b = c : Prop) !~>
#check_simp (b = c : Bool) !~>
#check_simp (b ↔ c : Prop) ~> b = c
#check_simp (b ↔ c : Bool) ~> decide (b = c)
#check_simp (b == c : Prop) ~> b = c
#check_simp (b == c : Bool) !~>

-- Partial evaluation
#check_simp (True = v : Prop)  ~> v
#check_simp (True = v : Bool)  ~> (v : Bool)
#check_simp (True ↔ v : Prop)  ~> v
#check_simp (True ↔ v : Bool)  ~> (v : Bool)
#check_simp (True == v : Prop) ~> v
#check_simp (True == v : Bool) ~> (v : Bool)
#check_simp (true =  c : Prop) ~> c = true
#check_simp (true =  c : Bool) ~> c
#check_simp (true ↔  c : Prop) ~> c = true
#check_simp (true ↔  c : Bool) ~> c
#check_simp (true == c : Prop) ~> (c : Prop)
#check_simp (true == c : Bool) ~> c

#check_simp (v = True : Prop)  ~> v
#check_simp (v = True : Bool)  ~> (v : Bool)
#check_simp (v ↔ True : Prop)  ~> v
#check_simp (v ↔ True : Bool)  ~> (v : Bool)
#check_simp (v == True : Prop) ~> v
#check_simp (v == True : Bool) ~> (v : Bool)
#check_simp (c = true : Prop) !~>
#check_simp (c = true : Bool) ~> c
#check_simp (c ↔ true : Prop) ~> c = true
#check_simp (c ↔ true : Bool) ~> c
#check_simp (c == true : Prop) ~> c = true
#check_simp (c == true : Bool) ~> c

#check_simp (True = v : Prop)  ~> v
#check_simp (True = v : Bool)  ~> (v : Bool)
#check_simp (True ↔ v : Prop)  ~> v
#check_simp (True ↔ v : Bool)  ~> (v : Bool)
#check_simp (True == v : Prop) ~> v
#check_simp (True == v : Bool) ~> (v : Bool)
#check_simp (true =  c : Prop) ~> c = true
#check_simp (true =  c : Bool) ~> c
#check_simp (true ↔  c : Prop) ~> c = true
#check_simp (true ↔  c : Bool) ~> c
#check_simp (true == c : Prop) ~> (c : Prop)
#check_simp (true == c : Bool) ~> c

#check_simp (v = False : Prop)  ~> ¬v
#check_simp (v = False : Bool)  ~> !v
#check_simp (v ↔ False : Prop)  ~> ¬v
#check_simp (v ↔ False : Bool)  ~> !v
#check_simp (v == False : Prop) ~> ¬v
#check_simp (v == False : Bool) ~> !v
#check_simp (c = false : Prop) !~>
#check_simp (c = false : Bool) ~> !c
#check_simp (c ↔ false : Prop) ~> c = false
#check_simp (c ↔ false : Bool) ~> !c
#check_simp (c == false : Prop) ~> c = false
#check_simp (c == false : Bool) ~> !c

#check_simp (False = v : Prop)  ~> ¬v
#check_simp (False = v : Bool)  ~> !v
#check_simp (False ↔ v : Prop)  ~> ¬v
#check_simp (False ↔ v : Bool)  ~> !v
#check_simp (False == v : Prop) ~> ¬v
#check_simp (False == v : Bool) ~> !v
#check_simp (false =  c : Prop) ~> c = false
#check_simp (false =  c : Bool) ~> !c
#check_simp (false ↔  c : Prop) ~> c = false
#check_simp (false ↔  c : Bool) ~> !c
#check_simp (false == c : Prop) ~> c = false
#check_simp (false == c : Bool) ~> !c

-- Ternary (expand these)

#check_simp (u == (v =  w)) ~> u == (v == w)
#check_simp (u == (v == w)) !~>

/- # bne -/

#check_simp p ≠ q ~> ¬(p ↔ q)
#check_simp (b != c : Bool) !~>
#check_simp ¬(p = q) ~> ¬(p ↔ q)
#check_simp b ≠ c    ~> b ≠ c
#check_simp ¬(b = c) !~>
#check_simp ¬(b ↔ c) ~> ¬(b = c)
#check_simp (b != c : Prop) ~> b ≠ c
#check_simp u ≠ v    ~> ¬(u ↔ v)
#check_simp ¬(u = v) ~> ¬(u ↔ v)
#check_simp ¬(u ↔ v) !~>
#check_simp ((u:Bool) != v : Bool) !~>
#check_simp ((u:Bool) != v : Prop) ~> ¬(u ↔ v)

/- # equality and and/or interactions -/

#check_simp (u == (v ∨ w)) ~>  u == (v || w)
#check_simp (u == (v || w)) !~>
#check_simp ((u ∧ v) == w) ~> (u && v) == w

/- # ite/cond -/

#check_simp if b then c else d !~>
#check_simp if b then p else q !~>
#check_simp if u then p else q !~>
#check_simp if u then b else c !~>
#check_simp if u then u else q ~> ¬u → q
#check_simp if u then q else u ~> u ∧ q
#check_simp if u then q else q  ~> q
#check_simp cond b c d !~>
