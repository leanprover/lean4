inductive RBColor where
  | red
  | black

inductive RBNode (α : Type u) where
  | nil
  | node (c : RBColor) (l : RBNode α) (v : α) (r : RBNode α)

namespace RBNode
open RBColor

inductive Balanced : RBNode α → RBColor → Nat → Prop where
  | protected nil : Balanced nil black 0
  | protected red : Balanced x black n → Balanced y black n → Balanced (node red x v y) red n
  | protected black : Balanced x c₁ n → Balanced y c₂ n → Balanced (node black x v y) black (n + 1)

@[inline] def balance1 : RBNode α → α → RBNode α → RBNode α
  | node red (node red a x b) y c, z, d
  | node red a x (node red b y c), z, d => node red (node black a x b) y (node black c z d)
  | a,                             x, b => node black a x b

@[inline] def balance2 : RBNode α → α → RBNode α → RBNode α
  | a, x, node red (node red b y c) z d
  | a, x, node red b y (node red c z d) => node red (node black a x b) y (node black c z d)
  | a, x, b                             => node black a x b

theorem balance1_eq {l : RBNode α} {v : α} {r : RBNode α}
    (hl : l.Balanced c n) : balance1 l v r = node black l v r := by
  unfold balance1; split <;> first | rfl | exact nomatch hl

@[inline] def isBlack : RBNode α → RBColor
  | node c .. => c
  | _         => red

def setRed : RBNode α → RBNode α
  | node _ a v b => node red a v b
  | nil          => nil

def balLeft (l : RBNode α) (v : α) (r : RBNode α) : RBNode α :=
  match l with
  | node red a x b                    => node red (node black a x b) v r
  | l => match r with
    | node black a y b                => balance2 l v (node red a y b)
    | node red (node black a y b) z c => node red (node black l v a) y (balance2 b z (setRed c))
    | r                               => node red l v r -- unreachable

def balRight (l : RBNode α) (v : α) (r : RBNode α) : RBNode α :=
  match r with
  | node red b y c                    => node red l v (node black b y c)
  | r => match l with
    | node black a x b                => balance1 (node red a x b) v r
    | node red a x (node black b y c) => node red (balance1 (setRed a) x b) y (node black c v r)
    | l                               => node red l v r -- unreachable

@[simp] def size : RBNode α → Nat
  | nil => 0
  | node _ x _ y => x.size + y.size + 1

def append : RBNode α → RBNode α → RBNode α
  | nil, x | x, nil => x
  | node red a x b, node red c y d =>
    match append b c with
    | node red b' z c' => node red (node red a x b') z (node red c' y d)
    | bc               => node red a x (node red bc y d)
  | node black a x b, node black c y d =>
    match append b c with
    | node red b' z c' => node red (node black a x b') z (node black c' y d)
    | bc               => balLeft a x (node black bc y d)
  | a@(node black ..), node red b x c => node red (append a b) x c
  | node red a x b, c@(node black ..) => node red a x (append b c)
termination_by x y => x.size + y.size

def del (cut : α → Ordering) : RBNode α → RBNode α
  | nil          => nil
  | node _ a y b =>
    match cut y with
    | .lt => match a.isBlack with
      | black => balLeft (del cut a) y b
      | red => node red (del cut a) y b
    | .gt => match b.isBlack with
      | black => balRight a y (del cut b)
      | red => node red a y (del cut b)
    | .eq => append a b

inductive RedRed (p : Prop) : RBNode α → Nat → Prop where
  | balanced : Balanced t c n → RedRed p t n
  | redred : p → Balanced a c₁ n → Balanced b c₂ n → RedRed p (node red a x b) n

def DelProp (p : RBColor) (t : RBNode α) (n : Nat) : Prop :=
  match p with
  | black => ∃ n', n = n' + 1 ∧ RedRed True t n'
  | red => ∃ c, Balanced t c n

protected theorem RedRed.of_red : RedRed p (node red a x b) n →
    ∃ c₁ c₂, Balanced a c₁ n ∧ Balanced b c₂ n
  | .balanced (.red ha hb) | .redred _ ha hb => ⟨_, _, ha, hb⟩

protected theorem RedRed.balance2 {l : RBNode α} {v : α} {r : RBNode α}
    (hl : l.Balanced c n) (hr : r.RedRed p n) : ∃ c, (balance2 l v r).Balanced c (n + 1) := by
  unfold balance2; split
  · have .redred _ (.red ha hb) hc := hr; exact ⟨_, .red (.black hl ha) (.black hb hc)⟩
  · have .redred _ ha (.red hb hc) := hr; exact ⟨_, .red (.black hl ha) (.black hb hc)⟩
  · next H1 H2 => match hr with
    | .balanced hr => exact ⟨_, .black hl hr⟩
    | .redred _ (c₁ := black) (c₂ := black) ha hb => exact ⟨_, .black hl (.red ha hb)⟩
    | .redred _ (c₁ := red) (.red ..) _ => cases H1 _ _ _ _ _ rfl
    | .redred _ (c₂ := red) _ (.red ..) => cases H2 _ _ _ _ _ rfl

protected theorem RedRed.balance1 {l : RBNode α} {v : α} {r : RBNode α}
    (hl : l.RedRed p n) (hr : r.Balanced c n) : ∃ c, (balance1 l v r).Balanced c (n + 1) := by
  unfold balance1; split
  · have .redred _ (.red ha hb) hc := hl; exact ⟨_, .red (.black ha hb) (.black hc hr)⟩
  · have .redred _ ha (.red hb hc) := hl; exact ⟨_, .red (.black ha hb) (.black hc hr)⟩
  · next H1 H2 => match hl with
    | .balanced hl => exact ⟨_, .black hl hr⟩
    | .redred _ (c₁ := black) (c₂ := black) ha hb => exact ⟨_, .black (.red ha hb) hr⟩
    | .redred _ (c₁ := red) (.red ..) _ => cases H1 _ _ _ _ _ rfl
    | .redred _ (c₂ := red) _ (.red ..) => cases H2 _ _ _ _ _ rfl

protected theorem Balanced.balRight (hl : l.Balanced cl (n + 1)) (hr : r.RedRed True n) :
    (balRight l v r).RedRed (cl = red) (n + 1) := by
  unfold balRight; split
  · next b y c => exact
    let ⟨cb, cc, hb, hc⟩ := hr.of_red
    match cl with
    | red => .redred rfl hl (.black hb hc)
    | black => .balanced (.red hl (.black hb hc))
  · next H => exact match hr with
    | .redred .. => nomatch H _ _ _ rfl
    | .balanced hr => match hl with
      | .black hb hc =>
        let ⟨c, h⟩ := RedRed.balance1 (.redred trivial hb hc) hr; .balanced h
      | .red (.black ha hb) (.black hc hd) =>
        let ⟨c, h⟩ := RedRed.balance1 (.redred trivial ha hb) hc; .redred rfl h (.black hd hr)

protected theorem Balanced.balLeft (hl : l.RedRed True n) (hr : r.Balanced cr (n + 1)) :
    (balLeft l v r).RedRed (cr = red) (n + 1) := by
  unfold balLeft; split
  · next a x b => exact
    let ⟨ca, cb, ha, hb⟩ := hl.of_red
    match cr with
    | red => .redred rfl (.black ha hb) hr
    | black => .balanced (.red (.black ha hb) hr)
  · next H => exact match hl with
    | .redred .. => nomatch H _ _ _ rfl
    | .balanced hl => match hr with
      | .black ha hb =>
        let ⟨c, h⟩ := RedRed.balance2 hl (.redred trivial ha hb); .balanced h
      | .red (.black ha hb) (.black hc hd) =>
        let ⟨c, h⟩ := RedRed.balance2 hb (.redred trivial hc hd); .redred rfl (.black hl ha) h

protected theorem RedRed.imp (h : p → q) : RedRed p t n → RedRed q t n
  | .balanced h => .balanced h
  | .redred hp ha hb => .redred (h hp) ha hb

protected theorem RedRed.of_false (h : ¬p) : RedRed p t n → ∃ c, Balanced t c n
  | .balanced h => ⟨_, h⟩
  | .redred hp .. => nomatch h hp

protected theorem Balanced.append {l r : RBNode α}
    (hl : l.Balanced c₁ n) (hr : r.Balanced c₂ n) :
    (l.append r).RedRed (c₁ = black → c₂ ≠ black) n := by
  unfold append; split
  · exact .balanced hr
  · exact .balanced hl
  · next b c _ _ =>
    have .red ha hb := hl; have .red hc hd := hr
    have ⟨_, IH⟩ := (hb.append hc).of_false (· rfl rfl); split
    · next e =>
      have .red hb' hc' := e ▸ IH
      exact .redred (nofun) (.red ha hb') (.red hc' hd)
    · next bcc _ H =>
      match bcc, append b c, IH, H with
      | black, _, IH, _ => exact .redred (nofun) ha (.red IH hd)
      | red, _, .red .., H => cases H _ _ _ rfl
  · next b c _ _ =>
    have .black ha hb := hl; have .black hc hd := hr
    have IH := hb.append hc; split
    · next e => match e ▸ IH with
      | .balanced (.red hb' hc') | .redred _ hb' hc' =>
        exact .balanced (.red (.black ha hb') (.black hc' hd))
    · next H =>
      match append b c, IH, H with
      | bc, .balanced hbc, _ =>
        unfold balLeft; split
        · have .red ha' hb' := ha
          exact .balanced (.red (.black ha' hb') (.black hbc hd))
        · exact have ⟨c, h⟩ := RedRed.balance2 ha (.redred trivial hbc hd); .balanced h
      | _, .redred .., H => cases H _ _ _ rfl
  · have .red hc hd := hr; have IH := hl.append hc
    have .black ha hb := hl; have ⟨c, IH⟩ := IH.of_false (· rfl rfl)
    exact .redred (nofun) IH hd
  · have .red ha hb := hl; have IH := hb.append hr
    have .black hc hd := hr; have ⟨c, IH⟩ := IH.of_false (· rfl rfl)
    exact .redred (nofun) ha IH
termination_by l.size + r.size

protected theorem Balanced.del {t : RBNode α} (h : t.Balanced c n) :
    (t.del cut).DelProp t.isBlack n := by
  induction h with
  | nil => exact ⟨_, .nil⟩
  | @black a _ n b _ _ ha hb iha ihb =>
    refine ⟨_, rfl, ?_⟩
    unfold del; split
    · exact match a, n, iha with
      | .nil, _, ⟨c, ha⟩ | .node red .., _, ⟨c, ha⟩ => .redred ⟨⟩ ha hb
      | .node black .., _, ⟨n, rfl, ha⟩ => (hb.balLeft ha).imp fun _ => ⟨⟩
    · exact match b, n, ihb with
      | .nil, _, ⟨c, hb⟩ | .node .red .., _, ⟨c, hb⟩ => .redred ⟨⟩ ha hb
      | .node black .., _, ⟨n, rfl, hb⟩ => (ha.balRight hb).imp fun _ => ⟨⟩
    · exact (ha.append hb).imp fun _ => ⟨⟩
  | @red a n b _ ha hb iha ihb =>
    unfold del; split
    · exact match a, n, iha with
      | .nil, _, _ => ⟨_, .red ha hb⟩
      | .node black .., _, ⟨n, rfl, ha⟩ => (hb.balLeft ha).of_false nofun
    · exact match b, n, ihb with
      | .nil, _, _ => ⟨_, .red ha hb⟩
      | .node black .., _, ⟨n, rfl, hb⟩ => (ha.balRight hb).of_false nofun
    · exact (ha.append hb).of_false (· rfl rfl)
