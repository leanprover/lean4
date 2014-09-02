-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad

import general_notation

definition Prop [inline] := Type.{0}


-- implication
-- -----------

abbreviation imp (a b : Prop) : Prop := a → b


-- true and false
-- --------------

inductive false : Prop

theorem false_elim {c : Prop} (H : false) : c :=
false_rec c H

inductive true : Prop :=
trivial : true

abbreviation not (a : Prop) := a → false
prefix `¬` := not


-- not
-- ---

theorem not_intro {a : Prop} (H : a → false) : ¬a := H

theorem not_elim {a : Prop} (H1 : ¬a) (H2 : a) : false := H1 H2

theorem absurd {a : Prop} {b : Prop} (H1 : a) (H2 : ¬a) : b :=
false_elim (H2 H1)

theorem not_not_intro {a : Prop} (Ha : a) : ¬¬a :=
assume Hna : ¬a, absurd Ha Hna

theorem mt {a b : Prop} (H1 : a → b) (H2 : ¬b) : ¬a :=
assume Ha : a, absurd (H1 Ha) H2

theorem not_false_trivial : ¬false :=
assume H : false, H

theorem not_implies_left {a b : Prop} (H : ¬(a → b)) : ¬¬a :=
assume Hna : ¬a, absurd (assume Ha : a, absurd Ha Hna) H

theorem not_implies_right {a b : Prop} (H : ¬(a → b)) : ¬b :=
assume Hb : b, absurd (assume Ha : a, Hb) H
