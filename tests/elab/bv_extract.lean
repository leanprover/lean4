import Std.Tactic.BVDecide

open BitVec

theorem bv_extract_1 (h : x = 1#64) : extractLsb' 32 32 x = 0#32 := by
  bv_decide

theorem bv_extract_2 (h : x = 1#64) : extractLsb' 0 32 x = 1#32 := by
  bv_decide

theorem bv_extract_3 (h : x = 1#64) : extractLsb 63 32 x = 0#32 := by
  bv_decide

theorem bv_extract_4 (h : x = 1#64) : extractLsb 31 0 x = 1#32 := by
  bv_decide

theorem bv_ofBool_1 (h : x = 1#64) : ofBool (x.getLsbD 0) = 1#1 := by
  bv_decide

theorem bv_ofBool_2 (h : x = 1#64) : ofBool (x.getLsbD 1) = 0#1 := by
  bv_decide

set_option maxHeartbeats 10000000000 in
theorem bv_ofBool_3 (h : x = 1#1) : ofBool x[0] = 1#1 := by
  bv_decide -native

theorem bv_ofBool_4 (h : x = 1#64) : ofBool x[1] = 0#1 := by
  bv_decide

/-
unexpected kernel projection term during structural definitional equality
  (match
        match h :
          (match
                    match h :
                      { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                        { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                    | some refs =>
                      if h : refs.size = 1 then
                        have refs := Vector.mk refs h;
                        some { refs := refs, hrefs := ⋯ }
                      else none
                    | none => none with
                  | some vec =>
                    { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                      cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                  | none =>
                    match
                      Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                        { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                    | { result := result, cache := cache } =>
                      { result := result,
                        cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).2.map.get?
            { w := 1, expr := Std.Tactic.BVDecide.BVExpr.const 1#1 } with
        | some refs =>
          if h : refs.size = 1 then
            have refs := Vector.mk refs h;
            some { refs := refs, hrefs := ⋯ }
          else none
        | none => none with
      | some vec =>
        {
          result :=
            ⟨{
                aig :=
                  (match
                          match h :
                            { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                              { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                          | some refs =>
                            if h : refs.size = 1 then
                              have refs := Vector.mk refs h;
                              some { refs := refs, hrefs := ⋯ }
                            else none
                          | none => none with
                        | some vec =>
                          { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                            cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                        | none =>
                          match
                            Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                              { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                          | { result := result, cache := cache } =>
                            { result := result,
                              cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).1.1.aig,
                vec := vec },
              ⋯⟩,
          cache :=
            (match
                match h :
                  { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                    { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                | some refs =>
                  if h : refs.size = 1 then
                    have refs := Vector.mk refs h;
                    some { refs := refs, hrefs := ⋯ }
                  else none
                | none => none with
              | some vec =>
                { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                  cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
              | none =>
                match
                  Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                    { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                | { result := result, cache := cache } =>
                  { result := result, cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).2 }
      | none =>
        match
          Std.Tactic.BVDecide.BVExpr.bitblast.go
            (match
                    match h :
                      { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                        { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                    | some refs =>
                      if h : refs.size = 1 then
                        have refs := Vector.mk refs h;
                        some { refs := refs, hrefs := ⋯ }
                      else none
                    | none => none with
                  | some vec =>
                    { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                      cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                  | none =>
                    match
                      Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                        { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                    | { result := result, cache := cache } =>
                      { result := result,
                        cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).1.1.aig
            (Std.Tactic.BVDecide.BVExpr.const 1#1)
            (match
                match h :
                  { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                    { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                | some refs =>
                  if h : refs.size = 1 then
                    have refs := Vector.mk refs h;
                    some { refs := refs, hrefs := ⋯ }
                  else none
                | none => none with
              | some vec =>
                { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                  cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
              | none =>
                match
                  Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                    { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                | { result := result, cache := cache } =>
                  { result := result, cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).2 with
        | { result := result, cache := cache } =>
          { result := result, cache := cache.insert (Std.Tactic.BVDecide.BVExpr.const 1#1) result.val.vec }).1.1
and
  {
    aig :=
      (match
              match h :
                (match
                          match h :
                            { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                              { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                          | some refs =>
                            if h : refs.size = 1 then
                              have refs := Vector.mk refs h;
                              some { refs := refs, hrefs := ⋯ }
                            else none
                          | none => none with
                        | some vec =>
                          { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                            cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                        | none =>
                          match
                            Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                              { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                          | { result := result, cache := cache } =>
                            { result := result,
                              cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).2.map.get?
                  { w := 1, expr := Std.Tactic.BVDecide.BVExpr.const 1#1 } with
              | some refs =>
                if h : refs.size = 1 then
                  have refs := Vector.mk refs h;
                  some { refs := refs, hrefs := ⋯ }
                else none
              | none => none with
            | some vec =>
              {
                result :=
                  ⟨{
                      aig :=
                        (match
                                match h :
                                  { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                                    { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                                | some refs =>
                                  if h : refs.size = 1 then
                                    have refs := Vector.mk refs h;
                                    some { refs := refs, hrefs := ⋯ }
                                  else none
                                | none => none with
                              | some vec =>
                                { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                                  cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                              | none =>
                                match
                                  Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty
                                    (Std.Tactic.BVDecide.BVExpr.var 0)
                                    { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                                | { result := result, cache := cache } =>
                                  { result := result,
                                    cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).1.1.aig,
                      vec := vec },
                    ⋯⟩,
                cache :=
                  (match
                      match h :
                        { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                          { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                      | some refs =>
                        if h : refs.size = 1 then
                          have refs := Vector.mk refs h;
                          some { refs := refs, hrefs := ⋯ }
                        else none
                      | none => none with
                    | some vec =>
                      { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                        cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                    | none =>
                      match
                        Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                          { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                      | { result := result, cache := cache } =>
                        { result := result,
                          cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).2 }
            | none =>
              match
                Std.Tactic.BVDecide.BVExpr.bitblast.go
                  (match
                          match h :
                            { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                              { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                          | some refs =>
                            if h : refs.size = 1 then
                              have refs := Vector.mk refs h;
                              some { refs := refs, hrefs := ⋯ }
                            else none
                          | none => none with
                        | some vec =>
                          { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                            cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                        | none =>
                          match
                            Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                              { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                          | { result := result, cache := cache } =>
                            { result := result,
                              cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).1.1.aig
                  (Std.Tactic.BVDecide.BVExpr.const 1#1)
                  (match
                      match h :
                        { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                          { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                      | some refs =>
                        if h : refs.size = 1 then
                          have refs := Vector.mk refs h;
                          some { refs := refs, hrefs := ⋯ }
                        else none
                      | none => none with
                    | some vec =>
                      { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                        cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                    | none =>
                      match
                        Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                          { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                      | { result := result, cache := cache } =>
                        { result := result,
                          cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).2 with
              | { result := result, cache := cache } =>
                { result := result,
                  cache := cache.insert (Std.Tactic.BVDecide.BVExpr.const 1#1) result.val.vec }).1.1.aig,
    vec :=
      (match
              match h :
                (match
                          match h :
                            { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                              { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                          | some refs =>
                            if h : refs.size = 1 then
                              have refs := Vector.mk refs h;
                              some { refs := refs, hrefs := ⋯ }
                            else none
                          | none => none with
                        | some vec =>
                          { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                            cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                        | none =>
                          match
                            Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                              { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                          | { result := result, cache := cache } =>
                            { result := result,
                              cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).2.map.get?
                  { w := 1, expr := Std.Tactic.BVDecide.BVExpr.const 1#1 } with
              | some refs =>
                if h : refs.size = 1 then
                  have refs := Vector.mk refs h;
                  some { refs := refs, hrefs := ⋯ }
                else none
              | none => none with
            | some vec =>
              {
                result :=
                  ⟨{
                      aig :=
                        (match
                                match h :
                                  { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                                    { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                                | some refs =>
                                  if h : refs.size = 1 then
                                    have refs := Vector.mk refs h;
                                    some { refs := refs, hrefs := ⋯ }
                                  else none
                                | none => none with
                              | some vec =>
                                { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                                  cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                              | none =>
                                match
                                  Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty
                                    (Std.Tactic.BVDecide.BVExpr.var 0)
                                    { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                                | { result := result, cache := cache } =>
                                  { result := result,
                                    cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).1.1.aig,
                      vec := vec },
                    ⋯⟩,
                cache :=
                  (match
                      match h :
                        { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                          { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                      | some refs =>
                        if h : refs.size = 1 then
                          have refs := Vector.mk refs h;
                          some { refs := refs, hrefs := ⋯ }
                        else none
                      | none => none with
                    | some vec =>
                      { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                        cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                    | none =>
                      match
                        Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                          { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                      | { result := result, cache := cache } =>
                        { result := result,
                          cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).2 }
            | none =>
              match
                Std.Tactic.BVDecide.BVExpr.bitblast.go
                  (match
                          match h :
                            { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                              { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                          | some refs =>
                            if h : refs.size = 1 then
                              have refs := Vector.mk refs h;
                              some { refs := refs, hrefs := ⋯ }
                            else none
                          | none => none with
                        | some vec =>
                          { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                            cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                        | none =>
                          match
                            Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                              { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                          | { result := result, cache := cache } =>
                            { result := result,
                              cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).1.1.aig
                  (Std.Tactic.BVDecide.BVExpr.const 1#1)
                  (match
                      match h :
                        { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ }.map.get?
                          { w := 1, expr := Std.Tactic.BVDecide.BVExpr.var 0 } with
                      | some refs =>
                        if h : refs.size = 1 then
                          have refs := Vector.mk refs h;
                          some { refs := refs, hrefs := ⋯ }
                        else none
                      | none => none with
                    | some vec =>
                      { result := ⟨{ aig := Std.Sat.AIG.empty, vec := vec }, ⋯⟩,
                        cache := { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } }
                    | none =>
                      match
                        Std.Tactic.BVDecide.BVExpr.bitblast.go Std.Sat.AIG.empty (Std.Tactic.BVDecide.BVExpr.var 0)
                          { map := Std.HashMap.emptyWithCapacity, hbound := ⋯ } with
                      | { result := result, cache := cache } =>
                        { result := result,
                          cache := cache.insert (Std.Tactic.BVDecide.BVExpr.var 0) result.val.vec }).2 with
              | { result := result, cache := cache } =>
                { result := result,
                  cache := cache.insert (Std.Tactic.BVDecide.BVExpr.const 1#1) result.val.vec }).1.1.vec }
pre-process and fold them as projection applications
-/
