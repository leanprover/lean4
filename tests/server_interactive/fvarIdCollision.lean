--^ waitForILeans

-- Regression test for a bug where (due to parallelism) the fvar ids weren't unique for the whole
-- module, leading to a conflict between `i` of `lt_next'` and the fvar id for `prev'`, thus
-- making go to definition jump to the wrong location.

theorem lt_next' (s : Substring.Raw) (i : String.Pos.Raw) (h : i.1 < s.bsize) :
    i.1 < (s.next i).1 := by
  sorry

def prev' : Substring.Raw → String.Pos.Raw → String.Pos.Raw := sorry

#check prev'
       --^ textDocument/definition
