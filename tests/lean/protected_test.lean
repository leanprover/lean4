namespace nat
  check induction_on      -- ERROR
  check rec_on            -- ERROR
  check nat.induction_on
  check le.rec_on         -- OK
  check nat.le.rec_on
  namespace le
    check rec_on          -- ERROR
    check le.rec_on
  end le
end nat
