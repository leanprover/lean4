namespace nat
  check induction_on      -- ERROR
  check rec_on            -- ERROR
  check nat.induction_on
  check lt.rec_on         -- OK
  check nat.lt.rec_on
  namespace lt
    check rec_on          -- ERROR
    check lt.rec_on
  end lt
end nat
