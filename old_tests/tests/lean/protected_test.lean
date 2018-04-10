namespace nat
  #check induction_on      -- ERROR
  #check rec_on            -- ERROR
  #check less_than_or_equal.rec_on         -- OK
  #check nat.less_than_or_equal.rec_on
  namespace le
    #check rec_on          -- ERROR
    #check less_than_or_equal.rec_on
  end le
end nat
