set_option trace.class_instances true

example (M : Type → Type) [Monad M] : ExceptT Unit (ReaderT Unit (StateT Unit M)) Unit := do
ctx ← read;
pure ()
/-
...
[class_instances] (1) ?x_8 : HasMonadLift
  (ReaderT ?x_10
     (OptionT
        (OptionT
           (OptionT
              (OptionT
                 (OptionT
                    (OptionT
                       (OptionT
                          (OptionT
                             (OptionT
                                (OptionT
                                   (OptionT
                                      (OptionT
                                         (OptionT
                                            (OptionT
                                               (OptionT
                                                  (OptionT
                                                     (OptionT
                                                        (OptionT
                                                           (OptionT (OptionT (OptionT (OptionT (OptionT (OptionT (OptionT (OptionT (OptionT (OptionT (OptionT List))))))))))))))))))))))))))))))
  (ExceptT Unit (ReaderT Unit (StateT Unit M))) := @ExceptT.exceptTOfExcept ?x_82 ?x_83 ?x_84
failed is_def_eq
...
error: maximum class-instance resolution depth has been reached
-/
