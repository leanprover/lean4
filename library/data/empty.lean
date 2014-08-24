-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad

-- TODO: add notation for negation (in the sense of homotopy type theory)

-- Empty type
-- ----------

inductive empty : Type

theorem empty_elim (A : Type) (H : empty) : A := empty_rec (λe, A) H
