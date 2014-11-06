-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Jakob von Raumer
-- Ported from Coq HoTT
import hott.path hott.equiv
open path Equiv

axiom ua {A B : Type} [H : A ≃ B] : A ≈ B
