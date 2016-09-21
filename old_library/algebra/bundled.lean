/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Bundled structures
-/
import algebra.group

structure Semigroup :=
(carrier : Type) (struct : semigroup carrier)

attribute Semigroup.struct [instance]

structure CommSemigroup :=
(carrier : Type) (struct : comm_semigroup carrier)

attribute CommSemigroup.struct [instance]

structure Monoid :=
(carrier : Type) (struct : monoid carrier)

attribute Monoid.struct [instance]

structure CommMonoid :=
(carrier : Type) (struct : comm_monoid carrier)

attribute CommMonoid.struct [instance]

structure Group :=
(carrier : Type) (struct : group carrier)

attribute Group.struct [instance]

structure CommGroup :=
(carrier : Type) (struct : comm_group carrier)

attribute CommGroup.struct [instance]

structure AddSemigroup :=
(carrier : Type) (struct : add_semigroup carrier)

attribute AddSemigroup.struct [instance]

structure AddCommSemigroup :=
(carrier : Type) (struct : add_comm_semigroup carrier)

attribute AddCommSemigroup.struct [instance]

structure AddMonoid :=
(carrier : Type) (struct : add_monoid carrier)

attribute AddMonoid.struct [instance]

structure AddCommMonoid :=
(carrier : Type) (struct : add_comm_monoid carrier)

attribute AddCommMonoid.struct [instance]

structure AddGroup :=
(carrier : Type) (struct : add_group carrier)

attribute AddGroup.struct [instance]

structure AddCommGroup :=
(carrier : Type) (struct : add_comm_group carrier)

attribute AddCommGroup.struct [instance]
