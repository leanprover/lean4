hit
===

Declaration and theorems of higher inductive types in Lean. We take two higher inductive types (hits) as primitive notions in Lean. We define all other hits in terms of these two hits. The hits which are primitive are n-truncation and type quotients. These are defined in [init.hit](../init.hit.hlean) and they have definitional computation rules on the point constructors.

Files in this folder:

* [type_quotient](type_quotient.hlean) (Type quotients, primitive)
* [trunc](trunc.hlean) (truncation, primitive)
* [colimit](colimit.hlean) (Colimits of arbitrary diagrams and sequential colimits, defined using type quotients)
* [pushout](pushout.hlean) (Pushouts, defined using type quotients)
* [coeq](coeq.hlean) (Co-equalizers, defined using type quotients)
* [cylinder](cylinder.hlean) (Mapping cylinders, defined using type quotients)
* [quotient](quotient.hlean) (Set-quotients, defined using type quotients and set-truncation)
* [suspension](suspension.hlean) (Suspensions, defined using pushouts)
* [sphere](sphere.hlean) (Higher spheres, defined recursively using suspensions)
* [circle](circle.hlean)