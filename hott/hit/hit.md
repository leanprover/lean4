hit
===

Declaration and theorems of higher inductive types in Lean. We take
two higher inductive types (hits) as primitive notions in Lean. We
define all other hits in terms of these two hits. The hits which are
primitive are n-truncation and quotients. These are defined in
[init.hit](../init/hit.hlean) and they have definitional computation
rules on the point constructors.

Files in this folder:

* [quotient](quotient.hlean) (quotients, primitive)
* [trunc](trunc.hlean) (truncation, primitive)
* [colimit](colimit.hlean) (Colimits of arbitrary diagrams and sequential colimits, defined using quotients)
* [pushout](pushout.hlean) (Pushouts, defined using quotients)
* [coeq](coeq.hlean) (Co-equalizers, defined using quotients)
* [cylinder](cylinder.hlean) (Mapping cylinders, defined using quotients)
* [set_quotient](set_quotient.hlean) (Set-quotients, defined using quotients and set-truncation)
* [suspension](suspension.hlean) (Suspensions, defined using pushouts)
* [sphere](sphere.hlean) (Higher spheres, defined recursively using suspensions)
* [circle](circle.hlean) (defined as sphere 1)
* [interval](interval.hlean) (defined as the suspension of unit)