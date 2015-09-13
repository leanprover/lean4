hit
===

Declaration and theorems of higher inductive types in Lean. We take
two higher inductive types (hits) as primitive notions in Lean. We
define all other hits in terms of these two hits. The hits which are
primitive are n-truncation and quotients. These are defined in
[init.hit](../init/hit.hlean) and they have definitional computation
rules on the point constructors.

Here we find hits related to the basic structure theory of HoTT.  The
hits related to homotopy theory are defined in
[homotopy](../homotopy/homotopy.md).

Files in this folder:

* [quotient](quotient.hlean) (quotients, primitive)
* [trunc](trunc.hlean) (truncation, primitive)
* [colimit](colimit.hlean) (Colimits of arbitrary diagrams and sequential colimits, defined using quotients)
* [pushout](pushout.hlean) (Pushouts, defined using quotients)
* [coeq](coeq.hlean) (Co-equalizers, defined using quotients)
* [set_quotient](set_quotient.hlean) (Set-quotients, defined using quotients and set-truncation)
