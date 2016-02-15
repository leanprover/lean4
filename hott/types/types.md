hott.types
==========

Types in Martin-Lӧf Type Theory:

* [unit](unit.hlean)
* [bool](bool.hlean)
* [num[(num.hlean) (natural numbers written in binary form)
* [nat](nat/nat.md) (subfolder)
* [int](int/int.md) (subfolder)
* [prod](prod.hlean)
* [sigma](sigma.hlean)
* [sum](sum.hlean)
* [pi](pi.hlean)
* [arrow](arrow.hlean)
* [arrow_2](arrow_2.hlean): alternative development of properties of arrows
* [W](W.hlean): W-types (not loaded by default)
* [lift](lift.hlean)
* [list](list.hlean)

The number systems (num, nat, int, ...) are for a large part ported from the standard libary.

Specific HoTT types

* [eq](eq.hlean): show that functions related to the identity type are equivalences
* [pointed](pointed.hlean): pointed types, pointed maps, pointed homotopies
* [fiber](fiber.hlean)
* [equiv](equiv.hlean)
* [pointed2](pointed2.hlean): pointed equivalences and pointed truncated types (this is a separate file, because it depends on types.equiv)
* [trunc](trunc.hlean): truncation levels, n-types, truncation
* [pullback](pullback.hlean)
* [univ](univ.hlean)