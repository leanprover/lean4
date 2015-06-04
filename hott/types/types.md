hott.types
==========

Types (not necessarily HoTT-related):

* [unit](unit.hlean)
* [bool](bool.hlean)
* [nat](nat/nat.md) (subfolder)
* [int](int/int.md) (subfolder)
* [prod](prod.hlean)
* [sigma](sigma.hlean)
* [pi](pi.hlean)
* [arrow](arrow.hlean)
* [W](W.hlean): W-types (not loaded by default)

HoTT types

* [hprop_trunc](hprop_trunc.hlean): in this file we prove that `is_trunc n A` is a mere proposition. We separate this from [trunc](trunc.hlean) to avoid circularity in imports.
* [eq](eq.hlean)
* [pointed](pointed.hlean)
* [fiber](fiber.hlean)
* [equiv](equiv.hlean)
* [function](function.hlean): embeddings, (split) surjections, retractions
* [trunc](trunc.hlean): truncation levels, n-Types, truncation
* [cubical](cubical/cubical.md): cubical types (subfolder)


