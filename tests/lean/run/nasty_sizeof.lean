def nasty_sizeof : list nat → nat
| []      := 100000000
| (a::as) := nasty_sizeof as + 100000000
