open eq

set_option pp.implicit true
set_option pp.universes true
set_option pp.notation false

check @idp_rec_on

attribute idp_rec_on [recursor]

print [recursor] idp_rec_on
