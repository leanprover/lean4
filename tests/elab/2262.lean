macro "foo" noWs ":" ws "bar" : command => `(command| /-! -/)
macro "foo'" hygieneInfo noWs hygieneInfo ":" hygieneInfo ws hygieneInfo "bar" : command => `(command| /-! -/)

foo: bar
foo': bar
