@[export hello]
def helloImpl (_ : Unit) := "precompiled world"

@[extern "hello"]
opaque getHello : Unit → String

def hello := getHello ()
