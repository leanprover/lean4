mutual

protected def Foo.toString : Foo → String
  := fun _ => "foo"

def toString' : Foo → String := fun _ => "foo"

end

#check @Foo.toString
