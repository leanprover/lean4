@[macro_inline] def rhs (_ : @Eq α x y) := y

def String.data' : type_of% data := fun self => rhs (data.eq_def self)
def ByteArray.data' : type_of% data := fun self => rhs (data.eq_def self)
def FloatArray.data' : type_of% data := fun self => rhs (data.eq_def self)
def Array.toList' : type_of% @toList := fun {α} self => rhs (toList.eq_def α self)
def Thunk.fn' : type_of% @fn := fun {α} self => rhs (fn.eq_def α self)
def Task.get' : type_of% @get := fun {α} self => rhs (get.eq_def α self)

#eval " ".data'
#eval ByteArray.empty.data'
#eval FloatArray.empty.data'
#eval #["", ""].toList'
#eval (Thunk.mk fun _ => "").fn' ()
#eval (Task.spawn fun _ => "").get'
