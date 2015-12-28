namespace f1
  definition flip := (20:num)
end f1

namespace f2
  definition flip := (10:num)
end f2

namespace f3
  export [declaration] f1
  export - [declaration] f2
end f3

export [declaration] f1
export - [declaration] f2
