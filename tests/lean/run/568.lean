namespace f1
  definition flip := 20
end f1

namespace f2
  definition flip := 10
end f2

namespace f3
  export [declarations] f1
  export -[declarations] f2
end f3

export [declarations] f1
export -[declarations] f2
