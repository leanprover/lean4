enum Color {
  case Red
  case Black
}

indirect enum Tree {
  case Leaf
  case Node(Color, Tree, UInt64, Bool, Tree)
}

func balance1(_ kv : UInt64, _ vv : Bool, _ t : Tree, _ n : Tree) -> Tree {
  switch n {
  case let .Node(_, .Node(.Red, l, kx, vx, r1), ky, vy, r2):
    return .Node(.Red, .Node(.Black, l, kx, vx, r1), ky, vy, .Node(.Black, r2, kv, vv, t))
  case let .Node(_, l1, ky, vy, .Node(.Red, l2, kx, vx, r)):
    return .Node(.Red, .Node(.Black, l1, ky, vy, l2), kx, vx, .Node(.Black, r, kv, vv, t))
  case let .Node(_, l, ky, vy, r):
    return .Node(.Black, .Node(.Red, l, ky, vy, r), kv, vv, t)
  default:
    return .Leaf
  }
}

func balance2(_ t : Tree, _ kv : UInt64, _ vv : Bool, _ n : Tree) -> Tree {
  switch n {
  case let .Node(_, .Node(.Red, l, kx1, vx1, r1), ky, vy, r2):
    return .Node(.Red, .Node(.Black, t, kv, vv, l), kx1, vx1, .Node(.Black, r1, ky, vy, r2))
  case let .Node(_, l1, ky, vy, .Node(.Red, l2, kx2, vx2, r2)):
    return .Node(.Red, .Node(.Black, t, kv, vv, l1), ky, vy, .Node(.Black, l2, kx2, vx2, r2))
  case let .Node (_, l, ky, vy, r):
    return .Node(.Black, t, kv, vv, .Node(.Red, l, ky, vy, r))
  default:
    return .Leaf
  }
}

func is_red (_ t : Tree) -> Bool {
  switch t {
  case .Node(.Red, _, _, _, _):
    return true
  default:
    return false
  }
}

func ins(_ t : Tree, _ kx : UInt64, _ vx : Bool) -> Tree {
  switch t {
  case .Leaf:
    return .Node(.Red, .Leaf, kx, vx, .Leaf)
  case let .Node(.Red, a, ky, vy, b):
    if kx < ky {
      return .Node(.Red, ins(a, kx, vx), ky, vy, b)
    } else if ky == kx {
      return .Node(.Red, a, kx, vx, b)
    } else {
      return .Node(.Red, a, ky, vy, ins(b, kx, vx))
    }
  case let .Node(.Black, a, ky, vy, b):
   if kx < ky {
    if is_red(a) {
      return balance1(ky, vy, b, ins(a, kx, vx))
    } else {
      return .Node(.Black, ins(a, kx, vx), ky, vy, b)
    }
   } else if kx == ky {
     return .Node(.Black, a, kx, vx, b)
   } else {
     if is_red(b) {
       return balance2(a, ky, vy, ins(b, kx, vx))
     } else {
       return .Node(.Black, a, ky, vy, ins(b, kx, vx))
     }
   }
  }
}

func set_black (_ n : Tree) -> Tree {
  switch n {
  case let .Node (_, l, k, v, r):
    return .Node (.Black, l, k, v, r)
  default:
    return n
  }
}

func insert (_ t : Tree, _ k : UInt64, _ v : Bool) -> Tree {
 if is_red(t) {
   return set_black(ins(t, k, v))
 } else {
   return ins(t, k, v)
 }
}

func fold (_ f : (_ k : UInt64, _ v : Bool, _ d : UInt64) -> UInt64, _ n : Tree, _ d : UInt64) -> UInt64 {
  switch n {
  case .Leaf:
    return d
  case let .Node(_, l, k, v, r):
    return fold(f, r, f(k, v, fold(f, l, d)))
  }
}

func mk_map (_ n : UInt64) -> Tree {
  var i = n
  var m : Tree = .Leaf
  while i > 0 {
    i = i - 1
    m = insert(m, i, (i%10 == 0))
  }
  return m
}

func aux (_ k : UInt64, _ v : Bool, _ r : UInt64) -> UInt64 {
  if v {
    return r + 1
  } else {
    return r
  }
}

if CommandLine.arguments.count != 2 {
  print("Incorrect number of arguments")
} else {
  let num  = UInt64(CommandLine.arguments[1])
  let m = mk_map(num!)
  let v = fold(aux, m, 0)
  print(v)
}
