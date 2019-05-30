indirect enum Expr {
  case Val(Int64)
  case Var(String)
  case Add(Expr, Expr)
  case Mul(Expr, Expr)
  case Pow(Expr, Expr)
  case Ln(Expr)
}

func pown(_ a : Int64, _ n : Int64) -> Int64 {
     if n == 0 {
        return 1
     } else if n == 1 {
        return a
     } else {
        let b = pown(a, n/2)
        if n % 2 == 0 {
           return b*b*a
        } else {
           return b*b
        }
     }
}

func add (_ e1 : Expr, _ e2 : Expr) -> Expr {
  switch (e1, e2) {
  case let (.Val(n), .Val(m)) :
     return .Val(n+m)
  case let (.Val(0), f):
     return f
  case let (f, .Val(0)):
     return f
  case let (f, .Val(n)):
     return add(.Val(n), f)
  case let (.Val(n), .Add(.Val(m), f)):
     return add(.Val(n+m), f)
  case let (f, .Add(.Val(n), g)):
     return add(.Val(n), add(f, g))
  case let (.Add(f, g), h):
     return add(f, add(g, h))
  default:
     return .Add(e1, e2)
  }
}

func mul (_ e1 : Expr, _ e2 : Expr) -> Expr {
  switch (e1, e2) {
  case let (.Val(n), .Val(m)):
    return .Val(n*m)
  case (.Val(0), _):
    return .Val(0)
  case (_, .Val(0)):
    return .Val(0)
  case let (.Val(1), f):
    return f
  case let (f, .Val(1)):
    return f
  case let (f, .Val(n)):
    return mul(.Val(n), f)
  case let (.Val(n), .Mul(.Val(m), f)):
    return mul(.Val(n*m), f)
  case let (f, .Mul(.Val(n), g)):
    return mul(.Val(n), mul(f, g))
  case let (.Mul(f, g), h):
    return mul(f, mul(g, h))
  default:
    return .Mul(e1, e2)
  }
}

func pow (_ e1 : Expr, _ e2 : Expr) -> Expr {
  switch (e1, e2) {
  case let (.Val(m), .Val(n)):
     return .Val(pown(m, n))
  case (_, .Val(0)):
     return .Val(1)
  case let (f, .Val(1)):
     return f
  case (.Val(0), _):
     return .Val(0)
  default:
     return .Pow(e1, e2)
  }
}

func ln (_ e : Expr) -> Expr {
  switch e {
  case .Val(1):
     return .Val(0)
  default:
     return .Ln(e)
  }
}

func d (_ x : String, _ e : Expr) -> Expr {
  switch e {
  case .Val(_):
    return .Val(0)
  case let .Var(y):
    if x == y {
       return .Val(1)
    } else {
       return .Val(0)
    }
  case let .Add(f, g):
    return add(d(x, f), d(x, g))
  case let .Mul(f, g):
    return add(mul(f, d(x, g)), mul(g, d(x, f)))
  case let .Pow(f, g):
    return mul(pow(f, g), add(mul(mul(g, d(x, f)), pow(f, .Val(-1))), mul(ln(f), d(x, g))))
  case let .Ln(f):
    return mul(d(x, f), pow(f, .Val(-1)))
  }
}

func toString (_ e : Expr) -> String {
  switch e {
  case let .Val(n):
    return String(n)
  case let .Var(x):
    return x
  case let .Add(f, g):
    return "(" + toString(f) + " + " + toString(g) + ")"
  case let .Mul(f, g):
    return "(" + toString(f) + " * " + toString(g) + ")"
  case let .Pow(f, g):
    return "(" + toString(f) + " ^ " + toString(g) + ")"
  case let .Ln(f):
    return "ln(" + toString(f) + ")"
  }
}

func count (_ e : Expr) -> UInt32 {
  switch e {
  case .Val(_):
    return 1
  case .Var(_):
    return 1
  case let .Add(f, g):
    return count(f) + count(g)
  case let .Mul(f, g):
    return count(f) + count(g)
  case let .Pow(f, g):
    return count(f) + count(g)
  case let .Ln(f):
    return count(f)
  }
}

func nest_aux (_ s : UInt32, _ f : (_ n : UInt32, _ e : Expr) -> Expr, _ n : UInt32, _ x : Expr) -> Expr {
  if n == 0 {
    return x
  } else {
    let x = f(s - n, x)
    return nest_aux(s, f, n-1, x)
  }
}

func nest (_ f : (_ n : UInt32, _ e : Expr) -> Expr, _ n : UInt32, _ e : Expr) -> Expr {
  return nest_aux(n, f, n, e)
}

func deriv (_ i : UInt32, _ f : Expr) -> Expr {
  let e = d("x", f)
  print(i+1, " count: ", count(e))
  return e
}

let x = Expr.Var("x")
let f = pow(x, x)
let e = nest(deriv, 10, f)
