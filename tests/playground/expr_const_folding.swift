indirect enum Expr {
    case Var(UInt64)
    case Val(UInt64)
    case Add(Expr, Expr)
    case Mul(Expr, Expr)
}

func mk_expr(_ n: UInt64, _ v: UInt64) -> Expr {
    if n == 0 {
        return v == 0 ? .Var(1) : .Val(v)
    } else {
        return .Add(mk_expr(n - 1, v+1), mk_expr(n - 1, v == 0 ? 0 : v - 1))
    }
}

func append_add(_ e₁: Expr, _ e₂: Expr) -> Expr {
    switch e₁ {
    case let .Add(e₁₁, e₁₂):
        return .Add(e₁₁, append_add(e₁₂, e₂))
    default:
        return .Add(e₁, e₂)
    }
}

func append_mul(_ e₁: Expr, _ e₂: Expr) -> Expr {
    switch e₁ {
    case let .Mul(e₁₁, e₁₂):
        return .Mul(e₁₁, append_mul(e₁₂, e₂))
    default:
        return .Mul(e₁, e₂)
    }
}

func reassoc(_ e: Expr) -> Expr {
    switch e {
    case let .Add(e₁, e₂):
        let e₁ = reassoc(e₁)
        let e₂ = reassoc(e₂)
        return append_add(e₁, e₂)
    case let .Mul(e₁, e₂):
        let e₁ = reassoc(e₁)
        let e₂ = reassoc(e₂)
        return append_mul(e₁, e₂)
    default:
        return e
    }
}

func const_folding(_ e: Expr) -> Expr {
    switch e {
    case let .Add(e₁, e₂):
        let e₁ = const_folding(e₁)
        let e₂ = const_folding(e₂)
        switch (e₁, e₂) {
        case let (.Val(a), .Val(b)):
            return .Val(a+b)
        case let (.Val(a), .Add(e, .Val(b))):
            return .Add(.Val(a+b), e)
        case let (.Val(a), .Add(.Val(b), e)):
            return .Add(.Val(a+b), e)
        default:
            return .Add(e₁, e₂)
        }
    case let .Mul(e₁, e₂):
        let e₁ = const_folding(e₁)
        let e₂ = const_folding(e₂)
        switch (e₁, e₂) {
        case let (.Val(a), .Val(b)):
            return .Val(a*b)
        case let (.Val(a), .Mul(e, .Val(b))):
            return .Mul(.Val(a*b), e)
        case let (.Val(a), .Mul(.Val(b), e)):
            return .Mul(.Val(a*b), e)
        default:
            return .Mul(e₁, e₂)
        }
    default:
        return e
    }
}

func eval(_ e: Expr) -> UInt64 {
    switch e {
    case .Var(_):
        return 0
    case let .Val(v):
        return v
    case let .Add(l, r):
        return eval(l) + eval(r)
    case let .Mul(l, r):
        return eval(l) * eval(r)
    }
}

let e  = mk_expr(23, 1)
let v₁ = eval(e)
let v₂ = eval(const_folding(reassoc(e)))
print(v₁, v₂)
