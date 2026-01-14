typealias Elem = UInt32

func badRand(_ seed : Elem) -> Elem {
    return seed &* 1664525 &+ 1013904223
}

func mkRandomArray(_ seed: Elem, _ n: Int) -> Array<Elem> {
    var a = [Elem](repeating: 0, count: n)
    var seed = seed
    for i in 0..<n {
        a[i] = seed
        seed = badRand(seed)
    }
    return a
}

func checkSorted(_ a: Array<Elem>) {
    if a.count > 0 {
        for i in 0..<a.count - 1 {
            if a[i] > a[i+1] {
                fatalError()
            }
        }
    }
}

func swap(_ i: Int, _ j: Int, _ a: inout Array<Elem>) {
    let x = a[i]
    let y = a[j]
    a[i] = y
    a[j] = x
}

func partitionAux(_ a: inout Array<Elem>, _ hi: Int, _ pivot: Elem, _ lo: Int) -> Int {
    var i = lo
    for j in lo..<hi {
        if a[j] < pivot {
            swap(i, j, &a)
            i += 1
        }
    }
    swap(i, hi, &a)
    return i
}

func partition(_ a: inout Array<Elem>, _ lo: Int, _ hi: Int) -> Int {
    let mid = (lo + hi) / 2
    if a[mid] < a[lo] { swap(lo, mid, &a) }
    if a[hi] < a[lo] { swap(lo, hi, &a) }
    if a[mid] < a[hi] { swap(mid, hi, &a) }
    return partitionAux(&a, hi, a[hi], lo)
}

func qsortAux(_ a: inout Array<Elem>, _ low: Int, _ high: Int) {
    if low < high {
        let mid = partition(&a, low, high)
        qsortAux(&a, low, mid)
        qsortAux(&a, mid+1, high)
    }
}

func qsort(_ a: inout Array<Elem>) {
    qsortAux(&a, 0, a.count - 1)
}


let n = Int(CommandLine.arguments[1])!
for _ in 0..<n {
    for i in 0..<n {
        var xs = mkRandomArray(UInt32(i), i)
        qsort(&xs)
        checkSorted(xs)
    }
}
