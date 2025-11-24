module

inductive S where
  | m (b e : Nat)
  | r (b e : Nat)
deriving Repr, BEq, DecidableEq

def run (s pat : String) : List S :=
  String.Slice.Pattern.ForwardSliceSearcher.iter pat.toSlice s.toSlice
    |>.map (fun | .matched b e => S.m b.offset.byteIdx e.offset.byteIdx | .rejected b e => S.r b.offset.byteIdx e.offset.byteIdx)
    |>.toList

-- 𝔸 is [240,157,148,184]
-- 𝕸 is [240,157,149,184]

#guard run "aababaab" "a" = [.m 0 1, .m 1 2, .r 2 3, .m 3 4, .r 4 5, .m 5 6, .m 6 7, .r 7 8]
#guard run "aab" "ab" = [.r 0 1, .m 1 3]
#guard run "aababacab" "ab" = [.r 0 1, .m 1 3, .m 3 5, .r 5 6, .r 6 7, .m 7 9]
#guard run "aaab" "aab" = [.r 0 1, .m 1 4]
#guard run "aaaaa" "aa" = [.m 0 2, .m 2 4, .r 4 5]
#guard run "abcabd" "abd" = [.r 0 2, .r 2 3, .m 3 6]
#guard run "αβ" "β" = [.r 0 2, .m 2 4]
#guard run "𝔸" "𝕸" = [.r 0 4]
#guard run "𝔸𝕸" "𝕸" = [.r 0 4, .m 4 8]
#guard run "α𝔸€α𝔸₭" "α𝔸₭" = [.r 0 9, .m 9 18]
#guard run "α𝔸𝕸α𝔸₭" "α𝔸₭" = [.r 0 6, .r 6 10, .m 10 19]
#guard run "𝕸𝔸𝕸𝔸₭" "𝕸𝔸₭" = [.r 0 8, .m 8 19]
#guard run "𝕸𝔸𝕸β₭" "𝕸𝔸₭" = [.r 0 8, .r 8 12, .r 12 14, .r 14 17]
#guard run "𝔸𝔸𝔸𝔸𝕸𝔸𝔸𝔸𝕸" "𝔸𝔸𝕸" = [.r 0 4, .r 4 8, .m 8 20, .r 20 24, .m 24 36]
#guard run "𝔸b" "𝕸" = [.r 0 4, .r 4 5]
#guard run "𝔸bb𝕸β" "𝕸" = [.r 0 4, .r 4 5, .r 5 6, .m 6 10, .r 10 12]
#guard run "𝔸bbββαβαββββ𝕸β" "ββ𝕸" = [.r 0 4, .r 4 5, .r 5 6, .r 6 8, .r 8 10, .r 10 12, .r 12 14, .r 14 16, .r 16 18, .r 18 20, .m 20 28, .r 28 30]
#guard run "𝔸β𝕸" "𝕸" = [.r 0 4, .r 4 6, .m 6 10]
#guard run "𝔸b𝕸xu∅" "𝕸x" = [.r 0 4, .r 4 5, .m 5 10, .r 10 11, .r 11 14]
#guard run "é" "ù" = [.r 0 2]
#guard run "éB" "ù" = [.r 0 2, .r 2 3]
#guard run "abcabdabcabcabcabe" "abcabdabcabe" = [.r 0 6, .r 6 9, .r 9 12, .r 12 15, .r 15 17, .r 17 18]
#guard run "abcabdabcxabcabdabcabe" "abcabdabcabe" = [.r 0 6, .r 6 9, .r 9 10, .m 10 22]
#guard run "€α𝕸€α𝔸€α𝕸€α𝕸€α𝕸€αù" "€α𝕸€α𝔸€α𝕸€αù" = [.r 0 18, .r 18 27, .r 27 36, .r 36 45,  .r 45 50, .r 50 52]
