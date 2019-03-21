#exit -- Disabled until we implement new VM
#eval "abc"

/- some "a" -/
#eval
 let s₁  := "abcde" in
 let it₁ := s₁.mkIterator in
 let it₂ := it₁.next in
 it₁.extract it₂

/- some "" -/
#eval
 let s₁  := "abcde" in
 let it₁ := s₁.mkIterator in
 it₁.extract it₁

/- none -/
#eval
 let s₁  := "abcde" in
 let it₁ := s₁.mkIterator in
 let it₂ := it₁.next in
 it₂.extract it₁

/- some "abc" -/
#eval
 let s₁  := "abcde" in
 let it₁ := s₁.mkIterator in
 let it₂ := it₁.next.next.next.prev.next in
 it₁.extract it₂

/- some "bcde" -/
#eval
 let s₁  := "abcde" in
 let it₁ := s₁.mkIterator.next in
 let it₂ := it₁.next.next.next.next in
 it₁.extract it₂

/- some "abcde" -/
#eval
 let s₁  := "abcde" in
 let it₁ := s₁.mkIterator in
 let it₂ := it₁.next.next.next.next.next in
 it₁.extract it₂

/- some "ab" -/
#eval
  let s₁  := "abcde" in
  let s₂  := "abcde" in
  let it₁ := s₁.mkIterator in
  let it₂ := s₂.mkIterator.next.next in
  it₁.extract it₂

/- none -/
#eval
  let s₁  := "abcde" in
  let s₂  := "abhde" in
  let it₁ := s₁.mkIterator in
  let it₂ := s₂.mkIterator.next.next in
  it₁.extract it₂

/- none -/
#eval
  let s₁  := "abcde" in
  let it₁ := s₁.mkIterator in
  let it₂ := it₁.next.setCurr 'a' in
  it₁.extract it₂

/- some "a" -/
#eval
  let s₁  := "abcde" in
  let it₁ := s₁.mkIterator in
  let it₂ := it₁.next.setCurr 'b' in
  it₁.extract it₂

/- some "a" -/
#eval
  let s₁  := "abcde" in
  let it₁ := s₁.mkIterator in
  let it₂ := (it₁.next.setCurr 'a').setCurr 'b' in
  it₁.extract it₂
