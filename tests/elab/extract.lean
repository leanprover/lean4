
#eval "abc"

/- some "a" -/
#eval
 let s₁  := "abcde";
 let it₁ := s₁.mkIterator;
 let it₂ := it₁.next;
 it₁.extract it₂

/- some "" -/
#eval
 let s₁  := "abcde";
 let it₁ := s₁.mkIterator;
 it₁.extract it₁

/- none -/
#eval
 let s₁  := "abcde";
 let it₁ := s₁.mkIterator;
 let it₂ := it₁.next;
 it₂.extract it₁

/- some "abc" -/
#eval
 let s₁  := "abcde";
 let it₁ := s₁.mkIterator;
 let it₂ := it₁.next.next.next.prev.next;
 it₁.extract it₂

/- some "bcde" -/
#eval
 let s₁  := "abcde";
 let it₁ := s₁.mkIterator.next;
 let it₂ := it₁.next.next.next.next;
 it₁.extract it₂

/- some "abcde" -/
#eval
 let s₁  := "abcde";
 let it₁ := s₁.mkIterator;
 let it₂ := it₁.next.next.next.next.next;
 it₁.extract it₂

/- some "ab" -/
#eval
  let s₁  := "abcde";
  let s₂  := "abcde";
  let it₁ := s₁.mkIterator;
  let it₂ := s₂.mkIterator.next.next;
  it₁.extract it₂

/- none -/
#eval
  let s₁  := "abcde";
  let s₂  := "abhde";
  let it₁ := s₁.mkIterator;
  let it₂ := s₂.mkIterator.next.next;
  it₁.extract it₂

/- none -/
#eval
  let s₁  := "abcde";
  let it₁ := s₁.mkIterator;
  let it₂ := it₁.next.setCurr 'a';
  it₁.extract it₂

/- some "a" -/
#eval
  let s₁  := "abcde";
  let it₁ := s₁.mkIterator;
  let it₂ := it₁.next.setCurr 'b';
  it₁.extract it₂

/- some "a" -/
#eval
  let s₁  := "abcde";
  let it₁ := s₁.mkIterator;
  let it₂ := (it₁.next.setCurr 'a').setCurr 'b';
  it₁.extract it₂
