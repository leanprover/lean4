module
namespace List
-- Should not panic
#guard_msgs (drop error) in
theorem countP_filterMap' {p : β → Bool} {f : α → Option β} {l : List α} :
    countP p (filterMap f l) = countP (fun a => ((f a).map p).getD false) l := by
  induction l with grind [=_ Option.getD_map]
