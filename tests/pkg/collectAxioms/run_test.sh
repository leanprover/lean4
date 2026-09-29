rm -rf .lake
lake build

# Without axiom tracking, the axioms used in a proof do not affect the module's `.olean`.
cp .lake/build/lib/lean/Untracked/Base.olean .lake/Base.olean.before
cp Untracked/Base.lean .lake/Base.lean.orig
trap 'cp .lake/Base.lean.orig Untracked/Base.lean' EXIT
sed -i 's/untrackedThm : True := untrackedAx/untrackedThm : True := trivial/' Untracked/Base.lean
grep -q 'untrackedThm : True := trivial' Untracked/Base.lean
lake build Untracked
cmp .lake/Base.olean.before .lake/build/lib/lean/Untracked/Base.olean
