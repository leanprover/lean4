# Per-declaration heartbeat costs always ride the build: compiling a module writes
# `<module>.hb.json` next to the `.olean`, split into `elab` and `kernel` phases, with
# auxiliary declarations rolled up to their user-written owner. See `Lean.HeartbeatEntry`.

LEAN_FILE="$TMP_DIR/hb.lean"
OLEAN="$TMP_DIR/hb.olean"
OUT="$TMP_DIR/hb.hb.json"

cat > "$LEAN_FILE" <<'EOF'
theorem hbCheap : 1 + 1 = 2 := rfl

theorem hbCostly : (List.range 100).length = 100 := by decide
EOF

# Compiling to an olean writes the sidecar unconditionally: no options involved.
run lean --root="$TMP_DIR" -o "$OLEAN" "$LEAN_FILE"
[[ -f "$OUT" ]] || fail "no heartbeat sidecar written next to the olean"

# Both declarations are attributed in both phases, with a nonzero cost.
for decl in hbCheap hbCostly; do
  for phase in elab kernel; do
    jq -e --arg d "$decl" --arg p "$phase" \
      '[.entries[] | select(.owner == $d and .phase == $p and .heartbeats > 0)] | length >= 1' \
      "$OUT" > /dev/null || fail "missing positive $phase entry for $decl"
  done
done

# The metric separates a brute-force proof from a cheap one.
jq -e '
  ([.entries[] | select(.owner == "hbCostly") | .heartbeats] | add) >
  ([.entries[] | select(.owner == "hbCheap")  | .heartbeats] | add)
' "$OUT" > /dev/null || fail 'expected the `decide` proof to outweigh the `rfl` proof'

# Counts are deterministic: a second compile produces identical entries.
cp "$LEAN_FILE" "$TMP_DIR/hb2.lean"
run lean --root="$TMP_DIR" -o "$TMP_DIR/hb2.olean" "$TMP_DIR/hb2.lean"
jq -S '.entries | sort_by(.owner, .decl, .phase)' "$OUT" > "$OUT.norm1"
jq -S '.entries | sort_by(.owner, .decl, .phase)' "$TMP_DIR/hb2.hb.json" > "$OUT.norm2"
$DIFF -- "$OUT.norm1" "$OUT.norm2" || fail "heartbeat counts differ between identical runs"

# Entries are also recorded under synchronous elaboration.
cp "$LEAN_FILE" "$TMP_DIR/hbsync.lean"
run lean --root="$TMP_DIR" -DElab.async=false -o "$TMP_DIR/hbsync.olean" "$TMP_DIR/hbsync.lean"
for decl in hbCheap hbCostly; do
  jq -e --arg d "$decl" \
    '[.entries[] | select(.owner == $d and .heartbeats > 0)] | length >= 1' \
    "$TMP_DIR/hbsync.hb.json" > /dev/null || fail "missing entry for $decl with Elab.async=false"
done

# Every entry's owner is a user-written declaration: matchers, codegen, and derived
# instances roll up to the declaration that caused them, and nothing is left anonymous.
OWNERS_FILE="$TMP_DIR/hb_owners.lean"
cat > "$OWNERS_FILE" <<'EOF'
namespace HbNs

def myMap : List Nat → List Nat
  | [] => []
  | x :: xs => (x + 1) :: myMap xs

mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

inductive Tree where
  | leaf
  | node (l r : Tree)
deriving Repr, BEq

instance treeToString : ToString Tree where
  toString _ := "tree"

-- anonymous instance with a matcher: its auxiliaries must still roll up to the instance
instance : Hashable Tree where
  hash t := match t with
    | .leaf => 0
    | .node .. => 1

theorem treeThm : (Tree.leaf == Tree.leaf) = true := rfl

end HbNs
EOF
run lean --root="$TMP_DIR" -o "$TMP_DIR/hb_owners.olean" "$OWNERS_FILE"
# owners must be the namespace-qualified user-written declarations (the anonymous instance
# elaborates as HbNs.instHashableTree)
jq -e '
  [.entries[].owner] | unique
    - ["HbNs.myMap", "HbNs.isEven", "HbNs.isOdd", "HbNs.Tree", "HbNs.treeToString",
       "HbNs.instHashableTree", "HbNs.treeThm"]
    | length == 0
' "$TMP_DIR/hb_owners.hb.json" > /dev/null || {
  jq '[.entries[].owner] | unique' "$TMP_DIR/hb_owners.hb.json"
  fail "heartbeats attributed to unexpected owners"
}
# the deriving-generated instances must not appear as owners: their cost belongs to Tree
jq -e '[.entries[].owner | select(test("inst(Repr|BEq)"))] | length == 0'   "$TMP_DIR/hb_owners.hb.json" > /dev/null || fail "deriving-generated instance stole ownership"

# Without an olean destination there is nowhere to anchor a sidecar; checking still succeeds.
NOOLEAN="$TMP_DIR/noolean.lean"
cp "$LEAN_FILE" "$NOOLEAN"
run lean "$NOOLEAN"
[[ ! -f "$TMP_DIR/noolean.hb.json" ]] || fail "unexpected sidecar without -o"
