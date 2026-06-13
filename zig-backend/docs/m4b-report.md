# M4b cleanup snapshot

- M3-end Zig-owned public symbol count baseline: `133` (from `docs/m3-report.md`).
- Post-F13 Zig-owned public symbol count: `271` (`nm -gU zig-out/lib/libleanrt-zig.a | awk '/ _lean_/ {print $3}' | sort -u | wc -l`).
- Post-F13 migrated-symbol count in `libleanrt_cpp_partial.a`: `0` for `lean_(nat_big|int_big|cstr_to_(nat|int)|big_(usize|uint64|int_to|size_t_to|int64_to)|uint(8|16|32|64)_of_big|int(8|16|32|64)_of_big|usize_of_big|isize_of_big|uint64_mix_hash)`.
- `libleanrt_cpp_partial.a` still retains `mpz` and compactor support (for example `__ZN4lean3mpz...`, `__ZN4lean16object_compactor10insert_mpzEP11lean_object`, and `_lean_compacted_region_size`).
