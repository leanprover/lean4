open expr list

meta def rwr_ctxs_lc (lc : expr) : expr → list expr
| (var _)   := []
| (app a b) := map (λc, app a c) (rwr_ctxs_lc b) ++ map (λc, app c b) (rwr_ctxs_lc a)
| e         := [lc]

meta def g (lc : expr) : expr → list expr
| (var _)   := []
| (app a b) := map (app a) (g b) ++ map (app b) (g a)
| e         := [lc]
