/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/
prelude

import init.meta.expr
import init.meta.format

import init.native.internal
import init.native.procedure
import init.native.config

namespace native

meta structure pass :=
  (name : string)
  (transform : config → procedure → procedure)

meta def file_name_for_dump (p : pass) :=
  (pass.name p)

-- Unit functions get optimized away, need to talk to Leo about this one.
meta def run_pass (conf : config) (p : pass) (proc : procedure) : (format × procedure × format) :=
  let result := pass.transform p conf proc in
  (repr proc, result, repr result)

meta def collect_dumps {A : Type} : list (format × A × format) → format × list A × format
| [] := (format.nil, [], format.nil)
| ((pre, body, post) :: fs) :=
  let (pre', bodies, post') := collect_dumps fs
  in (pre ++ format.line ++ format.line ++ pre',
      body :: bodies,
      post ++ format.line ++ format.line ++ post')

meta def inner_loop_debug (conf : config) (p : pass) (es : list procedure) : list procedure :=
  let (pre, bodies, post) := collect_dumps (list.map (fun e, run_pass conf p e) es) in
  match native.dump_format (file_name_for_dump p ++ ".pre") pre with
  | n := match native.dump_format (file_name_for_dump p ++ ".post") post with
         | m := if n = m then bodies else bodies
         end
  end

meta def inner_loop (conf : config) (p : pass) (es : list procedure) : list procedure :=
  if config.debug conf
  then inner_loop_debug conf p es
  else list.map (fun proc, pass.transform p conf proc) es

meta def run_passes (conf : config) (passes : list pass) (procs : list procedure) : list procedure :=
  list.foldl (fun pass procs, inner_loop conf procs pass) procs passes

end native
