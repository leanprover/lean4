(* https://github.com/ocaml-bench/sandmark/blob/c668eb05aebb1dc9f57f322399bea7182640518c/benchmarks/multicore-numerical/binarytrees5_multicore.ml *)
module T = Domainslib.Task

let num_domains = try int_of_string Sys.argv.(1) with _ -> 1
let max_depth = try int_of_string Sys.argv.(2) with _ -> 10

type 'a tree = Empty | Node of 'a tree * 'a tree

let rec make d =
(* if d = 0 then Empty *)
  if d = 0 then Node(Empty, Empty)
  else let d = d - 1 in Node(make d, make d)

let rec check t =
  match t with
  | Empty -> 0
  | Node(l, r) -> 1 + check l + check r

let min_depth = 4
let max_depth = max (min_depth + 2) max_depth
let stretch_depth = max_depth + 1

let () =
  (* Gc.set { (Gc.get()) with Gc.minor_heap_size = 1024 * 1024; max_overhead = -1; }; *)
  let _ = check (make stretch_depth) in
  ()
  (* Printf.printf "stretch tree of depth %i\t check: %i\n" stretch_depth c *)

let long_lived_tree = make max_depth

let values = Array.make num_domains 0

let calculate d st en ind =
  (* Printf.printf "st = %d en = %d\n" st en; *)
  let c = ref 0 in
  for _ = st to en do
  c := !c + check (make d)
  done;
  (* Printf.printf "ind = %d\n" ind; *)
  values.(ind) <- !c

let loop_depths d pool =
  for i = 0 to  ((max_depth - d) / 2 + 1) - 1 do
    let d = d + i * 2 in
    let niter = 1 lsl (max_depth - d + min_depth) in
    let rec loop acc i num_domains =
      if i = num_domains then begin
        List.rev acc |> List.iter (fun pr -> T.await pool pr)
      end else begin
        loop
          ((T.async pool (fun _ ->
            calculate d (i * niter / num_domains) (((i + 1) * niter / num_domains) - 1) i)) :: acc) 
          (i + 1)
          num_domains
        end in

    loop [] 0 num_domains;
    let _ = Array.fold_left (+) 0 values in
    ()
    (* Printf.printf "%i\t trees of depth %i\t check: %i\n" niter d sum *)
  done

let () =
  let pool = T.setup_pool ~num_domains:(num_domains - 1) () in
  T.run pool (fun _ -> loop_depths min_depth pool);
  let _ = max_depth in
  let _ = (check long_lived_tree) in
  T.teardown_pool pool
