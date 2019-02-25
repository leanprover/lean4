(* The Computer Language Benchmarks Game
 * https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
 *
 * Contributed by Troestler Christophe
 * Rough parallelization by Mauricio Fernandez
 * *reset*
 *)

type 'a tree = Empty | Node of 'a tree * 'a tree

let rec make d =
(* if d = 0 then Empty *)
  if d = 0 then Node(Empty, Empty)
  else let d = d - 1 in Node(make d, make d)

let rec check = function Empty -> 0 | Node(l, r) -> 1 + check l + check r

let min_depth = 4
let max_depth = (let n = try int_of_string(Array.get Sys.argv 1) with _ -> 10 in
                 max (min_depth + 2) n)
let stretch_depth = max_depth + 1

let () =
  (* Gc.set { (Gc.get()) with Gc.minor_heap_size = 1024 * 1024; max_overhead = -1; }; *)
  let c = check (make stretch_depth) in
  Printf.printf "stretch tree of depth %i\t check: %i\n" stretch_depth c

let long_lived_tree = make max_depth

let rec loop_depths d =
  let worker d =
    let niter = 1 lsl (max_depth - d + min_depth) and c = ref 0 in
    for i = 1 to niter do c := !c + check(make d) done;
    (niter, !c) in
  let workers = Array.init ((max_depth - d) / 2 + 1)
                  (fun i -> let d = d + i * 2 in (d, invoke worker d))
  in Array.iter
       (fun (d, w) ->
          let niter, c = w () in
          Printf.printf "%i\t trees of depth %i\t check: %i\n" niter d c)
       workers

(* function originally due to Jon D. Harrop *)
and invoke (f : 'a -> 'b) x : unit -> 'b =
  let input, output = Unix.pipe() in
  match Unix.fork() with
  | -1 -> Unix.close input; Unix.close output; (let v = f x in fun () -> v)
  | 0 ->
      Unix.close input;
      let output = Unix.out_channel_of_descr output in
      Marshal.to_channel output (try `Res(f x) with e -> `Exn e) [];
      close_out output;
      exit 0
  | pid ->
      Unix.close output;
      let input = Unix.in_channel_of_descr input in
      fun () ->
        let v = Marshal.from_channel input in
        ignore (Unix.waitpid [] pid);
        close_in input;
        match v with
        | `Res x -> x
        | `Exn e -> raise e

let () =
  flush stdout;
  loop_depths min_depth;
  Printf.printf "long lived tree of depth %i\t check: %i\n"
    max_depth (check long_lived_tree)
