open Prove_rewrite

let () =
  if Array.length Sys.argv <> 3 then (
    prerr_endline "Usage: rewrite_prove.exe <src.ml> <dst.ml>";
    exit 2
  );

  let src = Sys.argv.(1) in
  let dst = Sys.argv.(2) in
  Ocaml_prove_rewrite.rewrite_file ~src ~dst
