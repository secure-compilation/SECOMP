let inc_ref x = x := !x + 1
let sum_refs xs = List.fold_left (fun acc el -> acc + !el) 0 xs

let trace_len_min = ref Int.max_int
let trace_len_max = ref Int.min_int
let trace_calls = ref 0
let trace_rets = ref 0
let trace_builtins = ref 0

let register_trace trace =
  trace_len_min := Int.min (List.length trace) !trace_len_min;
  trace_len_max := Int.max (List.length trace) !trace_len_max;
  let analyse_event = function
    | BtInfoAsm.Bundle_call _ -> inc_ref trace_calls
    | BtInfoAsm.Bundle_return _ -> inc_ref trace_rets
    | BtInfoAsm.Bundle_builtin _ -> inc_ref trace_builtins
  in
  List.iter (fun (_, event) -> analyse_event event) trace

let print_trace_stats () =
  Printf.printf "Traces:\n";
  Printf.printf "  Min length: %d\n" !trace_len_min;
  Printf.printf "  Max length: %d\n" !trace_len_max;
  Printf.printf "  Calls: %d\n" !trace_calls;
  Printf.printf "  Returns: %d\n" !trace_rets;
  Printf.printf "  Builtins: %d\n" !trace_builtins

let min_comps = ref Int.max_int
let max_comps = ref Int.min_int
let min_glob_vars = ref Int.max_int
let max_glob_vars = ref Int.min_int

let register_asm_prog asm_prog =
  let count_if pred xs = List.length (List.filter pred xs) in
  let is_glob_var = function
    | AST.Gfun _ -> false
    | AST.Gvar _ -> true
  in
  let exports = AST.Policy.policy_export asm_prog.AST.prog_pol in
  let num_comps = List.length (Maps.PTree.elements exports) in
  let num_glob_vars = count_if (fun (_, def) -> is_glob_var def) asm_prog.AST.prog_defs in
  min_comps := Int.min num_comps !min_comps;
  max_comps := Int.max num_comps !max_comps;
  min_glob_vars := Int.min num_glob_vars !min_glob_vars;
  max_glob_vars := Int.max num_glob_vars !max_glob_vars

let print_asm_prog_stats () =
  Printf.printf "ASM Programs:\n";
  Printf.printf "  Min compartments: %d\n" !min_comps;
  Printf.printf "  Max compartments: %d\n" !max_comps;
  Printf.printf "  Min global vars: %d\n" !min_glob_vars;
  Printf.printf "  Max global vars: %d\n" !max_glob_vars

let mem_delta_len_max = ref Int.min_int
let mem_delta_len_min = ref Int.max_int
let mem_delta_storev = ref 0
let mem_delta_store = ref 0
let mem_delta_bytes = ref 0
let mem_delta_alloc = ref 0
let mem_delta_free = ref 0

let register_mem_delta md =
  mem_delta_len_max := Int.max (List.length md) !mem_delta_len_max;
  mem_delta_len_min := Int.min (List.length md) !mem_delta_len_min;
  let analyse_kinds = function
    | MemoryDelta.Coq_mem_delta_kind_storev _ -> inc_ref mem_delta_storev
    | MemoryDelta.Coq_mem_delta_kind_store _ -> inc_ref mem_delta_store
    | MemoryDelta.Coq_mem_delta_kind_bytes _ -> inc_ref mem_delta_bytes
    | MemoryDelta.Coq_mem_delta_kind_alloc _ -> inc_ref mem_delta_alloc
    | MemoryDelta.Coq_mem_delta_kind_free _ -> inc_ref mem_delta_free
  in
  List.iter analyse_kinds md

let print_mem_delta_stats () =
  Printf.printf "Memory Deltas:\n";
  Printf.printf "  Total: %d\n" (sum_refs [mem_delta_storev; mem_delta_store; mem_delta_bytes; mem_delta_alloc; mem_delta_free]);
  Printf.printf "  Min length: %d\n" !mem_delta_len_min;
  Printf.printf "  Max length: %d\n" !mem_delta_len_max;
  Printf.printf "  StoreV: %d\n" !mem_delta_storev;
  Printf.printf "  Store: %d\n" !mem_delta_store;
  Printf.printf "  Bytes: %d\n" !mem_delta_bytes;
  Printf.printf "  Alloc: %d\n" !mem_delta_alloc;
  Printf.printf "  Free: %d\n" !mem_delta_free

let ef_external = ref 0
let ef_builtin = ref 0
let ef_runtime = ref 0
let ef_vload = ref 0
let ef_vstore = ref 0
let ef_malloc = ref 0
let ef_free = ref 0
let ef_memcpy = ref 0
let ef_annot = ref 0
let ef_annot_val = ref 0
let ef_inline_asm = ref 0
let ef_debug = ref 0

let register_external_function = function
  | AST.EF_external _ -> inc_ref ef_external
  | AST.EF_builtin _ -> inc_ref ef_builtin
  | AST.EF_runtime _ -> inc_ref ef_runtime
  | AST.EF_vload _ -> inc_ref ef_vload
  | AST.EF_vstore _ -> inc_ref ef_vstore
  | AST.EF_malloc -> inc_ref ef_malloc
  | AST.EF_free -> inc_ref ef_free
  | AST.EF_memcpy _ -> inc_ref ef_memcpy
  | AST.EF_annot _ -> inc_ref ef_annot
  | AST.EF_annot_val _ -> inc_ref ef_annot_val
  | AST.EF_inline_asm _ -> inc_ref ef_inline_asm
  | AST.EF_debug _ -> inc_ref ef_debug

let print_ef_stats () =
  Printf.printf "External Functions:\n";
  Printf.printf "  Total: %d\n" (sum_refs [ef_external; ef_builtin; ef_runtime; ef_vload; ef_vstore; ef_malloc; ef_free; ef_memcpy; ef_annot; ef_annot_val; ef_inline_asm; ef_debug]);
  Printf.printf "  EF_external: %d\n" !ef_external;
  Printf.printf "  EF_builtin: %d\n" !ef_builtin;
  Printf.printf "  EF_runtime: %d\n" !ef_runtime;
  Printf.printf "  EF_vload: %d\n" !ef_vload;
  Printf.printf "  EF_vstore: %d\n" !ef_vstore;
  Printf.printf "  EF_malloc: %d\n" !ef_malloc;
  Printf.printf "  EF_free: %d\n" !ef_free;
  Printf.printf "  EF_memcpy: %d\n" !ef_memcpy;
  Printf.printf "  EF_annot: %d\n" !ef_annot;
  Printf.printf "  EF_annot_val: %d\n" !ef_annot_val;
  Printf.printf "  EF_inline_asm: %d\n" !ef_inline_asm;
  Printf.printf "  EF_debug: %d\n" !ef_debug

let print_stats () =
  print_trace_stats ();
  print_asm_prog_stats ();
  print_mem_delta_stats ();
  print_ef_stats ()

