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

let print_trace_stats out_channel =
  Printf.fprintf out_channel "Traces:\n";
  Printf.fprintf out_channel "  Min length: %d\n" !trace_len_min;
  Printf.fprintf out_channel "  Max length: %d\n" !trace_len_max;
  Printf.fprintf out_channel "  Calls: %d\n" !trace_calls;
  Printf.fprintf out_channel "  Returns: %d\n" !trace_rets;
  Printf.fprintf out_channel "  Builtins: %d\n" !trace_builtins

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

let print_asm_prog_stats out_channel =
  Printf.fprintf out_channel "ASM Programs:\n";
  Printf.fprintf out_channel "  Min compartments: %d\n" !min_comps;
  Printf.fprintf out_channel "  Max compartments: %d\n" !max_comps;
  Printf.fprintf out_channel "  Min global vars: %d\n" !min_glob_vars;
  Printf.fprintf out_channel "  Max global vars: %d\n" !max_glob_vars

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

let print_mem_delta_stats out_channel =
  Printf.fprintf out_channel "Memory Deltas:\n";
  Printf.fprintf out_channel "  Total: %d\n" (sum_refs [mem_delta_storev; mem_delta_store; mem_delta_bytes; mem_delta_alloc; mem_delta_free]);
  Printf.fprintf out_channel "  Min length: %d\n" !mem_delta_len_min;
  Printf.fprintf out_channel "  Max length: %d\n" !mem_delta_len_max;
  Printf.fprintf out_channel "  StoreV: %d\n" !mem_delta_storev;
  Printf.fprintf out_channel "  Store*: %d\n" !mem_delta_store;
  Printf.fprintf out_channel "  Bytes*: %d\n" !mem_delta_bytes;
  Printf.fprintf out_channel "  Alloc*: %d\n" !mem_delta_alloc;
  Printf.fprintf out_channel "  Free*: %d\n" !mem_delta_free

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

let print_ef_stats out_channel =
  Printf.fprintf out_channel "External Functions:\n";
  Printf.fprintf out_channel "  Total: %d\n" (sum_refs [ef_external; ef_builtin; ef_runtime; ef_vload; ef_vstore; ef_malloc; ef_free; ef_memcpy; ef_annot; ef_annot_val; ef_inline_asm; ef_debug]);
  Printf.fprintf out_channel "  EF_external: %d\n" !ef_external;
  Printf.fprintf out_channel "  EF_builtin: %d\n" !ef_builtin;
  Printf.fprintf out_channel "  EF_runtime: %d\n" !ef_runtime;
  Printf.fprintf out_channel "  EF_vload: %d\n" !ef_vload;
  Printf.fprintf out_channel "  EF_vstore: %d\n" !ef_vstore;
  Printf.fprintf out_channel "  EF_malloc: %d\n" !ef_malloc;
  Printf.fprintf out_channel "  EF_free: %d\n" !ef_free;
  Printf.fprintf out_channel "  EF_memcpy: %d\n" !ef_memcpy;
  Printf.fprintf out_channel "  EF_annot: %d\n" !ef_annot;
  Printf.fprintf out_channel "  EF_annot_val: %d\n" !ef_annot_val;
  Printf.fprintf out_channel "  EF_inline_asm: %d\n" !ef_inline_asm;
  Printf.fprintf out_channel "  EF_debug: %d\n" !ef_debug;
  Printf.fprintf out_channel "\n\nNote: the entries marked with * are ignored (or trivial) in the backtranslation.\n"

let print_stats out_channel =
  print_trace_stats out_channel;
  print_asm_prog_stats out_channel;
  print_mem_delta_stats out_channel;
  print_ef_stats out_channel

