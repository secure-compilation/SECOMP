let fmt = Printf.sprintf

let from_str_formatter p x =
  ignore (Format.flush_str_formatter ());
  p Format.str_formatter x;
  Format.flush_str_formatter()

let show_ident i = fmt "%d" (Camlcoq.P.to_int i)

let show_event e = from_str_formatter Interp.print_event e

let show_trace t =
  fmt "[\n%s\n  ]" (String.concat "\n" (List.map show_event t))

let show_eventval ev = from_str_formatter Interp.print_eventval ev

let show_eventval_list el = from_str_formatter Interp.print_eventval_list el

let show_signature _ = "<signature>"

let show_mem_chunk = function
  | AST.Mint8signed -> "Mint8signed"
  | AST.Mint8unsigned -> "Mint8unsigned"
  | AST.Mint16signed -> "Mint16signed"
  | AST.Mint16unsigned -> "Mint16unsigned"
  | AST.Mint32 -> "Mint32"
  | AST.Mint64 -> "Mint64"
  | AST.Mfloat32 -> "Mfloat32"
  | AST.Mfloat64 -> "Mfloat64"
  | AST.Many32 -> "Many32"
  | AST.Many64 -> "Many64"

let show_block b = fmt "%d" (Camlcoq.P.to_int b)

let show_coq_z z = fmt "%d" (Camlcoq.Z.to_int z)

let show_float f = "<float>"

let show_coq_val = function
  | Values.Vundef -> "undef"
  | Values.Vint i -> fmt "%s" (show_coq_z i)
  | Values.Vlong i -> fmt "%s" (show_coq_z i)
  | Values.Vfloat f -> fmt "%s" (show_float f)
  | Values.Vsingle f -> fmt "%s" (show_float f)
  | Values.Vptr (b, o) -> fmt "(%s, %s)" (show_block b) (show_coq_z o)

let show_comp = function
  | AST.COMP.Coq_bottom' -> "_bottom_"
  | AST.COMP.Coq_top' -> "_top_"
  | AST.COMP.Comp i -> show_ident i

let show_nat n = fmt "%d" (Camlcoq.Nat.to_int n)

let show_quantity = function
  | Memdata.Q32 -> "Q32"
  | Memdata.Q64 -> "Q64"

let show_memval = function
  | Memdata.Undef -> "Undef"
  | Memdata.Byte b -> fmt "%s" (show_coq_z b)
  | Memdata.Fragment (cv, q, n) -> fmt "(%s, %s, %s)" (show_coq_val cv) (show_quantity q) (show_nat n)

let show_memval_list mvl = String.concat "\n" (List.map show_memval mvl)

let show_mem_delta_storev (((chunk, addr), value), comp) =
  fmt "{ Storev | chunk = %s; addr = %s; value = %s; comp = %s }"
    (show_mem_chunk chunk)
    (show_coq_val addr)
    (show_coq_val value)
    (show_comp comp)

let show_mem_delta_store ((((chunk, block), offset), value), comp) =
  fmt "{ Store | chunk = %s; block = %s; offset = %s, value = %s; comp = %s }"
    (show_mem_chunk chunk)
    (show_block block)
    (show_coq_z offset)
    (show_coq_val value)
    (show_comp comp)

let show_mem_delta_bytes (((block, offset), bytes), comp) =
  fmt "{ Bytes | block = %s; offset = %s, bytes = %s; comp = %s }"
    (show_block block)
    (show_coq_z offset)
    (show_memval_list bytes)
    (show_comp comp)

let show_mem_delta_alloc ((comp, lower), upper) =
  fmt "{ Alloc | comp = %s; lower = %s; upper = %s }"
    (show_comp comp)
    (show_coq_z lower)
    (show_coq_z upper)

let show_mem_delta_free (((block, lower), upper), comp) =
  fmt "{ Free | block = %s; comp = %s; lower = %s; upper = %s }"
    (show_block block)
    (show_coq_z lower)
    (show_coq_z upper)
    (show_comp comp)

let show_mem_delta_kind mdk =
  let open MemoryDelta in
  match mdk with
  | Coq_mem_delta_kind_storev md -> show_mem_delta_storev md
  | Coq_mem_delta_kind_store md -> show_mem_delta_store md
  | Coq_mem_delta_kind_bytes md -> show_mem_delta_bytes md
  | Coq_mem_delta_kind_alloc md -> show_mem_delta_alloc md
  | Coq_mem_delta_kind_free md -> show_mem_delta_free md

let show_memdelta md = fmt "[\n%s\n  ]" (String.concat "\n" (List.map show_mem_delta_kind md))

let show_external_func _ = "<external_func>"

let show_bundle_event e =
  let open BtInfoAsm in
  match e with
  | _, Bundle_call (subtrace, ident, args, sign, memdelta) ->
     fmt "Call\n  subtrace: %s\n  ident: %s\n  args:%s\n  signature: %s\n  mem_delta: %s\n"
       (show_trace subtrace)
       (show_ident ident)
       (show_eventval_list args)
       (show_signature sign)
       (show_memdelta memdelta)
  | _, Bundle_return (subtrace, ret_val, memdelta) ->
     fmt "Ret\n  subtrace: %s\n  ret_val: %s\n  mem_delta: %s\n"
       (show_trace subtrace)
       (show_eventval ret_val)
       (show_memdelta memdelta)
  | _, Bundle_builtin (subtrace, external_func, args, memdelta) ->
     fmt "Builtin\n  subtrace: %s\n  external_func:  %s\n  arg: %s\n  mem_delta: %s\n"
       (show_trace subtrace)
       (show_external_func external_func)
       (show_eventval_list args)
       (show_memdelta memdelta)

let show_bundle_trace t = String.concat "\n" (List.map show_bundle_event t)

let show_c_light_program prog =
  let version = PrintClight.Clight1 in
  from_str_formatter (PrintClight.print_program version) prog
