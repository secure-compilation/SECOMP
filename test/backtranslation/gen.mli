val memory_chunk : AST.memory_chunk QCheck.Gen.t
val positive : BinNums.positive QCheck.Gen.t
val coq_Z : BinNums.coq_Z QCheck.Gen.t
val ident : AST.ident QCheck.Gen.t
val compartment : AST.compartment QCheck.Gen.t
val ptrofs : Integers.Ptrofs.int QCheck.Gen.t
val char_list : char list QCheck.Gen.t
val binary_float : Floats.float QCheck.Gen.t
val eventval : Events.eventval QCheck.Gen.t
val event_syscall : int QCheck.Gen.t -> Events.event QCheck.Gen.t
val event_vload : Events.event QCheck.Gen.t
val event_vstore : Events.event QCheck.Gen.t
val event_annot : int QCheck.Gen.t -> Events.event QCheck.Gen.t

val event_call :
  AST.compartment ->
  AST.compartment ->
  int QCheck.Gen.t ->
  Events.event QCheck.Gen.t

val event_return :
  AST.compartment -> AST.compartment -> Events.event QCheck.Gen.t

val typ : AST.typ QCheck.Gen.t
val rettype : AST.rettype QCheck.Gen.t
val calling_convention : AST.calling_convention QCheck.Gen.t
val signature : AST.signature QCheck.Gen.t
val mem_delta : MemoryDelta.mem_delta QCheck.Gen.t
val trace : Events.event list QCheck.Gen.t
val sublist : 'a list -> 'a list QCheck.Gen.t
val external_function : AST.external_function QCheck.Gen.t
val bundle_call : BtInfoAsm.bundle_event QCheck.Gen.t
val bundle_return : BtInfoAsm.bundle_event QCheck.Gen.t
val bundle_builtin : BtInfoAsm.bundle_event QCheck.Gen.t
val bundle_event : BtInfoAsm.bundle_event QCheck.Gen.t
val bundle_trace : BtInfoAsm.bundle_trace QCheck.Gen.t

val policy : (int * int list) list -> (int * (int * int) list) list -> AST.Policy.t QCheck.Gen.t

val asm_program : Asm.program QCheck.Gen.t
