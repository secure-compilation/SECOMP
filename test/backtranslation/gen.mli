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

val trace : Events.event list QCheck.Gen.t
val sublist : 'a list -> 'a list QCheck.Gen.t

val policy :
  (Graph.t * int list Array.t * int list Array.t Array.t) QCheck.Gen.t
