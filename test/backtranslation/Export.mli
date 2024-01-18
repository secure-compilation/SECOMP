(** Export a Clight program in raw form and as (valid) compilable C code.
    The exported code is written to the given filename and the suffix .raw
    is used to indicate the raw variant. *)
val c_light_prog : Clight.program -> string -> unit
