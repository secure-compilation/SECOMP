(*val trace : Events.event list QCheck.Gen.t *)
val bundle_trace : Gen_ctx.t -> BtInfoAsm.bundle_trace QCheck.Gen.t
val asm_program : Gen_ctx.gen_config -> (Asm.program * Gen_ctx.t) QCheck.Gen.t
