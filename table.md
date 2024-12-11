<div>

# Artifact {#artifact .page-title}

</div>

::: page-body
# Correctness: folder or branch `ccs-main` {#7071474a-5ac4-42f2-9913-d3769c176851}

## Generic Claims {#7eb3510e-9cc5-4990-a213-ba7b2170df9d}

  Claim                                                             File                  Location in file                                                                             Notes
  ----------------------------------------------------------------- --------------------- -------------------------------------------------------------------------------------------- ----------------------------------------------------------------------------------------------------------------------------------------------
  Compartment model                                                 common/AST.v          Module `COMP`                                                                                
  Compartments                                                      common/AST.v          Definition `compartment`                                                                     
  Interfaces                                                        common/AST.v          Module `Policy`                                                                              
  Programs                                                          common/AST.v          Record `program`                                                                             Standard CompCert definition with the addition of a `Policy.t`(interface) component, properties related to well-formedness of this component
  Assignment of compartment to definitions and objects              common/AST.v          Typeclass `has_comp`                                                                         This is defined as a typeclass because the type of functions varies.
  Interface checks: definition of allowed cross-compartment calls   common/Globalenvs.v   Definition `allowed_cross_call`                                                              
  Interface checks: allowed calls                                   common/Globalenvs.v   Definition `allowed_call`                                                                    Builds on top of the previous definition to allow for intra-compartment calls
  Interface checks: preservation by compilation of allowed calls    common/Globalenvs.v   Theorems `match_genvs_allowed_calls`, `allowed_call_transf_partial`, `allowed_call_transf`   
  Trace events                                                      common/Events.v       Definition `event`                                                                           
  Properties of system calls                                        common/Events.v       Record `extcall_properties`                                                                  
  Generation of the new trace events                                common/Events.v       Definitions `call_trace` and `return_trace`                                                  
  Memory containing compartment information                         common/Memory.v       Record `mem'` and in particular field `mem_compartments`                                     
  Memory operations require compartment permissions                 common/Memory.v       Definition `valid_access`                                                                    Given by the conjunct `can_access_block m b cp` meaning that `cp` can access the block `b` in memory `m`
  Registers are all caller saved                                                                                                                                                       

## How to check changes to CompCert's languages {#b79c5752-b66c-4758-a1f9-5dc7e09862b8}

All the languages are changed in similar ways. As such, we describe the
location of the changes on the Cminor language, and invite the reviewers
to check the other languages if they wish to do so.

  Claim                                                     File                         Location in file                                                                                                                                                                                                                         Notes
  --------------------------------------------------------- ---------------------------- ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- ----------------------------------------------------------------------------
  Interface checks at the point of calls and returns        backend/Cminor.v             In `step`, conditions `(ALLOWED: Genv.allowed_call ge (comp_of f) vf)` for calls.                                                                                                                                                        There is no check for allowed returns in most languages, including Cminor.
  Cross-compartment calls and returns don't pass pointers   backend/Cminor.v             In `step`, conditions `(NO_CROSS_PTR: Genv.type_of_call (comp_of f) (comp_of fd) = Genv.CrossCompartmentCall -> Forall not_ptr vargs)` and `(NO_CROSS_PTR: Genv.type_of_call (comp_of f) cp = Genv.CrossCompartmentCall -> not_ptr v)`   
  Generation of events                                      backend/Cminor.v             In `step`, condition `(EV: call_trace ge (comp_of f) (comp_of fd) vf vargs (sig_args sig) t)` and `(EV: return_trace ge (comp_of f) cp v ty t)`                                                                                          
  Correctness of the pass from Csharpminor to Cminor        cfrontend/Cminorgenproof.v   Entire file. The most important theorem is the theorem `transl_step_correct`                                                                                                                                                             

## Recomposition: folder or branch `ccs-main` {#6a3fbff0-9339-4c98-b10d-3333a5a95645}

  Claim                                                 File                       Location in file                                                    Notes
  ----------------------------------------------------- -------------------------- ------------------------------------------------------------------- -------
  Three-way simulation                                  common/Smallstep.v         Definition `tsim_properties`                                        
  Three-way simulation implies preservation of traces   common/Smallstep.v         Theorem `tsimulation_star`                                          
  Simulation diagrams                                   common/Smallstep.v         Section `THREEWAY_SIMU_DIAGRAM`                                     
  Proof of recomposition                                security/Recomposition.v   Theorems `simulation`, `step_E0_strong`, `step_E0_weak`, `step_t`   

## Language-specific claims {#8e8cd141-be2c-485d-b848-2d9f8f3d309d}

  Claim                                              File                       Location in file             Notes
  -------------------------------------------------- -------------------------- ---------------------------- ----------------------------------------------------------------------------------------------------------------------------------------------------------------
  Cross-compartment inlining disabled                backend/Inlining.v         Definition `can_inline`      This comes from the check `cp_eq_dec cp (comp_of f)`
  Cross-compartment tailcall optimization disabled   backend/Tailcall.v         Definition `transf_instr`    The `Itailcall` instruction is only generated when the condition `intra_compartment_call` holds.
  Cross-compartment tailcalls disabled               All languages definition   Semantics of the languages   When a tailcall instruction exists, then the semantics prevent it from being executed cross-compartment by having a condition `(COMP: comp_of fd = comp_of f)`

# Back-translation: folder or branch `ccs-backtranslation` {#788a3b83-9095-47b9-af7a-6deff08c2b48}

  Claim                                                                          File                               Location in file                                                 Notes
  ------------------------------------------------------------------------------ ---------------------------------- ---------------------------------------------------------------- ---------------------------------------------------------------------
  Informative events                                                             security/BtInfoAsm.v               Definition `bundle_event`                                        This is a more general version of the events presented in the paper
  Well-formed informative trace                                                  security/BtInfoAsm.v               Definition `istar` and `ir_step`                                 
  Memory deltas                                                                  security/MemoryDelta.v             Section `MEMDELTA`, definitions `mem_delta_kind` , `mem_delta`   
  Existence of a well-formed informative trace corresponding to a trace prefix   security/BtInfoAsm.v               Theorem `asm_to_ir`                                              
  Back-translation function on informative traces                                security/Backtranslation.v         Definition `gen_program`                                         
  Correctness of the back-translation from the intermediate language to Clight   security/BacktranslationProof.v    Definition `ir_to_clight`                                        
  Correctness of the back-translation                                            security/BacktranslationProof2.v   Theorem `backtranslation_proof`                                  

# Blame: folder or branch `ccs-blame` {#d8fe786d-136b-4a8f-bf55-f4e35c83be5a}

  ---------------------------------------------------------------------------------
  Claim             File               Location in file        Notes
  ----------------- ------------------ ----------------------- --------------------
  Main blame        security/Blame.v   Theorem                 
  theorem                              `does_prefix_star`      

  Definition 6:     security/Blame.v   Theorem `blame_program` Follows directly
  Blame                                                        from
                                                               `does_prefix_star`

  Full program run  security/Blame.v   Theorems                
  lemmas                               `parallel_exec` and\    
                                       \                       
                                       `parallel_exec'`.       

  Synchronized      security/Blame.v   Theorems                
  execution lemmas                     `parallel_star_E0`\     
                                       and\                    
                                       `parallel_exec1`        

  Stepwise lemmas   security/Blame.v   Theorems                
                                       `parallel_concrete`     
                                       and\                    
                                       \                       
                                       `parallel_abstract_t`   
  ---------------------------------------------------------------------------------
:::

[]{.sans style="font-size:14px;padding-top:2em"}
