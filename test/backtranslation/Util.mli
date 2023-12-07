val choose_disjoint : int -> int -> 'a list -> 'a list list QCheck.Gen.t
(* Sample n disjoint, non-empty subsets of size at most k from xs *)

val sublist : 'a list -> 'a list QCheck.Gen.t
(* Sample a non-empty subset from a given list *)
