type t

val random : int -> Random.State.t -> t
val size : t -> int
val vertices : t -> int list
val is_adjacent : int -> int -> t -> bool
val to_dot : t -> string
