module Make (T : Map.OrderedType) : sig
  type t = {
      count : int;
      map : int Map.Make (T).t;
    }

  val empty : t

  val of_fresh : int -> t

  val to_map : t -> int Map.Make (T).t

  val count : t -> int

  val fresh : t -> int * t

  val force_add : T.t -> t -> int * t

  val mem : T.t -> t -> bool

  val find : T.t -> t -> int

  val find_opt : T.t -> t -> int option

  val add : T.t -> t -> int * t

  val of_list : T.t option list -> t

  val union : t -> t -> t
end
