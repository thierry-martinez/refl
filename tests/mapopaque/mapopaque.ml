module Map = Map.Make (String)

type ('a, 'b) t = {
    map : ('a Map.t [@mapopaque]);
    payload : 'b;
  } [@@deriving refl]
