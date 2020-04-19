module Map = Map.Make (String)

type ('a, 'b) t = {
    map : ('a Map.t [@opaque]);
    payload : 'b;
  } [@@deriving refl]

type 'a u = (int, 'a) t
       [@@deriving refl]
