type ('a, 'b) t =
  | A of 'a
  | B of 'b option [@@deriving refl]

type 'a u = ('a, int) t
  [@@deriving refl]
