type 'a t = A
      [@@deriving refl]

type 'a u =
  | A of 'a t
  | B of 'a
      [@@deriving refl]

type v =
  | A of int u
      [@@deriving refl]
