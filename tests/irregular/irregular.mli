type 'a t =
  | Tree of 'a
  | Level of ('a * 'a) t
        [@@deriving refl]
