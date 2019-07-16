type 'a t =
  | Leaf
  | Node of { left : 'a t; label : 'a; right : 'a t }
        [@@deriving refl]
