type 'a t =
  | Tree of 'a
  | Level of ('a * 'a) t
        [@@deriving refl]

let () =
  assert (Refl.map [%refl: _ t] [%refl: _ t] [P string_of_int]
    (Level (Level (Tree ((1, 2), (3, 4))))) =
    (Level (Level (Tree (("1", "2"), ("3", "4"))))))

let () =
  assert (Refl.show [%refl: _ t] [Some Format.pp_print_int]
    (Level (Level (Tree ((1, 2), (3, 4))))) =
      "Level (Level (Tree (((1, 2), (3, 4)))))")
