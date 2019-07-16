type 'a t = < value : 'a; show : 'a -> string >
    [@@deriving refl]

let () =
  let o =
    Refl.map [%refl: _ t] [%refl: _ t] [PN (int_of_float, float_of_int)] (object
      method value = 1.
      method show = string_of_float
    end) in
  assert (o#show (succ o#value) = "2.")
