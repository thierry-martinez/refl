type 'a u = {
    f : 'b . 'a -> 'b -> 'a * 'b
  }
      [@@deriving refl]

let () =
  let u = { f = fun x y -> (succ x, y) } in
  let u' =
    Refl.map [%refl: _ u] [%refl: _ u] [PN (string_of_int, int_of_string)] u in
  assert (u'.f "1" true = ("2", true));
  assert (u'.f "3" 2.5 = ("4", 2.5));
  assert (Refl.show [%refl: _ u] [None] u' = "{ f = <fun> }")

type 'a v =
  | A of {
      a : float;
      f : 'b . 'a -> 'b -> 'a * 'b;
    }
  | B of {
      x : int;
      f : 'b . 'a -> 'b -> 'a * 'b;
      g : 'b . bool -> 'b -> 'b -> 'b;
    }
      [@@deriving refl]
