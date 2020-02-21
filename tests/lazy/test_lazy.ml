let () =
  let refl = [%refl: _ Lazy.t * int Lazy.t] in
  let (a, b) = Refl.map refl refl [P string_of_int]
    (lazy (1 + 1), lazy (1 + 2)) in
  assert (not (Lazy.is_val a));
  assert (Lazy.force a = "2");
  assert (not (Lazy.is_val b));
  assert (Lazy.force b = 3)
