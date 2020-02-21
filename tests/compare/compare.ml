let () =
  assert
    (Refl.compare [%refl: _ list] [Some Stdcompat.Int.compare] [1; 2; 3]
      [1; 2; 3] = 0)
