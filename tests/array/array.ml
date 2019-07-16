let () =
  assert
    (Refl.map [%refl: _ array] [%refl: _ array] [P string_of_int] [|1; 2; 3|]
       = [|"1"; "2"; "3"|])

let () =
  assert
    (Refl.compare [%refl: _ array] [Some Stdlib.compare]
       [|1; 2; 4|] [|1; 2; 3|] = 1)

let () =
  assert
    (Refl.compare [%refl: _ array] [Some Stdlib.compare]
       [|1; 2; 2|] [|1; 2; 3|] = -1)

let () =
  assert
    (Refl.compare [%refl: _ array] [Some Stdlib.compare]
       [|1; 2; 3|] [|1; 2; 3|] = 0)

let () =
  assert (Refl.show [%refl: string array] [] [|"a"; "b"|] = {|[|"a"; "b"|]|})
