type t = {
    a : int;
    b : string list [@refl.default ["hello"]];
  } [@@deriving refl]

let () =
  assert (
    let r = Refl.make [%refl: t] ([
        "a", Refl.F ([%refl: int], 1);
        "b", F ([%refl: string list], ["a"; "b"]);
      ] |> List.to_seq |> Refl.StringMap.of_seq) in
    r = { a = 1; b = ["a"; "b"] })

let () =
  assert (
    let r = Refl.make [%refl: t] ([
        "a", Refl.F ([%refl: int], 1);
      ] |> List.to_seq |> Refl.StringMap.of_seq) in
    r = { a = 1; b = ["hello"] })
