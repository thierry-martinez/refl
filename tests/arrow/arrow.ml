let () =
  let refl = [%refl: 'a -> 'a] in
  let f = Refl.map refl refl [PN (string_of_int, int_of_string)] succ in
  assert (f "3" = "4")

(* Ill-typed:
let () =
  let refl = [%refl: 'a -> 'a] in
  let _ = Refl.compare refl [Int.compare] in
  ()
*)

let () =
  let refl = [%refl: ('a -> 'a) [@mapopaque]] in
  assert (Refl.compare refl [None] succ pred = 0);
  ()

let () =
  let refl = [%refl: l:'a -> 'b] in
  let f =
    Refl.map refl refl [N int_of_string; P string_of_int]
      (fun ~l:x -> succ x) in
  assert (f ~l:"3" = "4")

let () =
  let refl = [%refl: ?l:'a -> unit -> 'b] in
  let f =
    Refl.map refl refl [N int_of_string; P string_of_int]
      (fun ?l:(x = 0) () -> succ x) in
  assert (f ~l:"3" () = "4");
  assert (f () = "1")

(* Ill-typed:
let () =
  let refl = [%refl: ?l:'a -> unit -> 'b] in
  let _ =
    Refl.map refl refl [P string_of_int; P string_of_int]
      (fun ?l:(x = 0) () -> succ x) in
  ()
*)

let () =
  let refl = [%refl: ('a -> 'a) * 'b] in
  assert (Refl.show refl [None; Some Format.pp_print_int] (succ, 0)
    = "(<fun>, 0)");
  ()

type ('a, 'b) arrow_pair = ('a -> 'b) * ('a -> 'b)
      [@@deriving refl]

let () =
  let f =
    Refl.map [%refl: ('a, 'b) arrow_pair list] [%refl: ('a, 'b) arrow_pair list]
      [N int_of_string; P string_of_int] [succ, pred] in
  assert (
    let fst, snd = List.hd f in
    fst "4" = "5" && snd "4" = "3")
