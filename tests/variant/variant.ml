type ('a, 'b) t = [ `A of 'a | `B of 'b ]
    [@@deriving refl]

let () =
  let refl = [%refl: ('a, 'b) t * ('a, 'b) t] in
  assert (Refl.map refl refl [P string_of_int; P float_of_int]
    (`A 1, `B 2) = (`A "1", `B 2.))

type variant = [`A | `B]
    [@@deriving refl]

type inherited = [`C | variant]
    [@@deriving refl]

let () =
  assert (Refl.compare [%refl: inherited] [] `A `C > 0);
  assert (Refl.compare [%refl: inherited] [] `A `B < 0);
  assert (Refl.compare [%refl: inherited] [] `B `B = 0)

type recursive = [`A of ([`A | `B of 'a] as 'a) | `C]
    [@@deriving refl]
