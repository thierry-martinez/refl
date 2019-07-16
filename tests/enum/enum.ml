type insn = Const [@refl.value 2] | Push | Pop | Add
  [@@deriving refl]

let () =
  assert (Refl.min [%refl: insn] = 2)

let () =
  assert (Refl.max [%refl: insn] = 5)

let () =
  assert (Refl.to_int [%refl: insn] Push = 3)

let () =
  assert (Refl.of_int_opt [%refl: insn] 5 = Some Add)

let () =
  assert (Refl.of_int_opt [%refl: insn] 7 = None)

let () =
  assert (Refl.to_string [%refl: insn] Pop = "Pop")

let () =
  assert (Refl.of_string_opt [%refl: insn] "Const" = Some Const)

let () =
  assert (Refl.of_string_opt [%refl: insn] "Add" = Some Add)

let () =
  assert (Refl.of_string_opt [%refl: insn] "_" = None)
