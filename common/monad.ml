module State = struct
  let (let*) x f acc =
    let (y, acc) = x acc in
    f y acc

  let return x acc =
    (x, acc)

  let rec map_aux f list acc_list =
    match list with
    |  [] -> return (List.rev acc_list)
    | head :: tail ->
        let* head = f head in
        map_aux f tail (head :: acc_list)

  let map f list =
    map_aux f list []
end

module Option = struct
  let (let*) x f =
    match x with
    | Some v -> f v
    | None -> None

  let return x =
    Some x
end

module Result = struct
  let (let*) x f =
    match x with
    | Ok v -> f v
    | Error e -> Error e

  let return x =
    Ok x
end
