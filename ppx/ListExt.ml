let fold_lefti f acc list =
  snd (List.fold_left (fun (i, acc) x -> (succ i, f i acc x)) (0, acc) list)
