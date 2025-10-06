open LambdaLib

let () =
  let open Vec in
  let v = VCons (1, VCons (2, VCons (3, VCons (4, VNil)))) in
  let (Ex (vfilt, k)) = filter (fun x -> x mod 2 = 0) v in
  print_string "Filtered vector: ";
  print_vec vfilt (Printf.printf "%d");
  Printf.printf "Filtered length: %d\n" (nat_to_int k);
  (match k with
  | Z -> ()
  | S _ ->
      let _h = head vfilt in
      ());
  ()

type showable = Show : ('a -> string) * 'a -> showable

let show_all xs = List.map (fun (Show (f, x)) -> f x) xs

let () =
  let xs = 1 :: [ 2 ] in
  let xs = List.map (fun s -> Show (string_of_int, s)) xs in
  let ss = show_all xs in
  let _ = List.iter print_endline ss in
  ()
