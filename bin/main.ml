open Lambda

let nested = Lam ("x", TInt, Lam ("x", TInt, Add (Var ("x", TInt), LitInt 1)))
let expr = App (nested, LitInt 5)

let () =
  match eval_full expr with
  | Lam (y, _, body) ->
      (* apply inner lambda to 10 *)
      let body_app = App (Lam (y, TInt, body), LitInt 10) in
      begin
        match eval_full body_app with
        | LitInt n -> Printf.printf "Result: %d\n" n
        | _ -> Printf.printf "Unexpected result\n"
      end
  | _ -> Printf.printf "Unexpected result\n"
