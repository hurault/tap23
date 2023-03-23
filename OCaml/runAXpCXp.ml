open Explain
open Dataset

module AllAXpCXp (D : Dataset) = struct
  let read_whole_file filename =
    let ch = open_in filename in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s

  let rec remove_last l =
    match l with [] -> [] | [ _ ] -> [] | t :: q -> t :: remove_last q

  let csv_to_string_list filename =
    let s = read_whole_file filename in
    let lines = String.split_on_char '\n' s in
    let lines_ok = List.filter (fun s -> s <> "") lines in
    let instances_with_output = List.map (String.split_on_char ',') lines_ok in
    List.map remove_last instances_with_output

  let path_dataset = "../XGBoost/datasets/"

  exception InstanceException of int

  (*
    Usage of pyml to execute the following python code
    import xgboost as xgb
    ### load the model
    model = xgb.Booster()
    model.load_model(path_model)
     *)
  let load_model () =
    Py.initialize ();
    let path_model =
      Py.String.of_string ("../XGBoost/models/" ^ D.model ^ ".json")
    in
    let xgb = Py.import "xgboost" in
    let model = Py.Module.get_function xgb "Booster" [||] in
    ignore (Py.Module.get_function model "load_model" [| path_model |]);
    (xgb, model)

  (* load the model only one time*)
  let xgbmodel = ref (load_model ())

  (** val k : t list -> tk **)
  let k lf =
    (*
      Usage of pyml to execute the following python code
      import xgboost as xgb
      ### create the instance
      instance = [float(f) for f in lf] # converte the feature into float
      di = xgb.DMatrix([instance])
      ### make prediction
      pred = model.predict(di)
       *)
    let xgb, model = !xgbmodel in
    let module ExpM = AxpCxp (D) in
    let instance =
      List.map (fun e -> Py.Float.of_float (D.float_of_t e)) (ExpM.from_list lf)
    in
    let di =
      Py.Module.get_function xgb "DMatrix"
        [| Py.List.of_list [ Py.List.of_list instance ] |]
    in
    let pred = Py.Module.get_function model "predict" [| di |] in
    let ts = Py.Float.to_float pred in
    D.tk_of_float ts

  let run_one_instance file i ls =
    try
      print_string (string_of_int i ^ " : Setup");
      print_newline ();

      let lf = List.map D.t_of_string ls in
      let module ExpM = AxpCxp (D) in
      print_string (string_of_int i ^ " : AXp");
      print_newline ();

      let expAxp = ExpM.findAXp_friendly k lf in

      print_string (string_of_int i ^ " : CXp");
      print_newline ();

      let expCxp = ExpM.findCXp_friendly k lf in
      (*
    print_string ((string_of_int i)^" : Print into file");
    print_newline();
    *)
      List.iter (fun i -> output_string file (string_of_int i ^ "-")) expAxp;
      output_string file " , ";
      List.iter (fun i -> output_string file (string_of_int i ^ "-")) expCxp;
      output_string file "\n";
      (List.length expAxp, List.length expCxp)
    with _ -> (0, 0)

  let run_all () =
    let file = open_out ("results/" ^ D.model ^ ".txt") in
    let instances =
      List.tl (csv_to_string_list (path_dataset ^ D.model ^ ".csv"))
    in
    (* let instances100 = List.filteri (fun i _ -> i <10) instances in *)
    try
      let lsize = List.mapi (run_one_instance file) instances in
      let lsizeAxp, lsizeCxp = List.split lsize in
      let mAxp =
        float_of_int (List.fold_left ( + ) 0 lsizeAxp)
        /. float_of_int (List.length instances)
      in
      let mCxp =
        float_of_int (List.fold_left ( + ) 0 lsizeCxp)
        /. float_of_int (List.length instances)
      in
      output_string file (string_of_float mAxp ^ " , " ^ string_of_float mCxp);
      close_out file
    with InstanceException _ -> close_out file
end

let run nom =
  match nom with
  | "heart" ->
      let module DRun = AllAXpCXp (Heart) in
      DRun.run_all ()
  | "placement" ->
      let module DRun = AllAXpCXp (Placement) in
      DRun.run_all ()
  | "car" ->
      let module DRun = AllAXpCXp (CarEvaluation) in
      DRun.run_all ()
  | "pokemon" ->
      let module DRun = AllAXpCXp (Pokemon) in
      DRun.run_all ()
  | _ -> failwith ("Unknown module :" ^ nom)

(* main *)

let _ = run Sys.argv.(1)
