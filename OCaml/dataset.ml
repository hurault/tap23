module type Dataset = sig
  (* type of the features *)
  type t

  (* type of the result *)
  type tk

  (* déterministic implantation of equality over the type*)
  val tk_eq_dec : tk -> tk -> bool

  (* number of features *)
  val nb_feature : int

  (* maximal value of the features *)
  val nu : int -> t

  (* minimal value of the features *)
  val lambda : int -> t

  (* name of the model - dataset and train model should be in file with coherent name *)
  val model : string

  (* fonction to convert t into a string *)
  val t_of_string : string -> t
  val float_of_t : t -> float
  val tk_of_float : float -> tk
end

(********************************)
(**** POKEMON *******************)
(********************************)
module Pokemon : Dataset with type t = float and type tk=int = struct
  type t = float
  type tk = int

  let tk_eq_dec = ( = )
  let nb_feature = 31

  let nu n =
    match n with
    | 0 -> 4.0
    | 1 -> 4.0
    | 2 -> 2.0
    | 3 -> 4.0
    | 4 -> 4.0
    | 5 -> 4.0
    | 6 -> 4.0
    | 7 -> 4.0
    | 8 -> 4.0
    | 9 -> 4.0
    | 10 -> 4.0
    | 11 -> 4.0
    | 12 -> 1.0
    | 13 -> 4.0
    | 14 -> 4.0
    | 15 -> 4.0
    | 16 -> 4.0
    | 17 -> 4.0
    | 18 -> 185.0
    | 19 -> 30720.0
    | 20 -> 140.0
    | 21 -> 780.0
    | 22 -> 255.0
    | 23 -> 230.0
    | 24 -> 1640000.0
    | 25 -> 255.0
    | 26 -> 801.0
    | 27 -> 194.0
    | 28 -> 230.0
    | 29 -> 180.0
    | _ -> 7.0

  let lambda n =
    match n with
    | 0 -> 0.25
    | 1 -> 0.25
    | 2 -> 0.0
    | 3 -> 0.0
    | 4 -> 0.25
    | 5 -> 0.0
    | 6 -> 0.25
    | 7 -> 0.25
    | 8 -> 0.0
    | 9 -> 0.25
    | 10 -> 0.0
    | 11 -> 0.25
    | 12 -> 0.0
    | 13 -> 0.0
    | 14 -> 0.0
    | 15 -> 0.25
    | 16 -> 0.25
    | 17 -> 0.25
    | 18 -> 5.0
    | 19 -> 1280.0
    | 20 -> 0.0
    | 21 -> 180.0
    | 22 -> 3.0
    | 23 -> 5.0
    | 24 -> 600000.0
    | 25 -> 1.0
    | 26 -> 1.0
    | 27 -> 10.0
    | 28 -> 20.0
    | 29 -> 5.0
    | _ -> 1.0

  let model = "pokemon"

  let t_of_string = float_of_string

  let float_of_t x = x
  let tk_of_float x = int_of_float x
end



(********************************)
(**** PLACEMENT *****************)
(********************************)
module Placement : Dataset with type t = float and type tk=int = struct
  type t = float
  type tk = int

  let tk_eq_dec = ( = )
  let nb_feature = 7

  let nu n =
    match n with
    | 0 -> 1.0
    | 1 -> 90.0
    | 2 -> 100.0
    | 3 -> 91.0
    | 4 -> 1.0
    | 5 -> 100.0
    | _ -> 80.0

  let lambda n =
    match n with
    | 0 -> 0.0
    | 1 -> 49.0
    | 2 -> 50.0
    | 3 -> 56.0
    | 4 -> 0.0
    | 5 -> 50.0
    | _ -> 52.0

  let model = "placement"


  let t_of_string = float_of_string
  let float_of_t x = x
  let tk_of_float x = int_of_float x
end




(********************************)
(**** CAR_EVALUATION ************)
(********************************)
module CarEvaluation: Dataset with type t = float and type tk=int = struct
  type t = float
  type tk = int

  let tk_eq_dec = ( = )
  let nb_feature = 6

  let nu n =
    match n with
    | 0 -> 0.0
    | 1 -> 0.0
    | 2 -> 6.0
    | 3 -> 6.0
    | 4 -> 2.0
    | _ -> 2.0

  let lambda n =
    match n with
    | 0 -> -3.0
    | 1 -> -3.0
    | 2 -> 2.0
    | 3 -> 2.0
    | 4 -> 0.0
    | _ -> 0.0

  let model = "car_evaluation"

  let t_of_string = float_of_string
  let float_of_t x = x
  let tk_of_float x = int_of_float x
end


(********************************)
(**** HEART************)
(********************************)
module Heart: Dataset with type t = float and type tk=int = struct
  type t = float
  type tk = int

  let tk_eq_dec = ( = )
  let nb_feature = 11

  let nu n =
    match n with
    | 0 -> 95.0
    | 1 -> 1.0
    | 2 -> 8000.0
    | 3 -> 1.0
    | 4 -> 80.0
    | 5 -> 1.0
    | 6 -> 850000.0
    | 7 -> 10.0
    | 8 -> 150.0
    | 9 -> 1.0
    | _ -> 1.0

  let lambda n =
    match n with
    | 0 -> 40.0
    | 1 -> 0.0
    | 2 -> 20.0
    | 3 -> 0.0
    | 4 -> 14.0
    | 5 -> 0.0
    | 6 -> 25000.0
    | 7 -> 0.0
    | 8 -> 110.0
    | 9 -> 0.0
    | _ -> 0.0

  let model = "heart"

  let t_of_string = float_of_string
  let float_of_t x = x
  let tk_of_float x = int_of_float x
end


