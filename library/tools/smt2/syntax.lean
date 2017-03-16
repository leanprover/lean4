namespace smt2

@[reducible] def symbol : Type := string
@[reducible] def identifier : Type := string

inductive special_constant : Type
| number : int → special_constant
| string : string → special_constant

inductive sort : Type
| id : identifier → sort
| apply : identifier → list sort → sort

instance : has_coe string sort :=
⟨ fun str, sort.id str ⟩

meta def sort.to_format : sort → format
| (sort.id i) := to_fmt i
| (sort.apply _ _) := "NYI"

meta instance sort_has_to_fmt : has_to_format sort :=
⟨ sort.to_format ⟩

inductive attr : Type

inductive qualified_name : Type
| id : identifier → qualified_name
| qual_id : identifier → sort → qualified_name

inductive term : Type
| qual_id : qualified_name → term
| const : special_constant → term
| apply : qualified_name → list term → term
| letb : list (name × term) → term → term
| forallq : list (symbol × sort) → term → term
| existsq : list (symbol × sort) → term → term
| annotate : term → list attr → term

inductive fun_def : Type
inductive info_flag : Type
inductive keyword : Type
inductive option : Type

inductive cmd : Type
| assert_cmd : term → cmd
| check_sat : cmd
| check_sat_assuming : term → cmd -- not complete
| declare_const : symbol → sort → cmd
| declare_fun : symbol → list sort → cmd
| declare_sort : symbol → nat → cmd
| define_fun : fun_def → cmd
| define_fun_rec : fun_def → cmd
| define_funs_rec : cmd -- not complete
| define_sort : symbol → list symbol → sort → cmd
| echo : string → cmd
| exit_cmd : cmd
| get_assertions : cmd
| get_assignment : cmd
| get_info : info_flag → cmd
| get_model : cmd
| get_option : keyword → cmd
| get_proof : cmd
| get_unsat_assumtpions : cmd
| get_unsat_core : cmd
| get_value : cmd -- not complete
| pop : nat → cmd
| push : nat → cmd
| reset : cmd
| reset_assertions : cmd
| set_info : attr → cmd
| set_logic : symbol → cmd
| set_opt : option → cmd

open cmd

meta def string_lit (s : string) : format :=
format.bracket "\"" "\"" (to_fmt s)

meta def cmd.to_format : cmd → format
| (echo msg) := "(echo " ++ string_lit msg ++ ")\n"
| (declare_const sym srt) := "(declare-const " ++ sym ++ " " ++ to_fmt srt ++ ")"
| _ := "NYI"

meta instance : has_to_format cmd :=
⟨ cmd.to_format ⟩

end smt2
