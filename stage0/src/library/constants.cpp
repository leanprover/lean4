// Copyright (c) 2015 Microsoft Corporation. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// DO NOT EDIT, automatically generated file, generator scripts/gen_constants_cpp.py
#include "util/name.h"
namespace lean{
name const * g_absurd = nullptr;
name const * g_and = nullptr;
name const * g_and_left = nullptr;
name const * g_and_right = nullptr;
name const * g_and_intro = nullptr;
name const * g_and_rec = nullptr;
name const * g_and_cases_on = nullptr;
name const * g_array = nullptr;
name const * g_array_sz = nullptr;
name const * g_array_to_list = nullptr;
name const * g_auto_param = nullptr;
name const * g_bit0 = nullptr;
name const * g_bit1 = nullptr;
name const * g_has_of_nat_of_nat = nullptr;
name const * g_byte_array = nullptr;
name const * g_byte_array_data = nullptr;
name const * g_bool = nullptr;
name const * g_bool_false = nullptr;
name const * g_bool_true = nullptr;
name const * g_bool_cases_on = nullptr;
name const * g_cast = nullptr;
name const * g_char = nullptr;
name const * g_congr_arg = nullptr;
name const * g_decidable = nullptr;
name const * g_decidable_is_true = nullptr;
name const * g_decidable_is_false = nullptr;
name const * g_decidable_decide = nullptr;
name const * g_empty = nullptr;
name const * g_empty_rec = nullptr;
name const * g_empty_cases_on = nullptr;
name const * g_exists = nullptr;
name const * g_eq = nullptr;
name const * g_eq_cases_on = nullptr;
name const * g_eq_rec_on = nullptr;
name const * g_eq_rec = nullptr;
name const * g_eq_ndrec = nullptr;
name const * g_eq_refl = nullptr;
name const * g_eq_subst = nullptr;
name const * g_eq_symm = nullptr;
name const * g_eq_trans = nullptr;
name const * g_float = nullptr;
name const * g_float_array = nullptr;
name const * g_float_array_data = nullptr;
name const * g_false = nullptr;
name const * g_false_rec = nullptr;
name const * g_false_cases_on = nullptr;
name const * g_has_add_add = nullptr;
name const * g_has_neg_neg = nullptr;
name const * g_has_one_one = nullptr;
name const * g_has_zero_zero = nullptr;
name const * g_heq = nullptr;
name const * g_heq_refl = nullptr;
name const * g_iff = nullptr;
name const * g_iff_refl = nullptr;
name const * g_int = nullptr;
name const * g_int_nat_abs = nullptr;
name const * g_int_dec_lt = nullptr;
name const * g_int_of_nat = nullptr;
name const * g_inline = nullptr;
name const * g_io = nullptr;
name const * g_ite = nullptr;
name const * g_lc_proof = nullptr;
name const * g_lc_unreachable = nullptr;
name const * g_list = nullptr;
name const * g_mut_quot = nullptr;
name const * g_nat = nullptr;
name const * g_nat_succ = nullptr;
name const * g_nat_zero = nullptr;
name const * g_nat_has_zero = nullptr;
name const * g_nat_has_one = nullptr;
name const * g_nat_has_add = nullptr;
name const * g_nat_add = nullptr;
name const * g_nat_dec_eq = nullptr;
name const * g_nat_sub = nullptr;
name const * g_ne = nullptr;
name const * g_not = nullptr;
name const * g_opt_param = nullptr;
name const * g_or = nullptr;
name const * g_panic = nullptr;
name const * g_punit = nullptr;
name const * g_punit_unit = nullptr;
name const * g_pprod = nullptr;
name const * g_pprod_mk = nullptr;
name const * g_pprod_fst = nullptr;
name const * g_pprod_snd = nullptr;
name const * g_propext = nullptr;
name const * g_quot_mk = nullptr;
name const * g_quot_lift = nullptr;
name const * g_sorry_ax = nullptr;
name const * g_string = nullptr;
name const * g_string_data = nullptr;
name const * g_subsingleton_elim = nullptr;
name const * g_task = nullptr;
name const * g_thunk = nullptr;
name const * g_thunk_mk = nullptr;
name const * g_thunk_get = nullptr;
name const * g_true = nullptr;
name const * g_true_intro = nullptr;
name const * g_unit = nullptr;
name const * g_unit_unit = nullptr;
name const * g_uint8 = nullptr;
name const * g_uint16 = nullptr;
name const * g_uint32 = nullptr;
name const * g_uint64 = nullptr;
name const * g_usize = nullptr;
void initialize_constants() {
    g_absurd = new name{"absurd"};
    mark_persistent(g_absurd->raw());
    g_and = new name{"And"};
    mark_persistent(g_and->raw());
    g_and_left = new name{"And", "left"};
    mark_persistent(g_and_left->raw());
    g_and_right = new name{"And", "right"};
    mark_persistent(g_and_right->raw());
    g_and_intro = new name{"And", "intro"};
    mark_persistent(g_and_intro->raw());
    g_and_rec = new name{"And", "rec"};
    mark_persistent(g_and_rec->raw());
    g_and_cases_on = new name{"And", "casesOn"};
    mark_persistent(g_and_cases_on->raw());
    g_array = new name{"Array"};
    mark_persistent(g_array->raw());
    g_array_sz = new name{"Array", "sz"};
    mark_persistent(g_array_sz->raw());
    g_array_to_list = new name{"Array", "toList"};
    mark_persistent(g_array_to_list->raw());
    g_auto_param = new name{"autoParam"};
    mark_persistent(g_auto_param->raw());
    g_bit0 = new name{"bit0"};
    mark_persistent(g_bit0->raw());
    g_bit1 = new name{"bit1"};
    mark_persistent(g_bit1->raw());
    g_has_of_nat_of_nat = new name{"HasOfNat", "ofNat"};
    mark_persistent(g_has_of_nat_of_nat->raw());
    g_byte_array = new name{"ByteArray"};
    mark_persistent(g_byte_array->raw());
    g_byte_array_data = new name{"ByteArray", "data"};
    mark_persistent(g_byte_array_data->raw());
    g_bool = new name{"Bool"};
    mark_persistent(g_bool->raw());
    g_bool_false = new name{"Bool", "false"};
    mark_persistent(g_bool_false->raw());
    g_bool_true = new name{"Bool", "true"};
    mark_persistent(g_bool_true->raw());
    g_bool_cases_on = new name{"Bool", "casesOn"};
    mark_persistent(g_bool_cases_on->raw());
    g_cast = new name{"cast"};
    mark_persistent(g_cast->raw());
    g_char = new name{"Char"};
    mark_persistent(g_char->raw());
    g_congr_arg = new name{"congrArg"};
    mark_persistent(g_congr_arg->raw());
    g_decidable = new name{"Decidable"};
    mark_persistent(g_decidable->raw());
    g_decidable_is_true = new name{"Decidable", "isTrue"};
    mark_persistent(g_decidable_is_true->raw());
    g_decidable_is_false = new name{"Decidable", "isFalse"};
    mark_persistent(g_decidable_is_false->raw());
    g_decidable_decide = new name{"Decidable", "decide"};
    mark_persistent(g_decidable_decide->raw());
    g_empty = new name{"Empty"};
    mark_persistent(g_empty->raw());
    g_empty_rec = new name{"Empty", "rec"};
    mark_persistent(g_empty_rec->raw());
    g_empty_cases_on = new name{"Empty", "casesOn"};
    mark_persistent(g_empty_cases_on->raw());
    g_exists = new name{"Exists"};
    mark_persistent(g_exists->raw());
    g_eq = new name{"Eq"};
    mark_persistent(g_eq->raw());
    g_eq_cases_on = new name{"Eq", "casesOn"};
    mark_persistent(g_eq_cases_on->raw());
    g_eq_rec_on = new name{"Eq", "recOn"};
    mark_persistent(g_eq_rec_on->raw());
    g_eq_rec = new name{"Eq", "rec"};
    mark_persistent(g_eq_rec->raw());
    g_eq_ndrec = new name{"Eq", "ndrec"};
    mark_persistent(g_eq_ndrec->raw());
    g_eq_refl = new name{"Eq", "refl"};
    mark_persistent(g_eq_refl->raw());
    g_eq_subst = new name{"Eq", "subst"};
    mark_persistent(g_eq_subst->raw());
    g_eq_symm = new name{"Eq", "symm"};
    mark_persistent(g_eq_symm->raw());
    g_eq_trans = new name{"Eq", "trans"};
    mark_persistent(g_eq_trans->raw());
    g_float = new name{"Float"};
    mark_persistent(g_float->raw());
    g_float_array = new name{"FloatArray"};
    mark_persistent(g_float_array->raw());
    g_float_array_data = new name{"FloatArray", "data"};
    mark_persistent(g_float_array_data->raw());
    g_false = new name{"False"};
    mark_persistent(g_false->raw());
    g_false_rec = new name{"False", "rec"};
    mark_persistent(g_false_rec->raw());
    g_false_cases_on = new name{"False", "casesOn"};
    mark_persistent(g_false_cases_on->raw());
    g_has_add_add = new name{"HasAdd", "add"};
    mark_persistent(g_has_add_add->raw());
    g_has_neg_neg = new name{"HasNeg", "neg"};
    mark_persistent(g_has_neg_neg->raw());
    g_has_one_one = new name{"HasOne", "one"};
    mark_persistent(g_has_one_one->raw());
    g_has_zero_zero = new name{"HasZero", "zero"};
    mark_persistent(g_has_zero_zero->raw());
    g_heq = new name{"HEq"};
    mark_persistent(g_heq->raw());
    g_heq_refl = new name{"HEq", "refl"};
    mark_persistent(g_heq_refl->raw());
    g_iff = new name{"Iff"};
    mark_persistent(g_iff->raw());
    g_iff_refl = new name{"Iff", "refl"};
    mark_persistent(g_iff_refl->raw());
    g_int = new name{"Int"};
    mark_persistent(g_int->raw());
    g_int_nat_abs = new name{"Int", "natAbs"};
    mark_persistent(g_int_nat_abs->raw());
    g_int_dec_lt = new name{"Int", "decLt"};
    mark_persistent(g_int_dec_lt->raw());
    g_int_of_nat = new name{"Int", "ofNat"};
    mark_persistent(g_int_of_nat->raw());
    g_inline = new name{"inline"};
    mark_persistent(g_inline->raw());
    g_io = new name{"IO"};
    mark_persistent(g_io->raw());
    g_ite = new name{"ite"};
    mark_persistent(g_ite->raw());
    g_lc_proof = new name{"lcProof"};
    mark_persistent(g_lc_proof->raw());
    g_lc_unreachable = new name{"lcUnreachable"};
    mark_persistent(g_lc_unreachable->raw());
    g_list = new name{"List"};
    mark_persistent(g_list->raw());
    g_mut_quot = new name{"MutQuot"};
    mark_persistent(g_mut_quot->raw());
    g_nat = new name{"Nat"};
    mark_persistent(g_nat->raw());
    g_nat_succ = new name{"Nat", "succ"};
    mark_persistent(g_nat_succ->raw());
    g_nat_zero = new name{"Nat", "zero"};
    mark_persistent(g_nat_zero->raw());
    g_nat_has_zero = new name{"Nat", "HasZero"};
    mark_persistent(g_nat_has_zero->raw());
    g_nat_has_one = new name{"Nat", "HasOne"};
    mark_persistent(g_nat_has_one->raw());
    g_nat_has_add = new name{"Nat", "HasAdd"};
    mark_persistent(g_nat_has_add->raw());
    g_nat_add = new name{"Nat", "add"};
    mark_persistent(g_nat_add->raw());
    g_nat_dec_eq = new name{"Nat", "decEq"};
    mark_persistent(g_nat_dec_eq->raw());
    g_nat_sub = new name{"Nat", "sub"};
    mark_persistent(g_nat_sub->raw());
    g_ne = new name{"ne"};
    mark_persistent(g_ne->raw());
    g_not = new name{"Not"};
    mark_persistent(g_not->raw());
    g_opt_param = new name{"optParam"};
    mark_persistent(g_opt_param->raw());
    g_or = new name{"Or"};
    mark_persistent(g_or->raw());
    g_panic = new name{"panic"};
    mark_persistent(g_panic->raw());
    g_punit = new name{"PUnit"};
    mark_persistent(g_punit->raw());
    g_punit_unit = new name{"PUnit", "unit"};
    mark_persistent(g_punit_unit->raw());
    g_pprod = new name{"PProd"};
    mark_persistent(g_pprod->raw());
    g_pprod_mk = new name{"PProd", "mk"};
    mark_persistent(g_pprod_mk->raw());
    g_pprod_fst = new name{"PProd", "fst"};
    mark_persistent(g_pprod_fst->raw());
    g_pprod_snd = new name{"PProd", "snd"};
    mark_persistent(g_pprod_snd->raw());
    g_propext = new name{"propext"};
    mark_persistent(g_propext->raw());
    g_quot_mk = new name{"Quot", "mk"};
    mark_persistent(g_quot_mk->raw());
    g_quot_lift = new name{"Quot", "lift"};
    mark_persistent(g_quot_lift->raw());
    g_sorry_ax = new name{"sorryAx"};
    mark_persistent(g_sorry_ax->raw());
    g_string = new name{"String"};
    mark_persistent(g_string->raw());
    g_string_data = new name{"String", "data"};
    mark_persistent(g_string_data->raw());
    g_subsingleton_elim = new name{"Subsingleton", "elim"};
    mark_persistent(g_subsingleton_elim->raw());
    g_task = new name{"Task"};
    mark_persistent(g_task->raw());
    g_thunk = new name{"Thunk"};
    mark_persistent(g_thunk->raw());
    g_thunk_mk = new name{"Thunk", "mk"};
    mark_persistent(g_thunk_mk->raw());
    g_thunk_get = new name{"Thunk", "get"};
    mark_persistent(g_thunk_get->raw());
    g_true = new name{"True"};
    mark_persistent(g_true->raw());
    g_true_intro = new name{"True", "intro"};
    mark_persistent(g_true_intro->raw());
    g_unit = new name{"Unit"};
    mark_persistent(g_unit->raw());
    g_unit_unit = new name{"Unit", "unit"};
    mark_persistent(g_unit_unit->raw());
    g_uint8 = new name{"UInt8"};
    mark_persistent(g_uint8->raw());
    g_uint16 = new name{"UInt16"};
    mark_persistent(g_uint16->raw());
    g_uint32 = new name{"UInt32"};
    mark_persistent(g_uint32->raw());
    g_uint64 = new name{"UInt64"};
    mark_persistent(g_uint64->raw());
    g_usize = new name{"USize"};
    mark_persistent(g_usize->raw());
}
void finalize_constants() {
    delete g_absurd;
    delete g_and;
    delete g_and_left;
    delete g_and_right;
    delete g_and_intro;
    delete g_and_rec;
    delete g_and_cases_on;
    delete g_array;
    delete g_array_sz;
    delete g_array_to_list;
    delete g_auto_param;
    delete g_bit0;
    delete g_bit1;
    delete g_has_of_nat_of_nat;
    delete g_byte_array;
    delete g_byte_array_data;
    delete g_bool;
    delete g_bool_false;
    delete g_bool_true;
    delete g_bool_cases_on;
    delete g_cast;
    delete g_char;
    delete g_congr_arg;
    delete g_decidable;
    delete g_decidable_is_true;
    delete g_decidable_is_false;
    delete g_decidable_decide;
    delete g_empty;
    delete g_empty_rec;
    delete g_empty_cases_on;
    delete g_exists;
    delete g_eq;
    delete g_eq_cases_on;
    delete g_eq_rec_on;
    delete g_eq_rec;
    delete g_eq_ndrec;
    delete g_eq_refl;
    delete g_eq_subst;
    delete g_eq_symm;
    delete g_eq_trans;
    delete g_float;
    delete g_float_array;
    delete g_float_array_data;
    delete g_false;
    delete g_false_rec;
    delete g_false_cases_on;
    delete g_has_add_add;
    delete g_has_neg_neg;
    delete g_has_one_one;
    delete g_has_zero_zero;
    delete g_heq;
    delete g_heq_refl;
    delete g_iff;
    delete g_iff_refl;
    delete g_int;
    delete g_int_nat_abs;
    delete g_int_dec_lt;
    delete g_int_of_nat;
    delete g_inline;
    delete g_io;
    delete g_ite;
    delete g_lc_proof;
    delete g_lc_unreachable;
    delete g_list;
    delete g_mut_quot;
    delete g_nat;
    delete g_nat_succ;
    delete g_nat_zero;
    delete g_nat_has_zero;
    delete g_nat_has_one;
    delete g_nat_has_add;
    delete g_nat_add;
    delete g_nat_dec_eq;
    delete g_nat_sub;
    delete g_ne;
    delete g_not;
    delete g_opt_param;
    delete g_or;
    delete g_panic;
    delete g_punit;
    delete g_punit_unit;
    delete g_pprod;
    delete g_pprod_mk;
    delete g_pprod_fst;
    delete g_pprod_snd;
    delete g_propext;
    delete g_quot_mk;
    delete g_quot_lift;
    delete g_sorry_ax;
    delete g_string;
    delete g_string_data;
    delete g_subsingleton_elim;
    delete g_task;
    delete g_thunk;
    delete g_thunk_mk;
    delete g_thunk_get;
    delete g_true;
    delete g_true_intro;
    delete g_unit;
    delete g_unit_unit;
    delete g_uint8;
    delete g_uint16;
    delete g_uint32;
    delete g_uint64;
    delete g_usize;
}
name const & get_absurd_name() { return *g_absurd; }
name const & get_and_name() { return *g_and; }
name const & get_and_left_name() { return *g_and_left; }
name const & get_and_right_name() { return *g_and_right; }
name const & get_and_intro_name() { return *g_and_intro; }
name const & get_and_rec_name() { return *g_and_rec; }
name const & get_and_cases_on_name() { return *g_and_cases_on; }
name const & get_array_name() { return *g_array; }
name const & get_array_sz_name() { return *g_array_sz; }
name const & get_array_to_list_name() { return *g_array_to_list; }
name const & get_auto_param_name() { return *g_auto_param; }
name const & get_bit0_name() { return *g_bit0; }
name const & get_bit1_name() { return *g_bit1; }
name const & get_has_of_nat_of_nat_name() { return *g_has_of_nat_of_nat; }
name const & get_byte_array_name() { return *g_byte_array; }
name const & get_byte_array_data_name() { return *g_byte_array_data; }
name const & get_bool_name() { return *g_bool; }
name const & get_bool_false_name() { return *g_bool_false; }
name const & get_bool_true_name() { return *g_bool_true; }
name const & get_bool_cases_on_name() { return *g_bool_cases_on; }
name const & get_cast_name() { return *g_cast; }
name const & get_char_name() { return *g_char; }
name const & get_congr_arg_name() { return *g_congr_arg; }
name const & get_decidable_name() { return *g_decidable; }
name const & get_decidable_is_true_name() { return *g_decidable_is_true; }
name const & get_decidable_is_false_name() { return *g_decidable_is_false; }
name const & get_decidable_decide_name() { return *g_decidable_decide; }
name const & get_empty_name() { return *g_empty; }
name const & get_empty_rec_name() { return *g_empty_rec; }
name const & get_empty_cases_on_name() { return *g_empty_cases_on; }
name const & get_exists_name() { return *g_exists; }
name const & get_eq_name() { return *g_eq; }
name const & get_eq_cases_on_name() { return *g_eq_cases_on; }
name const & get_eq_rec_on_name() { return *g_eq_rec_on; }
name const & get_eq_rec_name() { return *g_eq_rec; }
name const & get_eq_ndrec_name() { return *g_eq_ndrec; }
name const & get_eq_refl_name() { return *g_eq_refl; }
name const & get_eq_subst_name() { return *g_eq_subst; }
name const & get_eq_symm_name() { return *g_eq_symm; }
name const & get_eq_trans_name() { return *g_eq_trans; }
name const & get_float_name() { return *g_float; }
name const & get_float_array_name() { return *g_float_array; }
name const & get_float_array_data_name() { return *g_float_array_data; }
name const & get_false_name() { return *g_false; }
name const & get_false_rec_name() { return *g_false_rec; }
name const & get_false_cases_on_name() { return *g_false_cases_on; }
name const & get_has_add_add_name() { return *g_has_add_add; }
name const & get_has_neg_neg_name() { return *g_has_neg_neg; }
name const & get_has_one_one_name() { return *g_has_one_one; }
name const & get_has_zero_zero_name() { return *g_has_zero_zero; }
name const & get_heq_name() { return *g_heq; }
name const & get_heq_refl_name() { return *g_heq_refl; }
name const & get_iff_name() { return *g_iff; }
name const & get_iff_refl_name() { return *g_iff_refl; }
name const & get_int_name() { return *g_int; }
name const & get_int_nat_abs_name() { return *g_int_nat_abs; }
name const & get_int_dec_lt_name() { return *g_int_dec_lt; }
name const & get_int_of_nat_name() { return *g_int_of_nat; }
name const & get_inline_name() { return *g_inline; }
name const & get_io_name() { return *g_io; }
name const & get_ite_name() { return *g_ite; }
name const & get_lc_proof_name() { return *g_lc_proof; }
name const & get_lc_unreachable_name() { return *g_lc_unreachable; }
name const & get_list_name() { return *g_list; }
name const & get_mut_quot_name() { return *g_mut_quot; }
name const & get_nat_name() { return *g_nat; }
name const & get_nat_succ_name() { return *g_nat_succ; }
name const & get_nat_zero_name() { return *g_nat_zero; }
name const & get_nat_has_zero_name() { return *g_nat_has_zero; }
name const & get_nat_has_one_name() { return *g_nat_has_one; }
name const & get_nat_has_add_name() { return *g_nat_has_add; }
name const & get_nat_add_name() { return *g_nat_add; }
name const & get_nat_dec_eq_name() { return *g_nat_dec_eq; }
name const & get_nat_sub_name() { return *g_nat_sub; }
name const & get_ne_name() { return *g_ne; }
name const & get_not_name() { return *g_not; }
name const & get_opt_param_name() { return *g_opt_param; }
name const & get_or_name() { return *g_or; }
name const & get_panic_name() { return *g_panic; }
name const & get_punit_name() { return *g_punit; }
name const & get_punit_unit_name() { return *g_punit_unit; }
name const & get_pprod_name() { return *g_pprod; }
name const & get_pprod_mk_name() { return *g_pprod_mk; }
name const & get_pprod_fst_name() { return *g_pprod_fst; }
name const & get_pprod_snd_name() { return *g_pprod_snd; }
name const & get_propext_name() { return *g_propext; }
name const & get_quot_mk_name() { return *g_quot_mk; }
name const & get_quot_lift_name() { return *g_quot_lift; }
name const & get_sorry_ax_name() { return *g_sorry_ax; }
name const & get_string_name() { return *g_string; }
name const & get_string_data_name() { return *g_string_data; }
name const & get_subsingleton_elim_name() { return *g_subsingleton_elim; }
name const & get_task_name() { return *g_task; }
name const & get_thunk_name() { return *g_thunk; }
name const & get_thunk_mk_name() { return *g_thunk_mk; }
name const & get_thunk_get_name() { return *g_thunk_get; }
name const & get_true_name() { return *g_true; }
name const & get_true_intro_name() { return *g_true_intro; }
name const & get_unit_name() { return *g_unit; }
name const & get_unit_unit_name() { return *g_unit_unit; }
name const & get_uint8_name() { return *g_uint8; }
name const & get_uint16_name() { return *g_uint16; }
name const & get_uint32_name() { return *g_uint32; }
name const & get_uint64_name() { return *g_uint64; }
name const & get_usize_name() { return *g_usize; }
}
