// Lean compiler output
// Module: Init.Data.Dyadic.Round
// Imports: public import Init.Data.Dyadic.Basic import Init.Data.Dyadic.Instances import Init.Grind.Ordered.Rat import Init.Grind.Ordered.Field import Init.ByCases import Init.Data.Int.Bitwise.Lemmas import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.Pow import Init.Data.Option.Lemmas import Init.Omega
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Dyadic_pow_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Dyadic_pow_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Dyadic_pow_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_n_6_; lean_object* v_k_7_; lean_object* v___x_8_; 
lean_dec(v_h__1_2_);
v_n_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_n_6_);
v_k_7_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_k_7_);
lean_dec_ref_known(v_x_1_, 2);
v___x_8_ = lean_apply_3(v_h__2_3_, v_n_6_, v_k_7_, lean_box(0));
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Dyadic_pow_match__1_splitter(lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_12_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__1_11_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_n_15_; lean_object* v_k_16_; lean_object* v___x_17_; 
lean_dec(v_h__1_11_);
v_n_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_n_15_);
v_k_16_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_k_16_);
lean_dec_ref_known(v_x_10_, 2);
v___x_17_ = lean_apply_3(v_h__2_12_, v_n_15_, v_k_16_, lean_box(0));
return v___x_17_;
}
}
}
static lean_object* _init_l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_18_; lean_object* v_intZero_19_; 
v_natZero_18_ = lean_unsigned_to_nat(0u);
v_intZero_19_ = lean_nat_to_int(v_natZero_18_);
return v_intZero_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg(lean_object* v_prec_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_){
_start:
{
lean_object* v_intZero_23_; uint8_t v_isNeg_24_; 
v_intZero_23_ = lean_obj_once(&l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg___closed__0);
v_isNeg_24_ = lean_int_dec_lt(v_prec_20_, v_intZero_23_);
if (v_isNeg_24_ == 0)
{
lean_object* v_a_25_; lean_object* v___x_26_; 
lean_dec(v_h__2_22_);
v_a_25_ = lean_nat_abs(v_prec_20_);
v___x_26_ = lean_apply_1(v_h__1_21_, v_a_25_);
return v___x_26_;
}
else
{
lean_object* v_abs_27_; lean_object* v_one_28_; lean_object* v_a_29_; lean_object* v___x_30_; 
lean_dec(v_h__1_21_);
v_abs_27_ = lean_nat_abs(v_prec_20_);
v_one_28_ = lean_unsigned_to_nat(1u);
v_a_29_ = lean_nat_sub(v_abs_27_, v_one_28_);
lean_dec(v_abs_27_);
v___x_30_ = lean_apply_1(v_h__2_22_, v_a_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg___boxed(lean_object* v_prec_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg(v_prec_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_prec_31_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter(lean_object* v_motive_35_, lean_object* v_prec_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_){
_start:
{
lean_object* v_intZero_39_; uint8_t v_isNeg_40_; 
v_intZero_39_ = lean_obj_once(&l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___redArg___closed__0);
v_isNeg_40_ = lean_int_dec_lt(v_prec_36_, v_intZero_39_);
if (v_isNeg_40_ == 0)
{
lean_object* v_a_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_38_);
v_a_41_ = lean_nat_abs(v_prec_36_);
v___x_42_ = lean_apply_1(v_h__1_37_, v_a_41_);
return v___x_42_;
}
else
{
lean_object* v_abs_43_; lean_object* v_one_44_; lean_object* v_a_45_; lean_object* v___x_46_; 
lean_dec(v_h__1_37_);
v_abs_43_ = lean_nat_abs(v_prec_36_);
v_one_44_ = lean_unsigned_to_nat(1u);
v_a_45_ = lean_nat_sub(v_abs_43_, v_one_44_);
lean_dec(v_abs_43_);
v___x_46_ = lean_apply_1(v_h__2_38_, v_a_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter___boxed(lean_object* v_motive_47_, lean_object* v_prec_48_, lean_object* v_h__1_49_, lean_object* v_h__2_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Init_Data_Dyadic_Round_0__Rat_toDyadic_match__1_splitter(v_motive_47_, v_prec_48_, v_h__1_49_, v_h__2_50_);
lean_dec(v_prec_48_);
return v_res_51_;
}
}
lean_object* runtime_initialize_Init_Data_Dyadic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Dyadic_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Rat(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Field(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Dyadic_Round(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Dyadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Dyadic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ordered_Rat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ordered_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Dyadic_Round(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Dyadic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Dyadic_Instances(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Rat(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Field(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Dyadic_Round(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Dyadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Dyadic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Rat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Dyadic_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Dyadic_Round(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Dyadic_Round(builtin);
}
#ifdef __cplusplus
}
#endif
