// Lean compiler output
// Module: Init.Data.Dyadic.Basic
// Imports: public import Init.Data.Int.Bitwise.Lemmas public import Init.Data.Order.Classes public import Init.Data.Rat.Basic import Init.ByCases import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.Pow import Init.Data.Nat.Bitwise.Lemmas import Init.Data.Option.Lemmas import Init.Data.Rat.Lemmas import Init.Omega
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
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_trailing_zeros(lean_object*);
lean_object* l_Int_shiftRight(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_shiftLeft(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_zero_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_zero_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ofOdd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ofOdd_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqDyadic_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqDyadic_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqDyadic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqDyadic___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_ofIntWithPrec_spec__0(lean_object*);
static lean_once_cell_t l_Dyadic_ofIntWithPrec___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Dyadic_ofIntWithPrec___closed__0;
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ofInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_instOfNat(lean_object*);
static const lean_closure_object l_Dyadic_instIntCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instIntCast___closed__0 = (const lean_object*)&l_Dyadic_instIntCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Dyadic_instIntCast = (const lean_object*)&l_Dyadic_instIntCast___closed__0_value;
LEAN_EXPORT lean_object* l_Dyadic_instNatCast___lam__0(lean_object*);
static const lean_closure_object l_Dyadic_instNatCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_instNatCast___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instNatCast___closed__0 = (const lean_object*)&l_Dyadic_instNatCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Dyadic_instNatCast = (const lean_object*)&l_Dyadic_instNatCast___closed__0_value;
LEAN_EXPORT lean_object* l_Dyadic_add(lean_object*, lean_object*);
static const lean_closure_object l_Dyadic_instAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instAdd___closed__0 = (const lean_object*)&l_Dyadic_instAdd___closed__0_value;
LEAN_EXPORT const lean_object* l_Dyadic_instAdd = (const lean_object*)&l_Dyadic_instAdd___closed__0_value;
LEAN_EXPORT lean_object* l_Dyadic_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_mul___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Dyadic_instMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instMul___closed__0 = (const lean_object*)&l_Dyadic_instMul___closed__0_value;
LEAN_EXPORT const lean_object* l_Dyadic_instMul = (const lean_object*)&l_Dyadic_instMul___closed__0_value;
static lean_once_cell_t l_Dyadic_pow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Dyadic_pow___closed__0;
static lean_once_cell_t l_Dyadic_pow___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Dyadic_pow___closed__1;
static lean_once_cell_t l_Dyadic_pow___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Dyadic_pow___closed__2;
LEAN_EXPORT lean_object* l_Dyadic_pow(lean_object*, lean_object*);
static const lean_closure_object l_Dyadic_instPowNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_pow, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instPowNat___closed__0 = (const lean_object*)&l_Dyadic_instPowNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Dyadic_instPowNat = (const lean_object*)&l_Dyadic_instPowNat___closed__0_value;
LEAN_EXPORT lean_object* l_Dyadic_neg(lean_object*);
static const lean_closure_object l_Dyadic_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_neg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instNeg___closed__0 = (const lean_object*)&l_Dyadic_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Dyadic_instNeg = (const lean_object*)&l_Dyadic_instNeg___closed__0_value;
LEAN_EXPORT lean_object* l_Dyadic_sub(lean_object*, lean_object*);
static const lean_closure_object l_Dyadic_instSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_sub, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instSub___closed__0 = (const lean_object*)&l_Dyadic_instSub___closed__0_value;
LEAN_EXPORT const lean_object* l_Dyadic_instSub = (const lean_object*)&l_Dyadic_instSub___closed__0_value;
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_shiftRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_shiftRight___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Dyadic_instHShiftLeftInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instHShiftLeftInt___closed__0 = (const lean_object*)&l_Dyadic_instHShiftLeftInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Dyadic_instHShiftLeftInt = (const lean_object*)&l_Dyadic_instHShiftLeftInt___closed__0_value;
static const lean_closure_object l_Dyadic_instHShiftRightInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instHShiftRightInt___closed__0 = (const lean_object*)&l_Dyadic_instHShiftRightInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Dyadic_instHShiftRightInt = (const lean_object*)&l_Dyadic_instHShiftRightInt___closed__0_value;
LEAN_EXPORT lean_object* l_Dyadic_instHShiftLeftNat___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Dyadic_instHShiftLeftNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_instHShiftLeftNat___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instHShiftLeftNat___closed__0 = (const lean_object*)&l_Dyadic_instHShiftLeftNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Dyadic_instHShiftLeftNat = (const lean_object*)&l_Dyadic_instHShiftLeftNat___closed__0_value;
LEAN_EXPORT lean_object* l_Dyadic_instHShiftRightNat___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Dyadic_instHShiftRightNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_instHShiftRightNat___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Dyadic_instHShiftRightNat___closed__0 = (const lean_object*)&l_Dyadic_instHShiftRightNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Dyadic_instHShiftRightNat = (const lean_object*)&l_Dyadic_instHShiftRightNat___closed__0_value;
LEAN_EXPORT lean_object* l_Int_cast___at___00Dyadic_toRat_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_toRat_spec__0(lean_object*);
static lean_once_cell_t l_Dyadic_toRat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Dyadic_toRat___closed__0;
LEAN_EXPORT lean_object* l_Dyadic_toRat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_precision(lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_precision___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Rat_toDyadic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_toDyadic___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_roundDown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_roundDown___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Dyadic_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_blt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Dyadic_ble(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ble___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_instLT;
LEAN_EXPORT lean_object* l_Dyadic_instLE;
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_roundUp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_roundUp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Dyadic_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
return v_k_6_;
}
else
{
lean_object* v_n_7_; lean_object* v_k_8_; lean_object* v___x_9_; 
v_n_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_n_7_);
v_k_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_k_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_3(v_k_6_, v_n_7_, v_k_8_, lean_box(0));
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Dyadic_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Dyadic_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_zero_elim___redArg(lean_object* v_t_22_, lean_object* v_zero_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Dyadic_ctorElim___redArg(v_t_22_, v_zero_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_zero_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_zero_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Dyadic_ctorElim___redArg(v_t_26_, v_zero_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofOdd_elim___redArg(lean_object* v_t_30_, lean_object* v_ofOdd_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Dyadic_ctorElim___redArg(v_t_30_, v_ofOdd_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofOdd_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_ofOdd_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Dyadic_ctorElim___redArg(v_t_34_, v_ofOdd_36_);
return v___x_37_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqDyadic_decEq(lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
if (lean_obj_tag(v_x_39_) == 0)
{
uint8_t v___x_40_; 
v___x_40_ = 1;
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = 0;
return v___x_41_;
}
}
else
{
if (lean_obj_tag(v_x_39_) == 0)
{
uint8_t v___x_42_; 
v___x_42_ = 0;
return v___x_42_;
}
else
{
lean_object* v_n_43_; lean_object* v_k_44_; lean_object* v_n_45_; lean_object* v_k_46_; uint8_t v___x_47_; 
v_n_43_ = lean_ctor_get(v_x_38_, 0);
v_k_44_ = lean_ctor_get(v_x_38_, 1);
v_n_45_ = lean_ctor_get(v_x_39_, 0);
v_k_46_ = lean_ctor_get(v_x_39_, 1);
v___x_47_ = lean_int_dec_eq(v_n_43_, v_n_45_);
if (v___x_47_ == 0)
{
return v___x_47_;
}
else
{
uint8_t v___x_48_; 
v___x_48_ = lean_int_dec_eq(v_k_44_, v_k_46_);
return v___x_48_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqDyadic_decEq___boxed(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_instDecidableEqDyadic_decEq(v_x_49_, v_x_50_);
lean_dec(v_x_50_);
lean_dec(v_x_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqDyadic(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
uint8_t v___x_55_; 
v___x_55_ = l_instDecidableEqDyadic_decEq(v_x_53_, v_x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqDyadic___boxed(lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_instDecidableEqDyadic(v_x_56_, v_x_57_);
lean_dec(v_x_57_);
lean_dec(v_x_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_ofIntWithPrec_spec__0(lean_object* v_a_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_nat_to_int(v_a_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Dyadic_ofIntWithPrec___closed__0(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = lean_nat_to_int(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec(lean_object* v_i_64_, lean_object* v_prec_65_){
_start:
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v___x_67_ = lean_int_dec_eq(v_i_64_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_68_ = lean_int_trailing_zeros(v_i_64_);
v___x_69_ = l_Int_shiftRight(v_i_64_, v___x_68_);
v___x_70_ = lean_nat_to_int(v___x_68_);
v___x_71_ = lean_int_sub(v_prec_65_, v___x_70_);
lean_dec(v___x_70_);
v___x_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_69_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
return v___x_72_;
}
else
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(0);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec___boxed(lean_object* v_i_74_, lean_object* v_prec_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Dyadic_ofIntWithPrec(v_i_74_, v_prec_75_);
lean_dec(v_prec_75_);
lean_dec(v_i_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofInt(lean_object* v_i_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v___x_79_ = l_Dyadic_ofIntWithPrec(v_i_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofInt___boxed(lean_object* v_i_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Dyadic_ofInt(v_i_80_);
lean_dec(v_i_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instOfNat(lean_object* v_n_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_nat_to_int(v_n_82_);
v___x_84_ = l_Dyadic_ofInt(v___x_83_);
lean_dec(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instNatCast___lam__0(lean_object* v_x_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_nat_to_int(v_x_87_);
v___x_89_ = l_Dyadic_ofInt(v___x_88_);
lean_dec(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_add(lean_object* v_x_92_, lean_object* v_y_93_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
return v_y_93_;
}
else
{
if (lean_obj_tag(v_y_93_) == 0)
{
lean_object* v_n_94_; lean_object* v_k_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v_n_94_ = lean_ctor_get(v_x_92_, 0);
v_k_95_ = lean_ctor_get(v_x_92_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v_x_92_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v_x_92_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_k_95_);
lean_inc(v_n_94_);
lean_dec(v_x_92_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_n_94_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_k_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
lean_object* v_n_103_; lean_object* v_k_104_; lean_object* v_n_105_; lean_object* v_k_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_132_; 
v_n_103_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_n_103_);
v_k_104_ = lean_ctor_get(v_x_92_, 1);
lean_inc(v_k_104_);
lean_dec_ref_known(v_x_92_, 2);
v_n_105_ = lean_ctor_get(v_y_93_, 0);
v_k_106_ = lean_ctor_get(v_y_93_, 1);
v_isSharedCheck_132_ = !lean_is_exclusive(v_y_93_);
if (v_isSharedCheck_132_ == 0)
{
v___x_108_ = v_y_93_;
v_isShared_109_ = v_isSharedCheck_132_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_k_106_);
lean_inc(v_n_105_);
lean_dec(v_y_93_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_132_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v_natZero_111_; lean_object* v_intZero_112_; uint8_t v_isNeg_113_; 
v___x_110_ = lean_int_sub(v_k_104_, v_k_106_);
v_natZero_111_ = lean_unsigned_to_nat(0u);
v_intZero_112_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_113_ = lean_int_dec_lt(v___x_110_, v_intZero_112_);
if (v_isNeg_113_ == 0)
{
lean_object* v_a_114_; uint8_t v_isZero_115_; 
lean_dec(v_k_106_);
v_a_114_ = lean_nat_abs(v___x_110_);
lean_dec(v___x_110_);
v_isZero_115_ = lean_nat_dec_eq(v_a_114_, v_natZero_111_);
if (v_isZero_115_ == 1)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v_a_114_);
lean_del_object(v___x_108_);
v___x_116_ = lean_int_add(v_n_103_, v_n_105_);
lean_dec(v_n_105_);
lean_dec(v_n_103_);
v___x_117_ = l_Dyadic_ofIntWithPrec(v___x_116_, v_k_104_);
lean_dec(v_k_104_);
lean_dec(v___x_116_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_118_ = l_Int_shiftLeft(v_n_105_, v_a_114_);
lean_dec(v_a_114_);
lean_dec(v_n_105_);
v___x_119_ = lean_int_add(v_n_103_, v___x_118_);
lean_dec(v___x_118_);
lean_dec(v_n_103_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v_k_104_);
lean_ctor_set(v___x_108_, 0, v___x_119_);
v___x_121_ = v___x_108_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_k_104_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
else
{
lean_object* v_abs_123_; lean_object* v_one_124_; lean_object* v_a_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
lean_dec(v_k_104_);
v_abs_123_ = lean_nat_abs(v___x_110_);
lean_dec(v___x_110_);
v_one_124_ = lean_unsigned_to_nat(1u);
v_a_125_ = lean_nat_sub(v_abs_123_, v_one_124_);
lean_dec(v_abs_123_);
v___x_126_ = lean_nat_add(v_a_125_, v_one_124_);
lean_dec(v_a_125_);
v___x_127_ = l_Int_shiftLeft(v_n_103_, v___x_126_);
lean_dec(v___x_126_);
lean_dec(v_n_103_);
v___x_128_ = lean_int_add(v___x_127_, v_n_105_);
lean_dec(v_n_105_);
lean_dec(v___x_127_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_128_);
v___x_130_ = v___x_108_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_k_106_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_mul(lean_object* v_x_135_, lean_object* v_y_136_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_dec(v_y_136_);
return v_x_135_;
}
else
{
if (lean_obj_tag(v_y_136_) == 0)
{
return v_y_136_;
}
else
{
lean_object* v_n_137_; lean_object* v_k_138_; lean_object* v_n_139_; lean_object* v_k_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_149_; 
v_n_137_ = lean_ctor_get(v_x_135_, 0);
v_k_138_ = lean_ctor_get(v_x_135_, 1);
v_n_139_ = lean_ctor_get(v_y_136_, 0);
v_k_140_ = lean_ctor_get(v_y_136_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_y_136_);
if (v_isSharedCheck_149_ == 0)
{
v___x_142_ = v_y_136_;
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_k_140_);
lean_inc(v_n_139_);
lean_dec(v_y_136_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_144_ = lean_int_mul(v_n_137_, v_n_139_);
lean_dec(v_n_139_);
v___x_145_ = lean_int_add(v_k_138_, v_k_140_);
lean_dec(v_k_140_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___x_145_);
lean_ctor_set(v___x_142_, 0, v___x_144_);
v___x_147_ = v___x_142_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_mul___boxed(lean_object* v_x_150_, lean_object* v_y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Dyadic_mul(v_x_150_, v_y_151_);
lean_dec(v_x_150_);
return v_res_152_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__0(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v___x_156_ = l_Dyadic_ofInt(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__1(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_to_int(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__2(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_obj_once(&l_Dyadic_pow___closed__1, &l_Dyadic_pow___closed__1_once, _init_l_Dyadic_pow___closed__1);
v___x_160_ = l_Dyadic_ofInt(v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_pow(lean_object* v_x_161_, lean_object* v_i_162_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_nat_dec_eq(v_i_162_, v___x_163_);
lean_dec(v_i_162_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_once(&l_Dyadic_pow___closed__0, &l_Dyadic_pow___closed__0_once, _init_l_Dyadic_pow___closed__0);
return v___x_165_;
}
else
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&l_Dyadic_pow___closed__2, &l_Dyadic_pow___closed__2_once, _init_l_Dyadic_pow___closed__2);
return v___x_166_;
}
}
else
{
lean_object* v_n_167_; lean_object* v_k_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_178_; 
v_n_167_ = lean_ctor_get(v_x_161_, 0);
v_k_168_ = lean_ctor_get(v_x_161_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v_x_161_);
if (v_isSharedCheck_178_ == 0)
{
v___x_170_ = v_x_161_;
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_k_168_);
lean_inc(v_n_167_);
lean_dec(v_x_161_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_172_ = l_Int_pow(v_n_167_, v_i_162_);
lean_dec(v_n_167_);
v___x_173_ = lean_nat_to_int(v_i_162_);
v___x_174_ = lean_int_mul(v_k_168_, v___x_173_);
lean_dec(v___x_173_);
lean_dec(v_k_168_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 1, v___x_174_);
lean_ctor_set(v___x_170_, 0, v___x_172_);
v___x_176_ = v___x_170_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_neg(lean_object* v_x_181_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
return v_x_181_;
}
else
{
lean_object* v_n_182_; lean_object* v_k_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_191_; 
v_n_182_ = lean_ctor_get(v_x_181_, 0);
v_k_183_ = lean_ctor_get(v_x_181_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_191_ == 0)
{
v___x_185_ = v_x_181_;
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_k_183_);
lean_inc(v_n_182_);
lean_dec(v_x_181_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_int_neg(v_n_182_);
lean_dec(v_n_182_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_k_183_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_sub(lean_object* v_x_194_, lean_object* v_y_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = l_Dyadic_neg(v_y_195_);
v___x_197_ = l_Dyadic_add(v_x_194_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft(lean_object* v_x_200_, lean_object* v_i_201_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
return v_x_200_;
}
else
{
lean_object* v_n_202_; lean_object* v_k_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_211_; 
v_n_202_ = lean_ctor_get(v_x_200_, 0);
v_k_203_ = lean_ctor_get(v_x_200_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_211_ == 0)
{
v___x_205_ = v_x_200_;
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_k_203_);
lean_inc(v_n_202_);
lean_dec(v_x_200_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_211_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_int_sub(v_k_203_, v_i_201_);
lean_dec(v_k_203_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_n_202_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft___boxed(lean_object* v_x_212_, lean_object* v_i_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Dyadic_shiftLeft(v_x_212_, v_i_213_);
lean_dec(v_i_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftRight(lean_object* v_x_215_, lean_object* v_i_216_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
return v_x_215_;
}
else
{
lean_object* v_n_217_; lean_object* v_k_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_226_; 
v_n_217_ = lean_ctor_get(v_x_215_, 0);
v_k_218_ = lean_ctor_get(v_x_215_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_215_);
if (v_isSharedCheck_226_ == 0)
{
v___x_220_ = v_x_215_;
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_k_218_);
lean_inc(v_n_217_);
lean_dec(v_x_215_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = lean_int_add(v_k_218_, v_i_216_);
lean_dec(v_k_218_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_222_);
v___x_224_ = v___x_220_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_n_217_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftRight___boxed(lean_object* v_x_227_, lean_object* v_i_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Dyadic_shiftRight(v_x_227_, v_i_228_);
lean_dec(v_i_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instHShiftLeftNat___lam__0(lean_object* v_x_234_, lean_object* v_y_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_nat_to_int(v_y_235_);
v___x_237_ = l_Dyadic_shiftLeft(v_x_234_, v___x_236_);
lean_dec(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instHShiftRightNat___lam__0(lean_object* v_x_240_, lean_object* v_y_241_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_nat_to_int(v_y_241_);
v___x_243_ = l_Dyadic_shiftRight(v_x_240_, v___x_242_);
lean_dec(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Dyadic_toRat_spec__1(lean_object* v_a_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Rat_ofInt(v_a_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_toRat_spec__0(lean_object* v_a_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_nat_to_int(v_a_248_);
v___x_250_ = l_Rat_ofInt(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Dyadic_toRat___closed__0(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = l_Nat_cast___at___00Dyadic_toRat_spec__0(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_toRat(lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_object* v___x_254_; 
v___x_254_ = lean_obj_once(&l_Dyadic_toRat___closed__0, &l_Dyadic_toRat___closed__0_once, _init_l_Dyadic_toRat___closed__0);
return v___x_254_;
}
else
{
lean_object* v_n_255_; lean_object* v_k_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_277_; 
v_n_255_ = lean_ctor_get(v_x_253_, 0);
v_k_256_ = lean_ctor_get(v_x_253_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_253_);
if (v_isSharedCheck_277_ == 0)
{
v___x_258_ = v_x_253_;
v_isShared_259_ = v_isSharedCheck_277_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_k_256_);
lean_inc(v_n_255_);
lean_dec(v_x_253_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_277_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_intZero_260_; uint8_t v_isNeg_261_; 
v_intZero_260_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_261_ = lean_int_dec_lt(v_k_256_, v_intZero_260_);
if (v_isNeg_261_ == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v_a_262_ = lean_nat_abs(v_k_256_);
lean_dec(v_k_256_);
v___x_263_ = lean_unsigned_to_nat(2u);
v___x_264_ = lean_nat_pow(v___x_263_, v_a_262_);
lean_dec(v_a_262_);
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 0);
lean_ctor_set(v___x_258_, 1, v___x_264_);
v___x_266_ = v___x_258_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_n_255_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
else
{
lean_object* v_abs_268_; lean_object* v_one_269_; lean_object* v_a_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_del_object(v___x_258_);
v_abs_268_ = lean_nat_abs(v_k_256_);
lean_dec(v_k_256_);
v_one_269_ = lean_unsigned_to_nat(1u);
v_a_270_ = lean_nat_sub(v_abs_268_, v_one_269_);
lean_dec(v_abs_268_);
v___x_271_ = lean_unsigned_to_nat(2u);
v___x_272_ = lean_nat_add(v_a_270_, v_one_269_);
lean_dec(v_a_270_);
v___x_273_ = lean_nat_pow(v___x_271_, v___x_272_);
lean_dec(v___x_272_);
v___x_274_ = lean_nat_to_int(v___x_273_);
v___x_275_ = lean_int_mul(v_n_255_, v___x_274_);
lean_dec(v___x_274_);
lean_dec(v_n_255_);
v___x_276_ = l_Rat_ofInt(v___x_275_);
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter___redArg(lean_object* v_x_278_, lean_object* v_h__1_279_, lean_object* v_h__2_280_, lean_object* v_h__3_281_){
_start:
{
if (lean_obj_tag(v_x_278_) == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v_h__3_281_);
lean_dec(v_h__2_280_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_apply_1(v_h__1_279_, v___x_282_);
return v___x_283_;
}
else
{
lean_object* v_n_284_; lean_object* v_k_285_; lean_object* v_intZero_286_; uint8_t v_isNeg_287_; 
lean_dec(v_h__1_279_);
v_n_284_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_n_284_);
v_k_285_ = lean_ctor_get(v_x_278_, 1);
lean_inc(v_k_285_);
lean_dec_ref_known(v_x_278_, 2);
v_intZero_286_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_287_ = lean_int_dec_lt(v_k_285_, v_intZero_286_);
if (v_isNeg_287_ == 0)
{
lean_object* v_a_288_; lean_object* v___x_289_; 
lean_dec(v_h__3_281_);
v_a_288_ = lean_nat_abs(v_k_285_);
lean_dec(v_k_285_);
v___x_289_ = lean_apply_3(v_h__2_280_, v_n_284_, v_a_288_, lean_box(0));
return v___x_289_;
}
else
{
lean_object* v_abs_290_; lean_object* v_one_291_; lean_object* v_a_292_; lean_object* v___x_293_; 
lean_dec(v_h__2_280_);
v_abs_290_ = lean_nat_abs(v_k_285_);
lean_dec(v_k_285_);
v_one_291_ = lean_unsigned_to_nat(1u);
v_a_292_ = lean_nat_sub(v_abs_290_, v_one_291_);
lean_dec(v_abs_290_);
v___x_293_ = lean_apply_3(v_h__3_281_, v_n_284_, v_a_292_, lean_box(0));
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter(lean_object* v_motive_294_, lean_object* v_x_295_, lean_object* v_h__1_296_, lean_object* v_h__2_297_, lean_object* v_h__3_298_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v_h__3_298_);
lean_dec(v_h__2_297_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_apply_1(v_h__1_296_, v___x_299_);
return v___x_300_;
}
else
{
lean_object* v_n_301_; lean_object* v_k_302_; lean_object* v_intZero_303_; uint8_t v_isNeg_304_; 
lean_dec(v_h__1_296_);
v_n_301_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_n_301_);
v_k_302_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_k_302_);
lean_dec_ref_known(v_x_295_, 2);
v_intZero_303_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_304_ = lean_int_dec_lt(v_k_302_, v_intZero_303_);
if (v_isNeg_304_ == 0)
{
lean_object* v_a_305_; lean_object* v___x_306_; 
lean_dec(v_h__3_298_);
v_a_305_ = lean_nat_abs(v_k_302_);
lean_dec(v_k_302_);
v___x_306_ = lean_apply_3(v_h__2_297_, v_n_301_, v_a_305_, lean_box(0));
return v___x_306_;
}
else
{
lean_object* v_abs_307_; lean_object* v_one_308_; lean_object* v_a_309_; lean_object* v___x_310_; 
lean_dec(v_h__2_297_);
v_abs_307_ = lean_nat_abs(v_k_302_);
lean_dec(v_k_302_);
v_one_308_ = lean_unsigned_to_nat(1u);
v_a_309_ = lean_nat_sub(v_abs_307_, v_one_308_);
lean_dec(v_abs_307_);
v___x_310_ = lean_apply_3(v_h__3_298_, v_n_301_, v_a_309_, lean_box(0));
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter___redArg(lean_object* v_x_311_, lean_object* v_y_312_, lean_object* v_h__1_313_, lean_object* v_h__2_314_, lean_object* v_h__3_315_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
lean_object* v___x_316_; 
lean_dec(v_h__3_315_);
lean_dec(v_h__2_314_);
v___x_316_ = lean_apply_1(v_h__1_313_, v_y_312_);
return v___x_316_;
}
else
{
lean_dec(v_h__1_313_);
if (lean_obj_tag(v_y_312_) == 0)
{
lean_object* v_n_317_; lean_object* v_k_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_h__3_315_);
v_n_317_ = lean_ctor_get(v_x_311_, 0);
v_k_318_ = lean_ctor_get(v_x_311_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_311_);
if (v_isSharedCheck_326_ == 0)
{
v___x_320_ = v_x_311_;
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_k_318_);
lean_inc(v_n_317_);
lean_dec(v_x_311_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_n_317_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_k_318_);
v___x_323_ = v_reuseFailAlloc_325_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; 
v___x_324_ = lean_apply_2(v_h__2_314_, v___x_323_, lean_box(0));
return v___x_324_;
}
}
}
else
{
lean_object* v_n_327_; lean_object* v_k_328_; lean_object* v_n_329_; lean_object* v_k_330_; lean_object* v___x_331_; 
lean_dec(v_h__2_314_);
v_n_327_ = lean_ctor_get(v_x_311_, 0);
lean_inc(v_n_327_);
v_k_328_ = lean_ctor_get(v_x_311_, 1);
lean_inc(v_k_328_);
lean_dec_ref_known(v_x_311_, 2);
v_n_329_ = lean_ctor_get(v_y_312_, 0);
lean_inc(v_n_329_);
v_k_330_ = lean_ctor_get(v_y_312_, 1);
lean_inc(v_k_330_);
lean_dec_ref_known(v_y_312_, 2);
v___x_331_ = lean_apply_6(v_h__3_315_, v_n_327_, v_k_328_, lean_box(0), v_n_329_, v_k_330_, lean_box(0));
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter(lean_object* v_motive_332_, lean_object* v_x_333_, lean_object* v_y_334_, lean_object* v_h__1_335_, lean_object* v_h__2_336_, lean_object* v_h__3_337_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v___x_338_; 
lean_dec(v_h__3_337_);
lean_dec(v_h__2_336_);
v___x_338_ = lean_apply_1(v_h__1_335_, v_y_334_);
return v___x_338_;
}
else
{
lean_dec(v_h__1_335_);
if (lean_obj_tag(v_y_334_) == 0)
{
lean_object* v_n_339_; lean_object* v_k_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_h__3_337_);
v_n_339_ = lean_ctor_get(v_x_333_, 0);
v_k_340_ = lean_ctor_get(v_x_333_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v_x_333_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_k_340_);
lean_inc(v_n_339_);
lean_dec(v_x_333_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_n_339_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_k_340_);
v___x_345_ = v_reuseFailAlloc_347_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; 
v___x_346_ = lean_apply_2(v_h__2_336_, v___x_345_, lean_box(0));
return v___x_346_;
}
}
}
else
{
lean_object* v_n_349_; lean_object* v_k_350_; lean_object* v_n_351_; lean_object* v_k_352_; lean_object* v___x_353_; 
lean_dec(v_h__2_336_);
v_n_349_ = lean_ctor_get(v_x_333_, 0);
lean_inc(v_n_349_);
v_k_350_ = lean_ctor_get(v_x_333_, 1);
lean_inc(v_k_350_);
lean_dec_ref_known(v_x_333_, 2);
v_n_351_ = lean_ctor_get(v_y_334_, 0);
lean_inc(v_n_351_);
v_k_352_ = lean_ctor_get(v_y_334_, 1);
lean_inc(v_k_352_);
lean_dec_ref_known(v_y_334_, 2);
v___x_353_ = lean_apply_6(v_h__3_337_, v_n_349_, v_k_350_, lean_box(0), v_n_351_, v_k_352_, lean_box(0));
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(lean_object* v_x_354_, lean_object* v_h__1_355_, lean_object* v_h__2_356_, lean_object* v_h__3_357_){
_start:
{
lean_object* v_natZero_358_; lean_object* v_intZero_359_; uint8_t v_isNeg_360_; 
v_natZero_358_ = lean_unsigned_to_nat(0u);
v_intZero_359_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_360_ = lean_int_dec_lt(v_x_354_, v_intZero_359_);
if (v_isNeg_360_ == 0)
{
lean_object* v_a_361_; uint8_t v_isZero_362_; 
lean_dec(v_h__3_357_);
v_a_361_ = lean_nat_abs(v_x_354_);
v_isZero_362_ = lean_nat_dec_eq(v_a_361_, v_natZero_358_);
if (v_isZero_362_ == 1)
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v_a_361_);
lean_dec(v_h__2_356_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_apply_1(v_h__1_355_, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v_one_365_; lean_object* v_n_366_; lean_object* v___x_367_; 
lean_dec(v_h__1_355_);
v_one_365_ = lean_unsigned_to_nat(1u);
v_n_366_ = lean_nat_sub(v_a_361_, v_one_365_);
lean_dec(v_a_361_);
v___x_367_ = lean_apply_1(v_h__2_356_, v_n_366_);
return v___x_367_;
}
}
else
{
lean_object* v_abs_368_; lean_object* v_one_369_; lean_object* v_a_370_; lean_object* v___x_371_; 
lean_dec(v_h__2_356_);
lean_dec(v_h__1_355_);
v_abs_368_ = lean_nat_abs(v_x_354_);
v_one_369_ = lean_unsigned_to_nat(1u);
v_a_370_ = lean_nat_sub(v_abs_368_, v_one_369_);
lean_dec(v_abs_368_);
v___x_371_ = lean_apply_1(v_h__3_357_, v_a_370_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg___boxed(lean_object* v_x_372_, lean_object* v_h__1_373_, lean_object* v_h__2_374_, lean_object* v_h__3_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(v_x_372_, v_h__1_373_, v_h__2_374_, v_h__3_375_);
lean_dec(v_x_372_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(lean_object* v_motive_377_, lean_object* v_x_378_, lean_object* v_h__1_379_, lean_object* v_h__2_380_, lean_object* v_h__3_381_){
_start:
{
lean_object* v_natZero_382_; lean_object* v_intZero_383_; uint8_t v_isNeg_384_; 
v_natZero_382_ = lean_unsigned_to_nat(0u);
v_intZero_383_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_384_ = lean_int_dec_lt(v_x_378_, v_intZero_383_);
if (v_isNeg_384_ == 0)
{
lean_object* v_a_385_; uint8_t v_isZero_386_; 
lean_dec(v_h__3_381_);
v_a_385_ = lean_nat_abs(v_x_378_);
v_isZero_386_ = lean_nat_dec_eq(v_a_385_, v_natZero_382_);
if (v_isZero_386_ == 1)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v_a_385_);
lean_dec(v_h__2_380_);
v___x_387_ = lean_box(0);
v___x_388_ = lean_apply_1(v_h__1_379_, v___x_387_);
return v___x_388_;
}
else
{
lean_object* v_one_389_; lean_object* v_n_390_; lean_object* v___x_391_; 
lean_dec(v_h__1_379_);
v_one_389_ = lean_unsigned_to_nat(1u);
v_n_390_ = lean_nat_sub(v_a_385_, v_one_389_);
lean_dec(v_a_385_);
v___x_391_ = lean_apply_1(v_h__2_380_, v_n_390_);
return v___x_391_;
}
}
else
{
lean_object* v_abs_392_; lean_object* v_one_393_; lean_object* v_a_394_; lean_object* v___x_395_; 
lean_dec(v_h__2_380_);
lean_dec(v_h__1_379_);
v_abs_392_ = lean_nat_abs(v_x_378_);
v_one_393_ = lean_unsigned_to_nat(1u);
v_a_394_ = lean_nat_sub(v_abs_392_, v_one_393_);
lean_dec(v_abs_392_);
v___x_395_ = lean_apply_1(v_h__3_381_, v_a_394_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___boxed(lean_object* v_motive_396_, lean_object* v_x_397_, lean_object* v_h__1_398_, lean_object* v_h__2_399_, lean_object* v_h__3_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(v_motive_396_, v_x_397_, v_h__1_398_, v_h__2_399_, v_h__3_400_);
lean_dec(v_x_397_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter___redArg(lean_object* v_x_402_, lean_object* v_h__1_403_, lean_object* v_h__2_404_){
_start:
{
if (lean_obj_tag(v_x_402_) == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v_h__2_404_);
v___x_405_ = lean_box(0);
v___x_406_ = lean_apply_1(v_h__1_403_, v___x_405_);
return v___x_406_;
}
else
{
lean_object* v_n_407_; lean_object* v_k_408_; lean_object* v___x_409_; 
lean_dec(v_h__1_403_);
v_n_407_ = lean_ctor_get(v_x_402_, 0);
lean_inc(v_n_407_);
v_k_408_ = lean_ctor_get(v_x_402_, 1);
lean_inc(v_k_408_);
lean_dec_ref_known(v_x_402_, 2);
v___x_409_ = lean_apply_3(v_h__2_404_, v_n_407_, v_k_408_, lean_box(0));
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter(lean_object* v_motive_410_, lean_object* v_x_411_, lean_object* v_h__1_412_, lean_object* v_h__2_413_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v_h__2_413_);
v___x_414_ = lean_box(0);
v___x_415_ = lean_apply_1(v_h__1_412_, v___x_414_);
return v___x_415_;
}
else
{
lean_object* v_n_416_; lean_object* v_k_417_; lean_object* v___x_418_; 
lean_dec(v_h__1_412_);
v_n_416_ = lean_ctor_get(v_x_411_, 0);
lean_inc(v_n_416_);
v_k_417_ = lean_ctor_get(v_x_411_, 1);
lean_inc(v_k_417_);
lean_dec_ref_known(v_x_411_, 2);
v___x_418_ = lean_apply_3(v_h__2_413_, v_n_416_, v_k_417_, lean_box(0));
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_precision(lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
lean_object* v___x_420_; 
v___x_420_ = lean_box(0);
return v___x_420_;
}
else
{
lean_object* v_k_421_; lean_object* v___x_422_; 
v_k_421_ = lean_ctor_get(v_x_419_, 1);
lean_inc(v_k_421_);
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v_k_421_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_precision___boxed(lean_object* v_x_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Dyadic_precision(v_x_423_);
lean_dec(v_x_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Rat_toDyadic(lean_object* v_x_425_, lean_object* v_prec_426_){
_start:
{
lean_object* v_intZero_427_; uint8_t v_isNeg_428_; 
v_intZero_427_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_428_ = lean_int_dec_lt(v_prec_426_, v_intZero_427_);
if (v_isNeg_428_ == 0)
{
lean_object* v_num_429_; lean_object* v_den_430_; lean_object* v_a_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_num_429_ = lean_ctor_get(v_x_425_, 0);
lean_inc(v_num_429_);
v_den_430_ = lean_ctor_get(v_x_425_, 1);
lean_inc(v_den_430_);
lean_dec_ref(v_x_425_);
v_a_431_ = lean_nat_abs(v_prec_426_);
v___x_432_ = l_Int_shiftLeft(v_num_429_, v_a_431_);
lean_dec(v_a_431_);
lean_dec(v_num_429_);
v___x_433_ = lean_nat_to_int(v_den_430_);
v___x_434_ = lean_int_ediv(v___x_432_, v___x_433_);
lean_dec(v___x_433_);
lean_dec(v___x_432_);
v___x_435_ = l_Dyadic_ofIntWithPrec(v___x_434_, v_prec_426_);
lean_dec(v___x_434_);
return v___x_435_;
}
else
{
lean_object* v_num_436_; lean_object* v_den_437_; lean_object* v_abs_438_; lean_object* v_one_439_; lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_num_436_ = lean_ctor_get(v_x_425_, 0);
lean_inc(v_num_436_);
v_den_437_ = lean_ctor_get(v_x_425_, 1);
lean_inc(v_den_437_);
lean_dec_ref(v_x_425_);
v_abs_438_ = lean_nat_abs(v_prec_426_);
v_one_439_ = lean_unsigned_to_nat(1u);
v_a_440_ = lean_nat_sub(v_abs_438_, v_one_439_);
lean_dec(v_abs_438_);
v___x_441_ = lean_nat_add(v_a_440_, v_one_439_);
lean_dec(v_a_440_);
v___x_442_ = lean_nat_shiftl(v_den_437_, v___x_441_);
lean_dec(v___x_441_);
lean_dec(v_den_437_);
v___x_443_ = lean_nat_to_int(v___x_442_);
v___x_444_ = lean_int_ediv(v_num_436_, v___x_443_);
lean_dec(v___x_443_);
lean_dec(v_num_436_);
v___x_445_ = l_Dyadic_ofIntWithPrec(v___x_444_, v_prec_426_);
lean_dec(v___x_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_toDyadic___boxed(lean_object* v_x_446_, lean_object* v_prec_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Rat_toDyadic(v_x_446_, v_prec_447_);
lean_dec(v_prec_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(lean_object* v_prec_449_, lean_object* v_h__1_450_, lean_object* v_h__2_451_){
_start:
{
lean_object* v_intZero_452_; uint8_t v_isNeg_453_; 
v_intZero_452_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_453_ = lean_int_dec_lt(v_prec_449_, v_intZero_452_);
if (v_isNeg_453_ == 0)
{
lean_object* v_a_454_; lean_object* v___x_455_; 
lean_dec(v_h__2_451_);
v_a_454_ = lean_nat_abs(v_prec_449_);
v___x_455_ = lean_apply_1(v_h__1_450_, v_a_454_);
return v___x_455_;
}
else
{
lean_object* v_abs_456_; lean_object* v_one_457_; lean_object* v_a_458_; lean_object* v___x_459_; 
lean_dec(v_h__1_450_);
v_abs_456_ = lean_nat_abs(v_prec_449_);
v_one_457_ = lean_unsigned_to_nat(1u);
v_a_458_ = lean_nat_sub(v_abs_456_, v_one_457_);
lean_dec(v_abs_456_);
v___x_459_ = lean_apply_1(v_h__2_451_, v_a_458_);
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg___boxed(lean_object* v_prec_460_, lean_object* v_h__1_461_, lean_object* v_h__2_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(v_prec_460_, v_h__1_461_, v_h__2_462_);
lean_dec(v_prec_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(lean_object* v_motive_464_, lean_object* v_prec_465_, lean_object* v_h__1_466_, lean_object* v_h__2_467_){
_start:
{
lean_object* v_intZero_468_; uint8_t v_isNeg_469_; 
v_intZero_468_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_469_ = lean_int_dec_lt(v_prec_465_, v_intZero_468_);
if (v_isNeg_469_ == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
lean_dec(v_h__2_467_);
v_a_470_ = lean_nat_abs(v_prec_465_);
v___x_471_ = lean_apply_1(v_h__1_466_, v_a_470_);
return v___x_471_;
}
else
{
lean_object* v_abs_472_; lean_object* v_one_473_; lean_object* v_a_474_; lean_object* v___x_475_; 
lean_dec(v_h__1_466_);
v_abs_472_ = lean_nat_abs(v_prec_465_);
v_one_473_ = lean_unsigned_to_nat(1u);
v_a_474_ = lean_nat_sub(v_abs_472_, v_one_473_);
lean_dec(v_abs_472_);
v___x_475_ = lean_apply_1(v_h__2_467_, v_a_474_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___boxed(lean_object* v_motive_476_, lean_object* v_prec_477_, lean_object* v_h__1_478_, lean_object* v_h__2_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(v_motive_476_, v_prec_477_, v_h__1_478_, v_h__2_479_);
lean_dec(v_prec_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundDown(lean_object* v_x_481_, lean_object* v_prec_482_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
return v_x_481_;
}
else
{
lean_object* v_n_483_; lean_object* v_k_484_; lean_object* v___x_485_; lean_object* v_intZero_486_; uint8_t v_isNeg_487_; 
v_n_483_ = lean_ctor_get(v_x_481_, 0);
v_k_484_ = lean_ctor_get(v_x_481_, 1);
v___x_485_ = lean_int_sub(v_k_484_, v_prec_482_);
v_intZero_486_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_487_ = lean_int_dec_lt(v___x_485_, v_intZero_486_);
if (v_isNeg_487_ == 0)
{
lean_object* v_a_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_a_488_ = lean_nat_abs(v___x_485_);
lean_dec(v___x_485_);
v___x_489_ = l_Int_shiftRight(v_n_483_, v_a_488_);
lean_dec(v_a_488_);
v___x_490_ = l_Dyadic_ofIntWithPrec(v___x_489_, v_prec_482_);
lean_dec(v___x_489_);
return v___x_490_;
}
else
{
lean_dec(v___x_485_);
lean_inc_ref(v_x_481_);
return v_x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundDown___boxed(lean_object* v_x_491_, lean_object* v_prec_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Dyadic_roundDown(v_x_491_, v_prec_492_);
lean_dec(v_prec_492_);
lean_dec(v_x_491_);
return v_res_493_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_blt(lean_object* v_x_494_, lean_object* v_y_495_){
_start:
{
if (lean_obj_tag(v_x_494_) == 0)
{
if (lean_obj_tag(v_y_495_) == 0)
{
uint8_t v___x_496_; 
v___x_496_ = 0;
return v___x_496_;
}
else
{
lean_object* v_n_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_n_497_ = lean_ctor_get(v_y_495_, 0);
v___x_498_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v___x_499_ = lean_int_dec_lt(v___x_498_, v_n_497_);
return v___x_499_;
}
}
else
{
if (lean_obj_tag(v_y_495_) == 0)
{
lean_object* v_n_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_n_500_ = lean_ctor_get(v_x_494_, 0);
v___x_501_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v___x_502_ = lean_int_dec_lt(v_n_500_, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v_n_503_; lean_object* v_k_504_; lean_object* v_n_505_; lean_object* v_k_506_; lean_object* v___x_507_; lean_object* v_intZero_508_; uint8_t v_isNeg_509_; 
v_n_503_ = lean_ctor_get(v_x_494_, 0);
v_k_504_ = lean_ctor_get(v_x_494_, 1);
v_n_505_ = lean_ctor_get(v_y_495_, 0);
v_k_506_ = lean_ctor_get(v_y_495_, 1);
v___x_507_ = lean_int_sub(v_k_506_, v_k_504_);
v_intZero_508_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_509_ = lean_int_dec_lt(v___x_507_, v_intZero_508_);
if (v_isNeg_509_ == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_a_510_ = lean_nat_abs(v___x_507_);
lean_dec(v___x_507_);
v___x_511_ = l_Int_shiftLeft(v_n_503_, v_a_510_);
lean_dec(v_a_510_);
v___x_512_ = lean_int_dec_lt(v___x_511_, v_n_505_);
lean_dec(v___x_511_);
return v___x_512_;
}
else
{
lean_object* v_abs_513_; lean_object* v_one_514_; lean_object* v_a_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_abs_513_ = lean_nat_abs(v___x_507_);
lean_dec(v___x_507_);
v_one_514_ = lean_unsigned_to_nat(1u);
v_a_515_ = lean_nat_sub(v_abs_513_, v_one_514_);
lean_dec(v_abs_513_);
v___x_516_ = lean_nat_add(v_a_515_, v_one_514_);
lean_dec(v_a_515_);
v___x_517_ = l_Int_shiftLeft(v_n_505_, v___x_516_);
lean_dec(v___x_516_);
v___x_518_ = lean_int_dec_lt(v_n_503_, v___x_517_);
lean_dec(v___x_517_);
return v___x_518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_blt___boxed(lean_object* v_x_519_, lean_object* v_y_520_){
_start:
{
uint8_t v_res_521_; lean_object* v_r_522_; 
v_res_521_ = l_Dyadic_blt(v_x_519_, v_y_520_);
lean_dec(v_y_520_);
lean_dec(v_x_519_);
v_r_522_ = lean_box(v_res_521_);
return v_r_522_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_ble(lean_object* v_x_523_, lean_object* v_y_524_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
if (lean_obj_tag(v_y_524_) == 0)
{
uint8_t v___x_525_; 
v___x_525_ = 1;
return v___x_525_;
}
else
{
lean_object* v_n_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_n_526_ = lean_ctor_get(v_y_524_, 0);
v___x_527_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v___x_528_ = lean_int_dec_le(v___x_527_, v_n_526_);
return v___x_528_;
}
}
else
{
if (lean_obj_tag(v_y_524_) == 0)
{
lean_object* v_n_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_n_529_ = lean_ctor_get(v_x_523_, 0);
v___x_530_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v___x_531_ = lean_int_dec_le(v_n_529_, v___x_530_);
return v___x_531_;
}
else
{
lean_object* v_n_532_; lean_object* v_k_533_; lean_object* v_n_534_; lean_object* v_k_535_; lean_object* v___x_536_; lean_object* v_intZero_537_; uint8_t v_isNeg_538_; 
v_n_532_ = lean_ctor_get(v_x_523_, 0);
v_k_533_ = lean_ctor_get(v_x_523_, 1);
v_n_534_ = lean_ctor_get(v_y_524_, 0);
v_k_535_ = lean_ctor_get(v_y_524_, 1);
v___x_536_ = lean_int_sub(v_k_535_, v_k_533_);
v_intZero_537_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_538_ = lean_int_dec_lt(v___x_536_, v_intZero_537_);
if (v_isNeg_538_ == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_a_539_ = lean_nat_abs(v___x_536_);
lean_dec(v___x_536_);
v___x_540_ = l_Int_shiftLeft(v_n_532_, v_a_539_);
lean_dec(v_a_539_);
v___x_541_ = lean_int_dec_le(v___x_540_, v_n_534_);
lean_dec(v___x_540_);
return v___x_541_;
}
else
{
lean_object* v_abs_542_; lean_object* v_one_543_; lean_object* v_a_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_abs_542_ = lean_nat_abs(v___x_536_);
lean_dec(v___x_536_);
v_one_543_ = lean_unsigned_to_nat(1u);
v_a_544_ = lean_nat_sub(v_abs_542_, v_one_543_);
lean_dec(v_abs_542_);
v___x_545_ = lean_nat_add(v_a_544_, v_one_543_);
lean_dec(v_a_544_);
v___x_546_ = l_Int_shiftLeft(v_n_534_, v___x_545_);
lean_dec(v___x_545_);
v___x_547_ = lean_int_dec_le(v_n_532_, v___x_546_);
lean_dec(v___x_546_);
return v___x_547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ble___boxed(lean_object* v_x_548_, lean_object* v_y_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Dyadic_ble(v_x_548_, v_y_549_);
lean_dec(v_y_549_);
lean_dec(v_x_548_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter___redArg(lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_h__1_554_, lean_object* v_h__2_555_, lean_object* v_h__3_556_, lean_object* v_h__4_557_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
lean_dec(v_h__4_557_);
lean_dec(v_h__3_556_);
if (lean_obj_tag(v_x_553_) == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec(v_h__2_555_);
v___x_558_ = lean_box(0);
v___x_559_ = lean_apply_1(v_h__1_554_, v___x_558_);
return v___x_559_;
}
else
{
lean_object* v_n_560_; lean_object* v_k_561_; lean_object* v___x_562_; 
lean_dec(v_h__1_554_);
v_n_560_ = lean_ctor_get(v_x_553_, 0);
lean_inc(v_n_560_);
v_k_561_ = lean_ctor_get(v_x_553_, 1);
lean_inc(v_k_561_);
lean_dec_ref_known(v_x_553_, 2);
v___x_562_ = lean_apply_3(v_h__2_555_, v_n_560_, v_k_561_, lean_box(0));
return v___x_562_;
}
}
else
{
lean_dec(v_h__2_555_);
lean_dec(v_h__1_554_);
if (lean_obj_tag(v_x_553_) == 0)
{
lean_object* v_n_563_; lean_object* v_k_564_; lean_object* v___x_565_; 
lean_dec(v_h__4_557_);
v_n_563_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_n_563_);
v_k_564_ = lean_ctor_get(v_x_552_, 1);
lean_inc(v_k_564_);
lean_dec_ref_known(v_x_552_, 2);
v___x_565_ = lean_apply_3(v_h__3_556_, v_n_563_, v_k_564_, lean_box(0));
return v___x_565_;
}
else
{
lean_object* v_n_566_; lean_object* v_k_567_; lean_object* v_n_568_; lean_object* v_k_569_; lean_object* v___x_570_; 
lean_dec(v_h__3_556_);
v_n_566_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_n_566_);
v_k_567_ = lean_ctor_get(v_x_552_, 1);
lean_inc(v_k_567_);
lean_dec_ref_known(v_x_552_, 2);
v_n_568_ = lean_ctor_get(v_x_553_, 0);
lean_inc(v_n_568_);
v_k_569_ = lean_ctor_get(v_x_553_, 1);
lean_inc(v_k_569_);
lean_dec_ref_known(v_x_553_, 2);
v___x_570_ = lean_apply_6(v_h__4_557_, v_n_566_, v_k_567_, lean_box(0), v_n_568_, v_k_569_, lean_box(0));
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter(lean_object* v_motive_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_h__1_574_, lean_object* v_h__2_575_, lean_object* v_h__3_576_, lean_object* v_h__4_577_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
lean_dec(v_h__4_577_);
lean_dec(v_h__3_576_);
if (lean_obj_tag(v_x_573_) == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_h__2_575_);
v___x_578_ = lean_box(0);
v___x_579_ = lean_apply_1(v_h__1_574_, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v_n_580_; lean_object* v_k_581_; lean_object* v___x_582_; 
lean_dec(v_h__1_574_);
v_n_580_ = lean_ctor_get(v_x_573_, 0);
lean_inc(v_n_580_);
v_k_581_ = lean_ctor_get(v_x_573_, 1);
lean_inc(v_k_581_);
lean_dec_ref_known(v_x_573_, 2);
v___x_582_ = lean_apply_3(v_h__2_575_, v_n_580_, v_k_581_, lean_box(0));
return v___x_582_;
}
}
else
{
lean_dec(v_h__2_575_);
lean_dec(v_h__1_574_);
if (lean_obj_tag(v_x_573_) == 0)
{
lean_object* v_n_583_; lean_object* v_k_584_; lean_object* v___x_585_; 
lean_dec(v_h__4_577_);
v_n_583_ = lean_ctor_get(v_x_572_, 0);
lean_inc(v_n_583_);
v_k_584_ = lean_ctor_get(v_x_572_, 1);
lean_inc(v_k_584_);
lean_dec_ref_known(v_x_572_, 2);
v___x_585_ = lean_apply_3(v_h__3_576_, v_n_583_, v_k_584_, lean_box(0));
return v___x_585_;
}
else
{
lean_object* v_n_586_; lean_object* v_k_587_; lean_object* v_n_588_; lean_object* v_k_589_; lean_object* v___x_590_; 
lean_dec(v_h__3_576_);
v_n_586_ = lean_ctor_get(v_x_572_, 0);
lean_inc(v_n_586_);
v_k_587_ = lean_ctor_get(v_x_572_, 1);
lean_inc(v_k_587_);
lean_dec_ref_known(v_x_572_, 2);
v_n_588_ = lean_ctor_get(v_x_573_, 0);
lean_inc(v_n_588_);
v_k_589_ = lean_ctor_get(v_x_573_, 1);
lean_inc(v_k_589_);
lean_dec_ref_known(v_x_573_, 2);
v___x_590_ = lean_apply_6(v_h__4_577_, v_n_586_, v_k_587_, lean_box(0), v_n_588_, v_k_589_, lean_box(0));
return v___x_590_;
}
}
}
}
static lean_object* _init_l_Dyadic_instLT(void){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = lean_box(0);
return v___x_591_;
}
}
static lean_object* _init_l_Dyadic_instLE(void){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = lean_box(0);
return v___x_592_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLT(lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = l_Dyadic_blt(v_x_593_, v_x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLT___boxed(lean_object* v_x_596_, lean_object* v_x_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l_Dyadic_instDecidableLT(v_x_596_, v_x_597_);
lean_dec(v_x_597_);
lean_dec(v_x_596_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLE(lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = l_Dyadic_ble(v_x_600_, v_x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLE___boxed(lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l_Dyadic_instDecidableLE(v_x_603_, v_x_604_);
lean_dec(v_x_604_);
lean_dec(v_x_603_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundUp(lean_object* v_x_607_, lean_object* v_prec_608_){
_start:
{
if (lean_obj_tag(v_x_607_) == 0)
{
return v_x_607_;
}
else
{
lean_object* v_n_609_; lean_object* v_k_610_; lean_object* v___x_611_; lean_object* v_intZero_612_; uint8_t v_isNeg_613_; 
v_n_609_ = lean_ctor_get(v_x_607_, 0);
v_k_610_ = lean_ctor_get(v_x_607_, 1);
v___x_611_ = lean_int_sub(v_k_610_, v_prec_608_);
v_intZero_612_ = lean_obj_once(&l_Dyadic_ofIntWithPrec___closed__0, &l_Dyadic_ofIntWithPrec___closed__0_once, _init_l_Dyadic_ofIntWithPrec___closed__0);
v_isNeg_613_ = lean_int_dec_lt(v___x_611_, v_intZero_612_);
if (v_isNeg_613_ == 0)
{
lean_object* v_a_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_a_614_ = lean_nat_abs(v___x_611_);
lean_dec(v___x_611_);
v___x_615_ = lean_int_neg(v_n_609_);
v___x_616_ = l_Int_shiftRight(v___x_615_, v_a_614_);
lean_dec(v_a_614_);
lean_dec(v___x_615_);
v___x_617_ = lean_int_neg(v___x_616_);
lean_dec(v___x_616_);
v___x_618_ = l_Dyadic_ofIntWithPrec(v___x_617_, v_prec_608_);
lean_dec(v___x_617_);
return v___x_618_;
}
else
{
lean_dec(v___x_611_);
lean_inc_ref(v_x_607_);
return v_x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundUp___boxed(lean_object* v_x_619_, lean_object* v_prec_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Dyadic_roundUp(v_x_619_, v_prec_620_);
lean_dec(v_prec_620_);
lean_dec(v_x_619_);
return v_res_621_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Dyadic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Dyadic_instLT = _init_l_Dyadic_instLT();
lean_mark_persistent(l_Dyadic_instLT);
l_Dyadic_instLE = _init_l_Dyadic_instLE();
lean_mark_persistent(l_Dyadic_instLE);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Dyadic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_Data_Rat_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Rat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Dyadic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Dyadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Dyadic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Dyadic_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
