// Lean compiler output
// Module: Init.Data.Dyadic.Basic
// Imports: import Init.Data.Int.Bitwise.Lemmas public import Init.Data.Int.Bitwise.Basic public import Init.Data.Order.Classes public import Init.Data.Rat.Basic import Init.ByCases import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.Pow import Init.Data.Nat.Bitwise.Lemmas import Init.Data.Option.Lemmas import Init.Data.Rat.Lemmas import Init.Omega
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Int_shiftRight(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_shiftLeft(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
static lean_once_cell_t l_Int_trailingZeros_aux___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_trailingZeros_aux___redArg___closed__0;
static lean_once_cell_t l_Int_trailingZeros_aux___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_trailingZeros_aux___redArg___closed__1;
LEAN_EXPORT lean_object* l_Int_trailingZeros_aux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_trailingZeros_aux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_trailingZeros(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_instOfNat(lean_object*);
static const lean_closure_object l_Dyadic_instIntCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Dyadic_ofInt, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Dyadic_precision(lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_precision___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Rat_toDyadic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_toDyadic___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_roundDown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_roundDown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Dyadic_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_blt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Dyadic_ble(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ble___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_instLT;
LEAN_EXPORT lean_object* l_Dyadic_instLE;
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_roundUp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_roundUp___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Int_trailingZeros_aux___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Int_trailingZeros_aux___redArg___closed__1(void){
_start:
{
lean_object* v_zero_3_; lean_object* v___x_4_; 
v_zero_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_to_int(v_zero_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Int_trailingZeros_aux___redArg(lean_object* v_k_5_, lean_object* v_i_6_, lean_object* v_acc_7_){
_start:
{
lean_object* v_zero_8_; uint8_t v_isZero_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v_zero_8_ = lean_unsigned_to_nat(0u);
v_isZero_9_ = lean_nat_dec_eq(v_k_5_, v_zero_8_);
v___x_10_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__0, &l_Int_trailingZeros_aux___redArg___closed__0_once, _init_l_Int_trailingZeros_aux___redArg___closed__0);
v___x_11_ = lean_int_emod(v_i_6_, v___x_10_);
v___x_12_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_13_ = lean_int_dec_eq(v___x_11_, v___x_12_);
lean_dec(v___x_11_);
if (v___x_13_ == 0)
{
lean_dec(v_i_6_);
lean_dec(v_k_5_);
return v_acc_7_;
}
else
{
lean_object* v_one_14_; lean_object* v_n_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_one_14_ = lean_unsigned_to_nat(1u);
v_n_15_ = lean_nat_sub(v_k_5_, v_one_14_);
lean_dec(v_k_5_);
v___x_16_ = lean_int_ediv(v_i_6_, v___x_10_);
lean_dec(v_i_6_);
v___x_17_ = lean_nat_add(v_acc_7_, v_one_14_);
lean_dec(v_acc_7_);
v_k_5_ = v_n_15_;
v_i_6_ = v___x_16_;
v_acc_7_ = v___x_17_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Int_trailingZeros_aux(lean_object* v_k_19_, lean_object* v_i_20_, lean_object* v_hi_21_, lean_object* v_hk_22_, lean_object* v_acc_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Int_trailingZeros_aux___redArg(v_k_19_, v_i_20_, v_acc_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Int_trailingZeros(lean_object* v_i_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_28_ = lean_int_dec_eq(v_i_25_, v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_nat_abs(v_i_25_);
v___x_30_ = l_Int_trailingZeros_aux___redArg(v___x_29_, v_i_25_, v___x_26_);
return v___x_30_;
}
else
{
lean_dec(v_i_25_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg(lean_object* v_k_31_, lean_object* v_h__1_32_){
_start:
{
lean_object* v_zero_33_; uint8_t v_isZero_34_; lean_object* v_one_35_; lean_object* v_n_36_; lean_object* v___x_37_; 
v_zero_33_ = lean_unsigned_to_nat(0u);
v_isZero_34_ = lean_nat_dec_eq(v_k_31_, v_zero_33_);
v_one_35_ = lean_unsigned_to_nat(1u);
v_n_36_ = lean_nat_sub(v_k_31_, v_one_35_);
v___x_37_ = lean_apply_3(v_h__1_32_, v_n_36_, lean_box(0), lean_box(0));
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg___boxed(lean_object* v_k_38_, lean_object* v_h__1_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg(v_k_38_, v_h__1_39_);
lean_dec(v_k_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter(lean_object* v_i_41_, lean_object* v_motive_42_, lean_object* v_k_43_, lean_object* v_x_44_, lean_object* v_hk_45_, lean_object* v_h__1_46_){
_start:
{
lean_object* v_zero_47_; uint8_t v_isZero_48_; lean_object* v_one_49_; lean_object* v_n_50_; lean_object* v___x_51_; 
v_zero_47_ = lean_unsigned_to_nat(0u);
v_isZero_48_ = lean_nat_dec_eq(v_k_43_, v_zero_47_);
v_one_49_ = lean_unsigned_to_nat(1u);
v_n_50_ = lean_nat_sub(v_k_43_, v_one_49_);
v___x_51_ = lean_apply_3(v_h__1_46_, v_n_50_, lean_box(0), lean_box(0));
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___boxed(lean_object* v_i_52_, lean_object* v_motive_53_, lean_object* v_k_54_, lean_object* v_x_55_, lean_object* v_hk_56_, lean_object* v_h__1_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter(v_i_52_, v_motive_53_, v_k_54_, v_x_55_, v_hk_56_, v_h__1_57_);
lean_dec(v_k_54_);
lean_dec(v_i_52_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx___impl(lean_object* v_x_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_obj_tag_nat(v_x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx___impl___boxed(lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Dyadic_ctorIdx___impl(v_x_61_);
lean_dec(v_x_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim___redArg(lean_object* v_t_63_, lean_object* v_k_64_){
_start:
{
if (lean_obj_tag(v_t_63_) == 0)
{
return v_k_64_;
}
else
{
lean_object* v_n_65_; lean_object* v_k_66_; lean_object* v___x_67_; 
v_n_65_ = lean_ctor_get(v_t_63_, 0);
lean_inc(v_n_65_);
v_k_66_ = lean_ctor_get(v_t_63_, 1);
lean_inc(v_k_66_);
lean_dec_ref_known(v_t_63_, 2);
v___x_67_ = lean_apply_3(v_k_64_, v_n_65_, v_k_66_, lean_box(0));
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim(lean_object* v_motive_68_, lean_object* v_ctorIdx_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_k_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Dyadic_ctorElim___redArg(v_t_70_, v_k_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim___boxed(lean_object* v_motive_74_, lean_object* v_ctorIdx_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_k_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Dyadic_ctorElim(v_motive_74_, v_ctorIdx_75_, v_t_76_, v_h_77_, v_k_78_);
lean_dec(v_ctorIdx_75_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_zero_elim___redArg(lean_object* v_t_80_, lean_object* v_zero_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Dyadic_ctorElim___redArg(v_t_80_, v_zero_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_zero_elim(lean_object* v_motive_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_zero_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Dyadic_ctorElim___redArg(v_t_84_, v_zero_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofOdd_elim___redArg(lean_object* v_t_88_, lean_object* v_ofOdd_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Dyadic_ctorElim___redArg(v_t_88_, v_ofOdd_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofOdd_elim(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_ofOdd_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Dyadic_ctorElim___redArg(v_t_92_, v_ofOdd_94_);
return v___x_95_;
}
}
uint8_t l_instDecidableEqDyadic_decEq(lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
if (lean_obj_tag(v_x_97_) == 0)
{
uint8_t v___x_98_; 
v___x_98_ = 1;
return v___x_98_;
}
else
{
uint8_t v___x_99_; 
v___x_99_ = 0;
return v___x_99_;
}
}
else
{
if (lean_obj_tag(v_x_97_) == 0)
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
else
{
lean_object* v_n_101_; lean_object* v_k_102_; lean_object* v_n_103_; lean_object* v_k_104_; uint8_t v___x_105_; 
v_n_101_ = lean_ctor_get(v_x_96_, 0);
v_k_102_ = lean_ctor_get(v_x_96_, 1);
v_n_103_ = lean_ctor_get(v_x_97_, 0);
v_k_104_ = lean_ctor_get(v_x_97_, 1);
v___x_105_ = lean_int_dec_eq(v_n_101_, v_n_103_);
if (v___x_105_ == 0)
{
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = lean_int_dec_eq(v_k_102_, v_k_104_);
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT void l_instDecidableEqDyadic_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_96_ = stack[0].m_obj;
lean_object* v_x_97_ = stack[1].m_obj;
uint8_t v_res_107_;
v_res_107_ = l_instDecidableEqDyadic_decEq(v_x_96_, v_x_97_);
stack->m_num = v_res_107_;
}
LEAN_EXPORT lean_object* l_instDecidableEqDyadic_decEq___boxed(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_instDecidableEqDyadic_decEq(v_x_108_, v_x_109_);
lean_dec(v_x_109_);
lean_dec(v_x_108_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
uint8_t l_instDecidableEqDyadic(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = l_instDecidableEqDyadic_decEq(v_x_112_, v_x_113_);
return v___x_114_;
}
}
LEAN_EXPORT void l_instDecidableEqDyadic_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_112_ = stack[0].m_obj;
lean_object* v_x_113_ = stack[1].m_obj;
uint8_t v_res_115_;
v_res_115_ = l_instDecidableEqDyadic(v_x_112_, v_x_113_);
stack->m_num = v_res_115_;
}
LEAN_EXPORT lean_object* l_instDecidableEqDyadic___boxed(lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_instDecidableEqDyadic(v_x_116_, v_x_117_);
lean_dec(v_x_117_);
lean_dec(v_x_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_ofIntWithPrec_spec__0(lean_object* v_a_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_nat_to_int(v_a_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec(lean_object* v_i_122_, lean_object* v_prec_123_){
_start:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_125_ = lean_int_dec_eq(v_i_122_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_inc(v_i_122_);
v___x_126_ = l_Int_trailingZeros(v_i_122_);
v___x_127_ = l_Int_shiftRight(v_i_122_, v___x_126_);
lean_dec(v_i_122_);
v___x_128_ = lean_nat_to_int(v___x_126_);
v___x_129_ = lean_int_sub(v_prec_123_, v___x_128_);
lean_dec(v___x_128_);
v___x_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_127_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; 
lean_dec(v_i_122_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec___boxed(lean_object* v_i_132_, lean_object* v_prec_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Dyadic_ofIntWithPrec(v_i_132_, v_prec_133_);
lean_dec(v_prec_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofInt(lean_object* v_i_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_137_ = l_Dyadic_ofIntWithPrec(v_i_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instOfNat(lean_object* v_n_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_nat_to_int(v_n_138_);
v___x_140_ = l_Dyadic_ofInt(v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instNatCast___lam__0(lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_nat_to_int(v_x_143_);
v___x_145_ = l_Dyadic_ofInt(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_add(lean_object* v_x_148_, lean_object* v_y_149_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
return v_y_149_;
}
else
{
if (lean_obj_tag(v_y_149_) == 0)
{
lean_object* v_n_150_; lean_object* v_k_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_n_150_ = lean_ctor_get(v_x_148_, 0);
v_k_151_ = lean_ctor_get(v_x_148_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v_x_148_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_k_151_);
lean_inc(v_n_150_);
lean_dec(v_x_148_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_n_150_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_k_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
else
{
lean_object* v_n_159_; lean_object* v_k_160_; lean_object* v_n_161_; lean_object* v_k_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_188_; 
v_n_159_ = lean_ctor_get(v_x_148_, 0);
lean_inc(v_n_159_);
v_k_160_ = lean_ctor_get(v_x_148_, 1);
lean_inc(v_k_160_);
lean_dec_ref_known(v_x_148_, 2);
v_n_161_ = lean_ctor_get(v_y_149_, 0);
v_k_162_ = lean_ctor_get(v_y_149_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_y_149_);
if (v_isSharedCheck_188_ == 0)
{
v___x_164_ = v_y_149_;
v_isShared_165_ = v_isSharedCheck_188_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_k_162_);
lean_inc(v_n_161_);
lean_dec(v_y_149_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_188_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v_natZero_167_; lean_object* v_intZero_168_; uint8_t v_isNeg_169_; 
v___x_166_ = lean_int_sub(v_k_160_, v_k_162_);
v_natZero_167_ = lean_unsigned_to_nat(0u);
v_intZero_168_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_169_ = lean_int_dec_lt(v___x_166_, v_intZero_168_);
if (v_isNeg_169_ == 0)
{
lean_object* v_a_170_; uint8_t v_isZero_171_; 
lean_dec(v_k_162_);
v_a_170_ = lean_nat_abs(v___x_166_);
lean_dec(v___x_166_);
v_isZero_171_ = lean_nat_dec_eq(v_a_170_, v_natZero_167_);
if (v_isZero_171_ == 1)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec(v_a_170_);
lean_del_object(v___x_164_);
v___x_172_ = lean_int_add(v_n_159_, v_n_161_);
lean_dec(v_n_161_);
lean_dec(v_n_159_);
v___x_173_ = l_Dyadic_ofIntWithPrec(v___x_172_, v_k_160_);
lean_dec(v_k_160_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_174_ = l_Int_shiftLeft(v_n_161_, v_a_170_);
lean_dec(v_a_170_);
lean_dec(v_n_161_);
v___x_175_ = lean_int_add(v_n_159_, v___x_174_);
lean_dec(v___x_174_);
lean_dec(v_n_159_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 1, v_k_160_);
lean_ctor_set(v___x_164_, 0, v___x_175_);
v___x_177_ = v___x_164_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_k_160_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
else
{
lean_object* v_abs_179_; lean_object* v_one_180_; lean_object* v_a_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec(v_k_160_);
v_abs_179_ = lean_nat_abs(v___x_166_);
lean_dec(v___x_166_);
v_one_180_ = lean_unsigned_to_nat(1u);
v_a_181_ = lean_nat_sub(v_abs_179_, v_one_180_);
lean_dec(v_abs_179_);
v___x_182_ = lean_nat_add(v_a_181_, v_one_180_);
lean_dec(v_a_181_);
v___x_183_ = l_Int_shiftLeft(v_n_159_, v___x_182_);
lean_dec(v___x_182_);
lean_dec(v_n_159_);
v___x_184_ = lean_int_add(v___x_183_, v_n_161_);
lean_dec(v_n_161_);
lean_dec(v___x_183_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_184_);
v___x_186_ = v___x_164_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_k_162_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_mul(lean_object* v_x_191_, lean_object* v_y_192_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_dec(v_y_192_);
return v_x_191_;
}
else
{
if (lean_obj_tag(v_y_192_) == 0)
{
return v_y_192_;
}
else
{
lean_object* v_n_193_; lean_object* v_k_194_; lean_object* v_n_195_; lean_object* v_k_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_205_; 
v_n_193_ = lean_ctor_get(v_x_191_, 0);
v_k_194_ = lean_ctor_get(v_x_191_, 1);
v_n_195_ = lean_ctor_get(v_y_192_, 0);
v_k_196_ = lean_ctor_get(v_y_192_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_y_192_);
if (v_isSharedCheck_205_ == 0)
{
v___x_198_ = v_y_192_;
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_k_196_);
lean_inc(v_n_195_);
lean_dec(v_y_192_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_200_ = lean_int_mul(v_n_193_, v_n_195_);
lean_dec(v_n_195_);
v___x_201_ = lean_int_add(v_k_194_, v_k_196_);
lean_dec(v_k_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v___x_201_);
lean_ctor_set(v___x_198_, 0, v___x_200_);
v___x_203_ = v___x_198_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_mul___boxed(lean_object* v_x_206_, lean_object* v_y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Dyadic_mul(v_x_206_, v_y_207_);
lean_dec(v_x_206_);
return v_res_208_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__0(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_212_ = l_Dyadic_ofInt(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__1(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_to_int(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__2(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_obj_once(&l_Dyadic_pow___closed__1, &l_Dyadic_pow___closed__1_once, _init_l_Dyadic_pow___closed__1);
v___x_216_ = l_Dyadic_ofInt(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_pow(lean_object* v_x_217_, lean_object* v_i_218_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_nat_dec_eq(v_i_218_, v___x_219_);
lean_dec(v_i_218_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Dyadic_pow___closed__0, &l_Dyadic_pow___closed__0_once, _init_l_Dyadic_pow___closed__0);
return v___x_221_;
}
else
{
lean_object* v___x_222_; 
v___x_222_ = lean_obj_once(&l_Dyadic_pow___closed__2, &l_Dyadic_pow___closed__2_once, _init_l_Dyadic_pow___closed__2);
return v___x_222_;
}
}
else
{
lean_object* v_n_223_; lean_object* v_k_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_234_; 
v_n_223_ = lean_ctor_get(v_x_217_, 0);
v_k_224_ = lean_ctor_get(v_x_217_, 1);
v_isSharedCheck_234_ = !lean_is_exclusive(v_x_217_);
if (v_isSharedCheck_234_ == 0)
{
v___x_226_ = v_x_217_;
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_k_224_);
lean_inc(v_n_223_);
lean_dec(v_x_217_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_234_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_228_ = l_Int_pow(v_n_223_, v_i_218_);
lean_dec(v_n_223_);
v___x_229_ = lean_nat_to_int(v_i_218_);
v___x_230_ = lean_int_mul(v_k_224_, v___x_229_);
lean_dec(v___x_229_);
lean_dec(v_k_224_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_230_);
lean_ctor_set(v___x_226_, 0, v___x_228_);
v___x_232_ = v___x_226_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_neg(lean_object* v_x_237_){
_start:
{
if (lean_obj_tag(v_x_237_) == 0)
{
return v_x_237_;
}
else
{
lean_object* v_n_238_; lean_object* v_k_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
v_n_238_ = lean_ctor_get(v_x_237_, 0);
v_k_239_ = lean_ctor_get(v_x_237_, 1);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_247_ == 0)
{
v___x_241_ = v_x_237_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_k_239_);
lean_inc(v_n_238_);
lean_dec(v_x_237_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_int_neg(v_n_238_);
lean_dec(v_n_238_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_k_239_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_sub(lean_object* v_x_250_, lean_object* v_y_251_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = l_Dyadic_neg(v_y_251_);
v___x_253_ = l_Dyadic_add(v_x_250_, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft(lean_object* v_x_256_, lean_object* v_i_257_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
return v_x_256_;
}
else
{
lean_object* v_n_258_; lean_object* v_k_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_267_; 
v_n_258_ = lean_ctor_get(v_x_256_, 0);
v_k_259_ = lean_ctor_get(v_x_256_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_267_ == 0)
{
v___x_261_ = v_x_256_;
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_k_259_);
lean_inc(v_n_258_);
lean_dec(v_x_256_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_int_sub(v_k_259_, v_i_257_);
lean_dec(v_k_259_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_n_258_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft___boxed(lean_object* v_x_268_, lean_object* v_i_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Dyadic_shiftLeft(v_x_268_, v_i_269_);
lean_dec(v_i_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftRight(lean_object* v_x_271_, lean_object* v_i_272_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
return v_x_271_;
}
else
{
lean_object* v_n_273_; lean_object* v_k_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v_n_273_ = lean_ctor_get(v_x_271_, 0);
v_k_274_ = lean_ctor_get(v_x_271_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_282_ == 0)
{
v___x_276_ = v_x_271_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_k_274_);
lean_inc(v_n_273_);
lean_dec(v_x_271_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_int_add(v_k_274_, v_i_272_);
lean_dec(v_k_274_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v___x_278_);
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_n_273_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftRight___boxed(lean_object* v_x_283_, lean_object* v_i_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Dyadic_shiftRight(v_x_283_, v_i_284_);
lean_dec(v_i_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instHShiftLeftNat___lam__0(lean_object* v_x_290_, lean_object* v_y_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_nat_to_int(v_y_291_);
v___x_293_ = l_Dyadic_shiftLeft(v_x_290_, v___x_292_);
lean_dec(v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instHShiftRightNat___lam__0(lean_object* v_x_296_, lean_object* v_y_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_nat_to_int(v_y_297_);
v___x_299_ = l_Dyadic_shiftRight(v_x_296_, v___x_298_);
lean_dec(v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Dyadic_toRat_spec__1(lean_object* v_a_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Rat_ofInt(v_a_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_toRat_spec__0(lean_object* v_a_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_nat_to_int(v_a_304_);
v___x_306_ = l_Rat_ofInt(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Dyadic_toRat___closed__0(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = l_Nat_cast___at___00Dyadic_toRat_spec__0(v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_toRat(lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_Dyadic_toRat___closed__0, &l_Dyadic_toRat___closed__0_once, _init_l_Dyadic_toRat___closed__0);
return v___x_310_;
}
else
{
lean_object* v_n_311_; lean_object* v_k_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_333_; 
v_n_311_ = lean_ctor_get(v_x_309_, 0);
v_k_312_ = lean_ctor_get(v_x_309_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_333_ == 0)
{
v___x_314_ = v_x_309_;
v_isShared_315_ = v_isSharedCheck_333_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_k_312_);
lean_inc(v_n_311_);
lean_dec(v_x_309_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_333_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_intZero_316_; uint8_t v_isNeg_317_; 
v_intZero_316_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_317_ = lean_int_dec_lt(v_k_312_, v_intZero_316_);
if (v_isNeg_317_ == 0)
{
lean_object* v_a_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v_a_318_ = lean_nat_abs(v_k_312_);
lean_dec(v_k_312_);
v___x_319_ = lean_unsigned_to_nat(2u);
v___x_320_ = lean_nat_pow(v___x_319_, v_a_318_);
lean_dec(v_a_318_);
if (v_isShared_315_ == 0)
{
lean_ctor_set_tag(v___x_314_, 0);
lean_ctor_set(v___x_314_, 1, v___x_320_);
v___x_322_ = v___x_314_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_n_311_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
else
{
lean_object* v_abs_324_; lean_object* v_one_325_; lean_object* v_a_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_del_object(v___x_314_);
v_abs_324_ = lean_nat_abs(v_k_312_);
lean_dec(v_k_312_);
v_one_325_ = lean_unsigned_to_nat(1u);
v_a_326_ = lean_nat_sub(v_abs_324_, v_one_325_);
lean_dec(v_abs_324_);
v___x_327_ = lean_unsigned_to_nat(2u);
v___x_328_ = lean_nat_add(v_a_326_, v_one_325_);
lean_dec(v_a_326_);
v___x_329_ = lean_nat_pow(v___x_327_, v___x_328_);
lean_dec(v___x_328_);
v___x_330_ = lean_nat_to_int(v___x_329_);
v___x_331_ = lean_int_mul(v_n_311_, v___x_330_);
lean_dec(v___x_330_);
lean_dec(v_n_311_);
v___x_332_ = l_Rat_ofInt(v___x_331_);
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter___redArg(lean_object* v_x_334_, lean_object* v_h__1_335_, lean_object* v_h__2_336_, lean_object* v_h__3_337_){
_start:
{
if (lean_obj_tag(v_x_334_) == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec(v_h__3_337_);
lean_dec(v_h__2_336_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_apply_1(v_h__1_335_, v___x_338_);
return v___x_339_;
}
else
{
lean_object* v_n_340_; lean_object* v_k_341_; lean_object* v_intZero_342_; uint8_t v_isNeg_343_; 
lean_dec(v_h__1_335_);
v_n_340_ = lean_ctor_get(v_x_334_, 0);
lean_inc(v_n_340_);
v_k_341_ = lean_ctor_get(v_x_334_, 1);
lean_inc(v_k_341_);
lean_dec_ref_known(v_x_334_, 2);
v_intZero_342_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_343_ = lean_int_dec_lt(v_k_341_, v_intZero_342_);
if (v_isNeg_343_ == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; 
lean_dec(v_h__3_337_);
v_a_344_ = lean_nat_abs(v_k_341_);
lean_dec(v_k_341_);
v___x_345_ = lean_apply_3(v_h__2_336_, v_n_340_, v_a_344_, lean_box(0));
return v___x_345_;
}
else
{
lean_object* v_abs_346_; lean_object* v_one_347_; lean_object* v_a_348_; lean_object* v___x_349_; 
lean_dec(v_h__2_336_);
v_abs_346_ = lean_nat_abs(v_k_341_);
lean_dec(v_k_341_);
v_one_347_ = lean_unsigned_to_nat(1u);
v_a_348_ = lean_nat_sub(v_abs_346_, v_one_347_);
lean_dec(v_abs_346_);
v___x_349_ = lean_apply_3(v_h__3_337_, v_n_340_, v_a_348_, lean_box(0));
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter(lean_object* v_motive_350_, lean_object* v_x_351_, lean_object* v_h__1_352_, lean_object* v_h__2_353_, lean_object* v_h__3_354_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v_h__3_354_);
lean_dec(v_h__2_353_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_apply_1(v_h__1_352_, v___x_355_);
return v___x_356_;
}
else
{
lean_object* v_n_357_; lean_object* v_k_358_; lean_object* v_intZero_359_; uint8_t v_isNeg_360_; 
lean_dec(v_h__1_352_);
v_n_357_ = lean_ctor_get(v_x_351_, 0);
lean_inc(v_n_357_);
v_k_358_ = lean_ctor_get(v_x_351_, 1);
lean_inc(v_k_358_);
lean_dec_ref_known(v_x_351_, 2);
v_intZero_359_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_360_ = lean_int_dec_lt(v_k_358_, v_intZero_359_);
if (v_isNeg_360_ == 0)
{
lean_object* v_a_361_; lean_object* v___x_362_; 
lean_dec(v_h__3_354_);
v_a_361_ = lean_nat_abs(v_k_358_);
lean_dec(v_k_358_);
v___x_362_ = lean_apply_3(v_h__2_353_, v_n_357_, v_a_361_, lean_box(0));
return v___x_362_;
}
else
{
lean_object* v_abs_363_; lean_object* v_one_364_; lean_object* v_a_365_; lean_object* v___x_366_; 
lean_dec(v_h__2_353_);
v_abs_363_ = lean_nat_abs(v_k_358_);
lean_dec(v_k_358_);
v_one_364_ = lean_unsigned_to_nat(1u);
v_a_365_ = lean_nat_sub(v_abs_363_, v_one_364_);
lean_dec(v_abs_363_);
v___x_366_ = lean_apply_3(v_h__3_354_, v_n_357_, v_a_365_, lean_box(0));
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter___redArg(lean_object* v_x_367_, lean_object* v_y_368_, lean_object* v_h__1_369_, lean_object* v_h__2_370_, lean_object* v_h__3_371_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_object* v___x_372_; 
lean_dec(v_h__3_371_);
lean_dec(v_h__2_370_);
v___x_372_ = lean_apply_1(v_h__1_369_, v_y_368_);
return v___x_372_;
}
else
{
lean_dec(v_h__1_369_);
if (lean_obj_tag(v_y_368_) == 0)
{
lean_object* v_n_373_; lean_object* v_k_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_h__3_371_);
v_n_373_ = lean_ctor_get(v_x_367_, 0);
v_k_374_ = lean_ctor_get(v_x_367_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v_x_367_);
if (v_isSharedCheck_382_ == 0)
{
v___x_376_ = v_x_367_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_k_374_);
lean_inc(v_n_373_);
lean_dec(v_x_367_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_n_373_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_k_374_);
v___x_379_ = v_reuseFailAlloc_381_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; 
v___x_380_ = lean_apply_2(v_h__2_370_, v___x_379_, lean_box(0));
return v___x_380_;
}
}
}
else
{
lean_object* v_n_383_; lean_object* v_k_384_; lean_object* v_n_385_; lean_object* v_k_386_; lean_object* v___x_387_; 
lean_dec(v_h__2_370_);
v_n_383_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_n_383_);
v_k_384_ = lean_ctor_get(v_x_367_, 1);
lean_inc(v_k_384_);
lean_dec_ref_known(v_x_367_, 2);
v_n_385_ = lean_ctor_get(v_y_368_, 0);
lean_inc(v_n_385_);
v_k_386_ = lean_ctor_get(v_y_368_, 1);
lean_inc(v_k_386_);
lean_dec_ref_known(v_y_368_, 2);
v___x_387_ = lean_apply_6(v_h__3_371_, v_n_383_, v_k_384_, lean_box(0), v_n_385_, v_k_386_, lean_box(0));
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter(lean_object* v_motive_388_, lean_object* v_x_389_, lean_object* v_y_390_, lean_object* v_h__1_391_, lean_object* v_h__2_392_, lean_object* v_h__3_393_){
_start:
{
if (lean_obj_tag(v_x_389_) == 0)
{
lean_object* v___x_394_; 
lean_dec(v_h__3_393_);
lean_dec(v_h__2_392_);
v___x_394_ = lean_apply_1(v_h__1_391_, v_y_390_);
return v___x_394_;
}
else
{
lean_dec(v_h__1_391_);
if (lean_obj_tag(v_y_390_) == 0)
{
lean_object* v_n_395_; lean_object* v_k_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_h__3_393_);
v_n_395_ = lean_ctor_get(v_x_389_, 0);
v_k_396_ = lean_ctor_get(v_x_389_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_x_389_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v_x_389_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_k_396_);
lean_inc(v_n_395_);
lean_dec(v_x_389_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_n_395_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_k_396_);
v___x_401_ = v_reuseFailAlloc_403_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; 
v___x_402_ = lean_apply_2(v_h__2_392_, v___x_401_, lean_box(0));
return v___x_402_;
}
}
}
else
{
lean_object* v_n_405_; lean_object* v_k_406_; lean_object* v_n_407_; lean_object* v_k_408_; lean_object* v___x_409_; 
lean_dec(v_h__2_392_);
v_n_405_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_n_405_);
v_k_406_ = lean_ctor_get(v_x_389_, 1);
lean_inc(v_k_406_);
lean_dec_ref_known(v_x_389_, 2);
v_n_407_ = lean_ctor_get(v_y_390_, 0);
lean_inc(v_n_407_);
v_k_408_ = lean_ctor_get(v_y_390_, 1);
lean_inc(v_k_408_);
lean_dec_ref_known(v_y_390_, 2);
v___x_409_ = lean_apply_6(v_h__3_393_, v_n_405_, v_k_406_, lean_box(0), v_n_407_, v_k_408_, lean_box(0));
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(lean_object* v_x_410_, lean_object* v_h__1_411_, lean_object* v_h__2_412_, lean_object* v_h__3_413_){
_start:
{
lean_object* v_natZero_414_; lean_object* v_intZero_415_; uint8_t v_isNeg_416_; 
v_natZero_414_ = lean_unsigned_to_nat(0u);
v_intZero_415_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_416_ = lean_int_dec_lt(v_x_410_, v_intZero_415_);
if (v_isNeg_416_ == 0)
{
lean_object* v_a_417_; uint8_t v_isZero_418_; 
lean_dec(v_h__3_413_);
v_a_417_ = lean_nat_abs(v_x_410_);
v_isZero_418_ = lean_nat_dec_eq(v_a_417_, v_natZero_414_);
if (v_isZero_418_ == 1)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_a_417_);
lean_dec(v_h__2_412_);
v___x_419_ = lean_box(0);
v___x_420_ = lean_apply_1(v_h__1_411_, v___x_419_);
return v___x_420_;
}
else
{
lean_object* v_one_421_; lean_object* v_n_422_; lean_object* v___x_423_; 
lean_dec(v_h__1_411_);
v_one_421_ = lean_unsigned_to_nat(1u);
v_n_422_ = lean_nat_sub(v_a_417_, v_one_421_);
lean_dec(v_a_417_);
v___x_423_ = lean_apply_1(v_h__2_412_, v_n_422_);
return v___x_423_;
}
}
else
{
lean_object* v_abs_424_; lean_object* v_one_425_; lean_object* v_a_426_; lean_object* v___x_427_; 
lean_dec(v_h__2_412_);
lean_dec(v_h__1_411_);
v_abs_424_ = lean_nat_abs(v_x_410_);
v_one_425_ = lean_unsigned_to_nat(1u);
v_a_426_ = lean_nat_sub(v_abs_424_, v_one_425_);
lean_dec(v_abs_424_);
v___x_427_ = lean_apply_1(v_h__3_413_, v_a_426_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg___boxed(lean_object* v_x_428_, lean_object* v_h__1_429_, lean_object* v_h__2_430_, lean_object* v_h__3_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(v_x_428_, v_h__1_429_, v_h__2_430_, v_h__3_431_);
lean_dec(v_x_428_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(lean_object* v_motive_433_, lean_object* v_x_434_, lean_object* v_h__1_435_, lean_object* v_h__2_436_, lean_object* v_h__3_437_){
_start:
{
lean_object* v_natZero_438_; lean_object* v_intZero_439_; uint8_t v_isNeg_440_; 
v_natZero_438_ = lean_unsigned_to_nat(0u);
v_intZero_439_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_440_ = lean_int_dec_lt(v_x_434_, v_intZero_439_);
if (v_isNeg_440_ == 0)
{
lean_object* v_a_441_; uint8_t v_isZero_442_; 
lean_dec(v_h__3_437_);
v_a_441_ = lean_nat_abs(v_x_434_);
v_isZero_442_ = lean_nat_dec_eq(v_a_441_, v_natZero_438_);
if (v_isZero_442_ == 1)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v_a_441_);
lean_dec(v_h__2_436_);
v___x_443_ = lean_box(0);
v___x_444_ = lean_apply_1(v_h__1_435_, v___x_443_);
return v___x_444_;
}
else
{
lean_object* v_one_445_; lean_object* v_n_446_; lean_object* v___x_447_; 
lean_dec(v_h__1_435_);
v_one_445_ = lean_unsigned_to_nat(1u);
v_n_446_ = lean_nat_sub(v_a_441_, v_one_445_);
lean_dec(v_a_441_);
v___x_447_ = lean_apply_1(v_h__2_436_, v_n_446_);
return v___x_447_;
}
}
else
{
lean_object* v_abs_448_; lean_object* v_one_449_; lean_object* v_a_450_; lean_object* v___x_451_; 
lean_dec(v_h__2_436_);
lean_dec(v_h__1_435_);
v_abs_448_ = lean_nat_abs(v_x_434_);
v_one_449_ = lean_unsigned_to_nat(1u);
v_a_450_ = lean_nat_sub(v_abs_448_, v_one_449_);
lean_dec(v_abs_448_);
v___x_451_ = lean_apply_1(v_h__3_437_, v_a_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___boxed(lean_object* v_motive_452_, lean_object* v_x_453_, lean_object* v_h__1_454_, lean_object* v_h__2_455_, lean_object* v_h__3_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(v_motive_452_, v_x_453_, v_h__1_454_, v_h__2_455_, v_h__3_456_);
lean_dec(v_x_453_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_precision(lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v_k_460_; lean_object* v___x_461_; 
v_k_460_ = lean_ctor_get(v_x_458_, 1);
lean_inc(v_k_460_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_k_460_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_precision___boxed(lean_object* v_x_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Dyadic_precision(v_x_462_);
lean_dec(v_x_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Rat_toDyadic(lean_object* v_x_464_, lean_object* v_prec_465_){
_start:
{
lean_object* v_intZero_466_; uint8_t v_isNeg_467_; 
v_intZero_466_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_467_ = lean_int_dec_lt(v_prec_465_, v_intZero_466_);
if (v_isNeg_467_ == 0)
{
lean_object* v_num_468_; lean_object* v_den_469_; lean_object* v_a_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_num_468_ = lean_ctor_get(v_x_464_, 0);
lean_inc(v_num_468_);
v_den_469_ = lean_ctor_get(v_x_464_, 1);
lean_inc(v_den_469_);
lean_dec_ref(v_x_464_);
v_a_470_ = lean_nat_abs(v_prec_465_);
v___x_471_ = l_Int_shiftLeft(v_num_468_, v_a_470_);
lean_dec(v_a_470_);
lean_dec(v_num_468_);
v___x_472_ = lean_nat_to_int(v_den_469_);
v___x_473_ = lean_int_ediv(v___x_471_, v___x_472_);
lean_dec(v___x_472_);
lean_dec(v___x_471_);
v___x_474_ = l_Dyadic_ofIntWithPrec(v___x_473_, v_prec_465_);
return v___x_474_;
}
else
{
lean_object* v_num_475_; lean_object* v_den_476_; lean_object* v_abs_477_; lean_object* v_one_478_; lean_object* v_a_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_num_475_ = lean_ctor_get(v_x_464_, 0);
lean_inc(v_num_475_);
v_den_476_ = lean_ctor_get(v_x_464_, 1);
lean_inc(v_den_476_);
lean_dec_ref(v_x_464_);
v_abs_477_ = lean_nat_abs(v_prec_465_);
v_one_478_ = lean_unsigned_to_nat(1u);
v_a_479_ = lean_nat_sub(v_abs_477_, v_one_478_);
lean_dec(v_abs_477_);
v___x_480_ = lean_nat_add(v_a_479_, v_one_478_);
lean_dec(v_a_479_);
v___x_481_ = lean_nat_shiftl(v_den_476_, v___x_480_);
lean_dec(v___x_480_);
lean_dec(v_den_476_);
v___x_482_ = lean_nat_to_int(v___x_481_);
v___x_483_ = lean_int_ediv(v_num_475_, v___x_482_);
lean_dec(v___x_482_);
lean_dec(v_num_475_);
v___x_484_ = l_Dyadic_ofIntWithPrec(v___x_483_, v_prec_465_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_toDyadic___boxed(lean_object* v_x_485_, lean_object* v_prec_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Rat_toDyadic(v_x_485_, v_prec_486_);
lean_dec(v_prec_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundDown(lean_object* v_x_488_, lean_object* v_prec_489_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
return v_x_488_;
}
else
{
lean_object* v_n_490_; lean_object* v_k_491_; lean_object* v___x_492_; lean_object* v_intZero_493_; uint8_t v_isNeg_494_; 
v_n_490_ = lean_ctor_get(v_x_488_, 0);
v_k_491_ = lean_ctor_get(v_x_488_, 1);
v___x_492_ = lean_int_sub(v_k_491_, v_prec_489_);
v_intZero_493_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_494_ = lean_int_dec_lt(v___x_492_, v_intZero_493_);
if (v_isNeg_494_ == 0)
{
lean_object* v_a_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_a_495_ = lean_nat_abs(v___x_492_);
lean_dec(v___x_492_);
v___x_496_ = l_Int_shiftRight(v_n_490_, v_a_495_);
lean_dec(v_a_495_);
v___x_497_ = l_Dyadic_ofIntWithPrec(v___x_496_, v_prec_489_);
return v___x_497_;
}
else
{
lean_dec(v___x_492_);
lean_inc_ref(v_x_488_);
return v_x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundDown___boxed(lean_object* v_x_498_, lean_object* v_prec_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Dyadic_roundDown(v_x_498_, v_prec_499_);
lean_dec(v_prec_499_);
lean_dec(v_x_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(lean_object* v_prec_501_, lean_object* v_h__1_502_, lean_object* v_h__2_503_){
_start:
{
lean_object* v_intZero_504_; uint8_t v_isNeg_505_; 
v_intZero_504_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_505_ = lean_int_dec_lt(v_prec_501_, v_intZero_504_);
if (v_isNeg_505_ == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
lean_dec(v_h__2_503_);
v_a_506_ = lean_nat_abs(v_prec_501_);
v___x_507_ = lean_apply_1(v_h__1_502_, v_a_506_);
return v___x_507_;
}
else
{
lean_object* v_abs_508_; lean_object* v_one_509_; lean_object* v_a_510_; lean_object* v___x_511_; 
lean_dec(v_h__1_502_);
v_abs_508_ = lean_nat_abs(v_prec_501_);
v_one_509_ = lean_unsigned_to_nat(1u);
v_a_510_ = lean_nat_sub(v_abs_508_, v_one_509_);
lean_dec(v_abs_508_);
v___x_511_ = lean_apply_1(v_h__2_503_, v_a_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg___boxed(lean_object* v_prec_512_, lean_object* v_h__1_513_, lean_object* v_h__2_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(v_prec_512_, v_h__1_513_, v_h__2_514_);
lean_dec(v_prec_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(lean_object* v_motive_516_, lean_object* v_prec_517_, lean_object* v_h__1_518_, lean_object* v_h__2_519_){
_start:
{
lean_object* v_intZero_520_; uint8_t v_isNeg_521_; 
v_intZero_520_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_521_ = lean_int_dec_lt(v_prec_517_, v_intZero_520_);
if (v_isNeg_521_ == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
lean_dec(v_h__2_519_);
v_a_522_ = lean_nat_abs(v_prec_517_);
v___x_523_ = lean_apply_1(v_h__1_518_, v_a_522_);
return v___x_523_;
}
else
{
lean_object* v_abs_524_; lean_object* v_one_525_; lean_object* v_a_526_; lean_object* v___x_527_; 
lean_dec(v_h__1_518_);
v_abs_524_ = lean_nat_abs(v_prec_517_);
v_one_525_ = lean_unsigned_to_nat(1u);
v_a_526_ = lean_nat_sub(v_abs_524_, v_one_525_);
lean_dec(v_abs_524_);
v___x_527_ = lean_apply_1(v_h__2_519_, v_a_526_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___boxed(lean_object* v_motive_528_, lean_object* v_prec_529_, lean_object* v_h__1_530_, lean_object* v_h__2_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(v_motive_528_, v_prec_529_, v_h__1_530_, v_h__2_531_);
lean_dec(v_prec_529_);
return v_res_532_;
}
}
uint8_t l_Dyadic_blt(lean_object* v_x_533_, lean_object* v_y_534_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
if (lean_obj_tag(v_y_534_) == 0)
{
uint8_t v___x_535_; 
v___x_535_ = 0;
return v___x_535_;
}
else
{
lean_object* v_n_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_n_536_ = lean_ctor_get(v_y_534_, 0);
v___x_537_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_538_ = lean_int_dec_lt(v___x_537_, v_n_536_);
return v___x_538_;
}
}
else
{
if (lean_obj_tag(v_y_534_) == 0)
{
lean_object* v_n_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_n_539_ = lean_ctor_get(v_x_533_, 0);
v___x_540_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_541_ = lean_int_dec_lt(v_n_539_, v___x_540_);
return v___x_541_;
}
else
{
lean_object* v_n_542_; lean_object* v_k_543_; lean_object* v_n_544_; lean_object* v_k_545_; lean_object* v___x_546_; lean_object* v_intZero_547_; uint8_t v_isNeg_548_; 
v_n_542_ = lean_ctor_get(v_x_533_, 0);
v_k_543_ = lean_ctor_get(v_x_533_, 1);
v_n_544_ = lean_ctor_get(v_y_534_, 0);
v_k_545_ = lean_ctor_get(v_y_534_, 1);
v___x_546_ = lean_int_sub(v_k_545_, v_k_543_);
v_intZero_547_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_548_ = lean_int_dec_lt(v___x_546_, v_intZero_547_);
if (v_isNeg_548_ == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_a_549_ = lean_nat_abs(v___x_546_);
lean_dec(v___x_546_);
v___x_550_ = l_Int_shiftLeft(v_n_542_, v_a_549_);
lean_dec(v_a_549_);
v___x_551_ = lean_int_dec_lt(v___x_550_, v_n_544_);
lean_dec(v___x_550_);
return v___x_551_;
}
else
{
lean_object* v_abs_552_; lean_object* v_one_553_; lean_object* v_a_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_abs_552_ = lean_nat_abs(v___x_546_);
lean_dec(v___x_546_);
v_one_553_ = lean_unsigned_to_nat(1u);
v_a_554_ = lean_nat_sub(v_abs_552_, v_one_553_);
lean_dec(v_abs_552_);
v___x_555_ = lean_nat_add(v_a_554_, v_one_553_);
lean_dec(v_a_554_);
v___x_556_ = l_Int_shiftLeft(v_n_544_, v___x_555_);
lean_dec(v___x_555_);
v___x_557_ = lean_int_dec_lt(v_n_542_, v___x_556_);
lean_dec(v___x_556_);
return v___x_557_;
}
}
}
}
}
LEAN_EXPORT void l_Dyadic_blt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_533_ = stack[0].m_obj;
lean_object* v_y_534_ = stack[1].m_obj;
uint8_t v_res_558_;
v_res_558_ = l_Dyadic_blt(v_x_533_, v_y_534_);
stack->m_num = v_res_558_;
}
LEAN_EXPORT lean_object* l_Dyadic_blt___boxed(lean_object* v_x_559_, lean_object* v_y_560_){
_start:
{
uint8_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = l_Dyadic_blt(v_x_559_, v_y_560_);
lean_dec(v_y_560_);
lean_dec(v_x_559_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
uint8_t l_Dyadic_ble(lean_object* v_x_563_, lean_object* v_y_564_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
if (lean_obj_tag(v_y_564_) == 0)
{
uint8_t v___x_565_; 
v___x_565_ = 1;
return v___x_565_;
}
else
{
lean_object* v_n_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_n_566_ = lean_ctor_get(v_y_564_, 0);
v___x_567_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_568_ = lean_int_dec_le(v___x_567_, v_n_566_);
return v___x_568_;
}
}
else
{
if (lean_obj_tag(v_y_564_) == 0)
{
lean_object* v_n_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v_n_569_ = lean_ctor_get(v_x_563_, 0);
v___x_570_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_571_ = lean_int_dec_le(v_n_569_, v___x_570_);
return v___x_571_;
}
else
{
lean_object* v_n_572_; lean_object* v_k_573_; lean_object* v_n_574_; lean_object* v_k_575_; lean_object* v___x_576_; lean_object* v_intZero_577_; uint8_t v_isNeg_578_; 
v_n_572_ = lean_ctor_get(v_x_563_, 0);
v_k_573_ = lean_ctor_get(v_x_563_, 1);
v_n_574_ = lean_ctor_get(v_y_564_, 0);
v_k_575_ = lean_ctor_get(v_y_564_, 1);
v___x_576_ = lean_int_sub(v_k_575_, v_k_573_);
v_intZero_577_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_578_ = lean_int_dec_lt(v___x_576_, v_intZero_577_);
if (v_isNeg_578_ == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_a_579_ = lean_nat_abs(v___x_576_);
lean_dec(v___x_576_);
v___x_580_ = l_Int_shiftLeft(v_n_572_, v_a_579_);
lean_dec(v_a_579_);
v___x_581_ = lean_int_dec_le(v___x_580_, v_n_574_);
lean_dec(v___x_580_);
return v___x_581_;
}
else
{
lean_object* v_abs_582_; lean_object* v_one_583_; lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_abs_582_ = lean_nat_abs(v___x_576_);
lean_dec(v___x_576_);
v_one_583_ = lean_unsigned_to_nat(1u);
v_a_584_ = lean_nat_sub(v_abs_582_, v_one_583_);
lean_dec(v_abs_582_);
v___x_585_ = lean_nat_add(v_a_584_, v_one_583_);
lean_dec(v_a_584_);
v___x_586_ = l_Int_shiftLeft(v_n_574_, v___x_585_);
lean_dec(v___x_585_);
v___x_587_ = lean_int_dec_le(v_n_572_, v___x_586_);
lean_dec(v___x_586_);
return v___x_587_;
}
}
}
}
}
LEAN_EXPORT void l_Dyadic_ble_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_563_ = stack[0].m_obj;
lean_object* v_y_564_ = stack[1].m_obj;
uint8_t v_res_588_;
v_res_588_ = l_Dyadic_ble(v_x_563_, v_y_564_);
stack->m_num = v_res_588_;
}
LEAN_EXPORT lean_object* l_Dyadic_ble___boxed(lean_object* v_x_589_, lean_object* v_y_590_){
_start:
{
uint8_t v_res_591_; lean_object* v_r_592_; 
v_res_591_ = l_Dyadic_ble(v_x_589_, v_y_590_);
lean_dec(v_y_590_);
lean_dec(v_x_589_);
v_r_592_ = lean_box(v_res_591_);
return v_r_592_;
}
}
static lean_object* _init_l_Dyadic_instLT(void){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = lean_box(0);
return v___x_593_;
}
}
static lean_object* _init_l_Dyadic_instLE(void){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_box(0);
return v___x_594_;
}
}
uint8_t l_Dyadic_instDecidableLT(lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = l_Dyadic_blt(v_x_595_, v_x_596_);
return v___x_597_;
}
}
LEAN_EXPORT void l_Dyadic_instDecidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_595_ = stack[0].m_obj;
lean_object* v_x_596_ = stack[1].m_obj;
uint8_t v_res_598_;
v_res_598_ = l_Dyadic_instDecidableLT(v_x_595_, v_x_596_);
stack->m_num = v_res_598_;
}
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLT___boxed(lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
uint8_t v_res_601_; lean_object* v_r_602_; 
v_res_601_ = l_Dyadic_instDecidableLT(v_x_599_, v_x_600_);
lean_dec(v_x_600_);
lean_dec(v_x_599_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
uint8_t l_Dyadic_instDecidableLE(lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
uint8_t v___x_605_; 
v___x_605_ = l_Dyadic_ble(v_x_603_, v_x_604_);
return v___x_605_;
}
}
LEAN_EXPORT void l_Dyadic_instDecidableLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_603_ = stack[0].m_obj;
lean_object* v_x_604_ = stack[1].m_obj;
uint8_t v_res_606_;
v_res_606_ = l_Dyadic_instDecidableLE(v_x_603_, v_x_604_);
stack->m_num = v_res_606_;
}
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLE___boxed(lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
uint8_t v_res_609_; lean_object* v_r_610_; 
v_res_609_ = l_Dyadic_instDecidableLE(v_x_607_, v_x_608_);
lean_dec(v_x_608_);
lean_dec(v_x_607_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundUp(lean_object* v_x_611_, lean_object* v_prec_612_){
_start:
{
if (lean_obj_tag(v_x_611_) == 0)
{
return v_x_611_;
}
else
{
lean_object* v_n_613_; lean_object* v_k_614_; lean_object* v___x_615_; lean_object* v_intZero_616_; uint8_t v_isNeg_617_; 
v_n_613_ = lean_ctor_get(v_x_611_, 0);
v_k_614_ = lean_ctor_get(v_x_611_, 1);
v___x_615_ = lean_int_sub(v_k_614_, v_prec_612_);
v_intZero_616_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_617_ = lean_int_dec_lt(v___x_615_, v_intZero_616_);
if (v_isNeg_617_ == 0)
{
lean_object* v_a_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_a_618_ = lean_nat_abs(v___x_615_);
lean_dec(v___x_615_);
v___x_619_ = lean_int_neg(v_n_613_);
v___x_620_ = l_Int_shiftRight(v___x_619_, v_a_618_);
lean_dec(v_a_618_);
lean_dec(v___x_619_);
v___x_621_ = lean_int_neg(v___x_620_);
lean_dec(v___x_620_);
v___x_622_ = l_Dyadic_ofIntWithPrec(v___x_621_, v_prec_612_);
return v___x_622_;
}
else
{
lean_dec(v___x_615_);
lean_inc_ref(v_x_611_);
return v_x_611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundUp___boxed(lean_object* v_x_623_, lean_object* v_prec_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Dyadic_roundUp(v_x_623_, v_prec_624_);
lean_dec(v_prec_624_);
lean_dec(v_x_623_);
return v_res_625_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
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
lean_object* initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin);
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
res = initialize_Init_Data_Int_Bitwise_Basic(builtin);
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
