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
LEAN_EXPORT uint8_t l_instDecidableEqDyadic_decEq(lean_object* v_x_96_, lean_object* v_x_97_){
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
LEAN_EXPORT lean_object* l_instDecidableEqDyadic_decEq___boxed(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_instDecidableEqDyadic_decEq(v_x_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqDyadic(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = l_instDecidableEqDyadic_decEq(v_x_111_, v_x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqDyadic___boxed(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_instDecidableEqDyadic(v_x_114_, v_x_115_);
lean_dec(v_x_115_);
lean_dec(v_x_114_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_ofIntWithPrec_spec__0(lean_object* v_a_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_nat_to_int(v_a_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec(lean_object* v_i_120_, lean_object* v_prec_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_123_ = lean_int_dec_eq(v_i_120_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_inc(v_i_120_);
v___x_124_ = l_Int_trailingZeros(v_i_120_);
v___x_125_ = l_Int_shiftRight(v_i_120_, v___x_124_);
lean_dec(v_i_120_);
v___x_126_ = lean_nat_to_int(v___x_124_);
v___x_127_ = lean_int_sub(v_prec_121_, v___x_126_);
lean_dec(v___x_126_);
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_125_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
return v___x_128_;
}
else
{
lean_object* v___x_129_; 
lean_dec(v_i_120_);
v___x_129_ = lean_box(0);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec___boxed(lean_object* v_i_130_, lean_object* v_prec_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Dyadic_ofIntWithPrec(v_i_130_, v_prec_131_);
lean_dec(v_prec_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofInt(lean_object* v_i_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_135_ = l_Dyadic_ofIntWithPrec(v_i_133_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instOfNat(lean_object* v_n_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_nat_to_int(v_n_136_);
v___x_138_ = l_Dyadic_ofInt(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instNatCast___lam__0(lean_object* v_x_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_nat_to_int(v_x_141_);
v___x_143_ = l_Dyadic_ofInt(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_add(lean_object* v_x_146_, lean_object* v_y_147_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
return v_y_147_;
}
else
{
if (lean_obj_tag(v_y_147_) == 0)
{
lean_object* v_n_148_; lean_object* v_k_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_n_148_ = lean_ctor_get(v_x_146_, 0);
v_k_149_ = lean_ctor_get(v_x_146_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_146_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v_x_146_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_k_149_);
lean_inc(v_n_148_);
lean_dec(v_x_146_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_n_148_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_k_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_object* v_n_157_; lean_object* v_k_158_; lean_object* v_n_159_; lean_object* v_k_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_186_; 
v_n_157_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_n_157_);
v_k_158_ = lean_ctor_get(v_x_146_, 1);
lean_inc(v_k_158_);
lean_dec_ref_known(v_x_146_, 2);
v_n_159_ = lean_ctor_get(v_y_147_, 0);
v_k_160_ = lean_ctor_get(v_y_147_, 1);
v_isSharedCheck_186_ = !lean_is_exclusive(v_y_147_);
if (v_isSharedCheck_186_ == 0)
{
v___x_162_ = v_y_147_;
v_isShared_163_ = v_isSharedCheck_186_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_k_160_);
lean_inc(v_n_159_);
lean_dec(v_y_147_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_186_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v_natZero_165_; lean_object* v_intZero_166_; uint8_t v_isNeg_167_; 
v___x_164_ = lean_int_sub(v_k_158_, v_k_160_);
v_natZero_165_ = lean_unsigned_to_nat(0u);
v_intZero_166_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_167_ = lean_int_dec_lt(v___x_164_, v_intZero_166_);
if (v_isNeg_167_ == 0)
{
lean_object* v_a_168_; uint8_t v_isZero_169_; 
lean_dec(v_k_160_);
v_a_168_ = lean_nat_abs(v___x_164_);
lean_dec(v___x_164_);
v_isZero_169_ = lean_nat_dec_eq(v_a_168_, v_natZero_165_);
if (v_isZero_169_ == 1)
{
lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec(v_a_168_);
lean_del_object(v___x_162_);
v___x_170_ = lean_int_add(v_n_157_, v_n_159_);
lean_dec(v_n_159_);
lean_dec(v_n_157_);
v___x_171_ = l_Dyadic_ofIntWithPrec(v___x_170_, v_k_158_);
lean_dec(v_k_158_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_172_ = l_Int_shiftLeft(v_n_159_, v_a_168_);
lean_dec(v_a_168_);
lean_dec(v_n_159_);
v___x_173_ = lean_int_add(v_n_157_, v___x_172_);
lean_dec(v___x_172_);
lean_dec(v_n_157_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 1, v_k_158_);
lean_ctor_set(v___x_162_, 0, v___x_173_);
v___x_175_ = v___x_162_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_k_158_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
else
{
lean_object* v_abs_177_; lean_object* v_one_178_; lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
lean_dec(v_k_158_);
v_abs_177_ = lean_nat_abs(v___x_164_);
lean_dec(v___x_164_);
v_one_178_ = lean_unsigned_to_nat(1u);
v_a_179_ = lean_nat_sub(v_abs_177_, v_one_178_);
lean_dec(v_abs_177_);
v___x_180_ = lean_nat_add(v_a_179_, v_one_178_);
lean_dec(v_a_179_);
v___x_181_ = l_Int_shiftLeft(v_n_157_, v___x_180_);
lean_dec(v___x_180_);
lean_dec(v_n_157_);
v___x_182_ = lean_int_add(v___x_181_, v_n_159_);
lean_dec(v_n_159_);
lean_dec(v___x_181_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_182_);
v___x_184_ = v___x_162_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_k_160_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_mul(lean_object* v_x_189_, lean_object* v_y_190_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_dec(v_y_190_);
return v_x_189_;
}
else
{
if (lean_obj_tag(v_y_190_) == 0)
{
return v_y_190_;
}
else
{
lean_object* v_n_191_; lean_object* v_k_192_; lean_object* v_n_193_; lean_object* v_k_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_203_; 
v_n_191_ = lean_ctor_get(v_x_189_, 0);
v_k_192_ = lean_ctor_get(v_x_189_, 1);
v_n_193_ = lean_ctor_get(v_y_190_, 0);
v_k_194_ = lean_ctor_get(v_y_190_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_y_190_);
if (v_isSharedCheck_203_ == 0)
{
v___x_196_ = v_y_190_;
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_k_194_);
lean_inc(v_n_193_);
lean_dec(v_y_190_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_198_ = lean_int_mul(v_n_191_, v_n_193_);
lean_dec(v_n_193_);
v___x_199_ = lean_int_add(v_k_192_, v_k_194_);
lean_dec(v_k_194_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v___x_199_);
lean_ctor_set(v___x_196_, 0, v___x_198_);
v___x_201_ = v___x_196_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_mul___boxed(lean_object* v_x_204_, lean_object* v_y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Dyadic_mul(v_x_204_, v_y_205_);
lean_dec(v_x_204_);
return v_res_206_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__0(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_210_ = l_Dyadic_ofInt(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_to_int(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__2(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_obj_once(&l_Dyadic_pow___closed__1, &l_Dyadic_pow___closed__1_once, _init_l_Dyadic_pow___closed__1);
v___x_214_ = l_Dyadic_ofInt(v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_pow(lean_object* v_x_215_, lean_object* v_i_216_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_nat_dec_eq(v_i_216_, v___x_217_);
lean_dec(v_i_216_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_obj_once(&l_Dyadic_pow___closed__0, &l_Dyadic_pow___closed__0_once, _init_l_Dyadic_pow___closed__0);
return v___x_219_;
}
else
{
lean_object* v___x_220_; 
v___x_220_ = lean_obj_once(&l_Dyadic_pow___closed__2, &l_Dyadic_pow___closed__2_once, _init_l_Dyadic_pow___closed__2);
return v___x_220_;
}
}
else
{
lean_object* v_n_221_; lean_object* v_k_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_232_; 
v_n_221_ = lean_ctor_get(v_x_215_, 0);
v_k_222_ = lean_ctor_get(v_x_215_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_215_);
if (v_isSharedCheck_232_ == 0)
{
v___x_224_ = v_x_215_;
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_k_222_);
lean_inc(v_n_221_);
lean_dec(v_x_215_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_226_ = l_Int_pow(v_n_221_, v_i_216_);
lean_dec(v_n_221_);
v___x_227_ = lean_nat_to_int(v_i_216_);
v___x_228_ = lean_int_mul(v_k_222_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v_k_222_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v___x_228_);
lean_ctor_set(v___x_224_, 0, v___x_226_);
v___x_230_ = v___x_224_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_neg(lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
return v_x_235_;
}
else
{
lean_object* v_n_236_; lean_object* v_k_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_245_; 
v_n_236_ = lean_ctor_get(v_x_235_, 0);
v_k_237_ = lean_ctor_get(v_x_235_, 1);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_235_);
if (v_isSharedCheck_245_ == 0)
{
v___x_239_ = v_x_235_;
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_k_237_);
lean_inc(v_n_236_);
lean_dec(v_x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_241_ = lean_int_neg(v_n_236_);
lean_dec(v_n_236_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_241_);
v___x_243_ = v___x_239_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_k_237_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_sub(lean_object* v_x_248_, lean_object* v_y_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = l_Dyadic_neg(v_y_249_);
v___x_251_ = l_Dyadic_add(v_x_248_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft(lean_object* v_x_254_, lean_object* v_i_255_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
return v_x_254_;
}
else
{
lean_object* v_n_256_; lean_object* v_k_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_n_256_ = lean_ctor_get(v_x_254_, 0);
v_k_257_ = lean_ctor_get(v_x_254_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_265_ == 0)
{
v___x_259_ = v_x_254_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_k_257_);
lean_inc(v_n_256_);
lean_dec(v_x_254_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_int_sub(v_k_257_, v_i_255_);
lean_dec(v_k_257_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_n_256_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft___boxed(lean_object* v_x_266_, lean_object* v_i_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Dyadic_shiftLeft(v_x_266_, v_i_267_);
lean_dec(v_i_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftRight(lean_object* v_x_269_, lean_object* v_i_270_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
return v_x_269_;
}
else
{
lean_object* v_n_271_; lean_object* v_k_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_280_; 
v_n_271_ = lean_ctor_get(v_x_269_, 0);
v_k_272_ = lean_ctor_get(v_x_269_, 1);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_269_);
if (v_isSharedCheck_280_ == 0)
{
v___x_274_ = v_x_269_;
v_isShared_275_ = v_isSharedCheck_280_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_k_272_);
lean_inc(v_n_271_);
lean_dec(v_x_269_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_280_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = lean_int_add(v_k_272_, v_i_270_);
lean_dec(v_k_272_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 1, v___x_276_);
v___x_278_ = v___x_274_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_n_271_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftRight___boxed(lean_object* v_x_281_, lean_object* v_i_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Dyadic_shiftRight(v_x_281_, v_i_282_);
lean_dec(v_i_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instHShiftLeftNat___lam__0(lean_object* v_x_288_, lean_object* v_y_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_nat_to_int(v_y_289_);
v___x_291_ = l_Dyadic_shiftLeft(v_x_288_, v___x_290_);
lean_dec(v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instHShiftRightNat___lam__0(lean_object* v_x_294_, lean_object* v_y_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_nat_to_int(v_y_295_);
v___x_297_ = l_Dyadic_shiftRight(v_x_294_, v___x_296_);
lean_dec(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Dyadic_toRat_spec__1(lean_object* v_a_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Rat_ofInt(v_a_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_toRat_spec__0(lean_object* v_a_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_nat_to_int(v_a_302_);
v___x_304_ = l_Rat_ofInt(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l_Dyadic_toRat___closed__0(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = l_Nat_cast___at___00Dyadic_toRat_spec__0(v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_toRat(lean_object* v_x_307_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v___x_308_; 
v___x_308_ = lean_obj_once(&l_Dyadic_toRat___closed__0, &l_Dyadic_toRat___closed__0_once, _init_l_Dyadic_toRat___closed__0);
return v___x_308_;
}
else
{
lean_object* v_n_309_; lean_object* v_k_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_331_; 
v_n_309_ = lean_ctor_get(v_x_307_, 0);
v_k_310_ = lean_ctor_get(v_x_307_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_331_ == 0)
{
v___x_312_ = v_x_307_;
v_isShared_313_ = v_isSharedCheck_331_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_k_310_);
lean_inc(v_n_309_);
lean_dec(v_x_307_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_331_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_intZero_314_; uint8_t v_isNeg_315_; 
v_intZero_314_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_315_ = lean_int_dec_lt(v_k_310_, v_intZero_314_);
if (v_isNeg_315_ == 0)
{
lean_object* v_a_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
v_a_316_ = lean_nat_abs(v_k_310_);
lean_dec(v_k_310_);
v___x_317_ = lean_unsigned_to_nat(2u);
v___x_318_ = lean_nat_pow(v___x_317_, v_a_316_);
lean_dec(v_a_316_);
if (v_isShared_313_ == 0)
{
lean_ctor_set_tag(v___x_312_, 0);
lean_ctor_set(v___x_312_, 1, v___x_318_);
v___x_320_ = v___x_312_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_n_309_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
else
{
lean_object* v_abs_322_; lean_object* v_one_323_; lean_object* v_a_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_del_object(v___x_312_);
v_abs_322_ = lean_nat_abs(v_k_310_);
lean_dec(v_k_310_);
v_one_323_ = lean_unsigned_to_nat(1u);
v_a_324_ = lean_nat_sub(v_abs_322_, v_one_323_);
lean_dec(v_abs_322_);
v___x_325_ = lean_unsigned_to_nat(2u);
v___x_326_ = lean_nat_add(v_a_324_, v_one_323_);
lean_dec(v_a_324_);
v___x_327_ = lean_nat_pow(v___x_325_, v___x_326_);
lean_dec(v___x_326_);
v___x_328_ = lean_nat_to_int(v___x_327_);
v___x_329_ = lean_int_mul(v_n_309_, v___x_328_);
lean_dec(v___x_328_);
lean_dec(v_n_309_);
v___x_330_ = l_Rat_ofInt(v___x_329_);
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter___redArg(lean_object* v_x_332_, lean_object* v_h__1_333_, lean_object* v_h__2_334_, lean_object* v_h__3_335_){
_start:
{
if (lean_obj_tag(v_x_332_) == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v_h__3_335_);
lean_dec(v_h__2_334_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_apply_1(v_h__1_333_, v___x_336_);
return v___x_337_;
}
else
{
lean_object* v_n_338_; lean_object* v_k_339_; lean_object* v_intZero_340_; uint8_t v_isNeg_341_; 
lean_dec(v_h__1_333_);
v_n_338_ = lean_ctor_get(v_x_332_, 0);
lean_inc(v_n_338_);
v_k_339_ = lean_ctor_get(v_x_332_, 1);
lean_inc(v_k_339_);
lean_dec_ref_known(v_x_332_, 2);
v_intZero_340_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_341_ = lean_int_dec_lt(v_k_339_, v_intZero_340_);
if (v_isNeg_341_ == 0)
{
lean_object* v_a_342_; lean_object* v___x_343_; 
lean_dec(v_h__3_335_);
v_a_342_ = lean_nat_abs(v_k_339_);
lean_dec(v_k_339_);
v___x_343_ = lean_apply_3(v_h__2_334_, v_n_338_, v_a_342_, lean_box(0));
return v___x_343_;
}
else
{
lean_object* v_abs_344_; lean_object* v_one_345_; lean_object* v_a_346_; lean_object* v___x_347_; 
lean_dec(v_h__2_334_);
v_abs_344_ = lean_nat_abs(v_k_339_);
lean_dec(v_k_339_);
v_one_345_ = lean_unsigned_to_nat(1u);
v_a_346_ = lean_nat_sub(v_abs_344_, v_one_345_);
lean_dec(v_abs_344_);
v___x_347_ = lean_apply_3(v_h__3_335_, v_n_338_, v_a_346_, lean_box(0));
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter(lean_object* v_motive_348_, lean_object* v_x_349_, lean_object* v_h__1_350_, lean_object* v_h__2_351_, lean_object* v_h__3_352_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_h__3_352_);
lean_dec(v_h__2_351_);
v___x_353_ = lean_box(0);
v___x_354_ = lean_apply_1(v_h__1_350_, v___x_353_);
return v___x_354_;
}
else
{
lean_object* v_n_355_; lean_object* v_k_356_; lean_object* v_intZero_357_; uint8_t v_isNeg_358_; 
lean_dec(v_h__1_350_);
v_n_355_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_n_355_);
v_k_356_ = lean_ctor_get(v_x_349_, 1);
lean_inc(v_k_356_);
lean_dec_ref_known(v_x_349_, 2);
v_intZero_357_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_358_ = lean_int_dec_lt(v_k_356_, v_intZero_357_);
if (v_isNeg_358_ == 0)
{
lean_object* v_a_359_; lean_object* v___x_360_; 
lean_dec(v_h__3_352_);
v_a_359_ = lean_nat_abs(v_k_356_);
lean_dec(v_k_356_);
v___x_360_ = lean_apply_3(v_h__2_351_, v_n_355_, v_a_359_, lean_box(0));
return v___x_360_;
}
else
{
lean_object* v_abs_361_; lean_object* v_one_362_; lean_object* v_a_363_; lean_object* v___x_364_; 
lean_dec(v_h__2_351_);
v_abs_361_ = lean_nat_abs(v_k_356_);
lean_dec(v_k_356_);
v_one_362_ = lean_unsigned_to_nat(1u);
v_a_363_ = lean_nat_sub(v_abs_361_, v_one_362_);
lean_dec(v_abs_361_);
v___x_364_ = lean_apply_3(v_h__3_352_, v_n_355_, v_a_363_, lean_box(0));
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter___redArg(lean_object* v_x_365_, lean_object* v_y_366_, lean_object* v_h__1_367_, lean_object* v_h__2_368_, lean_object* v_h__3_369_){
_start:
{
if (lean_obj_tag(v_x_365_) == 0)
{
lean_object* v___x_370_; 
lean_dec(v_h__3_369_);
lean_dec(v_h__2_368_);
v___x_370_ = lean_apply_1(v_h__1_367_, v_y_366_);
return v___x_370_;
}
else
{
lean_dec(v_h__1_367_);
if (lean_obj_tag(v_y_366_) == 0)
{
lean_object* v_n_371_; lean_object* v_k_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_380_; 
lean_dec(v_h__3_369_);
v_n_371_ = lean_ctor_get(v_x_365_, 0);
v_k_372_ = lean_ctor_get(v_x_365_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_x_365_);
if (v_isSharedCheck_380_ == 0)
{
v___x_374_ = v_x_365_;
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_k_372_);
lean_inc(v_n_371_);
lean_dec(v_x_365_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_380_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_n_371_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_k_372_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
v___x_378_ = lean_apply_2(v_h__2_368_, v___x_377_, lean_box(0));
return v___x_378_;
}
}
}
else
{
lean_object* v_n_381_; lean_object* v_k_382_; lean_object* v_n_383_; lean_object* v_k_384_; lean_object* v___x_385_; 
lean_dec(v_h__2_368_);
v_n_381_ = lean_ctor_get(v_x_365_, 0);
lean_inc(v_n_381_);
v_k_382_ = lean_ctor_get(v_x_365_, 1);
lean_inc(v_k_382_);
lean_dec_ref_known(v_x_365_, 2);
v_n_383_ = lean_ctor_get(v_y_366_, 0);
lean_inc(v_n_383_);
v_k_384_ = lean_ctor_get(v_y_366_, 1);
lean_inc(v_k_384_);
lean_dec_ref_known(v_y_366_, 2);
v___x_385_ = lean_apply_6(v_h__3_369_, v_n_381_, v_k_382_, lean_box(0), v_n_383_, v_k_384_, lean_box(0));
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter(lean_object* v_motive_386_, lean_object* v_x_387_, lean_object* v_y_388_, lean_object* v_h__1_389_, lean_object* v_h__2_390_, lean_object* v_h__3_391_){
_start:
{
if (lean_obj_tag(v_x_387_) == 0)
{
lean_object* v___x_392_; 
lean_dec(v_h__3_391_);
lean_dec(v_h__2_390_);
v___x_392_ = lean_apply_1(v_h__1_389_, v_y_388_);
return v___x_392_;
}
else
{
lean_dec(v_h__1_389_);
if (lean_obj_tag(v_y_388_) == 0)
{
lean_object* v_n_393_; lean_object* v_k_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_h__3_391_);
v_n_393_ = lean_ctor_get(v_x_387_, 0);
v_k_394_ = lean_ctor_get(v_x_387_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v_x_387_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v_x_387_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_k_394_);
lean_inc(v_n_393_);
lean_dec(v_x_387_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_n_393_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_k_394_);
v___x_399_ = v_reuseFailAlloc_401_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; 
v___x_400_ = lean_apply_2(v_h__2_390_, v___x_399_, lean_box(0));
return v___x_400_;
}
}
}
else
{
lean_object* v_n_403_; lean_object* v_k_404_; lean_object* v_n_405_; lean_object* v_k_406_; lean_object* v___x_407_; 
lean_dec(v_h__2_390_);
v_n_403_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_n_403_);
v_k_404_ = lean_ctor_get(v_x_387_, 1);
lean_inc(v_k_404_);
lean_dec_ref_known(v_x_387_, 2);
v_n_405_ = lean_ctor_get(v_y_388_, 0);
lean_inc(v_n_405_);
v_k_406_ = lean_ctor_get(v_y_388_, 1);
lean_inc(v_k_406_);
lean_dec_ref_known(v_y_388_, 2);
v___x_407_ = lean_apply_6(v_h__3_391_, v_n_403_, v_k_404_, lean_box(0), v_n_405_, v_k_406_, lean_box(0));
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(lean_object* v_x_408_, lean_object* v_h__1_409_, lean_object* v_h__2_410_, lean_object* v_h__3_411_){
_start:
{
lean_object* v_natZero_412_; lean_object* v_intZero_413_; uint8_t v_isNeg_414_; 
v_natZero_412_ = lean_unsigned_to_nat(0u);
v_intZero_413_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_414_ = lean_int_dec_lt(v_x_408_, v_intZero_413_);
if (v_isNeg_414_ == 0)
{
lean_object* v_a_415_; uint8_t v_isZero_416_; 
lean_dec(v_h__3_411_);
v_a_415_ = lean_nat_abs(v_x_408_);
v_isZero_416_ = lean_nat_dec_eq(v_a_415_, v_natZero_412_);
if (v_isZero_416_ == 1)
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec(v_a_415_);
lean_dec(v_h__2_410_);
v___x_417_ = lean_box(0);
v___x_418_ = lean_apply_1(v_h__1_409_, v___x_417_);
return v___x_418_;
}
else
{
lean_object* v_one_419_; lean_object* v_n_420_; lean_object* v___x_421_; 
lean_dec(v_h__1_409_);
v_one_419_ = lean_unsigned_to_nat(1u);
v_n_420_ = lean_nat_sub(v_a_415_, v_one_419_);
lean_dec(v_a_415_);
v___x_421_ = lean_apply_1(v_h__2_410_, v_n_420_);
return v___x_421_;
}
}
else
{
lean_object* v_abs_422_; lean_object* v_one_423_; lean_object* v_a_424_; lean_object* v___x_425_; 
lean_dec(v_h__2_410_);
lean_dec(v_h__1_409_);
v_abs_422_ = lean_nat_abs(v_x_408_);
v_one_423_ = lean_unsigned_to_nat(1u);
v_a_424_ = lean_nat_sub(v_abs_422_, v_one_423_);
lean_dec(v_abs_422_);
v___x_425_ = lean_apply_1(v_h__3_411_, v_a_424_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg___boxed(lean_object* v_x_426_, lean_object* v_h__1_427_, lean_object* v_h__2_428_, lean_object* v_h__3_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(v_x_426_, v_h__1_427_, v_h__2_428_, v_h__3_429_);
lean_dec(v_x_426_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(lean_object* v_motive_431_, lean_object* v_x_432_, lean_object* v_h__1_433_, lean_object* v_h__2_434_, lean_object* v_h__3_435_){
_start:
{
lean_object* v_natZero_436_; lean_object* v_intZero_437_; uint8_t v_isNeg_438_; 
v_natZero_436_ = lean_unsigned_to_nat(0u);
v_intZero_437_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_438_ = lean_int_dec_lt(v_x_432_, v_intZero_437_);
if (v_isNeg_438_ == 0)
{
lean_object* v_a_439_; uint8_t v_isZero_440_; 
lean_dec(v_h__3_435_);
v_a_439_ = lean_nat_abs(v_x_432_);
v_isZero_440_ = lean_nat_dec_eq(v_a_439_, v_natZero_436_);
if (v_isZero_440_ == 1)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec(v_a_439_);
lean_dec(v_h__2_434_);
v___x_441_ = lean_box(0);
v___x_442_ = lean_apply_1(v_h__1_433_, v___x_441_);
return v___x_442_;
}
else
{
lean_object* v_one_443_; lean_object* v_n_444_; lean_object* v___x_445_; 
lean_dec(v_h__1_433_);
v_one_443_ = lean_unsigned_to_nat(1u);
v_n_444_ = lean_nat_sub(v_a_439_, v_one_443_);
lean_dec(v_a_439_);
v___x_445_ = lean_apply_1(v_h__2_434_, v_n_444_);
return v___x_445_;
}
}
else
{
lean_object* v_abs_446_; lean_object* v_one_447_; lean_object* v_a_448_; lean_object* v___x_449_; 
lean_dec(v_h__2_434_);
lean_dec(v_h__1_433_);
v_abs_446_ = lean_nat_abs(v_x_432_);
v_one_447_ = lean_unsigned_to_nat(1u);
v_a_448_ = lean_nat_sub(v_abs_446_, v_one_447_);
lean_dec(v_abs_446_);
v___x_449_ = lean_apply_1(v_h__3_435_, v_a_448_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___boxed(lean_object* v_motive_450_, lean_object* v_x_451_, lean_object* v_h__1_452_, lean_object* v_h__2_453_, lean_object* v_h__3_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(v_motive_450_, v_x_451_, v_h__1_452_, v_h__2_453_, v_h__3_454_);
lean_dec(v_x_451_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter___redArg(lean_object* v_x_456_, lean_object* v_h__1_457_, lean_object* v_h__2_458_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec(v_h__2_458_);
v___x_459_ = lean_box(0);
v___x_460_ = lean_apply_1(v_h__1_457_, v___x_459_);
return v___x_460_;
}
else
{
lean_object* v_n_461_; lean_object* v_k_462_; lean_object* v___x_463_; 
lean_dec(v_h__1_457_);
v_n_461_ = lean_ctor_get(v_x_456_, 0);
lean_inc(v_n_461_);
v_k_462_ = lean_ctor_get(v_x_456_, 1);
lean_inc(v_k_462_);
lean_dec_ref_known(v_x_456_, 2);
v___x_463_ = lean_apply_3(v_h__2_458_, v_n_461_, v_k_462_, lean_box(0));
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter(lean_object* v_motive_464_, lean_object* v_x_465_, lean_object* v_h__1_466_, lean_object* v_h__2_467_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v_h__2_467_);
v___x_468_ = lean_box(0);
v___x_469_ = lean_apply_1(v_h__1_466_, v___x_468_);
return v___x_469_;
}
else
{
lean_object* v_n_470_; lean_object* v_k_471_; lean_object* v___x_472_; 
lean_dec(v_h__1_466_);
v_n_470_ = lean_ctor_get(v_x_465_, 0);
lean_inc(v_n_470_);
v_k_471_ = lean_ctor_get(v_x_465_, 1);
lean_inc(v_k_471_);
lean_dec_ref_known(v_x_465_, 2);
v___x_472_ = lean_apply_3(v_h__2_467_, v_n_470_, v_k_471_, lean_box(0));
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_precision(lean_object* v_x_473_){
_start:
{
if (lean_obj_tag(v_x_473_) == 0)
{
lean_object* v___x_474_; 
v___x_474_ = lean_box(0);
return v___x_474_;
}
else
{
lean_object* v_k_475_; lean_object* v___x_476_; 
v_k_475_ = lean_ctor_get(v_x_473_, 1);
lean_inc(v_k_475_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v_k_475_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_precision___boxed(lean_object* v_x_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Dyadic_precision(v_x_477_);
lean_dec(v_x_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Rat_toDyadic(lean_object* v_x_479_, lean_object* v_prec_480_){
_start:
{
lean_object* v_intZero_481_; uint8_t v_isNeg_482_; 
v_intZero_481_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_482_ = lean_int_dec_lt(v_prec_480_, v_intZero_481_);
if (v_isNeg_482_ == 0)
{
lean_object* v_num_483_; lean_object* v_den_484_; lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_num_483_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_num_483_);
v_den_484_ = lean_ctor_get(v_x_479_, 1);
lean_inc(v_den_484_);
lean_dec_ref(v_x_479_);
v_a_485_ = lean_nat_abs(v_prec_480_);
v___x_486_ = l_Int_shiftLeft(v_num_483_, v_a_485_);
lean_dec(v_a_485_);
lean_dec(v_num_483_);
v___x_487_ = lean_nat_to_int(v_den_484_);
v___x_488_ = lean_int_ediv(v___x_486_, v___x_487_);
lean_dec(v___x_487_);
lean_dec(v___x_486_);
v___x_489_ = l_Dyadic_ofIntWithPrec(v___x_488_, v_prec_480_);
return v___x_489_;
}
else
{
lean_object* v_num_490_; lean_object* v_den_491_; lean_object* v_abs_492_; lean_object* v_one_493_; lean_object* v_a_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_num_490_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_num_490_);
v_den_491_ = lean_ctor_get(v_x_479_, 1);
lean_inc(v_den_491_);
lean_dec_ref(v_x_479_);
v_abs_492_ = lean_nat_abs(v_prec_480_);
v_one_493_ = lean_unsigned_to_nat(1u);
v_a_494_ = lean_nat_sub(v_abs_492_, v_one_493_);
lean_dec(v_abs_492_);
v___x_495_ = lean_nat_add(v_a_494_, v_one_493_);
lean_dec(v_a_494_);
v___x_496_ = lean_nat_shiftl(v_den_491_, v___x_495_);
lean_dec(v___x_495_);
lean_dec(v_den_491_);
v___x_497_ = lean_nat_to_int(v___x_496_);
v___x_498_ = lean_int_ediv(v_num_490_, v___x_497_);
lean_dec(v___x_497_);
lean_dec(v_num_490_);
v___x_499_ = l_Dyadic_ofIntWithPrec(v___x_498_, v_prec_480_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_toDyadic___boxed(lean_object* v_x_500_, lean_object* v_prec_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Rat_toDyadic(v_x_500_, v_prec_501_);
lean_dec(v_prec_501_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(lean_object* v_prec_503_, lean_object* v_h__1_504_, lean_object* v_h__2_505_){
_start:
{
lean_object* v_intZero_506_; uint8_t v_isNeg_507_; 
v_intZero_506_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_507_ = lean_int_dec_lt(v_prec_503_, v_intZero_506_);
if (v_isNeg_507_ == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
lean_dec(v_h__2_505_);
v_a_508_ = lean_nat_abs(v_prec_503_);
v___x_509_ = lean_apply_1(v_h__1_504_, v_a_508_);
return v___x_509_;
}
else
{
lean_object* v_abs_510_; lean_object* v_one_511_; lean_object* v_a_512_; lean_object* v___x_513_; 
lean_dec(v_h__1_504_);
v_abs_510_ = lean_nat_abs(v_prec_503_);
v_one_511_ = lean_unsigned_to_nat(1u);
v_a_512_ = lean_nat_sub(v_abs_510_, v_one_511_);
lean_dec(v_abs_510_);
v___x_513_ = lean_apply_1(v_h__2_505_, v_a_512_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg___boxed(lean_object* v_prec_514_, lean_object* v_h__1_515_, lean_object* v_h__2_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(v_prec_514_, v_h__1_515_, v_h__2_516_);
lean_dec(v_prec_514_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(lean_object* v_motive_518_, lean_object* v_prec_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_){
_start:
{
lean_object* v_intZero_522_; uint8_t v_isNeg_523_; 
v_intZero_522_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_523_ = lean_int_dec_lt(v_prec_519_, v_intZero_522_);
if (v_isNeg_523_ == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
lean_dec(v_h__2_521_);
v_a_524_ = lean_nat_abs(v_prec_519_);
v___x_525_ = lean_apply_1(v_h__1_520_, v_a_524_);
return v___x_525_;
}
else
{
lean_object* v_abs_526_; lean_object* v_one_527_; lean_object* v_a_528_; lean_object* v___x_529_; 
lean_dec(v_h__1_520_);
v_abs_526_ = lean_nat_abs(v_prec_519_);
v_one_527_ = lean_unsigned_to_nat(1u);
v_a_528_ = lean_nat_sub(v_abs_526_, v_one_527_);
lean_dec(v_abs_526_);
v___x_529_ = lean_apply_1(v_h__2_521_, v_a_528_);
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___boxed(lean_object* v_motive_530_, lean_object* v_prec_531_, lean_object* v_h__1_532_, lean_object* v_h__2_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(v_motive_530_, v_prec_531_, v_h__1_532_, v_h__2_533_);
lean_dec(v_prec_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundDown(lean_object* v_x_535_, lean_object* v_prec_536_){
_start:
{
if (lean_obj_tag(v_x_535_) == 0)
{
return v_x_535_;
}
else
{
lean_object* v_n_537_; lean_object* v_k_538_; lean_object* v___x_539_; lean_object* v_intZero_540_; uint8_t v_isNeg_541_; 
v_n_537_ = lean_ctor_get(v_x_535_, 0);
v_k_538_ = lean_ctor_get(v_x_535_, 1);
v___x_539_ = lean_int_sub(v_k_538_, v_prec_536_);
v_intZero_540_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_541_ = lean_int_dec_lt(v___x_539_, v_intZero_540_);
if (v_isNeg_541_ == 0)
{
lean_object* v_a_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_a_542_ = lean_nat_abs(v___x_539_);
lean_dec(v___x_539_);
v___x_543_ = l_Int_shiftRight(v_n_537_, v_a_542_);
lean_dec(v_a_542_);
v___x_544_ = l_Dyadic_ofIntWithPrec(v___x_543_, v_prec_536_);
return v___x_544_;
}
else
{
lean_dec(v___x_539_);
lean_inc_ref(v_x_535_);
return v_x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundDown___boxed(lean_object* v_x_545_, lean_object* v_prec_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Dyadic_roundDown(v_x_545_, v_prec_546_);
lean_dec(v_prec_546_);
lean_dec(v_x_545_);
return v_res_547_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_blt(lean_object* v_x_548_, lean_object* v_y_549_){
_start:
{
if (lean_obj_tag(v_x_548_) == 0)
{
if (lean_obj_tag(v_y_549_) == 0)
{
uint8_t v___x_550_; 
v___x_550_ = 0;
return v___x_550_;
}
else
{
lean_object* v_n_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v_n_551_ = lean_ctor_get(v_y_549_, 0);
v___x_552_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_553_ = lean_int_dec_lt(v___x_552_, v_n_551_);
return v___x_553_;
}
}
else
{
if (lean_obj_tag(v_y_549_) == 0)
{
lean_object* v_n_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_n_554_ = lean_ctor_get(v_x_548_, 0);
v___x_555_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_556_ = lean_int_dec_lt(v_n_554_, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v_n_557_; lean_object* v_k_558_; lean_object* v_n_559_; lean_object* v_k_560_; lean_object* v___x_561_; lean_object* v_intZero_562_; uint8_t v_isNeg_563_; 
v_n_557_ = lean_ctor_get(v_x_548_, 0);
v_k_558_ = lean_ctor_get(v_x_548_, 1);
v_n_559_ = lean_ctor_get(v_y_549_, 0);
v_k_560_ = lean_ctor_get(v_y_549_, 1);
v___x_561_ = lean_int_sub(v_k_560_, v_k_558_);
v_intZero_562_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_563_ = lean_int_dec_lt(v___x_561_, v_intZero_562_);
if (v_isNeg_563_ == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_a_564_ = lean_nat_abs(v___x_561_);
lean_dec(v___x_561_);
v___x_565_ = l_Int_shiftLeft(v_n_557_, v_a_564_);
lean_dec(v_a_564_);
v___x_566_ = lean_int_dec_lt(v___x_565_, v_n_559_);
lean_dec(v___x_565_);
return v___x_566_;
}
else
{
lean_object* v_abs_567_; lean_object* v_one_568_; lean_object* v_a_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_abs_567_ = lean_nat_abs(v___x_561_);
lean_dec(v___x_561_);
v_one_568_ = lean_unsigned_to_nat(1u);
v_a_569_ = lean_nat_sub(v_abs_567_, v_one_568_);
lean_dec(v_abs_567_);
v___x_570_ = lean_nat_add(v_a_569_, v_one_568_);
lean_dec(v_a_569_);
v___x_571_ = l_Int_shiftLeft(v_n_559_, v___x_570_);
lean_dec(v___x_570_);
v___x_572_ = lean_int_dec_lt(v_n_557_, v___x_571_);
lean_dec(v___x_571_);
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_blt___boxed(lean_object* v_x_573_, lean_object* v_y_574_){
_start:
{
uint8_t v_res_575_; lean_object* v_r_576_; 
v_res_575_ = l_Dyadic_blt(v_x_573_, v_y_574_);
lean_dec(v_y_574_);
lean_dec(v_x_573_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_ble(lean_object* v_x_577_, lean_object* v_y_578_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
if (lean_obj_tag(v_y_578_) == 0)
{
uint8_t v___x_579_; 
v___x_579_ = 1;
return v___x_579_;
}
else
{
lean_object* v_n_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_n_580_ = lean_ctor_get(v_y_578_, 0);
v___x_581_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_582_ = lean_int_dec_le(v___x_581_, v_n_580_);
return v___x_582_;
}
}
else
{
if (lean_obj_tag(v_y_578_) == 0)
{
lean_object* v_n_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_n_583_ = lean_ctor_get(v_x_577_, 0);
v___x_584_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_585_ = lean_int_dec_le(v_n_583_, v___x_584_);
return v___x_585_;
}
else
{
lean_object* v_n_586_; lean_object* v_k_587_; lean_object* v_n_588_; lean_object* v_k_589_; lean_object* v___x_590_; lean_object* v_intZero_591_; uint8_t v_isNeg_592_; 
v_n_586_ = lean_ctor_get(v_x_577_, 0);
v_k_587_ = lean_ctor_get(v_x_577_, 1);
v_n_588_ = lean_ctor_get(v_y_578_, 0);
v_k_589_ = lean_ctor_get(v_y_578_, 1);
v___x_590_ = lean_int_sub(v_k_589_, v_k_587_);
v_intZero_591_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_592_ = lean_int_dec_lt(v___x_590_, v_intZero_591_);
if (v_isNeg_592_ == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_a_593_ = lean_nat_abs(v___x_590_);
lean_dec(v___x_590_);
v___x_594_ = l_Int_shiftLeft(v_n_586_, v_a_593_);
lean_dec(v_a_593_);
v___x_595_ = lean_int_dec_le(v___x_594_, v_n_588_);
lean_dec(v___x_594_);
return v___x_595_;
}
else
{
lean_object* v_abs_596_; lean_object* v_one_597_; lean_object* v_a_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_abs_596_ = lean_nat_abs(v___x_590_);
lean_dec(v___x_590_);
v_one_597_ = lean_unsigned_to_nat(1u);
v_a_598_ = lean_nat_sub(v_abs_596_, v_one_597_);
lean_dec(v_abs_596_);
v___x_599_ = lean_nat_add(v_a_598_, v_one_597_);
lean_dec(v_a_598_);
v___x_600_ = l_Int_shiftLeft(v_n_588_, v___x_599_);
lean_dec(v___x_599_);
v___x_601_ = lean_int_dec_le(v_n_586_, v___x_600_);
lean_dec(v___x_600_);
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ble___boxed(lean_object* v_x_602_, lean_object* v_y_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Dyadic_ble(v_x_602_, v_y_603_);
lean_dec(v_y_603_);
lean_dec(v_x_602_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter___redArg(lean_object* v_x_606_, lean_object* v_x_607_, lean_object* v_h__1_608_, lean_object* v_h__2_609_, lean_object* v_h__3_610_, lean_object* v_h__4_611_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_dec(v_h__4_611_);
lean_dec(v_h__3_610_);
if (lean_obj_tag(v_x_607_) == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v_h__2_609_);
v___x_612_ = lean_box(0);
v___x_613_ = lean_apply_1(v_h__1_608_, v___x_612_);
return v___x_613_;
}
else
{
lean_object* v_n_614_; lean_object* v_k_615_; lean_object* v___x_616_; 
lean_dec(v_h__1_608_);
v_n_614_ = lean_ctor_get(v_x_607_, 0);
lean_inc(v_n_614_);
v_k_615_ = lean_ctor_get(v_x_607_, 1);
lean_inc(v_k_615_);
lean_dec_ref_known(v_x_607_, 2);
v___x_616_ = lean_apply_3(v_h__2_609_, v_n_614_, v_k_615_, lean_box(0));
return v___x_616_;
}
}
else
{
lean_dec(v_h__2_609_);
lean_dec(v_h__1_608_);
if (lean_obj_tag(v_x_607_) == 0)
{
lean_object* v_n_617_; lean_object* v_k_618_; lean_object* v___x_619_; 
lean_dec(v_h__4_611_);
v_n_617_ = lean_ctor_get(v_x_606_, 0);
lean_inc(v_n_617_);
v_k_618_ = lean_ctor_get(v_x_606_, 1);
lean_inc(v_k_618_);
lean_dec_ref_known(v_x_606_, 2);
v___x_619_ = lean_apply_3(v_h__3_610_, v_n_617_, v_k_618_, lean_box(0));
return v___x_619_;
}
else
{
lean_object* v_n_620_; lean_object* v_k_621_; lean_object* v_n_622_; lean_object* v_k_623_; lean_object* v___x_624_; 
lean_dec(v_h__3_610_);
v_n_620_ = lean_ctor_get(v_x_606_, 0);
lean_inc(v_n_620_);
v_k_621_ = lean_ctor_get(v_x_606_, 1);
lean_inc(v_k_621_);
lean_dec_ref_known(v_x_606_, 2);
v_n_622_ = lean_ctor_get(v_x_607_, 0);
lean_inc(v_n_622_);
v_k_623_ = lean_ctor_get(v_x_607_, 1);
lean_inc(v_k_623_);
lean_dec_ref_known(v_x_607_, 2);
v___x_624_ = lean_apply_6(v_h__4_611_, v_n_620_, v_k_621_, lean_box(0), v_n_622_, v_k_623_, lean_box(0));
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter(lean_object* v_motive_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_h__1_628_, lean_object* v_h__2_629_, lean_object* v_h__3_630_, lean_object* v_h__4_631_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
lean_dec(v_h__4_631_);
lean_dec(v_h__3_630_);
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v_h__2_629_);
v___x_632_ = lean_box(0);
v___x_633_ = lean_apply_1(v_h__1_628_, v___x_632_);
return v___x_633_;
}
else
{
lean_object* v_n_634_; lean_object* v_k_635_; lean_object* v___x_636_; 
lean_dec(v_h__1_628_);
v_n_634_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_n_634_);
v_k_635_ = lean_ctor_get(v_x_627_, 1);
lean_inc(v_k_635_);
lean_dec_ref_known(v_x_627_, 2);
v___x_636_ = lean_apply_3(v_h__2_629_, v_n_634_, v_k_635_, lean_box(0));
return v___x_636_;
}
}
else
{
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v_n_637_; lean_object* v_k_638_; lean_object* v___x_639_; 
lean_dec(v_h__4_631_);
v_n_637_ = lean_ctor_get(v_x_626_, 0);
lean_inc(v_n_637_);
v_k_638_ = lean_ctor_get(v_x_626_, 1);
lean_inc(v_k_638_);
lean_dec_ref_known(v_x_626_, 2);
v___x_639_ = lean_apply_3(v_h__3_630_, v_n_637_, v_k_638_, lean_box(0));
return v___x_639_;
}
else
{
lean_object* v_n_640_; lean_object* v_k_641_; lean_object* v_n_642_; lean_object* v_k_643_; lean_object* v___x_644_; 
lean_dec(v_h__3_630_);
v_n_640_ = lean_ctor_get(v_x_626_, 0);
lean_inc(v_n_640_);
v_k_641_ = lean_ctor_get(v_x_626_, 1);
lean_inc(v_k_641_);
lean_dec_ref_known(v_x_626_, 2);
v_n_642_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_n_642_);
v_k_643_ = lean_ctor_get(v_x_627_, 1);
lean_inc(v_k_643_);
lean_dec_ref_known(v_x_627_, 2);
v___x_644_ = lean_apply_6(v_h__4_631_, v_n_640_, v_k_641_, lean_box(0), v_n_642_, v_k_643_, lean_box(0));
return v___x_644_;
}
}
}
}
static lean_object* _init_l_Dyadic_instLT(void){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = lean_box(0);
return v___x_645_;
}
}
static lean_object* _init_l_Dyadic_instLE(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_box(0);
return v___x_646_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLT(lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
uint8_t v___x_649_; 
v___x_649_ = l_Dyadic_blt(v_x_647_, v_x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLT___boxed(lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
uint8_t v_res_652_; lean_object* v_r_653_; 
v_res_652_ = l_Dyadic_instDecidableLT(v_x_650_, v_x_651_);
lean_dec(v_x_651_);
lean_dec(v_x_650_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLE(lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
uint8_t v___x_656_; 
v___x_656_ = l_Dyadic_ble(v_x_654_, v_x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLE___boxed(lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
uint8_t v_res_659_; lean_object* v_r_660_; 
v_res_659_ = l_Dyadic_instDecidableLE(v_x_657_, v_x_658_);
lean_dec(v_x_658_);
lean_dec(v_x_657_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundUp(lean_object* v_x_661_, lean_object* v_prec_662_){
_start:
{
if (lean_obj_tag(v_x_661_) == 0)
{
return v_x_661_;
}
else
{
lean_object* v_n_663_; lean_object* v_k_664_; lean_object* v___x_665_; lean_object* v_intZero_666_; uint8_t v_isNeg_667_; 
v_n_663_ = lean_ctor_get(v_x_661_, 0);
v_k_664_ = lean_ctor_get(v_x_661_, 1);
v___x_665_ = lean_int_sub(v_k_664_, v_prec_662_);
v_intZero_666_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_667_ = lean_int_dec_lt(v___x_665_, v_intZero_666_);
if (v_isNeg_667_ == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_a_668_ = lean_nat_abs(v___x_665_);
lean_dec(v___x_665_);
v___x_669_ = lean_int_neg(v_n_663_);
v___x_670_ = l_Int_shiftRight(v___x_669_, v_a_668_);
lean_dec(v_a_668_);
lean_dec(v___x_669_);
v___x_671_ = lean_int_neg(v___x_670_);
lean_dec(v___x_670_);
v___x_672_ = l_Dyadic_ofIntWithPrec(v___x_671_, v_prec_662_);
return v___x_672_;
}
else
{
lean_dec(v___x_665_);
lean_inc_ref(v_x_661_);
return v_x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundUp___boxed(lean_object* v_x_673_, lean_object* v_prec_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Dyadic_roundUp(v_x_673_, v_prec_674_);
lean_dec(v_prec_674_);
lean_dec(v_x_673_);
return v_res_675_;
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
