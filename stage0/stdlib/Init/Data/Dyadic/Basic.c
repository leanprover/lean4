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
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx___boxed(lean_object*);
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
lean_object* v___x_47_; 
v___x_47_ = l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg(v_k_43_, v_h__1_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___boxed(lean_object* v_i_48_, lean_object* v_motive_49_, lean_object* v_k_50_, lean_object* v_x_51_, lean_object* v_hk_52_, lean_object* v_h__1_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter(v_i_48_, v_motive_49_, v_k_50_, v_x_51_, v_hk_52_, v_h__1_53_);
lean_dec(v_k_50_);
lean_dec(v_i_48_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx(lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v___x_56_; 
v___x_56_ = lean_unsigned_to_nat(0u);
return v___x_56_;
}
else
{
lean_object* v___x_57_; 
v___x_57_ = lean_unsigned_to_nat(1u);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx___boxed(lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Dyadic_ctorIdx(v_x_58_);
lean_dec(v_x_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim___redArg(lean_object* v_t_60_, lean_object* v_k_61_){
_start:
{
if (lean_obj_tag(v_t_60_) == 0)
{
return v_k_61_;
}
else
{
lean_object* v_n_62_; lean_object* v_k_63_; lean_object* v___x_64_; 
v_n_62_ = lean_ctor_get(v_t_60_, 0);
lean_inc(v_n_62_);
v_k_63_ = lean_ctor_get(v_t_60_, 1);
lean_inc(v_k_63_);
lean_dec_ref(v_t_60_);
v___x_64_ = lean_apply_3(v_k_61_, v_n_62_, v_k_63_, lean_box(0));
return v___x_64_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim(lean_object* v_motive_65_, lean_object* v_ctorIdx_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_k_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Dyadic_ctorElim___redArg(v_t_67_, v_k_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim___boxed(lean_object* v_motive_71_, lean_object* v_ctorIdx_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_k_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Dyadic_ctorElim(v_motive_71_, v_ctorIdx_72_, v_t_73_, v_h_74_, v_k_75_);
lean_dec(v_ctorIdx_72_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_zero_elim___redArg(lean_object* v_t_77_, lean_object* v_zero_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Dyadic_ctorElim___redArg(v_t_77_, v_zero_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_zero_elim(lean_object* v_motive_80_, lean_object* v_t_81_, lean_object* v_h_82_, lean_object* v_zero_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Dyadic_ctorElim___redArg(v_t_81_, v_zero_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofOdd_elim___redArg(lean_object* v_t_85_, lean_object* v_ofOdd_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Dyadic_ctorElim___redArg(v_t_85_, v_ofOdd_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofOdd_elim(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_ofOdd_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Dyadic_ctorElim___redArg(v_t_89_, v_ofOdd_91_);
return v___x_92_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqDyadic_decEq(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
if (lean_obj_tag(v_x_94_) == 0)
{
uint8_t v___x_95_; 
v___x_95_ = 1;
return v___x_95_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
else
{
if (lean_obj_tag(v_x_94_) == 0)
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
else
{
lean_object* v_n_98_; lean_object* v_k_99_; lean_object* v_n_100_; lean_object* v_k_101_; uint8_t v___x_102_; 
v_n_98_ = lean_ctor_get(v_x_93_, 0);
v_k_99_ = lean_ctor_get(v_x_93_, 1);
v_n_100_ = lean_ctor_get(v_x_94_, 0);
v_k_101_ = lean_ctor_get(v_x_94_, 1);
v___x_102_ = lean_int_dec_eq(v_n_98_, v_n_100_);
if (v___x_102_ == 0)
{
return v___x_102_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = lean_int_dec_eq(v_k_99_, v_k_101_);
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqDyadic_decEq___boxed(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l_instDecidableEqDyadic_decEq(v_x_104_, v_x_105_);
lean_dec(v_x_105_);
lean_dec(v_x_104_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqDyadic(lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = l_instDecidableEqDyadic_decEq(v_x_108_, v_x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqDyadic___boxed(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_instDecidableEqDyadic(v_x_111_, v_x_112_);
lean_dec(v_x_112_);
lean_dec(v_x_111_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_ofIntWithPrec_spec__0(lean_object* v_a_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_nat_to_int(v_a_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec(lean_object* v_i_117_, lean_object* v_prec_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_120_ = lean_int_dec_eq(v_i_117_, v___x_119_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
lean_inc(v_i_117_);
v___x_121_ = l_Int_trailingZeros(v_i_117_);
v___x_122_ = l_Int_shiftRight(v_i_117_, v___x_121_);
lean_dec(v_i_117_);
v___x_123_ = lean_nat_to_int(v___x_121_);
v___x_124_ = lean_int_sub(v_prec_118_, v___x_123_);
lean_dec(v___x_123_);
v___x_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_122_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; 
lean_dec(v_i_117_);
v___x_126_ = lean_box(0);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec___boxed(lean_object* v_i_127_, lean_object* v_prec_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Dyadic_ofIntWithPrec(v_i_127_, v_prec_128_);
lean_dec(v_prec_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofInt(lean_object* v_i_130_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_132_ = l_Dyadic_ofIntWithPrec(v_i_130_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instOfNat(lean_object* v_n_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_nat_to_int(v_n_133_);
v___x_135_ = l_Dyadic_ofInt(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instNatCast___lam__0(lean_object* v_x_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_nat_to_int(v_x_138_);
v___x_140_ = l_Dyadic_ofInt(v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_add(lean_object* v_x_143_, lean_object* v_y_144_){
_start:
{
if (lean_obj_tag(v_x_143_) == 0)
{
return v_y_144_;
}
else
{
if (lean_obj_tag(v_y_144_) == 0)
{
lean_object* v_n_145_; lean_object* v_k_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
v_n_145_ = lean_ctor_get(v_x_143_, 0);
v_k_146_ = lean_ctor_get(v_x_143_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_x_143_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v_x_143_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_k_146_);
lean_inc(v_n_145_);
lean_dec(v_x_143_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_n_145_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_k_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
else
{
lean_object* v_n_154_; lean_object* v_k_155_; lean_object* v_n_156_; lean_object* v_k_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_183_; 
v_n_154_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_n_154_);
v_k_155_ = lean_ctor_get(v_x_143_, 1);
lean_inc(v_k_155_);
lean_dec_ref(v_x_143_);
v_n_156_ = lean_ctor_get(v_y_144_, 0);
v_k_157_ = lean_ctor_get(v_y_144_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_y_144_);
if (v_isSharedCheck_183_ == 0)
{
v___x_159_ = v_y_144_;
v_isShared_160_ = v_isSharedCheck_183_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_k_157_);
lean_inc(v_n_156_);
lean_dec(v_y_144_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_183_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v_natZero_162_; lean_object* v_intZero_163_; uint8_t v_isNeg_164_; 
v___x_161_ = lean_int_sub(v_k_155_, v_k_157_);
v_natZero_162_ = lean_unsigned_to_nat(0u);
v_intZero_163_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_164_ = lean_int_dec_lt(v___x_161_, v_intZero_163_);
if (v_isNeg_164_ == 0)
{
lean_object* v_a_165_; uint8_t v_isZero_166_; 
lean_dec(v_k_157_);
v_a_165_ = lean_nat_abs(v___x_161_);
lean_dec(v___x_161_);
v_isZero_166_ = lean_nat_dec_eq(v_a_165_, v_natZero_162_);
if (v_isZero_166_ == 1)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v_a_165_);
lean_del_object(v___x_159_);
v___x_167_ = lean_int_add(v_n_154_, v_n_156_);
lean_dec(v_n_156_);
lean_dec(v_n_154_);
v___x_168_ = l_Dyadic_ofIntWithPrec(v___x_167_, v_k_155_);
lean_dec(v_k_155_);
return v___x_168_;
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_169_ = l_Int_shiftLeft(v_n_156_, v_a_165_);
lean_dec(v_a_165_);
lean_dec(v_n_156_);
v___x_170_ = lean_int_add(v_n_154_, v___x_169_);
lean_dec(v___x_169_);
lean_dec(v_n_154_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_k_155_);
lean_ctor_set(v___x_159_, 0, v___x_170_);
v___x_172_ = v___x_159_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_k_155_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
else
{
lean_object* v_abs_174_; lean_object* v_one_175_; lean_object* v_a_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
lean_dec(v_k_155_);
v_abs_174_ = lean_nat_abs(v___x_161_);
lean_dec(v___x_161_);
v_one_175_ = lean_unsigned_to_nat(1u);
v_a_176_ = lean_nat_sub(v_abs_174_, v_one_175_);
lean_dec(v_abs_174_);
v___x_177_ = lean_nat_add(v_a_176_, v_one_175_);
lean_dec(v_a_176_);
v___x_178_ = l_Int_shiftLeft(v_n_154_, v___x_177_);
lean_dec(v___x_177_);
lean_dec(v_n_154_);
v___x_179_ = lean_int_add(v___x_178_, v_n_156_);
lean_dec(v_n_156_);
lean_dec(v___x_178_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_179_);
v___x_181_ = v___x_159_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_k_157_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_mul(lean_object* v_x_186_, lean_object* v_y_187_){
_start:
{
if (lean_obj_tag(v_x_186_) == 0)
{
lean_dec(v_y_187_);
return v_x_186_;
}
else
{
if (lean_obj_tag(v_y_187_) == 0)
{
return v_y_187_;
}
else
{
lean_object* v_n_188_; lean_object* v_k_189_; lean_object* v_n_190_; lean_object* v_k_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_200_; 
v_n_188_ = lean_ctor_get(v_x_186_, 0);
v_k_189_ = lean_ctor_get(v_x_186_, 1);
v_n_190_ = lean_ctor_get(v_y_187_, 0);
v_k_191_ = lean_ctor_get(v_y_187_, 1);
v_isSharedCheck_200_ = !lean_is_exclusive(v_y_187_);
if (v_isSharedCheck_200_ == 0)
{
v___x_193_ = v_y_187_;
v_isShared_194_ = v_isSharedCheck_200_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_k_191_);
lean_inc(v_n_190_);
lean_dec(v_y_187_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_200_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_195_ = lean_int_mul(v_n_188_, v_n_190_);
lean_dec(v_n_190_);
v___x_196_ = lean_int_add(v_k_189_, v_k_191_);
lean_dec(v_k_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 1, v___x_196_);
lean_ctor_set(v___x_193_, 0, v___x_195_);
v___x_198_ = v___x_193_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_mul___boxed(lean_object* v_x_201_, lean_object* v_y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Dyadic_mul(v_x_201_, v_y_202_);
lean_dec(v_x_201_);
return v_res_203_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__0(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_207_ = l_Dyadic_ofInt(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__1(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_to_int(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__2(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_obj_once(&l_Dyadic_pow___closed__1, &l_Dyadic_pow___closed__1_once, _init_l_Dyadic_pow___closed__1);
v___x_211_ = l_Dyadic_ofInt(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_pow(lean_object* v_x_212_, lean_object* v_i_213_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_nat_dec_eq(v_i_213_, v___x_214_);
lean_dec(v_i_213_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&l_Dyadic_pow___closed__0, &l_Dyadic_pow___closed__0_once, _init_l_Dyadic_pow___closed__0);
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Dyadic_pow___closed__2, &l_Dyadic_pow___closed__2_once, _init_l_Dyadic_pow___closed__2);
return v___x_217_;
}
}
else
{
lean_object* v_n_218_; lean_object* v_k_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_229_; 
v_n_218_ = lean_ctor_get(v_x_212_, 0);
v_k_219_ = lean_ctor_get(v_x_212_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_212_);
if (v_isSharedCheck_229_ == 0)
{
v___x_221_ = v_x_212_;
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_k_219_);
lean_inc(v_n_218_);
lean_dec(v_x_212_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_223_ = l_Int_pow(v_n_218_, v_i_213_);
lean_dec(v_n_218_);
v___x_224_ = lean_nat_to_int(v_i_213_);
v___x_225_ = lean_int_mul(v_k_219_, v___x_224_);
lean_dec(v___x_224_);
lean_dec(v_k_219_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v___x_225_);
lean_ctor_set(v___x_221_, 0, v___x_223_);
v___x_227_ = v___x_221_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_neg(lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
return v_x_232_;
}
else
{
lean_object* v_n_233_; lean_object* v_k_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_242_; 
v_n_233_ = lean_ctor_get(v_x_232_, 0);
v_k_234_ = lean_ctor_get(v_x_232_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_242_ == 0)
{
v___x_236_ = v_x_232_;
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_k_234_);
lean_inc(v_n_233_);
lean_dec(v_x_232_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = lean_int_neg(v_n_233_);
lean_dec(v_n_233_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_238_);
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_k_234_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_sub(lean_object* v_x_245_, lean_object* v_y_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = l_Dyadic_neg(v_y_246_);
v___x_248_ = l_Dyadic_add(v_x_245_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft(lean_object* v_x_251_, lean_object* v_i_252_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
return v_x_251_;
}
else
{
lean_object* v_n_253_; lean_object* v_k_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_262_; 
v_n_253_ = lean_ctor_get(v_x_251_, 0);
v_k_254_ = lean_ctor_get(v_x_251_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_251_);
if (v_isSharedCheck_262_ == 0)
{
v___x_256_ = v_x_251_;
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_k_254_);
lean_inc(v_n_253_);
lean_dec(v_x_251_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = lean_int_sub(v_k_254_, v_i_252_);
lean_dec(v_k_254_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_258_);
v___x_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_n_253_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft___boxed(lean_object* v_x_263_, lean_object* v_i_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Dyadic_shiftLeft(v_x_263_, v_i_264_);
lean_dec(v_i_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftRight(lean_object* v_x_266_, lean_object* v_i_267_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
return v_x_266_;
}
else
{
lean_object* v_n_268_; lean_object* v_k_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_n_268_ = lean_ctor_get(v_x_266_, 0);
v_k_269_ = lean_ctor_get(v_x_266_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_266_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v_x_266_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_k_269_);
lean_inc(v_n_268_);
lean_dec(v_x_266_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_int_add(v_k_269_, v_i_267_);
lean_dec(v_k_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 1, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_n_268_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftRight___boxed(lean_object* v_x_278_, lean_object* v_i_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Dyadic_shiftRight(v_x_278_, v_i_279_);
lean_dec(v_i_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instHShiftLeftNat___lam__0(lean_object* v_x_285_, lean_object* v_y_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_nat_to_int(v_y_286_);
v___x_288_ = l_Dyadic_shiftLeft(v_x_285_, v___x_287_);
lean_dec(v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instHShiftRightNat___lam__0(lean_object* v_x_291_, lean_object* v_y_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_nat_to_int(v_y_292_);
v___x_294_ = l_Dyadic_shiftRight(v_x_291_, v___x_293_);
lean_dec(v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Dyadic_toRat_spec__1(lean_object* v_a_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Rat_ofInt(v_a_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_toRat_spec__0(lean_object* v_a_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_nat_to_int(v_a_299_);
v___x_301_ = l_Rat_ofInt(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Dyadic_toRat___closed__0(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = l_Nat_cast___at___00Dyadic_toRat_spec__0(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_toRat(lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Dyadic_toRat___closed__0, &l_Dyadic_toRat___closed__0_once, _init_l_Dyadic_toRat___closed__0);
return v___x_305_;
}
else
{
lean_object* v_n_306_; lean_object* v_k_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_328_; 
v_n_306_ = lean_ctor_get(v_x_304_, 0);
v_k_307_ = lean_ctor_get(v_x_304_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_304_);
if (v_isSharedCheck_328_ == 0)
{
v___x_309_ = v_x_304_;
v_isShared_310_ = v_isSharedCheck_328_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_k_307_);
lean_inc(v_n_306_);
lean_dec(v_x_304_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_328_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v_intZero_311_; uint8_t v_isNeg_312_; 
v_intZero_311_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_312_ = lean_int_dec_lt(v_k_307_, v_intZero_311_);
if (v_isNeg_312_ == 0)
{
lean_object* v_a_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v_a_313_ = lean_nat_abs(v_k_307_);
lean_dec(v_k_307_);
v___x_314_ = lean_unsigned_to_nat(2u);
v___x_315_ = lean_nat_pow(v___x_314_, v_a_313_);
lean_dec(v_a_313_);
if (v_isShared_310_ == 0)
{
lean_ctor_set_tag(v___x_309_, 0);
lean_ctor_set(v___x_309_, 1, v___x_315_);
v___x_317_ = v___x_309_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_n_306_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
lean_object* v_abs_319_; lean_object* v_one_320_; lean_object* v_a_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_del_object(v___x_309_);
v_abs_319_ = lean_nat_abs(v_k_307_);
lean_dec(v_k_307_);
v_one_320_ = lean_unsigned_to_nat(1u);
v_a_321_ = lean_nat_sub(v_abs_319_, v_one_320_);
lean_dec(v_abs_319_);
v___x_322_ = lean_unsigned_to_nat(2u);
v___x_323_ = lean_nat_add(v_a_321_, v_one_320_);
lean_dec(v_a_321_);
v___x_324_ = lean_nat_pow(v___x_322_, v___x_323_);
lean_dec(v___x_323_);
v___x_325_ = lean_nat_to_int(v___x_324_);
v___x_326_ = lean_int_mul(v_n_306_, v___x_325_);
lean_dec(v___x_325_);
lean_dec(v_n_306_);
v___x_327_ = l_Rat_ofInt(v___x_326_);
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter___redArg(lean_object* v_x_329_, lean_object* v_h__1_330_, lean_object* v_h__2_331_, lean_object* v_h__3_332_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_h__3_332_);
lean_dec(v_h__2_331_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_apply_1(v_h__1_330_, v___x_333_);
return v___x_334_;
}
else
{
lean_object* v_n_335_; lean_object* v_k_336_; lean_object* v_intZero_337_; uint8_t v_isNeg_338_; 
lean_dec(v_h__1_330_);
v_n_335_ = lean_ctor_get(v_x_329_, 0);
lean_inc(v_n_335_);
v_k_336_ = lean_ctor_get(v_x_329_, 1);
lean_inc(v_k_336_);
lean_dec_ref(v_x_329_);
v_intZero_337_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_338_ = lean_int_dec_lt(v_k_336_, v_intZero_337_);
if (v_isNeg_338_ == 0)
{
lean_object* v_a_339_; lean_object* v___x_340_; 
lean_dec(v_h__3_332_);
v_a_339_ = lean_nat_abs(v_k_336_);
lean_dec(v_k_336_);
v___x_340_ = lean_apply_3(v_h__2_331_, v_n_335_, v_a_339_, lean_box(0));
return v___x_340_;
}
else
{
lean_object* v_abs_341_; lean_object* v_one_342_; lean_object* v_a_343_; lean_object* v___x_344_; 
lean_dec(v_h__2_331_);
v_abs_341_ = lean_nat_abs(v_k_336_);
lean_dec(v_k_336_);
v_one_342_ = lean_unsigned_to_nat(1u);
v_a_343_ = lean_nat_sub(v_abs_341_, v_one_342_);
lean_dec(v_abs_341_);
v___x_344_ = lean_apply_3(v_h__3_332_, v_n_335_, v_a_343_, lean_box(0));
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter(lean_object* v_motive_345_, lean_object* v_x_346_, lean_object* v_h__1_347_, lean_object* v_h__2_348_, lean_object* v_h__3_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter___redArg(v_x_346_, v_h__1_347_, v_h__2_348_, v_h__3_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter___redArg(lean_object* v_x_351_, lean_object* v_y_352_, lean_object* v_h__1_353_, lean_object* v_h__2_354_, lean_object* v_h__3_355_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v___x_356_; 
lean_dec(v_h__3_355_);
lean_dec(v_h__2_354_);
v___x_356_ = lean_apply_1(v_h__1_353_, v_y_352_);
return v___x_356_;
}
else
{
lean_dec(v_h__1_353_);
if (lean_obj_tag(v_y_352_) == 0)
{
lean_object* v_n_357_; lean_object* v_k_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_h__3_355_);
v_n_357_ = lean_ctor_get(v_x_351_, 0);
v_k_358_ = lean_ctor_get(v_x_351_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_x_351_);
if (v_isSharedCheck_366_ == 0)
{
v___x_360_ = v_x_351_;
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_k_358_);
lean_inc(v_n_357_);
lean_dec(v_x_351_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_n_357_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_k_358_);
v___x_363_ = v_reuseFailAlloc_365_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; 
v___x_364_ = lean_apply_2(v_h__2_354_, v___x_363_, lean_box(0));
return v___x_364_;
}
}
}
else
{
lean_object* v_n_367_; lean_object* v_k_368_; lean_object* v_n_369_; lean_object* v_k_370_; lean_object* v___x_371_; 
lean_dec(v_h__2_354_);
v_n_367_ = lean_ctor_get(v_x_351_, 0);
lean_inc(v_n_367_);
v_k_368_ = lean_ctor_get(v_x_351_, 1);
lean_inc(v_k_368_);
lean_dec_ref(v_x_351_);
v_n_369_ = lean_ctor_get(v_y_352_, 0);
lean_inc(v_n_369_);
v_k_370_ = lean_ctor_get(v_y_352_, 1);
lean_inc(v_k_370_);
lean_dec_ref(v_y_352_);
v___x_371_ = lean_apply_6(v_h__3_355_, v_n_367_, v_k_368_, lean_box(0), v_n_369_, v_k_370_, lean_box(0));
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter(lean_object* v_motive_372_, lean_object* v_x_373_, lean_object* v_y_374_, lean_object* v_h__1_375_, lean_object* v_h__2_376_, lean_object* v_h__3_377_){
_start:
{
if (lean_obj_tag(v_x_373_) == 0)
{
lean_object* v___x_378_; 
lean_dec(v_h__3_377_);
lean_dec(v_h__2_376_);
v___x_378_ = lean_apply_1(v_h__1_375_, v_y_374_);
return v___x_378_;
}
else
{
lean_dec(v_h__1_375_);
if (lean_obj_tag(v_y_374_) == 0)
{
lean_object* v_n_379_; lean_object* v_k_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_388_; 
lean_dec(v_h__3_377_);
v_n_379_ = lean_ctor_get(v_x_373_, 0);
v_k_380_ = lean_ctor_get(v_x_373_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_388_ == 0)
{
v___x_382_ = v_x_373_;
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_k_380_);
lean_inc(v_n_379_);
lean_dec(v_x_373_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_388_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_n_379_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_k_380_);
v___x_385_ = v_reuseFailAlloc_387_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; 
v___x_386_ = lean_apply_2(v_h__2_376_, v___x_385_, lean_box(0));
return v___x_386_;
}
}
}
else
{
lean_object* v_n_389_; lean_object* v_k_390_; lean_object* v_n_391_; lean_object* v_k_392_; lean_object* v___x_393_; 
lean_dec(v_h__2_376_);
v_n_389_ = lean_ctor_get(v_x_373_, 0);
lean_inc(v_n_389_);
v_k_390_ = lean_ctor_get(v_x_373_, 1);
lean_inc(v_k_390_);
lean_dec_ref(v_x_373_);
v_n_391_ = lean_ctor_get(v_y_374_, 0);
lean_inc(v_n_391_);
v_k_392_ = lean_ctor_get(v_y_374_, 1);
lean_inc(v_k_392_);
lean_dec_ref(v_y_374_);
v___x_393_ = lean_apply_6(v_h__3_377_, v_n_389_, v_k_390_, lean_box(0), v_n_391_, v_k_392_, lean_box(0));
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(lean_object* v_x_394_, lean_object* v_h__1_395_, lean_object* v_h__2_396_, lean_object* v_h__3_397_){
_start:
{
lean_object* v_natZero_398_; lean_object* v_intZero_399_; uint8_t v_isNeg_400_; 
v_natZero_398_ = lean_unsigned_to_nat(0u);
v_intZero_399_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_400_ = lean_int_dec_lt(v_x_394_, v_intZero_399_);
if (v_isNeg_400_ == 0)
{
lean_object* v_a_401_; uint8_t v_isZero_402_; 
lean_dec(v_h__3_397_);
v_a_401_ = lean_nat_abs(v_x_394_);
v_isZero_402_ = lean_nat_dec_eq(v_a_401_, v_natZero_398_);
if (v_isZero_402_ == 1)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_a_401_);
lean_dec(v_h__2_396_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_apply_1(v_h__1_395_, v___x_403_);
return v___x_404_;
}
else
{
lean_object* v_one_405_; lean_object* v_n_406_; lean_object* v___x_407_; 
lean_dec(v_h__1_395_);
v_one_405_ = lean_unsigned_to_nat(1u);
v_n_406_ = lean_nat_sub(v_a_401_, v_one_405_);
lean_dec(v_a_401_);
v___x_407_ = lean_apply_1(v_h__2_396_, v_n_406_);
return v___x_407_;
}
}
else
{
lean_object* v_abs_408_; lean_object* v_one_409_; lean_object* v_a_410_; lean_object* v___x_411_; 
lean_dec(v_h__2_396_);
lean_dec(v_h__1_395_);
v_abs_408_ = lean_nat_abs(v_x_394_);
v_one_409_ = lean_unsigned_to_nat(1u);
v_a_410_ = lean_nat_sub(v_abs_408_, v_one_409_);
lean_dec(v_abs_408_);
v___x_411_ = lean_apply_1(v_h__3_397_, v_a_410_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg___boxed(lean_object* v_x_412_, lean_object* v_h__1_413_, lean_object* v_h__2_414_, lean_object* v_h__3_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(v_x_412_, v_h__1_413_, v_h__2_414_, v_h__3_415_);
lean_dec(v_x_412_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(lean_object* v_motive_417_, lean_object* v_x_418_, lean_object* v_h__1_419_, lean_object* v_h__2_420_, lean_object* v_h__3_421_){
_start:
{
lean_object* v_natZero_422_; lean_object* v_intZero_423_; uint8_t v_isNeg_424_; 
v_natZero_422_ = lean_unsigned_to_nat(0u);
v_intZero_423_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_424_ = lean_int_dec_lt(v_x_418_, v_intZero_423_);
if (v_isNeg_424_ == 0)
{
lean_object* v_a_425_; uint8_t v_isZero_426_; 
lean_dec(v_h__3_421_);
v_a_425_ = lean_nat_abs(v_x_418_);
v_isZero_426_ = lean_nat_dec_eq(v_a_425_, v_natZero_422_);
if (v_isZero_426_ == 1)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_a_425_);
lean_dec(v_h__2_420_);
v___x_427_ = lean_box(0);
v___x_428_ = lean_apply_1(v_h__1_419_, v___x_427_);
return v___x_428_;
}
else
{
lean_object* v_one_429_; lean_object* v_n_430_; lean_object* v___x_431_; 
lean_dec(v_h__1_419_);
v_one_429_ = lean_unsigned_to_nat(1u);
v_n_430_ = lean_nat_sub(v_a_425_, v_one_429_);
lean_dec(v_a_425_);
v___x_431_ = lean_apply_1(v_h__2_420_, v_n_430_);
return v___x_431_;
}
}
else
{
lean_object* v_abs_432_; lean_object* v_one_433_; lean_object* v_a_434_; lean_object* v___x_435_; 
lean_dec(v_h__2_420_);
lean_dec(v_h__1_419_);
v_abs_432_ = lean_nat_abs(v_x_418_);
v_one_433_ = lean_unsigned_to_nat(1u);
v_a_434_ = lean_nat_sub(v_abs_432_, v_one_433_);
lean_dec(v_abs_432_);
v___x_435_ = lean_apply_1(v_h__3_421_, v_a_434_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___boxed(lean_object* v_motive_436_, lean_object* v_x_437_, lean_object* v_h__1_438_, lean_object* v_h__2_439_, lean_object* v_h__3_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(v_motive_436_, v_x_437_, v_h__1_438_, v_h__2_439_, v_h__3_440_);
lean_dec(v_x_437_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter___redArg(lean_object* v_x_442_, lean_object* v_h__1_443_, lean_object* v_h__2_444_){
_start:
{
if (lean_obj_tag(v_x_442_) == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_h__2_444_);
v___x_445_ = lean_box(0);
v___x_446_ = lean_apply_1(v_h__1_443_, v___x_445_);
return v___x_446_;
}
else
{
lean_object* v_n_447_; lean_object* v_k_448_; lean_object* v___x_449_; 
lean_dec(v_h__1_443_);
v_n_447_ = lean_ctor_get(v_x_442_, 0);
lean_inc(v_n_447_);
v_k_448_ = lean_ctor_get(v_x_442_, 1);
lean_inc(v_k_448_);
lean_dec_ref(v_x_442_);
v___x_449_ = lean_apply_3(v_h__2_444_, v_n_447_, v_k_448_, lean_box(0));
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter(lean_object* v_motive_450_, lean_object* v_x_451_, lean_object* v_h__1_452_, lean_object* v_h__2_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter___redArg(v_x_451_, v_h__1_452_, v_h__2_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_precision(lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_box(0);
return v___x_456_;
}
else
{
lean_object* v_k_457_; lean_object* v___x_458_; 
v_k_457_ = lean_ctor_get(v_x_455_, 1);
lean_inc(v_k_457_);
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_k_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_precision___boxed(lean_object* v_x_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Dyadic_precision(v_x_459_);
lean_dec(v_x_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Rat_toDyadic(lean_object* v_x_461_, lean_object* v_prec_462_){
_start:
{
lean_object* v_intZero_463_; uint8_t v_isNeg_464_; 
v_intZero_463_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_464_ = lean_int_dec_lt(v_prec_462_, v_intZero_463_);
if (v_isNeg_464_ == 0)
{
lean_object* v_num_465_; lean_object* v_den_466_; lean_object* v_a_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_num_465_ = lean_ctor_get(v_x_461_, 0);
lean_inc(v_num_465_);
v_den_466_ = lean_ctor_get(v_x_461_, 1);
lean_inc(v_den_466_);
lean_dec_ref(v_x_461_);
v_a_467_ = lean_nat_abs(v_prec_462_);
v___x_468_ = l_Int_shiftLeft(v_num_465_, v_a_467_);
lean_dec(v_a_467_);
lean_dec(v_num_465_);
v___x_469_ = lean_nat_to_int(v_den_466_);
v___x_470_ = lean_int_ediv(v___x_468_, v___x_469_);
lean_dec(v___x_469_);
lean_dec(v___x_468_);
v___x_471_ = l_Dyadic_ofIntWithPrec(v___x_470_, v_prec_462_);
return v___x_471_;
}
else
{
lean_object* v_num_472_; lean_object* v_den_473_; lean_object* v_abs_474_; lean_object* v_one_475_; lean_object* v_a_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_num_472_ = lean_ctor_get(v_x_461_, 0);
lean_inc(v_num_472_);
v_den_473_ = lean_ctor_get(v_x_461_, 1);
lean_inc(v_den_473_);
lean_dec_ref(v_x_461_);
v_abs_474_ = lean_nat_abs(v_prec_462_);
v_one_475_ = lean_unsigned_to_nat(1u);
v_a_476_ = lean_nat_sub(v_abs_474_, v_one_475_);
lean_dec(v_abs_474_);
v___x_477_ = lean_nat_add(v_a_476_, v_one_475_);
lean_dec(v_a_476_);
v___x_478_ = lean_nat_shiftl(v_den_473_, v___x_477_);
lean_dec(v___x_477_);
lean_dec(v_den_473_);
v___x_479_ = lean_nat_to_int(v___x_478_);
v___x_480_ = lean_int_ediv(v_num_472_, v___x_479_);
lean_dec(v___x_479_);
lean_dec(v_num_472_);
v___x_481_ = l_Dyadic_ofIntWithPrec(v___x_480_, v_prec_462_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_toDyadic___boxed(lean_object* v_x_482_, lean_object* v_prec_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Rat_toDyadic(v_x_482_, v_prec_483_);
lean_dec(v_prec_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(lean_object* v_prec_485_, lean_object* v_h__1_486_, lean_object* v_h__2_487_){
_start:
{
lean_object* v_intZero_488_; uint8_t v_isNeg_489_; 
v_intZero_488_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_489_ = lean_int_dec_lt(v_prec_485_, v_intZero_488_);
if (v_isNeg_489_ == 0)
{
lean_object* v_a_490_; lean_object* v___x_491_; 
lean_dec(v_h__2_487_);
v_a_490_ = lean_nat_abs(v_prec_485_);
v___x_491_ = lean_apply_1(v_h__1_486_, v_a_490_);
return v___x_491_;
}
else
{
lean_object* v_abs_492_; lean_object* v_one_493_; lean_object* v_a_494_; lean_object* v___x_495_; 
lean_dec(v_h__1_486_);
v_abs_492_ = lean_nat_abs(v_prec_485_);
v_one_493_ = lean_unsigned_to_nat(1u);
v_a_494_ = lean_nat_sub(v_abs_492_, v_one_493_);
lean_dec(v_abs_492_);
v___x_495_ = lean_apply_1(v_h__2_487_, v_a_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg___boxed(lean_object* v_prec_496_, lean_object* v_h__1_497_, lean_object* v_h__2_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(v_prec_496_, v_h__1_497_, v_h__2_498_);
lean_dec(v_prec_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(lean_object* v_motive_500_, lean_object* v_prec_501_, lean_object* v_h__1_502_, lean_object* v_h__2_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(v_prec_501_, v_h__1_502_, v_h__2_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___boxed(lean_object* v_motive_505_, lean_object* v_prec_506_, lean_object* v_h__1_507_, lean_object* v_h__2_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(v_motive_505_, v_prec_506_, v_h__1_507_, v_h__2_508_);
lean_dec(v_prec_506_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundDown(lean_object* v_x_510_, lean_object* v_prec_511_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
return v_x_510_;
}
else
{
lean_object* v_n_512_; lean_object* v_k_513_; lean_object* v___x_514_; lean_object* v_intZero_515_; uint8_t v_isNeg_516_; 
v_n_512_ = lean_ctor_get(v_x_510_, 0);
v_k_513_ = lean_ctor_get(v_x_510_, 1);
v___x_514_ = lean_int_sub(v_k_513_, v_prec_511_);
v_intZero_515_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_516_ = lean_int_dec_lt(v___x_514_, v_intZero_515_);
if (v_isNeg_516_ == 0)
{
lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_a_517_ = lean_nat_abs(v___x_514_);
lean_dec(v___x_514_);
v___x_518_ = l_Int_shiftRight(v_n_512_, v_a_517_);
lean_dec(v_a_517_);
v___x_519_ = l_Dyadic_ofIntWithPrec(v___x_518_, v_prec_511_);
return v___x_519_;
}
else
{
lean_dec(v___x_514_);
lean_inc_ref(v_x_510_);
return v_x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundDown___boxed(lean_object* v_x_520_, lean_object* v_prec_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Dyadic_roundDown(v_x_520_, v_prec_521_);
lean_dec(v_prec_521_);
lean_dec(v_x_520_);
return v_res_522_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_blt(lean_object* v_x_523_, lean_object* v_y_524_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
if (lean_obj_tag(v_y_524_) == 0)
{
uint8_t v___x_525_; 
v___x_525_ = 0;
return v___x_525_;
}
else
{
lean_object* v_n_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_n_526_ = lean_ctor_get(v_y_524_, 0);
v___x_527_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_528_ = lean_int_dec_lt(v___x_527_, v_n_526_);
return v___x_528_;
}
}
else
{
if (lean_obj_tag(v_y_524_) == 0)
{
lean_object* v_n_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_n_529_ = lean_ctor_get(v_x_523_, 0);
v___x_530_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_531_ = lean_int_dec_lt(v_n_529_, v___x_530_);
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
v_intZero_537_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_538_ = lean_int_dec_lt(v___x_536_, v_intZero_537_);
if (v_isNeg_538_ == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_a_539_ = lean_nat_abs(v___x_536_);
lean_dec(v___x_536_);
v___x_540_ = l_Int_shiftLeft(v_n_532_, v_a_539_);
lean_dec(v_a_539_);
v___x_541_ = lean_int_dec_lt(v___x_540_, v_n_534_);
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
v___x_547_ = lean_int_dec_lt(v_n_532_, v___x_546_);
lean_dec(v___x_546_);
return v___x_547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_blt___boxed(lean_object* v_x_548_, lean_object* v_y_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Dyadic_blt(v_x_548_, v_y_549_);
lean_dec(v_y_549_);
lean_dec(v_x_548_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_ble(lean_object* v_x_552_, lean_object* v_y_553_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
if (lean_obj_tag(v_y_553_) == 0)
{
uint8_t v___x_554_; 
v___x_554_ = 1;
return v___x_554_;
}
else
{
lean_object* v_n_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_n_555_ = lean_ctor_get(v_y_553_, 0);
v___x_556_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_557_ = lean_int_dec_le(v___x_556_, v_n_555_);
return v___x_557_;
}
}
else
{
if (lean_obj_tag(v_y_553_) == 0)
{
lean_object* v_n_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_n_558_ = lean_ctor_get(v_x_552_, 0);
v___x_559_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_560_ = lean_int_dec_le(v_n_558_, v___x_559_);
return v___x_560_;
}
else
{
lean_object* v_n_561_; lean_object* v_k_562_; lean_object* v_n_563_; lean_object* v_k_564_; lean_object* v___x_565_; lean_object* v_intZero_566_; uint8_t v_isNeg_567_; 
v_n_561_ = lean_ctor_get(v_x_552_, 0);
v_k_562_ = lean_ctor_get(v_x_552_, 1);
v_n_563_ = lean_ctor_get(v_y_553_, 0);
v_k_564_ = lean_ctor_get(v_y_553_, 1);
v___x_565_ = lean_int_sub(v_k_564_, v_k_562_);
v_intZero_566_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_567_ = lean_int_dec_lt(v___x_565_, v_intZero_566_);
if (v_isNeg_567_ == 0)
{
lean_object* v_a_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_a_568_ = lean_nat_abs(v___x_565_);
lean_dec(v___x_565_);
v___x_569_ = l_Int_shiftLeft(v_n_561_, v_a_568_);
lean_dec(v_a_568_);
v___x_570_ = lean_int_dec_le(v___x_569_, v_n_563_);
lean_dec(v___x_569_);
return v___x_570_;
}
else
{
lean_object* v_abs_571_; lean_object* v_one_572_; lean_object* v_a_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_abs_571_ = lean_nat_abs(v___x_565_);
lean_dec(v___x_565_);
v_one_572_ = lean_unsigned_to_nat(1u);
v_a_573_ = lean_nat_sub(v_abs_571_, v_one_572_);
lean_dec(v_abs_571_);
v___x_574_ = lean_nat_add(v_a_573_, v_one_572_);
lean_dec(v_a_573_);
v___x_575_ = l_Int_shiftLeft(v_n_563_, v___x_574_);
lean_dec(v___x_574_);
v___x_576_ = lean_int_dec_le(v_n_561_, v___x_575_);
lean_dec(v___x_575_);
return v___x_576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ble___boxed(lean_object* v_x_577_, lean_object* v_y_578_){
_start:
{
uint8_t v_res_579_; lean_object* v_r_580_; 
v_res_579_ = l_Dyadic_ble(v_x_577_, v_y_578_);
lean_dec(v_y_578_);
lean_dec(v_x_577_);
v_r_580_ = lean_box(v_res_579_);
return v_r_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter___redArg(lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_h__1_583_, lean_object* v_h__2_584_, lean_object* v_h__3_585_, lean_object* v_h__4_586_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
lean_dec(v_h__4_586_);
lean_dec(v_h__3_585_);
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_h__2_584_);
v___x_587_ = lean_box(0);
v___x_588_ = lean_apply_1(v_h__1_583_, v___x_587_);
return v___x_588_;
}
else
{
lean_object* v_n_589_; lean_object* v_k_590_; lean_object* v___x_591_; 
lean_dec(v_h__1_583_);
v_n_589_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_n_589_);
v_k_590_ = lean_ctor_get(v_x_582_, 1);
lean_inc(v_k_590_);
lean_dec_ref(v_x_582_);
v___x_591_ = lean_apply_3(v_h__2_584_, v_n_589_, v_k_590_, lean_box(0));
return v___x_591_;
}
}
else
{
lean_dec(v_h__2_584_);
lean_dec(v_h__1_583_);
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v_n_592_; lean_object* v_k_593_; lean_object* v___x_594_; 
lean_dec(v_h__4_586_);
v_n_592_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_n_592_);
v_k_593_ = lean_ctor_get(v_x_581_, 1);
lean_inc(v_k_593_);
lean_dec_ref(v_x_581_);
v___x_594_ = lean_apply_3(v_h__3_585_, v_n_592_, v_k_593_, lean_box(0));
return v___x_594_;
}
else
{
lean_object* v_n_595_; lean_object* v_k_596_; lean_object* v_n_597_; lean_object* v_k_598_; lean_object* v___x_599_; 
lean_dec(v_h__3_585_);
v_n_595_ = lean_ctor_get(v_x_581_, 0);
lean_inc(v_n_595_);
v_k_596_ = lean_ctor_get(v_x_581_, 1);
lean_inc(v_k_596_);
lean_dec_ref(v_x_581_);
v_n_597_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_n_597_);
v_k_598_ = lean_ctor_get(v_x_582_, 1);
lean_inc(v_k_598_);
lean_dec_ref(v_x_582_);
v___x_599_ = lean_apply_6(v_h__4_586_, v_n_595_, v_k_596_, lean_box(0), v_n_597_, v_k_598_, lean_box(0));
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter(lean_object* v_motive_600_, lean_object* v_x_601_, lean_object* v_x_602_, lean_object* v_h__1_603_, lean_object* v_h__2_604_, lean_object* v_h__3_605_, lean_object* v_h__4_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter___redArg(v_x_601_, v_x_602_, v_h__1_603_, v_h__2_604_, v_h__3_605_, v_h__4_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Dyadic_instLT(void){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_box(0);
return v___x_608_;
}
}
static lean_object* _init_l_Dyadic_instLE(void){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_box(0);
return v___x_609_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLT(lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = l_Dyadic_blt(v_x_610_, v_x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLT___boxed(lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
uint8_t v_res_615_; lean_object* v_r_616_; 
v_res_615_ = l_Dyadic_instDecidableLT(v_x_613_, v_x_614_);
lean_dec(v_x_614_);
lean_dec(v_x_613_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLE(lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
uint8_t v___x_619_; 
v___x_619_ = l_Dyadic_ble(v_x_617_, v_x_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLE___boxed(lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Dyadic_instDecidableLE(v_x_620_, v_x_621_);
lean_dec(v_x_621_);
lean_dec(v_x_620_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundUp(lean_object* v_x_624_, lean_object* v_prec_625_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
return v_x_624_;
}
else
{
lean_object* v_n_626_; lean_object* v_k_627_; lean_object* v___x_628_; lean_object* v_intZero_629_; uint8_t v_isNeg_630_; 
v_n_626_ = lean_ctor_get(v_x_624_, 0);
v_k_627_ = lean_ctor_get(v_x_624_, 1);
v___x_628_ = lean_int_sub(v_k_627_, v_prec_625_);
v_intZero_629_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_630_ = lean_int_dec_lt(v___x_628_, v_intZero_629_);
if (v_isNeg_630_ == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_a_631_ = lean_nat_abs(v___x_628_);
lean_dec(v___x_628_);
v___x_632_ = lean_int_neg(v_n_626_);
v___x_633_ = l_Int_shiftRight(v___x_632_, v_a_631_);
lean_dec(v_a_631_);
lean_dec(v___x_632_);
v___x_634_ = lean_int_neg(v___x_633_);
lean_dec(v___x_633_);
v___x_635_ = l_Dyadic_ofIntWithPrec(v___x_634_, v_prec_625_);
return v___x_635_;
}
else
{
lean_dec(v___x_628_);
lean_inc_ref(v_x_624_);
return v_x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundUp___boxed(lean_object* v_x_636_, lean_object* v_prec_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Dyadic_roundUp(v_x_636_, v_prec_637_);
lean_dec(v_prec_637_);
lean_dec(v_x_636_);
return v_res_638_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Dyadic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
