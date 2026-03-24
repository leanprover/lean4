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
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx(lean_object* v_x_59_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v___x_60_; 
v___x_60_ = lean_unsigned_to_nat(0u);
return v___x_60_;
}
else
{
lean_object* v___x_61_; 
v___x_61_ = lean_unsigned_to_nat(1u);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorIdx___boxed(lean_object* v_x_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Dyadic_ctorIdx(v_x_62_);
lean_dec(v_x_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim___redArg(lean_object* v_t_64_, lean_object* v_k_65_){
_start:
{
if (lean_obj_tag(v_t_64_) == 0)
{
return v_k_65_;
}
else
{
lean_object* v_n_66_; lean_object* v_k_67_; lean_object* v___x_68_; 
v_n_66_ = lean_ctor_get(v_t_64_, 0);
lean_inc(v_n_66_);
v_k_67_ = lean_ctor_get(v_t_64_, 1);
lean_inc(v_k_67_);
lean_dec_ref(v_t_64_);
v___x_68_ = lean_apply_3(v_k_65_, v_n_66_, v_k_67_, lean_box(0));
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim(lean_object* v_motive_69_, lean_object* v_ctorIdx_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_k_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Dyadic_ctorElim___redArg(v_t_71_, v_k_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ctorElim___boxed(lean_object* v_motive_75_, lean_object* v_ctorIdx_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_k_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Dyadic_ctorElim(v_motive_75_, v_ctorIdx_76_, v_t_77_, v_h_78_, v_k_79_);
lean_dec(v_ctorIdx_76_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_zero_elim___redArg(lean_object* v_t_81_, lean_object* v_zero_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Dyadic_ctorElim___redArg(v_t_81_, v_zero_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_zero_elim(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_zero_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Dyadic_ctorElim___redArg(v_t_85_, v_zero_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofOdd_elim___redArg(lean_object* v_t_89_, lean_object* v_ofOdd_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Dyadic_ctorElim___redArg(v_t_89_, v_ofOdd_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofOdd_elim(lean_object* v_motive_92_, lean_object* v_t_93_, lean_object* v_h_94_, lean_object* v_ofOdd_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Dyadic_ctorElim___redArg(v_t_93_, v_ofOdd_95_);
return v___x_96_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqDyadic_decEq(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_97_) == 0)
{
if (lean_obj_tag(v_x_98_) == 0)
{
uint8_t v___x_99_; 
v___x_99_ = 1;
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
}
else
{
if (lean_obj_tag(v_x_98_) == 0)
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
else
{
lean_object* v_n_102_; lean_object* v_k_103_; lean_object* v_n_104_; lean_object* v_k_105_; uint8_t v___x_106_; 
v_n_102_ = lean_ctor_get(v_x_97_, 0);
v_k_103_ = lean_ctor_get(v_x_97_, 1);
v_n_104_ = lean_ctor_get(v_x_98_, 0);
v_k_105_ = lean_ctor_get(v_x_98_, 1);
v___x_106_ = lean_int_dec_eq(v_n_102_, v_n_104_);
if (v___x_106_ == 0)
{
return v___x_106_;
}
else
{
uint8_t v___x_107_; 
v___x_107_ = lean_int_dec_eq(v_k_103_, v_k_105_);
return v___x_107_;
}
}
}
}
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
LEAN_EXPORT uint8_t l_instDecidableEqDyadic(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = l_instDecidableEqDyadic_decEq(v_x_112_, v_x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqDyadic___boxed(lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_instDecidableEqDyadic(v_x_115_, v_x_116_);
lean_dec(v_x_116_);
lean_dec(v_x_115_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_ofIntWithPrec_spec__0(lean_object* v_a_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_nat_to_int(v_a_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec(lean_object* v_i_121_, lean_object* v_prec_122_){
_start:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_124_ = lean_int_dec_eq(v_i_121_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
lean_inc(v_i_121_);
v___x_125_ = l_Int_trailingZeros(v_i_121_);
v___x_126_ = l_Int_shiftRight(v_i_121_, v___x_125_);
lean_dec(v_i_121_);
v___x_127_ = lean_nat_to_int(v___x_125_);
v___x_128_ = lean_int_sub(v_prec_122_, v___x_127_);
lean_dec(v___x_127_);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_126_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
lean_dec(v_i_121_);
v___x_130_ = lean_box(0);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofIntWithPrec___boxed(lean_object* v_i_131_, lean_object* v_prec_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Dyadic_ofIntWithPrec(v_i_131_, v_prec_132_);
lean_dec(v_prec_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_ofInt(lean_object* v_i_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_136_ = l_Dyadic_ofIntWithPrec(v_i_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instOfNat(lean_object* v_n_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_nat_to_int(v_n_137_);
v___x_139_ = l_Dyadic_ofInt(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instNatCast___lam__0(lean_object* v_x_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_nat_to_int(v_x_142_);
v___x_144_ = l_Dyadic_ofInt(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_add(lean_object* v_x_147_, lean_object* v_y_148_){
_start:
{
if (lean_obj_tag(v_x_147_) == 0)
{
return v_y_148_;
}
else
{
if (lean_obj_tag(v_y_148_) == 0)
{
lean_object* v_n_149_; lean_object* v_k_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_n_149_ = lean_ctor_get(v_x_147_, 0);
v_k_150_ = lean_ctor_get(v_x_147_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v_x_147_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_k_150_);
lean_inc(v_n_149_);
lean_dec(v_x_147_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_n_149_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_k_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
else
{
lean_object* v_n_158_; lean_object* v_k_159_; lean_object* v_n_160_; lean_object* v_k_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_187_; 
v_n_158_ = lean_ctor_get(v_x_147_, 0);
lean_inc(v_n_158_);
v_k_159_ = lean_ctor_get(v_x_147_, 1);
lean_inc(v_k_159_);
lean_dec_ref(v_x_147_);
v_n_160_ = lean_ctor_get(v_y_148_, 0);
v_k_161_ = lean_ctor_get(v_y_148_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_y_148_);
if (v_isSharedCheck_187_ == 0)
{
v___x_163_ = v_y_148_;
v_isShared_164_ = v_isSharedCheck_187_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_k_161_);
lean_inc(v_n_160_);
lean_dec(v_y_148_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_187_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v_natZero_166_; lean_object* v_intZero_167_; uint8_t v_isNeg_168_; 
v___x_165_ = lean_int_sub(v_k_159_, v_k_161_);
v_natZero_166_ = lean_unsigned_to_nat(0u);
v_intZero_167_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_168_ = lean_int_dec_lt(v___x_165_, v_intZero_167_);
if (v_isNeg_168_ == 0)
{
lean_object* v_a_169_; uint8_t v_isZero_170_; 
lean_dec(v_k_161_);
v_a_169_ = lean_nat_abs(v___x_165_);
lean_dec(v___x_165_);
v_isZero_170_ = lean_nat_dec_eq(v_a_169_, v_natZero_166_);
if (v_isZero_170_ == 1)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_a_169_);
lean_del_object(v___x_163_);
v___x_171_ = lean_int_add(v_n_158_, v_n_160_);
lean_dec(v_n_160_);
lean_dec(v_n_158_);
v___x_172_ = l_Dyadic_ofIntWithPrec(v___x_171_, v_k_159_);
lean_dec(v_k_159_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_173_ = l_Int_shiftLeft(v_n_160_, v_a_169_);
lean_dec(v_a_169_);
lean_dec(v_n_160_);
v___x_174_ = lean_int_add(v_n_158_, v___x_173_);
lean_dec(v___x_173_);
lean_dec(v_n_158_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v_k_159_);
lean_ctor_set(v___x_163_, 0, v___x_174_);
v___x_176_ = v___x_163_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_k_159_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
else
{
lean_object* v_abs_178_; lean_object* v_one_179_; lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
lean_dec(v_k_159_);
v_abs_178_ = lean_nat_abs(v___x_165_);
lean_dec(v___x_165_);
v_one_179_ = lean_unsigned_to_nat(1u);
v_a_180_ = lean_nat_sub(v_abs_178_, v_one_179_);
lean_dec(v_abs_178_);
v___x_181_ = lean_nat_add(v_a_180_, v_one_179_);
lean_dec(v_a_180_);
v___x_182_ = l_Int_shiftLeft(v_n_158_, v___x_181_);
lean_dec(v___x_181_);
lean_dec(v_n_158_);
v___x_183_ = lean_int_add(v___x_182_, v_n_160_);
lean_dec(v_n_160_);
lean_dec(v___x_182_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_183_);
v___x_185_ = v___x_163_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_k_161_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_mul(lean_object* v_x_190_, lean_object* v_y_191_){
_start:
{
if (lean_obj_tag(v_x_190_) == 0)
{
lean_dec(v_y_191_);
return v_x_190_;
}
else
{
if (lean_obj_tag(v_y_191_) == 0)
{
return v_y_191_;
}
else
{
lean_object* v_n_192_; lean_object* v_k_193_; lean_object* v_n_194_; lean_object* v_k_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_204_; 
v_n_192_ = lean_ctor_get(v_x_190_, 0);
v_k_193_ = lean_ctor_get(v_x_190_, 1);
v_n_194_ = lean_ctor_get(v_y_191_, 0);
v_k_195_ = lean_ctor_get(v_y_191_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_y_191_);
if (v_isSharedCheck_204_ == 0)
{
v___x_197_ = v_y_191_;
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_k_195_);
lean_inc(v_n_194_);
lean_dec(v_y_191_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_199_ = lean_int_mul(v_n_192_, v_n_194_);
lean_dec(v_n_194_);
v___x_200_ = lean_int_add(v_k_193_, v_k_195_);
lean_dec(v_k_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_200_);
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_202_ = v___x_197_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_mul___boxed(lean_object* v_x_205_, lean_object* v_y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Dyadic_mul(v_x_205_, v_y_206_);
lean_dec(v_x_205_);
return v_res_207_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__0(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_211_ = l_Dyadic_ofInt(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__1(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_unsigned_to_nat(1u);
v___x_213_ = lean_nat_to_int(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Dyadic_pow___closed__2(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_obj_once(&l_Dyadic_pow___closed__1, &l_Dyadic_pow___closed__1_once, _init_l_Dyadic_pow___closed__1);
v___x_215_ = l_Dyadic_ofInt(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_pow(lean_object* v_x_216_, lean_object* v_i_217_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_nat_dec_eq(v_i_217_, v___x_218_);
lean_dec(v_i_217_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_obj_once(&l_Dyadic_pow___closed__0, &l_Dyadic_pow___closed__0_once, _init_l_Dyadic_pow___closed__0);
return v___x_220_;
}
else
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Dyadic_pow___closed__2, &l_Dyadic_pow___closed__2_once, _init_l_Dyadic_pow___closed__2);
return v___x_221_;
}
}
else
{
lean_object* v_n_222_; lean_object* v_k_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_233_; 
v_n_222_ = lean_ctor_get(v_x_216_, 0);
v_k_223_ = lean_ctor_get(v_x_216_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_216_);
if (v_isSharedCheck_233_ == 0)
{
v___x_225_ = v_x_216_;
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_k_223_);
lean_inc(v_n_222_);
lean_dec(v_x_216_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_227_ = l_Int_pow(v_n_222_, v_i_217_);
lean_dec(v_n_222_);
v___x_228_ = lean_nat_to_int(v_i_217_);
v___x_229_ = lean_int_mul(v_k_223_, v___x_228_);
lean_dec(v___x_228_);
lean_dec(v_k_223_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_229_);
lean_ctor_set(v___x_225_, 0, v___x_227_);
v___x_231_ = v___x_225_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_neg(lean_object* v_x_236_){
_start:
{
if (lean_obj_tag(v_x_236_) == 0)
{
return v_x_236_;
}
else
{
lean_object* v_n_237_; lean_object* v_k_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_246_; 
v_n_237_ = lean_ctor_get(v_x_236_, 0);
v_k_238_ = lean_ctor_get(v_x_236_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_236_);
if (v_isSharedCheck_246_ == 0)
{
v___x_240_ = v_x_236_;
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_k_238_);
lean_inc(v_n_237_);
lean_dec(v_x_236_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_246_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_242_ = lean_int_neg(v_n_237_);
lean_dec(v_n_237_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_242_);
v___x_244_ = v___x_240_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_k_238_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_sub(lean_object* v_x_249_, lean_object* v_y_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = l_Dyadic_neg(v_y_250_);
v___x_252_ = l_Dyadic_add(v_x_249_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft(lean_object* v_x_255_, lean_object* v_i_256_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
return v_x_255_;
}
else
{
lean_object* v_n_257_; lean_object* v_k_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_n_257_ = lean_ctor_get(v_x_255_, 0);
v_k_258_ = lean_ctor_get(v_x_255_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_266_ == 0)
{
v___x_260_ = v_x_255_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_k_258_);
lean_inc(v_n_257_);
lean_dec(v_x_255_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_int_sub(v_k_258_, v_i_256_);
lean_dec(v_k_258_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_n_257_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftLeft___boxed(lean_object* v_x_267_, lean_object* v_i_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Dyadic_shiftLeft(v_x_267_, v_i_268_);
lean_dec(v_i_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftRight(lean_object* v_x_270_, lean_object* v_i_271_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
return v_x_270_;
}
else
{
lean_object* v_n_272_; lean_object* v_k_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_281_; 
v_n_272_ = lean_ctor_get(v_x_270_, 0);
v_k_273_ = lean_ctor_get(v_x_270_, 1);
v_isSharedCheck_281_ = !lean_is_exclusive(v_x_270_);
if (v_isSharedCheck_281_ == 0)
{
v___x_275_ = v_x_270_;
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_k_273_);
lean_inc(v_n_272_);
lean_dec(v_x_270_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_int_add(v_k_273_, v_i_271_);
lean_dec(v_k_273_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v___x_277_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_n_272_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_shiftRight___boxed(lean_object* v_x_282_, lean_object* v_i_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Dyadic_shiftRight(v_x_282_, v_i_283_);
lean_dec(v_i_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instHShiftLeftNat___lam__0(lean_object* v_x_289_, lean_object* v_y_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_nat_to_int(v_y_290_);
v___x_292_ = l_Dyadic_shiftLeft(v_x_289_, v___x_291_);
lean_dec(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instHShiftRightNat___lam__0(lean_object* v_x_295_, lean_object* v_y_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_nat_to_int(v_y_296_);
v___x_298_ = l_Dyadic_shiftRight(v_x_295_, v___x_297_);
lean_dec(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Dyadic_toRat_spec__1(lean_object* v_a_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Rat_ofInt(v_a_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Dyadic_toRat_spec__0(lean_object* v_a_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_nat_to_int(v_a_303_);
v___x_305_ = l_Rat_ofInt(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Dyadic_toRat___closed__0(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = l_Nat_cast___at___00Dyadic_toRat_spec__0(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_toRat(lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_obj_once(&l_Dyadic_toRat___closed__0, &l_Dyadic_toRat___closed__0_once, _init_l_Dyadic_toRat___closed__0);
return v___x_309_;
}
else
{
lean_object* v_n_310_; lean_object* v_k_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_332_; 
v_n_310_ = lean_ctor_get(v_x_308_, 0);
v_k_311_ = lean_ctor_get(v_x_308_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_332_ == 0)
{
v___x_313_ = v_x_308_;
v_isShared_314_ = v_isSharedCheck_332_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_k_311_);
lean_inc(v_n_310_);
lean_dec(v_x_308_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_332_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_intZero_315_; uint8_t v_isNeg_316_; 
v_intZero_315_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_316_ = lean_int_dec_lt(v_k_311_, v_intZero_315_);
if (v_isNeg_316_ == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v_a_317_ = lean_nat_abs(v_k_311_);
lean_dec(v_k_311_);
v___x_318_ = lean_unsigned_to_nat(2u);
v___x_319_ = lean_nat_pow(v___x_318_, v_a_317_);
lean_dec(v_a_317_);
if (v_isShared_314_ == 0)
{
lean_ctor_set_tag(v___x_313_, 0);
lean_ctor_set(v___x_313_, 1, v___x_319_);
v___x_321_ = v___x_313_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_n_310_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
else
{
lean_object* v_abs_323_; lean_object* v_one_324_; lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
lean_del_object(v___x_313_);
v_abs_323_ = lean_nat_abs(v_k_311_);
lean_dec(v_k_311_);
v_one_324_ = lean_unsigned_to_nat(1u);
v_a_325_ = lean_nat_sub(v_abs_323_, v_one_324_);
lean_dec(v_abs_323_);
v___x_326_ = lean_unsigned_to_nat(2u);
v___x_327_ = lean_nat_add(v_a_325_, v_one_324_);
lean_dec(v_a_325_);
v___x_328_ = lean_nat_pow(v___x_326_, v___x_327_);
lean_dec(v___x_327_);
v___x_329_ = lean_nat_to_int(v___x_328_);
v___x_330_ = lean_int_mul(v_n_310_, v___x_329_);
lean_dec(v___x_329_);
lean_dec(v_n_310_);
v___x_331_ = l_Rat_ofInt(v___x_330_);
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter___redArg(lean_object* v_x_333_, lean_object* v_h__1_334_, lean_object* v_h__2_335_, lean_object* v_h__3_336_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_h__3_336_);
lean_dec(v_h__2_335_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_apply_1(v_h__1_334_, v___x_337_);
return v___x_338_;
}
else
{
lean_object* v_n_339_; lean_object* v_k_340_; lean_object* v_intZero_341_; uint8_t v_isNeg_342_; 
lean_dec(v_h__1_334_);
v_n_339_ = lean_ctor_get(v_x_333_, 0);
lean_inc(v_n_339_);
v_k_340_ = lean_ctor_get(v_x_333_, 1);
lean_inc(v_k_340_);
lean_dec_ref(v_x_333_);
v_intZero_341_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_342_ = lean_int_dec_lt(v_k_340_, v_intZero_341_);
if (v_isNeg_342_ == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; 
lean_dec(v_h__3_336_);
v_a_343_ = lean_nat_abs(v_k_340_);
lean_dec(v_k_340_);
v___x_344_ = lean_apply_3(v_h__2_335_, v_n_339_, v_a_343_, lean_box(0));
return v___x_344_;
}
else
{
lean_object* v_abs_345_; lean_object* v_one_346_; lean_object* v_a_347_; lean_object* v___x_348_; 
lean_dec(v_h__2_335_);
v_abs_345_ = lean_nat_abs(v_k_340_);
lean_dec(v_k_340_);
v_one_346_ = lean_unsigned_to_nat(1u);
v_a_347_ = lean_nat_sub(v_abs_345_, v_one_346_);
lean_dec(v_abs_345_);
v___x_348_ = lean_apply_3(v_h__3_336_, v_n_339_, v_a_347_, lean_box(0));
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter(lean_object* v_motive_349_, lean_object* v_x_350_, lean_object* v_h__1_351_, lean_object* v_h__2_352_, lean_object* v_h__3_353_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_h__3_353_);
lean_dec(v_h__2_352_);
v___x_354_ = lean_box(0);
v___x_355_ = lean_apply_1(v_h__1_351_, v___x_354_);
return v___x_355_;
}
else
{
lean_object* v_n_356_; lean_object* v_k_357_; lean_object* v_intZero_358_; uint8_t v_isNeg_359_; 
lean_dec(v_h__1_351_);
v_n_356_ = lean_ctor_get(v_x_350_, 0);
lean_inc(v_n_356_);
v_k_357_ = lean_ctor_get(v_x_350_, 1);
lean_inc(v_k_357_);
lean_dec_ref(v_x_350_);
v_intZero_358_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_359_ = lean_int_dec_lt(v_k_357_, v_intZero_358_);
if (v_isNeg_359_ == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; 
lean_dec(v_h__3_353_);
v_a_360_ = lean_nat_abs(v_k_357_);
lean_dec(v_k_357_);
v___x_361_ = lean_apply_3(v_h__2_352_, v_n_356_, v_a_360_, lean_box(0));
return v___x_361_;
}
else
{
lean_object* v_abs_362_; lean_object* v_one_363_; lean_object* v_a_364_; lean_object* v___x_365_; 
lean_dec(v_h__2_352_);
v_abs_362_ = lean_nat_abs(v_k_357_);
lean_dec(v_k_357_);
v_one_363_ = lean_unsigned_to_nat(1u);
v_a_364_ = lean_nat_sub(v_abs_362_, v_one_363_);
lean_dec(v_abs_362_);
v___x_365_ = lean_apply_3(v_h__3_353_, v_n_356_, v_a_364_, lean_box(0));
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter___redArg(lean_object* v_x_366_, lean_object* v_y_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_, lean_object* v_h__3_370_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
lean_object* v___x_371_; 
lean_dec(v_h__3_370_);
lean_dec(v_h__2_369_);
v___x_371_ = lean_apply_1(v_h__1_368_, v_y_367_);
return v___x_371_;
}
else
{
lean_dec(v_h__1_368_);
if (lean_obj_tag(v_y_367_) == 0)
{
lean_object* v_n_372_; lean_object* v_k_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_h__3_370_);
v_n_372_ = lean_ctor_get(v_x_366_, 0);
v_k_373_ = lean_ctor_get(v_x_366_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_x_366_);
if (v_isSharedCheck_381_ == 0)
{
v___x_375_ = v_x_366_;
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_k_373_);
lean_inc(v_n_372_);
lean_dec(v_x_366_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_n_372_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_k_373_);
v___x_378_ = v_reuseFailAlloc_380_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; 
v___x_379_ = lean_apply_2(v_h__2_369_, v___x_378_, lean_box(0));
return v___x_379_;
}
}
}
else
{
lean_object* v_n_382_; lean_object* v_k_383_; lean_object* v_n_384_; lean_object* v_k_385_; lean_object* v___x_386_; 
lean_dec(v_h__2_369_);
v_n_382_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_n_382_);
v_k_383_ = lean_ctor_get(v_x_366_, 1);
lean_inc(v_k_383_);
lean_dec_ref(v_x_366_);
v_n_384_ = lean_ctor_get(v_y_367_, 0);
lean_inc(v_n_384_);
v_k_385_ = lean_ctor_get(v_y_367_, 1);
lean_inc(v_k_385_);
lean_dec_ref(v_y_367_);
v___x_386_ = lean_apply_6(v_h__3_370_, v_n_382_, v_k_383_, lean_box(0), v_n_384_, v_k_385_, lean_box(0));
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter(lean_object* v_motive_387_, lean_object* v_x_388_, lean_object* v_y_389_, lean_object* v_h__1_390_, lean_object* v_h__2_391_, lean_object* v_h__3_392_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
lean_object* v___x_393_; 
lean_dec(v_h__3_392_);
lean_dec(v_h__2_391_);
v___x_393_ = lean_apply_1(v_h__1_390_, v_y_389_);
return v___x_393_;
}
else
{
lean_dec(v_h__1_390_);
if (lean_obj_tag(v_y_389_) == 0)
{
lean_object* v_n_394_; lean_object* v_k_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
lean_dec(v_h__3_392_);
v_n_394_ = lean_ctor_get(v_x_388_, 0);
v_k_395_ = lean_ctor_get(v_x_388_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_388_);
if (v_isSharedCheck_403_ == 0)
{
v___x_397_ = v_x_388_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_k_395_);
lean_inc(v_n_394_);
lean_dec(v_x_388_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_n_394_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_k_395_);
v___x_400_ = v_reuseFailAlloc_402_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; 
v___x_401_ = lean_apply_2(v_h__2_391_, v___x_400_, lean_box(0));
return v___x_401_;
}
}
}
else
{
lean_object* v_n_404_; lean_object* v_k_405_; lean_object* v_n_406_; lean_object* v_k_407_; lean_object* v___x_408_; 
lean_dec(v_h__2_391_);
v_n_404_ = lean_ctor_get(v_x_388_, 0);
lean_inc(v_n_404_);
v_k_405_ = lean_ctor_get(v_x_388_, 1);
lean_inc(v_k_405_);
lean_dec_ref(v_x_388_);
v_n_406_ = lean_ctor_get(v_y_389_, 0);
lean_inc(v_n_406_);
v_k_407_ = lean_ctor_get(v_y_389_, 1);
lean_inc(v_k_407_);
lean_dec_ref(v_y_389_);
v___x_408_ = lean_apply_6(v_h__3_392_, v_n_404_, v_k_405_, lean_box(0), v_n_406_, v_k_407_, lean_box(0));
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(lean_object* v_x_409_, lean_object* v_h__1_410_, lean_object* v_h__2_411_, lean_object* v_h__3_412_){
_start:
{
lean_object* v_natZero_413_; lean_object* v_intZero_414_; uint8_t v_isNeg_415_; 
v_natZero_413_ = lean_unsigned_to_nat(0u);
v_intZero_414_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_415_ = lean_int_dec_lt(v_x_409_, v_intZero_414_);
if (v_isNeg_415_ == 0)
{
lean_object* v_a_416_; uint8_t v_isZero_417_; 
lean_dec(v_h__3_412_);
v_a_416_ = lean_nat_abs(v_x_409_);
v_isZero_417_ = lean_nat_dec_eq(v_a_416_, v_natZero_413_);
if (v_isZero_417_ == 1)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_a_416_);
lean_dec(v_h__2_411_);
v___x_418_ = lean_box(0);
v___x_419_ = lean_apply_1(v_h__1_410_, v___x_418_);
return v___x_419_;
}
else
{
lean_object* v_one_420_; lean_object* v_n_421_; lean_object* v___x_422_; 
lean_dec(v_h__1_410_);
v_one_420_ = lean_unsigned_to_nat(1u);
v_n_421_ = lean_nat_sub(v_a_416_, v_one_420_);
lean_dec(v_a_416_);
v___x_422_ = lean_apply_1(v_h__2_411_, v_n_421_);
return v___x_422_;
}
}
else
{
lean_object* v_abs_423_; lean_object* v_one_424_; lean_object* v_a_425_; lean_object* v___x_426_; 
lean_dec(v_h__2_411_);
lean_dec(v_h__1_410_);
v_abs_423_ = lean_nat_abs(v_x_409_);
v_one_424_ = lean_unsigned_to_nat(1u);
v_a_425_ = lean_nat_sub(v_abs_423_, v_one_424_);
lean_dec(v_abs_423_);
v___x_426_ = lean_apply_1(v_h__3_412_, v_a_425_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg___boxed(lean_object* v_x_427_, lean_object* v_h__1_428_, lean_object* v_h__2_429_, lean_object* v_h__3_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(v_x_427_, v_h__1_428_, v_h__2_429_, v_h__3_430_);
lean_dec(v_x_427_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(lean_object* v_motive_432_, lean_object* v_x_433_, lean_object* v_h__1_434_, lean_object* v_h__2_435_, lean_object* v_h__3_436_){
_start:
{
lean_object* v_natZero_437_; lean_object* v_intZero_438_; uint8_t v_isNeg_439_; 
v_natZero_437_ = lean_unsigned_to_nat(0u);
v_intZero_438_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_439_ = lean_int_dec_lt(v_x_433_, v_intZero_438_);
if (v_isNeg_439_ == 0)
{
lean_object* v_a_440_; uint8_t v_isZero_441_; 
lean_dec(v_h__3_436_);
v_a_440_ = lean_nat_abs(v_x_433_);
v_isZero_441_ = lean_nat_dec_eq(v_a_440_, v_natZero_437_);
if (v_isZero_441_ == 1)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v_a_440_);
lean_dec(v_h__2_435_);
v___x_442_ = lean_box(0);
v___x_443_ = lean_apply_1(v_h__1_434_, v___x_442_);
return v___x_443_;
}
else
{
lean_object* v_one_444_; lean_object* v_n_445_; lean_object* v___x_446_; 
lean_dec(v_h__1_434_);
v_one_444_ = lean_unsigned_to_nat(1u);
v_n_445_ = lean_nat_sub(v_a_440_, v_one_444_);
lean_dec(v_a_440_);
v___x_446_ = lean_apply_1(v_h__2_435_, v_n_445_);
return v___x_446_;
}
}
else
{
lean_object* v_abs_447_; lean_object* v_one_448_; lean_object* v_a_449_; lean_object* v___x_450_; 
lean_dec(v_h__2_435_);
lean_dec(v_h__1_434_);
v_abs_447_ = lean_nat_abs(v_x_433_);
v_one_448_ = lean_unsigned_to_nat(1u);
v_a_449_ = lean_nat_sub(v_abs_447_, v_one_448_);
lean_dec(v_abs_447_);
v___x_450_ = lean_apply_1(v_h__3_436_, v_a_449_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___boxed(lean_object* v_motive_451_, lean_object* v_x_452_, lean_object* v_h__1_453_, lean_object* v_h__2_454_, lean_object* v_h__3_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(v_motive_451_, v_x_452_, v_h__1_453_, v_h__2_454_, v_h__3_455_);
lean_dec(v_x_452_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter___redArg(lean_object* v_x_457_, lean_object* v_h__1_458_, lean_object* v_h__2_459_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec(v_h__2_459_);
v___x_460_ = lean_box(0);
v___x_461_ = lean_apply_1(v_h__1_458_, v___x_460_);
return v___x_461_;
}
else
{
lean_object* v_n_462_; lean_object* v_k_463_; lean_object* v___x_464_; 
lean_dec(v_h__1_458_);
v_n_462_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_n_462_);
v_k_463_ = lean_ctor_get(v_x_457_, 1);
lean_inc(v_k_463_);
lean_dec_ref(v_x_457_);
v___x_464_ = lean_apply_3(v_h__2_459_, v_n_462_, v_k_463_, lean_box(0));
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter(lean_object* v_motive_465_, lean_object* v_x_466_, lean_object* v_h__1_467_, lean_object* v_h__2_468_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_h__2_468_);
v___x_469_ = lean_box(0);
v___x_470_ = lean_apply_1(v_h__1_467_, v___x_469_);
return v___x_470_;
}
else
{
lean_object* v_n_471_; lean_object* v_k_472_; lean_object* v___x_473_; 
lean_dec(v_h__1_467_);
v_n_471_ = lean_ctor_get(v_x_466_, 0);
lean_inc(v_n_471_);
v_k_472_ = lean_ctor_get(v_x_466_, 1);
lean_inc(v_k_472_);
lean_dec_ref(v_x_466_);
v___x_473_ = lean_apply_3(v_h__2_468_, v_n_471_, v_k_472_, lean_box(0));
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_precision(lean_object* v_x_474_){
_start:
{
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_box(0);
return v___x_475_;
}
else
{
lean_object* v_k_476_; lean_object* v___x_477_; 
v_k_476_ = lean_ctor_get(v_x_474_, 1);
lean_inc(v_k_476_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_k_476_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_precision___boxed(lean_object* v_x_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Dyadic_precision(v_x_478_);
lean_dec(v_x_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Rat_toDyadic(lean_object* v_x_480_, lean_object* v_prec_481_){
_start:
{
lean_object* v_intZero_482_; uint8_t v_isNeg_483_; 
v_intZero_482_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_483_ = lean_int_dec_lt(v_prec_481_, v_intZero_482_);
if (v_isNeg_483_ == 0)
{
lean_object* v_num_484_; lean_object* v_den_485_; lean_object* v_a_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_num_484_ = lean_ctor_get(v_x_480_, 0);
lean_inc(v_num_484_);
v_den_485_ = lean_ctor_get(v_x_480_, 1);
lean_inc(v_den_485_);
lean_dec_ref(v_x_480_);
v_a_486_ = lean_nat_abs(v_prec_481_);
v___x_487_ = l_Int_shiftLeft(v_num_484_, v_a_486_);
lean_dec(v_a_486_);
lean_dec(v_num_484_);
v___x_488_ = lean_nat_to_int(v_den_485_);
v___x_489_ = lean_int_ediv(v___x_487_, v___x_488_);
lean_dec(v___x_488_);
lean_dec(v___x_487_);
v___x_490_ = l_Dyadic_ofIntWithPrec(v___x_489_, v_prec_481_);
return v___x_490_;
}
else
{
lean_object* v_num_491_; lean_object* v_den_492_; lean_object* v_abs_493_; lean_object* v_one_494_; lean_object* v_a_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_num_491_ = lean_ctor_get(v_x_480_, 0);
lean_inc(v_num_491_);
v_den_492_ = lean_ctor_get(v_x_480_, 1);
lean_inc(v_den_492_);
lean_dec_ref(v_x_480_);
v_abs_493_ = lean_nat_abs(v_prec_481_);
v_one_494_ = lean_unsigned_to_nat(1u);
v_a_495_ = lean_nat_sub(v_abs_493_, v_one_494_);
lean_dec(v_abs_493_);
v___x_496_ = lean_nat_add(v_a_495_, v_one_494_);
lean_dec(v_a_495_);
v___x_497_ = lean_nat_shiftl(v_den_492_, v___x_496_);
lean_dec(v___x_496_);
lean_dec(v_den_492_);
v___x_498_ = lean_nat_to_int(v___x_497_);
v___x_499_ = lean_int_ediv(v_num_491_, v___x_498_);
lean_dec(v___x_498_);
lean_dec(v_num_491_);
v___x_500_ = l_Dyadic_ofIntWithPrec(v___x_499_, v_prec_481_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_toDyadic___boxed(lean_object* v_x_501_, lean_object* v_prec_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Rat_toDyadic(v_x_501_, v_prec_502_);
lean_dec(v_prec_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(lean_object* v_prec_504_, lean_object* v_h__1_505_, lean_object* v_h__2_506_){
_start:
{
lean_object* v_intZero_507_; uint8_t v_isNeg_508_; 
v_intZero_507_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_508_ = lean_int_dec_lt(v_prec_504_, v_intZero_507_);
if (v_isNeg_508_ == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; 
lean_dec(v_h__2_506_);
v_a_509_ = lean_nat_abs(v_prec_504_);
v___x_510_ = lean_apply_1(v_h__1_505_, v_a_509_);
return v___x_510_;
}
else
{
lean_object* v_abs_511_; lean_object* v_one_512_; lean_object* v_a_513_; lean_object* v___x_514_; 
lean_dec(v_h__1_505_);
v_abs_511_ = lean_nat_abs(v_prec_504_);
v_one_512_ = lean_unsigned_to_nat(1u);
v_a_513_ = lean_nat_sub(v_abs_511_, v_one_512_);
lean_dec(v_abs_511_);
v___x_514_ = lean_apply_1(v_h__2_506_, v_a_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg___boxed(lean_object* v_prec_515_, lean_object* v_h__1_516_, lean_object* v_h__2_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(v_prec_515_, v_h__1_516_, v_h__2_517_);
lean_dec(v_prec_515_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(lean_object* v_motive_519_, lean_object* v_prec_520_, lean_object* v_h__1_521_, lean_object* v_h__2_522_){
_start:
{
lean_object* v_intZero_523_; uint8_t v_isNeg_524_; 
v_intZero_523_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_524_ = lean_int_dec_lt(v_prec_520_, v_intZero_523_);
if (v_isNeg_524_ == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; 
lean_dec(v_h__2_522_);
v_a_525_ = lean_nat_abs(v_prec_520_);
v___x_526_ = lean_apply_1(v_h__1_521_, v_a_525_);
return v___x_526_;
}
else
{
lean_object* v_abs_527_; lean_object* v_one_528_; lean_object* v_a_529_; lean_object* v___x_530_; 
lean_dec(v_h__1_521_);
v_abs_527_ = lean_nat_abs(v_prec_520_);
v_one_528_ = lean_unsigned_to_nat(1u);
v_a_529_ = lean_nat_sub(v_abs_527_, v_one_528_);
lean_dec(v_abs_527_);
v___x_530_ = lean_apply_1(v_h__2_522_, v_a_529_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___boxed(lean_object* v_motive_531_, lean_object* v_prec_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(v_motive_531_, v_prec_532_, v_h__1_533_, v_h__2_534_);
lean_dec(v_prec_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundDown(lean_object* v_x_536_, lean_object* v_prec_537_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
return v_x_536_;
}
else
{
lean_object* v_n_538_; lean_object* v_k_539_; lean_object* v___x_540_; lean_object* v_intZero_541_; uint8_t v_isNeg_542_; 
v_n_538_ = lean_ctor_get(v_x_536_, 0);
v_k_539_ = lean_ctor_get(v_x_536_, 1);
v___x_540_ = lean_int_sub(v_k_539_, v_prec_537_);
v_intZero_541_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_542_ = lean_int_dec_lt(v___x_540_, v_intZero_541_);
if (v_isNeg_542_ == 0)
{
lean_object* v_a_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_a_543_ = lean_nat_abs(v___x_540_);
lean_dec(v___x_540_);
v___x_544_ = l_Int_shiftRight(v_n_538_, v_a_543_);
lean_dec(v_a_543_);
v___x_545_ = l_Dyadic_ofIntWithPrec(v___x_544_, v_prec_537_);
return v___x_545_;
}
else
{
lean_dec(v___x_540_);
lean_inc_ref(v_x_536_);
return v_x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundDown___boxed(lean_object* v_x_546_, lean_object* v_prec_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Dyadic_roundDown(v_x_546_, v_prec_547_);
lean_dec(v_prec_547_);
lean_dec(v_x_546_);
return v_res_548_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_blt(lean_object* v_x_549_, lean_object* v_y_550_){
_start:
{
if (lean_obj_tag(v_x_549_) == 0)
{
if (lean_obj_tag(v_y_550_) == 0)
{
uint8_t v___x_551_; 
v___x_551_ = 0;
return v___x_551_;
}
else
{
lean_object* v_n_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_n_552_ = lean_ctor_get(v_y_550_, 0);
v___x_553_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_554_ = lean_int_dec_lt(v___x_553_, v_n_552_);
return v___x_554_;
}
}
else
{
if (lean_obj_tag(v_y_550_) == 0)
{
lean_object* v_n_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_n_555_ = lean_ctor_get(v_x_549_, 0);
v___x_556_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_557_ = lean_int_dec_lt(v_n_555_, v___x_556_);
return v___x_557_;
}
else
{
lean_object* v_n_558_; lean_object* v_k_559_; lean_object* v_n_560_; lean_object* v_k_561_; lean_object* v___x_562_; lean_object* v_intZero_563_; uint8_t v_isNeg_564_; 
v_n_558_ = lean_ctor_get(v_x_549_, 0);
v_k_559_ = lean_ctor_get(v_x_549_, 1);
v_n_560_ = lean_ctor_get(v_y_550_, 0);
v_k_561_ = lean_ctor_get(v_y_550_, 1);
v___x_562_ = lean_int_sub(v_k_561_, v_k_559_);
v_intZero_563_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_564_ = lean_int_dec_lt(v___x_562_, v_intZero_563_);
if (v_isNeg_564_ == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_a_565_ = lean_nat_abs(v___x_562_);
lean_dec(v___x_562_);
v___x_566_ = l_Int_shiftLeft(v_n_558_, v_a_565_);
lean_dec(v_a_565_);
v___x_567_ = lean_int_dec_lt(v___x_566_, v_n_560_);
lean_dec(v___x_566_);
return v___x_567_;
}
else
{
lean_object* v_abs_568_; lean_object* v_one_569_; lean_object* v_a_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_abs_568_ = lean_nat_abs(v___x_562_);
lean_dec(v___x_562_);
v_one_569_ = lean_unsigned_to_nat(1u);
v_a_570_ = lean_nat_sub(v_abs_568_, v_one_569_);
lean_dec(v_abs_568_);
v___x_571_ = lean_nat_add(v_a_570_, v_one_569_);
lean_dec(v_a_570_);
v___x_572_ = l_Int_shiftLeft(v_n_560_, v___x_571_);
lean_dec(v___x_571_);
v___x_573_ = lean_int_dec_lt(v_n_558_, v___x_572_);
lean_dec(v___x_572_);
return v___x_573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_blt___boxed(lean_object* v_x_574_, lean_object* v_y_575_){
_start:
{
uint8_t v_res_576_; lean_object* v_r_577_; 
v_res_576_ = l_Dyadic_blt(v_x_574_, v_y_575_);
lean_dec(v_y_575_);
lean_dec(v_x_574_);
v_r_577_ = lean_box(v_res_576_);
return v_r_577_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_ble(lean_object* v_x_578_, lean_object* v_y_579_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
if (lean_obj_tag(v_y_579_) == 0)
{
uint8_t v___x_580_; 
v___x_580_ = 1;
return v___x_580_;
}
else
{
lean_object* v_n_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_n_581_ = lean_ctor_get(v_y_579_, 0);
v___x_582_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_583_ = lean_int_dec_le(v___x_582_, v_n_581_);
return v___x_583_;
}
}
else
{
if (lean_obj_tag(v_y_579_) == 0)
{
lean_object* v_n_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_n_584_ = lean_ctor_get(v_x_578_, 0);
v___x_585_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v___x_586_ = lean_int_dec_le(v_n_584_, v___x_585_);
return v___x_586_;
}
else
{
lean_object* v_n_587_; lean_object* v_k_588_; lean_object* v_n_589_; lean_object* v_k_590_; lean_object* v___x_591_; lean_object* v_intZero_592_; uint8_t v_isNeg_593_; 
v_n_587_ = lean_ctor_get(v_x_578_, 0);
v_k_588_ = lean_ctor_get(v_x_578_, 1);
v_n_589_ = lean_ctor_get(v_y_579_, 0);
v_k_590_ = lean_ctor_get(v_y_579_, 1);
v___x_591_ = lean_int_sub(v_k_590_, v_k_588_);
v_intZero_592_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_593_ = lean_int_dec_lt(v___x_591_, v_intZero_592_);
if (v_isNeg_593_ == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_a_594_ = lean_nat_abs(v___x_591_);
lean_dec(v___x_591_);
v___x_595_ = l_Int_shiftLeft(v_n_587_, v_a_594_);
lean_dec(v_a_594_);
v___x_596_ = lean_int_dec_le(v___x_595_, v_n_589_);
lean_dec(v___x_595_);
return v___x_596_;
}
else
{
lean_object* v_abs_597_; lean_object* v_one_598_; lean_object* v_a_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_abs_597_ = lean_nat_abs(v___x_591_);
lean_dec(v___x_591_);
v_one_598_ = lean_unsigned_to_nat(1u);
v_a_599_ = lean_nat_sub(v_abs_597_, v_one_598_);
lean_dec(v_abs_597_);
v___x_600_ = lean_nat_add(v_a_599_, v_one_598_);
lean_dec(v_a_599_);
v___x_601_ = l_Int_shiftLeft(v_n_589_, v___x_600_);
lean_dec(v___x_600_);
v___x_602_ = lean_int_dec_le(v_n_587_, v___x_601_);
lean_dec(v___x_601_);
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_ble___boxed(lean_object* v_x_603_, lean_object* v_y_604_){
_start:
{
uint8_t v_res_605_; lean_object* v_r_606_; 
v_res_605_ = l_Dyadic_ble(v_x_603_, v_y_604_);
lean_dec(v_y_604_);
lean_dec(v_x_603_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter___redArg(lean_object* v_x_607_, lean_object* v_x_608_, lean_object* v_h__1_609_, lean_object* v_h__2_610_, lean_object* v_h__3_611_, lean_object* v_h__4_612_){
_start:
{
if (lean_obj_tag(v_x_607_) == 0)
{
lean_dec(v_h__4_612_);
lean_dec(v_h__3_611_);
if (lean_obj_tag(v_x_608_) == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_h__2_610_);
v___x_613_ = lean_box(0);
v___x_614_ = lean_apply_1(v_h__1_609_, v___x_613_);
return v___x_614_;
}
else
{
lean_object* v_n_615_; lean_object* v_k_616_; lean_object* v___x_617_; 
lean_dec(v_h__1_609_);
v_n_615_ = lean_ctor_get(v_x_608_, 0);
lean_inc(v_n_615_);
v_k_616_ = lean_ctor_get(v_x_608_, 1);
lean_inc(v_k_616_);
lean_dec_ref(v_x_608_);
v___x_617_ = lean_apply_3(v_h__2_610_, v_n_615_, v_k_616_, lean_box(0));
return v___x_617_;
}
}
else
{
lean_dec(v_h__2_610_);
lean_dec(v_h__1_609_);
if (lean_obj_tag(v_x_608_) == 0)
{
lean_object* v_n_618_; lean_object* v_k_619_; lean_object* v___x_620_; 
lean_dec(v_h__4_612_);
v_n_618_ = lean_ctor_get(v_x_607_, 0);
lean_inc(v_n_618_);
v_k_619_ = lean_ctor_get(v_x_607_, 1);
lean_inc(v_k_619_);
lean_dec_ref(v_x_607_);
v___x_620_ = lean_apply_3(v_h__3_611_, v_n_618_, v_k_619_, lean_box(0));
return v___x_620_;
}
else
{
lean_object* v_n_621_; lean_object* v_k_622_; lean_object* v_n_623_; lean_object* v_k_624_; lean_object* v___x_625_; 
lean_dec(v_h__3_611_);
v_n_621_ = lean_ctor_get(v_x_607_, 0);
lean_inc(v_n_621_);
v_k_622_ = lean_ctor_get(v_x_607_, 1);
lean_inc(v_k_622_);
lean_dec_ref(v_x_607_);
v_n_623_ = lean_ctor_get(v_x_608_, 0);
lean_inc(v_n_623_);
v_k_624_ = lean_ctor_get(v_x_608_, 1);
lean_inc(v_k_624_);
lean_dec_ref(v_x_608_);
v___x_625_ = lean_apply_6(v_h__4_612_, v_n_621_, v_k_622_, lean_box(0), v_n_623_, v_k_624_, lean_box(0));
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter(lean_object* v_motive_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_h__1_629_, lean_object* v_h__2_630_, lean_object* v_h__3_631_, lean_object* v_h__4_632_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
lean_dec(v_h__4_632_);
lean_dec(v_h__3_631_);
if (lean_obj_tag(v_x_628_) == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v_h__2_630_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_apply_1(v_h__1_629_, v___x_633_);
return v___x_634_;
}
else
{
lean_object* v_n_635_; lean_object* v_k_636_; lean_object* v___x_637_; 
lean_dec(v_h__1_629_);
v_n_635_ = lean_ctor_get(v_x_628_, 0);
lean_inc(v_n_635_);
v_k_636_ = lean_ctor_get(v_x_628_, 1);
lean_inc(v_k_636_);
lean_dec_ref(v_x_628_);
v___x_637_ = lean_apply_3(v_h__2_630_, v_n_635_, v_k_636_, lean_box(0));
return v___x_637_;
}
}
else
{
lean_dec(v_h__2_630_);
lean_dec(v_h__1_629_);
if (lean_obj_tag(v_x_628_) == 0)
{
lean_object* v_n_638_; lean_object* v_k_639_; lean_object* v___x_640_; 
lean_dec(v_h__4_632_);
v_n_638_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_n_638_);
v_k_639_ = lean_ctor_get(v_x_627_, 1);
lean_inc(v_k_639_);
lean_dec_ref(v_x_627_);
v___x_640_ = lean_apply_3(v_h__3_631_, v_n_638_, v_k_639_, lean_box(0));
return v___x_640_;
}
else
{
lean_object* v_n_641_; lean_object* v_k_642_; lean_object* v_n_643_; lean_object* v_k_644_; lean_object* v___x_645_; 
lean_dec(v_h__3_631_);
v_n_641_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_n_641_);
v_k_642_ = lean_ctor_get(v_x_627_, 1);
lean_inc(v_k_642_);
lean_dec_ref(v_x_627_);
v_n_643_ = lean_ctor_get(v_x_628_, 0);
lean_inc(v_n_643_);
v_k_644_ = lean_ctor_get(v_x_628_, 1);
lean_inc(v_k_644_);
lean_dec_ref(v_x_628_);
v___x_645_ = lean_apply_6(v_h__4_632_, v_n_641_, v_k_642_, lean_box(0), v_n_643_, v_k_644_, lean_box(0));
return v___x_645_;
}
}
}
}
static lean_object* _init_l_Dyadic_instLT(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_box(0);
return v___x_646_;
}
}
static lean_object* _init_l_Dyadic_instLE(void){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = lean_box(0);
return v___x_647_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLT(lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
uint8_t v___x_650_; 
v___x_650_ = l_Dyadic_blt(v_x_648_, v_x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLT___boxed(lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
uint8_t v_res_653_; lean_object* v_r_654_; 
v_res_653_ = l_Dyadic_instDecidableLT(v_x_651_, v_x_652_);
lean_dec(v_x_652_);
lean_dec(v_x_651_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
LEAN_EXPORT uint8_t l_Dyadic_instDecidableLE(lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = l_Dyadic_ble(v_x_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_instDecidableLE___boxed(lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
uint8_t v_res_660_; lean_object* v_r_661_; 
v_res_660_ = l_Dyadic_instDecidableLE(v_x_658_, v_x_659_);
lean_dec(v_x_659_);
lean_dec(v_x_658_);
v_r_661_ = lean_box(v_res_660_);
return v_r_661_;
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundUp(lean_object* v_x_662_, lean_object* v_prec_663_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
return v_x_662_;
}
else
{
lean_object* v_n_664_; lean_object* v_k_665_; lean_object* v___x_666_; lean_object* v_intZero_667_; uint8_t v_isNeg_668_; 
v_n_664_ = lean_ctor_get(v_x_662_, 0);
v_k_665_ = lean_ctor_get(v_x_662_, 1);
v___x_666_ = lean_int_sub(v_k_665_, v_prec_663_);
v_intZero_667_ = lean_obj_once(&l_Int_trailingZeros_aux___redArg___closed__1, &l_Int_trailingZeros_aux___redArg___closed__1_once, _init_l_Int_trailingZeros_aux___redArg___closed__1);
v_isNeg_668_ = lean_int_dec_lt(v___x_666_, v_intZero_667_);
if (v_isNeg_668_ == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_a_669_ = lean_nat_abs(v___x_666_);
lean_dec(v___x_666_);
v___x_670_ = lean_int_neg(v_n_664_);
v___x_671_ = l_Int_shiftRight(v___x_670_, v_a_669_);
lean_dec(v_a_669_);
lean_dec(v___x_670_);
v___x_672_ = lean_int_neg(v___x_671_);
lean_dec(v___x_671_);
v___x_673_ = l_Dyadic_ofIntWithPrec(v___x_672_, v_prec_663_);
return v___x_673_;
}
else
{
lean_dec(v___x_666_);
lean_inc_ref(v_x_662_);
return v_x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Dyadic_roundUp___boxed(lean_object* v_x_674_, lean_object* v_prec_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Dyadic_roundUp(v_x_674_, v_prec_675_);
lean_dec(v_prec_675_);
lean_dec(v_x_674_);
return v_res_676_;
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
