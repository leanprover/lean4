// Lean compiler output
// Module: Init.Grind.Ring.Kronecker
// Imports: public import Init.Grind.Ring.Packed public import Init.Grind.Ring.FieldSolver import Init.Omega import Init.ByCases import Init.Data.Int.Order import Init.Data.Int.LemmasAux import Init.Data.Nat.Lemmas import Init.Data.Nat.Bitwise.Lemmas import Init.Data.List.Impl
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_kron(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_kron___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_PPoly_coeff___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_PPoly_coeff___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_coeff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_coeff___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_size___boxed(lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_PPoly_removeCode___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_PPoly_removeCode___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_removeCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_removeCode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_shiftDown(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_kron_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_kron_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append_addConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append_addConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_neg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_addConst_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_addConst_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1List(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_denoteG___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_denoteG(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_scale(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_scale___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Expr_evalConst_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_evalConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_nil_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_nil_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_cons_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_cons_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_nil_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_nil_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_cons_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_cons_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_evalConst_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_evalConst_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_toPPQ_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_toPPQ_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTL(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_PPoly_powTL___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_PPoly_powTL___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_PPoly_powTL___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_PPoly_powTL___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_kron(lean_object* v_X_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v_k_3_; 
v_k_3_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_k_3_);
return v_k_3_;
}
else
{
lean_object* v_k_4_; lean_object* v_v_5_; lean_object* v_p_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_k_4_ = lean_ctor_get(v_x_2_, 0);
v_v_5_ = lean_ctor_get(v_x_2_, 2);
v_p_6_ = lean_ctor_get(v_x_2_, 3);
v___x_7_ = l_Int_pow(v_X_1_, v_v_5_);
v___x_8_ = lean_int_mul(v_k_4_, v___x_7_);
lean_dec(v___x_7_);
v___x_9_ = l_Lean_Grind_CommRing_PPoly_kron(v_X_1_, v_p_6_);
v___x_10_ = lean_int_add(v___x_8_, v___x_9_);
lean_dec(v___x_9_);
lean_dec(v___x_8_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_kron___boxed(lean_object* v_X_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Grind_CommRing_PPoly_kron(v_X_11_, v_x_12_);
lean_dec_ref(v_x_12_);
lean_dec(v_X_11_);
return v_res_13_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_PPoly_coeff___closed__0(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_nat_to_int(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_coeff(lean_object* v_c_16_, lean_object* v_x_17_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v_k_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v_k_18_ = lean_ctor_get(v_x_17_, 0);
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_nat_dec_eq(v_c_16_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_coeff___closed__0, &l_Lean_Grind_CommRing_PPoly_coeff___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_coeff___closed__0);
return v___x_21_;
}
else
{
lean_inc(v_k_18_);
return v_k_18_;
}
}
else
{
lean_object* v_k_22_; lean_object* v_v_23_; lean_object* v_p_24_; lean_object* v___y_26_; uint8_t v___x_29_; 
v_k_22_ = lean_ctor_get(v_x_17_, 0);
v_v_23_ = lean_ctor_get(v_x_17_, 2);
v_p_24_ = lean_ctor_get(v_x_17_, 3);
v___x_29_ = lean_nat_dec_eq(v_v_23_, v_c_16_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_coeff___closed__0, &l_Lean_Grind_CommRing_PPoly_coeff___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_coeff___closed__0);
v___y_26_ = v___x_30_;
goto v___jp_25_;
}
else
{
v___y_26_ = v_k_22_;
goto v___jp_25_;
}
v___jp_25_:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = l_Lean_Grind_CommRing_PPoly_coeff(v_c_16_, v_p_24_);
v___x_28_ = lean_int_add(v___y_26_, v___x_27_);
lean_dec(v___x_27_);
return v___x_28_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_coeff___boxed(lean_object* v_c_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Grind_CommRing_PPoly_coeff(v_c_31_, v_x_32_);
lean_dec_ref(v_x_32_);
lean_dec(v_c_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1(lean_object* v_x_34_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v_k_35_; lean_object* v___x_36_; 
v_k_35_ = lean_ctor_get(v_x_34_, 0);
v___x_36_ = lean_nat_abs(v_k_35_);
return v___x_36_;
}
else
{
lean_object* v_k_37_; lean_object* v_p_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_k_37_ = lean_ctor_get(v_x_34_, 0);
v_p_38_ = lean_ctor_get(v_x_34_, 3);
v___x_39_ = lean_nat_abs(v_k_37_);
v___x_40_ = l_Lean_Grind_CommRing_PPoly_norm1(v_p_38_);
v___x_41_ = lean_nat_add(v___x_39_, v___x_40_);
lean_dec(v___x_40_);
lean_dec(v___x_39_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1___boxed(lean_object* v_x_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Grind_CommRing_PPoly_norm1(v_x_42_);
lean_dec_ref(v_x_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_size(lean_object* v_x_44_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v___x_45_; 
v___x_45_ = lean_unsigned_to_nat(0u);
return v___x_45_;
}
else
{
lean_object* v_p_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_p_46_ = lean_ctor_get(v_x_44_, 3);
v___x_47_ = l_Lean_Grind_CommRing_PPoly_size(v_p_46_);
v___x_48_ = lean_unsigned_to_nat(1u);
v___x_49_ = lean_nat_add(v___x_47_, v___x_48_);
lean_dec(v___x_47_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_size___boxed(lean_object* v_x_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Grind_CommRing_PPoly_size(v_x_50_);
lean_dec_ref(v_x_50_);
return v_res_51_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_PPoly_removeCode___closed__0(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_coeff___closed__0, &l_Lean_Grind_CommRing_PPoly_coeff___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_coeff___closed__0);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_removeCode(lean_object* v_c_54_, lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_nat_dec_eq(v_c_54_, v___x_56_);
if (v___x_57_ == 0)
{
return v_x_55_;
}
else
{
lean_object* v___x_58_; 
lean_dec_ref_known(v_x_55_, 1);
v___x_58_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_removeCode___closed__0, &l_Lean_Grind_CommRing_PPoly_removeCode___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_removeCode___closed__0);
return v___x_58_;
}
}
else
{
lean_object* v_k_59_; lean_object* v_d_60_; lean_object* v_v_61_; lean_object* v_p_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_72_; 
v_k_59_ = lean_ctor_get(v_x_55_, 0);
v_d_60_ = lean_ctor_get(v_x_55_, 1);
v_v_61_ = lean_ctor_get(v_x_55_, 2);
v_p_62_ = lean_ctor_get(v_x_55_, 3);
v_isSharedCheck_72_ = !lean_is_exclusive(v_x_55_);
if (v_isSharedCheck_72_ == 0)
{
v___x_64_ = v_x_55_;
v_isShared_65_ = v_isSharedCheck_72_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_p_62_);
lean_inc(v_v_61_);
lean_inc(v_d_60_);
lean_inc(v_k_59_);
lean_dec(v_x_55_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_72_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
uint8_t v___x_66_; 
v___x_66_ = lean_nat_dec_eq(v_v_61_, v_c_54_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = l_Lean_Grind_CommRing_PPoly_removeCode(v_c_54_, v_p_62_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 3, v___x_67_);
v___x_69_ = v___x_64_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_k_59_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v_d_60_);
lean_ctor_set(v_reuseFailAlloc_70_, 2, v_v_61_);
lean_ctor_set(v_reuseFailAlloc_70_, 3, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
else
{
lean_del_object(v___x_64_);
lean_dec(v_v_61_);
lean_dec(v_d_60_);
lean_dec(v_k_59_);
v_x_55_ = v_p_62_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_removeCode___boxed(lean_object* v_c_73_, lean_object* v_x_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Grind_CommRing_PPoly_removeCode(v_c_73_, v_x_74_);
lean_dec(v_c_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_shiftDown(lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v___x_77_; 
lean_dec_ref_known(v_x_76_, 1);
v___x_77_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_removeCode___closed__0, &l_Lean_Grind_CommRing_PPoly_removeCode___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_removeCode___closed__0);
return v___x_77_;
}
else
{
lean_object* v_k_78_; lean_object* v_d_79_; lean_object* v_v_80_; lean_object* v_p_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_94_; 
v_k_78_ = lean_ctor_get(v_x_76_, 0);
v_d_79_ = lean_ctor_get(v_x_76_, 1);
v_v_80_ = lean_ctor_get(v_x_76_, 2);
v_p_81_ = lean_ctor_get(v_x_76_, 3);
v_isSharedCheck_94_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_94_ == 0)
{
v___x_83_ = v_x_76_;
v_isShared_84_ = v_isSharedCheck_94_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_p_81_);
lean_inc(v_v_80_);
lean_inc(v_d_79_);
lean_inc(v_k_78_);
lean_dec(v_x_76_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_94_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = lean_nat_dec_eq(v_v_80_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_sub(v_v_80_, v___x_87_);
lean_dec(v_v_80_);
v___x_89_ = l_Lean_Grind_CommRing_PPoly_shiftDown(v_p_81_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 3, v___x_89_);
lean_ctor_set(v___x_83_, 2, v___x_88_);
v___x_91_ = v___x_83_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_k_78_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_d_79_);
lean_ctor_set(v_reuseFailAlloc_92_, 2, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_92_, 3, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
else
{
lean_del_object(v___x_83_);
lean_dec(v_v_80_);
lean_dec(v_d_79_);
lean_dec(v_k_78_);
v_x_76_ = v_p_81_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_kron_match__1_splitter___redArg(lean_object* v_x_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
if (lean_obj_tag(v_x_95_) == 0)
{
lean_object* v_k_98_; lean_object* v___x_99_; 
lean_dec(v_h__2_97_);
v_k_98_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_k_98_);
lean_dec_ref_known(v_x_95_, 1);
v___x_99_ = lean_apply_1(v_h__1_96_, v_k_98_);
return v___x_99_;
}
else
{
lean_object* v_k_100_; lean_object* v_d_101_; lean_object* v_v_102_; lean_object* v_p_103_; lean_object* v___x_104_; 
lean_dec(v_h__1_96_);
v_k_100_ = lean_ctor_get(v_x_95_, 0);
lean_inc(v_k_100_);
v_d_101_ = lean_ctor_get(v_x_95_, 1);
lean_inc(v_d_101_);
v_v_102_ = lean_ctor_get(v_x_95_, 2);
lean_inc(v_v_102_);
v_p_103_ = lean_ctor_get(v_x_95_, 3);
lean_inc_ref(v_p_103_);
lean_dec_ref_known(v_x_95_, 4);
v___x_104_ = lean_apply_4(v_h__2_97_, v_k_100_, v_d_101_, v_v_102_, v_p_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_kron_match__1_splitter(lean_object* v_motive_105_, lean_object* v_x_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
lean_object* v_k_109_; lean_object* v___x_110_; 
lean_dec(v_h__2_108_);
v_k_109_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_k_109_);
lean_dec_ref_known(v_x_106_, 1);
v___x_110_ = lean_apply_1(v_h__1_107_, v_k_109_);
return v___x_110_;
}
else
{
lean_object* v_k_111_; lean_object* v_d_112_; lean_object* v_v_113_; lean_object* v_p_114_; lean_object* v___x_115_; 
lean_dec(v_h__1_107_);
v_k_111_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_k_111_);
v_d_112_ = lean_ctor_get(v_x_106_, 1);
lean_inc(v_d_112_);
v_v_113_ = lean_ctor_get(v_x_106_, 2);
lean_inc(v_v_113_);
v_p_114_ = lean_ctor_get(v_x_106_, 3);
lean_inc_ref(v_p_114_);
lean_dec_ref_known(v_x_106_, 4);
v___x_115_ = lean_apply_4(v_h__2_108_, v_k_111_, v_d_112_, v_v_113_, v_p_114_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_denote_match__1_splitter___redArg(lean_object* v_x_116_, lean_object* v_h__1_117_, lean_object* v_h__2_118_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_object* v_k_119_; lean_object* v___x_120_; 
lean_dec(v_h__2_118_);
v_k_119_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_k_119_);
lean_dec_ref_known(v_x_116_, 1);
v___x_120_ = lean_apply_1(v_h__1_117_, v_k_119_);
return v___x_120_;
}
else
{
lean_object* v_k_121_; lean_object* v_d_122_; lean_object* v_v_123_; lean_object* v_p_124_; lean_object* v___x_125_; 
lean_dec(v_h__1_117_);
v_k_121_ = lean_ctor_get(v_x_116_, 0);
lean_inc(v_k_121_);
v_d_122_ = lean_ctor_get(v_x_116_, 1);
lean_inc(v_d_122_);
v_v_123_ = lean_ctor_get(v_x_116_, 2);
lean_inc(v_v_123_);
v_p_124_ = lean_ctor_get(v_x_116_, 3);
lean_inc_ref(v_p_124_);
lean_dec_ref_known(v_x_116_, 4);
v___x_125_ = lean_apply_4(v_h__2_118_, v_k_121_, v_d_122_, v_v_123_, v_p_124_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_denote_match__1_splitter(lean_object* v_motive_126_, lean_object* v_x_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v_k_130_; lean_object* v___x_131_; 
lean_dec(v_h__2_129_);
v_k_130_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_k_130_);
lean_dec_ref_known(v_x_127_, 1);
v___x_131_ = lean_apply_1(v_h__1_128_, v_k_130_);
return v___x_131_;
}
else
{
lean_object* v_k_132_; lean_object* v_d_133_; lean_object* v_v_134_; lean_object* v_p_135_; lean_object* v___x_136_; 
lean_dec(v_h__1_128_);
v_k_132_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_k_132_);
v_d_133_ = lean_ctor_get(v_x_127_, 1);
lean_inc(v_d_133_);
v_v_134_ = lean_ctor_get(v_x_127_, 2);
lean_inc(v_v_134_);
v_p_135_ = lean_ctor_get(v_x_127_, 3);
lean_inc_ref(v_p_135_);
lean_dec_ref_known(v_x_127_, 4);
v___x_136_ = lean_apply_4(v_h__2_129_, v_k_132_, v_d_133_, v_v_134_, v_p_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append_addConst(lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
if (lean_obj_tag(v_a_137_) == 0)
{
lean_object* v_k_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_147_; 
v_k_139_ = lean_ctor_get(v_a_137_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_a_137_);
if (v_isSharedCheck_147_ == 0)
{
v___x_141_ = v_a_137_;
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_k_139_);
lean_dec(v_a_137_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_147_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_143_ = lean_int_add(v_k_139_, v_a_138_);
lean_dec(v_k_139_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_143_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v_k_148_; lean_object* v_d_149_; lean_object* v_v_150_; lean_object* v_p_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_159_; 
v_k_148_ = lean_ctor_get(v_a_137_, 0);
v_d_149_ = lean_ctor_get(v_a_137_, 1);
v_v_150_ = lean_ctor_get(v_a_137_, 2);
v_p_151_ = lean_ctor_get(v_a_137_, 3);
v_isSharedCheck_159_ = !lean_is_exclusive(v_a_137_);
if (v_isSharedCheck_159_ == 0)
{
v___x_153_ = v_a_137_;
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_p_151_);
lean_inc(v_v_150_);
lean_inc(v_d_149_);
lean_inc(v_k_148_);
lean_dec(v_a_137_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_155_ = l_Lean_Grind_CommRing_PPoly_append_addConst(v_p_151_, v_a_138_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 3, v___x_155_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_k_148_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_d_149_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_v_150_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append_addConst___boxed(lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Grind_CommRing_PPoly_append_addConst(v_a_160_, v_a_161_);
lean_dec(v_a_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v_k_165_; lean_object* v___x_166_; 
v_k_165_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_k_165_);
lean_dec_ref_known(v_x_163_, 1);
v___x_166_ = l_Lean_Grind_CommRing_PPoly_append_addConst(v_x_164_, v_k_165_);
lean_dec(v_k_165_);
return v___x_166_;
}
else
{
lean_object* v_k_167_; lean_object* v_d_168_; lean_object* v_v_169_; lean_object* v_p_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_178_; 
v_k_167_ = lean_ctor_get(v_x_163_, 0);
v_d_168_ = lean_ctor_get(v_x_163_, 1);
v_v_169_ = lean_ctor_get(v_x_163_, 2);
v_p_170_ = lean_ctor_get(v_x_163_, 3);
v_isSharedCheck_178_ = !lean_is_exclusive(v_x_163_);
if (v_isSharedCheck_178_ == 0)
{
v___x_172_ = v_x_163_;
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_p_170_);
lean_inc(v_v_169_);
lean_inc(v_d_168_);
lean_inc(v_k_167_);
lean_dec(v_x_163_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = l_Lean_Grind_CommRing_PPoly_append(v_p_170_, v_x_164_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 3, v___x_174_);
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_k_167_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v_d_168_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_v_169_);
lean_ctor_set(v_reuseFailAlloc_177_, 3, v___x_174_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_neg(lean_object* v_x_179_){
_start:
{
if (lean_obj_tag(v_x_179_) == 0)
{
lean_object* v_k_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_188_; 
v_k_180_ = lean_ctor_get(v_x_179_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_188_ == 0)
{
v___x_182_ = v_x_179_;
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_k_180_);
lean_dec(v_x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_184_ = lean_int_neg(v_k_180_);
lean_dec(v_k_180_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_184_);
v___x_186_ = v___x_182_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
lean_object* v_k_189_; lean_object* v_d_190_; lean_object* v_v_191_; lean_object* v_p_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_201_; 
v_k_189_ = lean_ctor_get(v_x_179_, 0);
v_d_190_ = lean_ctor_get(v_x_179_, 1);
v_v_191_ = lean_ctor_get(v_x_179_, 2);
v_p_192_ = lean_ctor_get(v_x_179_, 3);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_201_ == 0)
{
v___x_194_ = v_x_179_;
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_p_192_);
lean_inc(v_v_191_);
lean_inc(v_d_190_);
lean_inc(v_k_189_);
lean_dec(v_x_179_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_196_ = lean_int_neg(v_k_189_);
lean_dec(v_k_189_);
v___x_197_ = l_Lean_Grind_CommRing_PPoly_neg(v_p_192_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 3, v___x_197_);
lean_ctor_set(v___x_194_, 0, v___x_196_);
v___x_199_ = v___x_194_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_d_190_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_v_191_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_addConst_match__1_splitter___redArg(lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_h__1_204_, lean_object* v_h__2_205_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
lean_object* v_k_206_; lean_object* v___x_207_; 
lean_dec(v_h__2_205_);
v_k_206_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_k_206_);
lean_dec_ref_known(v_x_202_, 1);
v___x_207_ = lean_apply_2(v_h__1_204_, v_k_206_, v_x_203_);
return v___x_207_;
}
else
{
lean_object* v_k_208_; lean_object* v_d_209_; lean_object* v_v_210_; lean_object* v_p_211_; lean_object* v___x_212_; 
lean_dec(v_h__1_204_);
v_k_208_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_k_208_);
v_d_209_ = lean_ctor_get(v_x_202_, 1);
lean_inc(v_d_209_);
v_v_210_ = lean_ctor_get(v_x_202_, 2);
lean_inc(v_v_210_);
v_p_211_ = lean_ctor_get(v_x_202_, 3);
lean_inc_ref(v_p_211_);
lean_dec_ref_known(v_x_202_, 4);
v___x_212_ = lean_apply_5(v_h__2_205_, v_k_208_, v_d_209_, v_v_210_, v_p_211_, v_x_203_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_addConst_match__1_splitter(lean_object* v_motive_213_, lean_object* v_x_214_, lean_object* v_x_215_, lean_object* v_h__1_216_, lean_object* v_h__2_217_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v_k_218_; lean_object* v___x_219_; 
lean_dec(v_h__2_217_);
v_k_218_ = lean_ctor_get(v_x_214_, 0);
lean_inc(v_k_218_);
lean_dec_ref_known(v_x_214_, 1);
v___x_219_ = lean_apply_2(v_h__1_216_, v_k_218_, v_x_215_);
return v___x_219_;
}
else
{
lean_object* v_k_220_; lean_object* v_d_221_; lean_object* v_v_222_; lean_object* v_p_223_; lean_object* v___x_224_; 
lean_dec(v_h__1_216_);
v_k_220_ = lean_ctor_get(v_x_214_, 0);
lean_inc(v_k_220_);
v_d_221_ = lean_ctor_get(v_x_214_, 1);
lean_inc(v_d_221_);
v_v_222_ = lean_ctor_get(v_x_214_, 2);
lean_inc(v_v_222_);
v_p_223_ = lean_ctor_get(v_x_214_, 3);
lean_inc_ref(v_p_223_);
lean_dec_ref_known(v_x_214_, 4);
v___x_224_ = lean_apply_5(v_h__2_217_, v_k_220_, v_d_221_, v_v_222_, v_p_223_, v_x_215_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_match__1_splitter___redArg(lean_object* v_x_225_, lean_object* v_x_226_, lean_object* v_h__1_227_, lean_object* v_h__2_228_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_object* v_k_229_; lean_object* v___x_230_; 
lean_dec(v_h__2_228_);
v_k_229_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_k_229_);
lean_dec_ref_known(v_x_225_, 1);
v___x_230_ = lean_apply_2(v_h__1_227_, v_k_229_, v_x_226_);
return v___x_230_;
}
else
{
lean_object* v_k_231_; lean_object* v_d_232_; lean_object* v_v_233_; lean_object* v_p_234_; lean_object* v___x_235_; 
lean_dec(v_h__1_227_);
v_k_231_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_k_231_);
v_d_232_ = lean_ctor_get(v_x_225_, 1);
lean_inc(v_d_232_);
v_v_233_ = lean_ctor_get(v_x_225_, 2);
lean_inc(v_v_233_);
v_p_234_ = lean_ctor_get(v_x_225_, 3);
lean_inc_ref(v_p_234_);
lean_dec_ref_known(v_x_225_, 4);
v___x_235_ = lean_apply_5(v_h__2_228_, v_k_231_, v_d_232_, v_v_233_, v_p_234_, v_x_226_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_match__1_splitter(lean_object* v_motive_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_h__1_239_, lean_object* v_h__2_240_){
_start:
{
if (lean_obj_tag(v_x_237_) == 0)
{
lean_object* v_k_241_; lean_object* v___x_242_; 
lean_dec(v_h__2_240_);
v_k_241_ = lean_ctor_get(v_x_237_, 0);
lean_inc(v_k_241_);
lean_dec_ref_known(v_x_237_, 1);
v___x_242_ = lean_apply_2(v_h__1_239_, v_k_241_, v_x_238_);
return v___x_242_;
}
else
{
lean_object* v_k_243_; lean_object* v_d_244_; lean_object* v_v_245_; lean_object* v_p_246_; lean_object* v___x_247_; 
lean_dec(v_h__1_239_);
v_k_243_ = lean_ctor_get(v_x_237_, 0);
lean_inc(v_k_243_);
v_d_244_ = lean_ctor_get(v_x_237_, 1);
lean_inc(v_d_244_);
v_v_245_ = lean_ctor_get(v_x_237_, 2);
lean_inc(v_v_245_);
v_p_246_ = lean_ctor_get(v_x_237_, 3);
lean_inc_ref(v_p_246_);
lean_dec_ref_known(v_x_237_, 4);
v___x_247_ = lean_apply_5(v_h__2_240_, v_k_243_, v_d_244_, v_v_245_, v_p_246_, v_x_238_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0_spec__0(lean_object* v_as_248_, size_t v_i_249_, size_t v_stop_250_, lean_object* v_b_251_){
_start:
{
uint8_t v___x_252_; 
v___x_252_ = lean_usize_dec_eq(v_i_249_, v_stop_250_);
if (v___x_252_ == 0)
{
size_t v___x_253_; size_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_253_ = ((size_t)1ULL);
v___x_254_ = lean_usize_sub(v_i_249_, v___x_253_);
v___x_255_ = lean_array_uget_borrowed(v_as_248_, v___x_254_);
v___x_256_ = l_Lean_Grind_CommRing_PPoly_norm1(v___x_255_);
v___x_257_ = lean_nat_add(v___x_256_, v_b_251_);
lean_dec(v_b_251_);
lean_dec(v___x_256_);
v_i_249_ = v___x_254_;
v_b_251_ = v___x_257_;
goto _start;
}
else
{
return v_b_251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0_spec__0___boxed(lean_object* v_as_259_, lean_object* v_i_260_, lean_object* v_stop_261_, lean_object* v_b_262_){
_start:
{
size_t v_i_boxed_263_; size_t v_stop_boxed_264_; lean_object* v_res_265_; 
v_i_boxed_263_ = lean_unbox_usize(v_i_260_);
lean_dec(v_i_260_);
v_stop_boxed_264_ = lean_unbox_usize(v_stop_261_);
lean_dec(v_stop_261_);
v_res_265_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0_spec__0(v_as_259_, v_i_boxed_263_, v_stop_boxed_264_, v_b_262_);
lean_dec_ref(v_as_259_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(lean_object* v_init_266_, lean_object* v_l_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_268_ = lean_array_mk(v_l_267_);
v___x_269_ = lean_array_get_size(v___x_268_);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_nat_dec_lt(v___x_270_, v___x_269_);
if (v___x_271_ == 0)
{
lean_dec_ref(v___x_268_);
return v_init_266_;
}
else
{
size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_usize_of_nat(v___x_269_);
v___x_273_ = ((size_t)0ULL);
v___x_274_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0_spec__0(v___x_268_, v___x_272_, v___x_273_, v_init_266_);
lean_dec_ref(v___x_268_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1List(lean_object* v_ps_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = l_List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(v___x_276_, v_ps_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_denoteG___redArg(lean_object* v_inst_278_, lean_object* v_g_279_, lean_object* v_x_280_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
lean_object* v_intCast_281_; lean_object* v_k_282_; lean_object* v___x_283_; 
lean_dec(v_g_279_);
v_intCast_281_ = lean_ctor_get(v_inst_278_, 3);
lean_inc(v_intCast_281_);
lean_dec_ref(v_inst_278_);
v_k_282_ = lean_ctor_get(v_x_280_, 0);
lean_inc(v_k_282_);
lean_dec_ref_known(v_x_280_, 1);
v___x_283_ = lean_apply_1(v_intCast_281_, v_k_282_);
return v___x_283_;
}
else
{
lean_object* v_toSemiring_284_; lean_object* v_intCast_285_; lean_object* v_toAdd_286_; lean_object* v_toMul_287_; lean_object* v_k_288_; lean_object* v_v_289_; lean_object* v_p_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_toSemiring_284_ = lean_ctor_get(v_inst_278_, 0);
v_intCast_285_ = lean_ctor_get(v_inst_278_, 3);
v_toAdd_286_ = lean_ctor_get(v_toSemiring_284_, 0);
lean_inc(v_toAdd_286_);
v_toMul_287_ = lean_ctor_get(v_toSemiring_284_, 1);
v_k_288_ = lean_ctor_get(v_x_280_, 0);
lean_inc(v_k_288_);
v_v_289_ = lean_ctor_get(v_x_280_, 2);
lean_inc(v_v_289_);
v_p_290_ = lean_ctor_get(v_x_280_, 3);
lean_inc_ref(v_p_290_);
lean_dec_ref_known(v_x_280_, 4);
lean_inc(v_intCast_285_);
v___x_291_ = lean_apply_1(v_intCast_285_, v_k_288_);
lean_inc(v_g_279_);
v___x_292_ = lean_apply_1(v_g_279_, v_v_289_);
lean_inc(v_toMul_287_);
v___x_293_ = lean_apply_2(v_toMul_287_, v___x_291_, v___x_292_);
v___x_294_ = l_Lean_Grind_CommRing_PPoly_denoteG___redArg(v_inst_278_, v_g_279_, v_p_290_);
v___x_295_ = lean_apply_2(v_toAdd_286_, v___x_293_, v___x_294_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_denoteG(lean_object* v_00_u03b1_296_, lean_object* v_inst_297_, lean_object* v_g_298_, lean_object* v_x_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Grind_CommRing_PPoly_denoteG___redArg(v_inst_297_, v_g_298_, v_x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_scale(lean_object* v_k_301_, lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_302_) == 0)
{
lean_object* v_k_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_311_; 
v_k_303_ = lean_ctor_get(v_x_302_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_311_ == 0)
{
v___x_305_ = v_x_302_;
v_isShared_306_ = v_isSharedCheck_311_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_k_303_);
lean_dec(v_x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_311_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_307_ = lean_int_mul(v_k_301_, v_k_303_);
lean_dec(v_k_303_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_307_);
v___x_309_ = v___x_305_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
else
{
lean_object* v_k_312_; lean_object* v_d_313_; lean_object* v_v_314_; lean_object* v_p_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_324_; 
v_k_312_ = lean_ctor_get(v_x_302_, 0);
v_d_313_ = lean_ctor_get(v_x_302_, 1);
v_v_314_ = lean_ctor_get(v_x_302_, 2);
v_p_315_ = lean_ctor_get(v_x_302_, 3);
v_isSharedCheck_324_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_324_ == 0)
{
v___x_317_ = v_x_302_;
v_isShared_318_ = v_isSharedCheck_324_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_p_315_);
lean_inc(v_v_314_);
lean_inc(v_d_313_);
lean_inc(v_k_312_);
lean_dec(v_x_302_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_324_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_319_ = lean_int_mul(v_k_301_, v_k_312_);
lean_dec(v_k_312_);
v___x_320_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_301_, v_p_315_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 3, v___x_320_);
lean_ctor_set(v___x_317_, 0, v___x_319_);
v___x_322_ = v___x_317_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_d_313_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v_v_314_);
lean_ctor_set(v_reuseFailAlloc_323_, 3, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_scale___boxed(lean_object* v_k_325_, lean_object* v_x_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_325_, v_x_326_);
lean_dec(v_k_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Expr_evalConst_spec__0(lean_object* v_a_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_nat_to_int(v_a_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_evalConst(lean_object* v_x_330_){
_start:
{
switch(lean_obj_tag(v_x_330_))
{
case 1:
{
lean_object* v_k_331_; lean_object* v___x_332_; 
v_k_331_ = lean_ctor_get(v_x_330_, 0);
lean_inc(v_k_331_);
lean_dec_ref_known(v_x_330_, 1);
v___x_332_ = lean_nat_to_int(v_k_331_);
return v___x_332_;
}
case 3:
{
lean_object* v___x_333_; 
lean_dec_ref_known(v_x_330_, 1);
v___x_333_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_coeff___closed__0, &l_Lean_Grind_CommRing_PPoly_coeff___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_coeff___closed__0);
return v___x_333_;
}
case 4:
{
lean_object* v_a_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_a_334_ = lean_ctor_get(v_x_330_, 0);
lean_inc_ref(v_a_334_);
lean_dec_ref_known(v_x_330_, 1);
v___x_335_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_334_);
v___x_336_ = lean_int_neg(v___x_335_);
lean_dec(v___x_335_);
return v___x_336_;
}
case 5:
{
lean_object* v_a_337_; lean_object* v_b_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_a_337_ = lean_ctor_get(v_x_330_, 0);
lean_inc_ref(v_a_337_);
v_b_338_ = lean_ctor_get(v_x_330_, 1);
lean_inc_ref(v_b_338_);
lean_dec_ref_known(v_x_330_, 2);
v___x_339_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_337_);
v___x_340_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_338_);
v___x_341_ = lean_int_add(v___x_339_, v___x_340_);
lean_dec(v___x_340_);
lean_dec(v___x_339_);
return v___x_341_;
}
case 6:
{
lean_object* v_a_342_; lean_object* v_b_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_a_342_ = lean_ctor_get(v_x_330_, 0);
lean_inc_ref(v_a_342_);
v_b_343_ = lean_ctor_get(v_x_330_, 1);
lean_inc_ref(v_b_343_);
lean_dec_ref_known(v_x_330_, 2);
v___x_344_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_342_);
v___x_345_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_343_);
v___x_346_ = lean_int_sub(v___x_344_, v___x_345_);
lean_dec(v___x_345_);
lean_dec(v___x_344_);
return v___x_346_;
}
case 7:
{
lean_object* v_a_347_; lean_object* v_b_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_a_347_ = lean_ctor_get(v_x_330_, 0);
lean_inc_ref(v_a_347_);
v_b_348_ = lean_ctor_get(v_x_330_, 1);
lean_inc_ref(v_b_348_);
lean_dec_ref_known(v_x_330_, 2);
v___x_349_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_347_);
v___x_350_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_348_);
v___x_351_ = lean_int_mul(v___x_349_, v___x_350_);
lean_dec(v___x_350_);
lean_dec(v___x_349_);
return v___x_351_;
}
case 8:
{
lean_object* v_a_352_; lean_object* v_k_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_a_352_ = lean_ctor_get(v_x_330_, 0);
lean_inc_ref(v_a_352_);
v_k_353_ = lean_ctor_get(v_x_330_, 1);
lean_inc(v_k_353_);
lean_dec_ref_known(v_x_330_, 2);
v___x_354_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_352_);
v___x_355_ = l_Int_pow(v___x_354_, v_k_353_);
lean_dec(v_k_353_);
lean_dec(v___x_354_);
return v___x_355_;
}
default: 
{
lean_object* v_k_356_; 
v_k_356_ = lean_ctor_get(v_x_330_, 0);
lean_inc(v_k_356_);
lean_dec_ref(v_x_330_);
return v_k_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___redArg(lean_object* v_inst_357_, lean_object* v_f_358_, lean_object* v_v_359_){
_start:
{
lean_object* v_toSemiring_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_toSemiring_360_ = lean_ctor_get(v_inst_357_, 0);
lean_inc_ref(v_toSemiring_360_);
lean_dec_ref(v_inst_357_);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_nat_dec_eq(v_v_359_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec_ref(v_toSemiring_360_);
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_nat_sub(v_v_359_, v___x_363_);
v___x_365_ = lean_apply_1(v_f_358_, v___x_364_);
return v___x_365_;
}
else
{
lean_object* v_ofNat_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec(v_f_358_);
v_ofNat_366_ = lean_ctor_get(v_toSemiring_360_, 3);
lean_inc(v_ofNat_366_);
lean_dec_ref(v_toSemiring_360_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_apply_1(v_ofNat_366_, v___x_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___redArg___boxed(lean_object* v_inst_369_, lean_object* v_f_370_, lean_object* v_v_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Grind_CommRing_PPoly_linVal___redArg(v_inst_369_, v_f_370_, v_v_371_);
lean_dec(v_v_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal(lean_object* v_00_u03b1_373_, lean_object* v_inst_374_, lean_object* v_f_375_, lean_object* v_v_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Grind_CommRing_PPoly_linVal___redArg(v_inst_374_, v_f_375_, v_v_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___boxed(lean_object* v_00_u03b1_378_, lean_object* v_inst_379_, lean_object* v_f_380_, lean_object* v_v_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Grind_CommRing_PPoly_linVal(v_00_u03b1_378_, v_inst_379_, v_f_380_, v_v_381_);
lean_dec(v_v_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorIdx___impl(lean_object* v_x_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_obj_tag_nat(v_x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorIdx___impl___boxed(lean_object* v_x_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Grind_CommRing_KList_ctorIdx___impl(v_x_385_);
lean_dec(v_x_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim___redArg(lean_object* v_t_387_, lean_object* v_k_388_){
_start:
{
if (lean_obj_tag(v_t_387_) == 0)
{
return v_k_388_;
}
else
{
lean_object* v_k_389_; lean_object* v_m_390_; lean_object* v_q_391_; lean_object* v_ls_392_; lean_object* v___x_393_; 
v_k_389_ = lean_ctor_get(v_t_387_, 0);
lean_inc(v_k_389_);
v_m_390_ = lean_ctor_get(v_t_387_, 1);
lean_inc(v_m_390_);
v_q_391_ = lean_ctor_get(v_t_387_, 2);
lean_inc_ref(v_q_391_);
v_ls_392_ = lean_ctor_get(v_t_387_, 3);
lean_inc(v_ls_392_);
lean_dec_ref_known(v_t_387_, 4);
v___x_393_ = lean_apply_4(v_k_388_, v_k_389_, v_m_390_, v_q_391_, v_ls_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim(lean_object* v_motive_394_, lean_object* v_ctorIdx_395_, lean_object* v_t_396_, lean_object* v_h_397_, lean_object* v_k_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_396_, v_k_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim___boxed(lean_object* v_motive_400_, lean_object* v_ctorIdx_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_k_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Grind_CommRing_KList_ctorElim(v_motive_400_, v_ctorIdx_401_, v_t_402_, v_h_403_, v_k_404_);
lean_dec(v_ctorIdx_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_nil_elim___redArg(lean_object* v_t_406_, lean_object* v_nil_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_406_, v_nil_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_nil_elim(lean_object* v_motive_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_nil_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_410_, v_nil_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_cons_elim___redArg(lean_object* v_t_414_, lean_object* v_cons_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_414_, v_cons_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_cons_elim(lean_object* v_motive_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_cons_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_418_, v_cons_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorIdx___impl(lean_object* v_x_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = lean_obj_tag_nat(v_x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorIdx___impl___boxed(lean_object* v_x_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Grind_CommRing_MList_ctorIdx___impl(v_x_424_);
lean_dec(v_x_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim___redArg(lean_object* v_t_426_, lean_object* v_k_427_){
_start:
{
if (lean_obj_tag(v_t_426_) == 0)
{
return v_k_427_;
}
else
{
lean_object* v_M_428_; lean_object* v_q_429_; lean_object* v_ls_430_; lean_object* v___x_431_; 
v_M_428_ = lean_ctor_get(v_t_426_, 0);
lean_inc_ref(v_M_428_);
v_q_429_ = lean_ctor_get(v_t_426_, 1);
lean_inc_ref(v_q_429_);
v_ls_430_ = lean_ctor_get(v_t_426_, 2);
lean_inc(v_ls_430_);
lean_dec_ref_known(v_t_426_, 3);
v___x_431_ = lean_apply_3(v_k_427_, v_M_428_, v_q_429_, v_ls_430_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim(lean_object* v_motive_432_, lean_object* v_ctorIdx_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_k_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_434_, v_k_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim___boxed(lean_object* v_motive_438_, lean_object* v_ctorIdx_439_, lean_object* v_t_440_, lean_object* v_h_441_, lean_object* v_k_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Grind_CommRing_MList_ctorElim(v_motive_438_, v_ctorIdx_439_, v_t_440_, v_h_441_, v_k_442_);
lean_dec(v_ctorIdx_439_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_nil_elim___redArg(lean_object* v_t_444_, lean_object* v_nil_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_444_, v_nil_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_nil_elim(lean_object* v_motive_447_, lean_object* v_t_448_, lean_object* v_h_449_, lean_object* v_nil_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_448_, v_nil_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_cons_elim___redArg(lean_object* v_t_452_, lean_object* v_cons_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_452_, v_cons_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_cons_elim(lean_object* v_motive_455_, lean_object* v_t_456_, lean_object* v_h_457_, lean_object* v_cons_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_456_, v_cons_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object* v_p_460_, lean_object* v_h__1_461_, lean_object* v_h__2_462_){
_start:
{
if (lean_obj_tag(v_p_460_) == 0)
{
lean_object* v_k_463_; lean_object* v___x_464_; 
lean_dec(v_h__2_462_);
v_k_463_ = lean_ctor_get(v_p_460_, 0);
lean_inc(v_k_463_);
lean_dec_ref_known(v_p_460_, 1);
v___x_464_ = lean_apply_1(v_h__1_461_, v_k_463_);
return v___x_464_;
}
else
{
lean_object* v_k_465_; lean_object* v_v_466_; lean_object* v_p_467_; lean_object* v___x_468_; 
lean_dec(v_h__1_461_);
v_k_465_ = lean_ctor_get(v_p_460_, 0);
lean_inc(v_k_465_);
v_v_466_ = lean_ctor_get(v_p_460_, 1);
lean_inc(v_v_466_);
v_p_467_ = lean_ctor_get(v_p_460_, 2);
lean_inc_ref(v_p_467_);
lean_dec_ref_known(v_p_460_, 3);
v___x_468_ = lean_apply_3(v_h__2_462_, v_k_465_, v_v_466_, v_p_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object* v_motive_469_, lean_object* v_p_470_, lean_object* v_h__1_471_, lean_object* v_h__2_472_){
_start:
{
if (lean_obj_tag(v_p_470_) == 0)
{
lean_object* v_k_473_; lean_object* v___x_474_; 
lean_dec(v_h__2_472_);
v_k_473_ = lean_ctor_get(v_p_470_, 0);
lean_inc(v_k_473_);
lean_dec_ref_known(v_p_470_, 1);
v___x_474_ = lean_apply_1(v_h__1_471_, v_k_473_);
return v___x_474_;
}
else
{
lean_object* v_k_475_; lean_object* v_v_476_; lean_object* v_p_477_; lean_object* v___x_478_; 
lean_dec(v_h__1_471_);
v_k_475_ = lean_ctor_get(v_p_470_, 0);
lean_inc(v_k_475_);
v_v_476_ = lean_ctor_get(v_p_470_, 1);
lean_inc(v_v_476_);
v_p_477_ = lean_ctor_get(v_p_470_, 2);
lean_inc_ref(v_p_477_);
lean_dec_ref_known(v_p_470_, 3);
v___x_478_ = lean_apply_3(v_h__2_472_, v_k_475_, v_v_476_, v_p_477_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_evalConst_match__1_splitter___redArg(lean_object* v_x_479_, lean_object* v_h__1_480_, lean_object* v_h__2_481_, lean_object* v_h__3_482_, lean_object* v_h__4_483_, lean_object* v_h__5_484_, lean_object* v_h__6_485_, lean_object* v_h__7_486_, lean_object* v_h__8_487_, lean_object* v_h__9_488_){
_start:
{
switch(lean_obj_tag(v_x_479_))
{
case 0:
{
lean_object* v_k_489_; lean_object* v___x_490_; 
lean_dec(v_h__9_488_);
lean_dec(v_h__8_487_);
lean_dec(v_h__7_486_);
lean_dec(v_h__6_485_);
lean_dec(v_h__5_484_);
lean_dec(v_h__4_483_);
lean_dec(v_h__3_482_);
lean_dec(v_h__2_481_);
v_k_489_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_k_489_);
lean_dec_ref_known(v_x_479_, 1);
v___x_490_ = lean_apply_1(v_h__1_480_, v_k_489_);
return v___x_490_;
}
case 1:
{
lean_object* v_k_491_; lean_object* v___x_492_; 
lean_dec(v_h__9_488_);
lean_dec(v_h__8_487_);
lean_dec(v_h__7_486_);
lean_dec(v_h__6_485_);
lean_dec(v_h__5_484_);
lean_dec(v_h__4_483_);
lean_dec(v_h__2_481_);
lean_dec(v_h__1_480_);
v_k_491_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_k_491_);
lean_dec_ref_known(v_x_479_, 1);
v___x_492_ = lean_apply_1(v_h__3_482_, v_k_491_);
return v___x_492_;
}
case 2:
{
lean_object* v_k_493_; lean_object* v___x_494_; 
lean_dec(v_h__9_488_);
lean_dec(v_h__8_487_);
lean_dec(v_h__7_486_);
lean_dec(v_h__6_485_);
lean_dec(v_h__5_484_);
lean_dec(v_h__4_483_);
lean_dec(v_h__3_482_);
lean_dec(v_h__1_480_);
v_k_493_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_k_493_);
lean_dec_ref_known(v_x_479_, 1);
v___x_494_ = lean_apply_1(v_h__2_481_, v_k_493_);
return v___x_494_;
}
case 3:
{
lean_object* v_i_495_; lean_object* v___x_496_; 
lean_dec(v_h__9_488_);
lean_dec(v_h__8_487_);
lean_dec(v_h__7_486_);
lean_dec(v_h__6_485_);
lean_dec(v_h__5_484_);
lean_dec(v_h__3_482_);
lean_dec(v_h__2_481_);
lean_dec(v_h__1_480_);
v_i_495_ = lean_ctor_get(v_x_479_, 0);
lean_inc(v_i_495_);
lean_dec_ref_known(v_x_479_, 1);
v___x_496_ = lean_apply_1(v_h__4_483_, v_i_495_);
return v___x_496_;
}
case 4:
{
lean_object* v_a_497_; lean_object* v___x_498_; 
lean_dec(v_h__9_488_);
lean_dec(v_h__8_487_);
lean_dec(v_h__7_486_);
lean_dec(v_h__6_485_);
lean_dec(v_h__4_483_);
lean_dec(v_h__3_482_);
lean_dec(v_h__2_481_);
lean_dec(v_h__1_480_);
v_a_497_ = lean_ctor_get(v_x_479_, 0);
lean_inc_ref(v_a_497_);
lean_dec_ref_known(v_x_479_, 1);
v___x_498_ = lean_apply_1(v_h__5_484_, v_a_497_);
return v___x_498_;
}
case 5:
{
lean_object* v_a_499_; lean_object* v_b_500_; lean_object* v___x_501_; 
lean_dec(v_h__9_488_);
lean_dec(v_h__8_487_);
lean_dec(v_h__7_486_);
lean_dec(v_h__5_484_);
lean_dec(v_h__4_483_);
lean_dec(v_h__3_482_);
lean_dec(v_h__2_481_);
lean_dec(v_h__1_480_);
v_a_499_ = lean_ctor_get(v_x_479_, 0);
lean_inc_ref(v_a_499_);
v_b_500_ = lean_ctor_get(v_x_479_, 1);
lean_inc_ref(v_b_500_);
lean_dec_ref_known(v_x_479_, 2);
v___x_501_ = lean_apply_2(v_h__6_485_, v_a_499_, v_b_500_);
return v___x_501_;
}
case 6:
{
lean_object* v_a_502_; lean_object* v_b_503_; lean_object* v___x_504_; 
lean_dec(v_h__9_488_);
lean_dec(v_h__8_487_);
lean_dec(v_h__6_485_);
lean_dec(v_h__5_484_);
lean_dec(v_h__4_483_);
lean_dec(v_h__3_482_);
lean_dec(v_h__2_481_);
lean_dec(v_h__1_480_);
v_a_502_ = lean_ctor_get(v_x_479_, 0);
lean_inc_ref(v_a_502_);
v_b_503_ = lean_ctor_get(v_x_479_, 1);
lean_inc_ref(v_b_503_);
lean_dec_ref_known(v_x_479_, 2);
v___x_504_ = lean_apply_2(v_h__7_486_, v_a_502_, v_b_503_);
return v___x_504_;
}
case 7:
{
lean_object* v_a_505_; lean_object* v_b_506_; lean_object* v___x_507_; 
lean_dec(v_h__9_488_);
lean_dec(v_h__7_486_);
lean_dec(v_h__6_485_);
lean_dec(v_h__5_484_);
lean_dec(v_h__4_483_);
lean_dec(v_h__3_482_);
lean_dec(v_h__2_481_);
lean_dec(v_h__1_480_);
v_a_505_ = lean_ctor_get(v_x_479_, 0);
lean_inc_ref(v_a_505_);
v_b_506_ = lean_ctor_get(v_x_479_, 1);
lean_inc_ref(v_b_506_);
lean_dec_ref_known(v_x_479_, 2);
v___x_507_ = lean_apply_2(v_h__8_487_, v_a_505_, v_b_506_);
return v___x_507_;
}
default: 
{
lean_object* v_a_508_; lean_object* v_k_509_; lean_object* v___x_510_; 
lean_dec(v_h__8_487_);
lean_dec(v_h__7_486_);
lean_dec(v_h__6_485_);
lean_dec(v_h__5_484_);
lean_dec(v_h__4_483_);
lean_dec(v_h__3_482_);
lean_dec(v_h__2_481_);
lean_dec(v_h__1_480_);
v_a_508_ = lean_ctor_get(v_x_479_, 0);
lean_inc_ref(v_a_508_);
v_k_509_ = lean_ctor_get(v_x_479_, 1);
lean_inc(v_k_509_);
lean_dec_ref_known(v_x_479_, 2);
v___x_510_ = lean_apply_2(v_h__9_488_, v_a_508_, v_k_509_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_evalConst_match__1_splitter(lean_object* v_motive_511_, lean_object* v_x_512_, lean_object* v_h__1_513_, lean_object* v_h__2_514_, lean_object* v_h__3_515_, lean_object* v_h__4_516_, lean_object* v_h__5_517_, lean_object* v_h__6_518_, lean_object* v_h__7_519_, lean_object* v_h__8_520_, lean_object* v_h__9_521_){
_start:
{
switch(lean_obj_tag(v_x_512_))
{
case 0:
{
lean_object* v_k_522_; lean_object* v___x_523_; 
lean_dec(v_h__9_521_);
lean_dec(v_h__8_520_);
lean_dec(v_h__7_519_);
lean_dec(v_h__6_518_);
lean_dec(v_h__5_517_);
lean_dec(v_h__4_516_);
lean_dec(v_h__3_515_);
lean_dec(v_h__2_514_);
v_k_522_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_k_522_);
lean_dec_ref_known(v_x_512_, 1);
v___x_523_ = lean_apply_1(v_h__1_513_, v_k_522_);
return v___x_523_;
}
case 1:
{
lean_object* v_k_524_; lean_object* v___x_525_; 
lean_dec(v_h__9_521_);
lean_dec(v_h__8_520_);
lean_dec(v_h__7_519_);
lean_dec(v_h__6_518_);
lean_dec(v_h__5_517_);
lean_dec(v_h__4_516_);
lean_dec(v_h__2_514_);
lean_dec(v_h__1_513_);
v_k_524_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_k_524_);
lean_dec_ref_known(v_x_512_, 1);
v___x_525_ = lean_apply_1(v_h__3_515_, v_k_524_);
return v___x_525_;
}
case 2:
{
lean_object* v_k_526_; lean_object* v___x_527_; 
lean_dec(v_h__9_521_);
lean_dec(v_h__8_520_);
lean_dec(v_h__7_519_);
lean_dec(v_h__6_518_);
lean_dec(v_h__5_517_);
lean_dec(v_h__4_516_);
lean_dec(v_h__3_515_);
lean_dec(v_h__1_513_);
v_k_526_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_k_526_);
lean_dec_ref_known(v_x_512_, 1);
v___x_527_ = lean_apply_1(v_h__2_514_, v_k_526_);
return v___x_527_;
}
case 3:
{
lean_object* v_i_528_; lean_object* v___x_529_; 
lean_dec(v_h__9_521_);
lean_dec(v_h__8_520_);
lean_dec(v_h__7_519_);
lean_dec(v_h__6_518_);
lean_dec(v_h__5_517_);
lean_dec(v_h__3_515_);
lean_dec(v_h__2_514_);
lean_dec(v_h__1_513_);
v_i_528_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_i_528_);
lean_dec_ref_known(v_x_512_, 1);
v___x_529_ = lean_apply_1(v_h__4_516_, v_i_528_);
return v___x_529_;
}
case 4:
{
lean_object* v_a_530_; lean_object* v___x_531_; 
lean_dec(v_h__9_521_);
lean_dec(v_h__8_520_);
lean_dec(v_h__7_519_);
lean_dec(v_h__6_518_);
lean_dec(v_h__4_516_);
lean_dec(v_h__3_515_);
lean_dec(v_h__2_514_);
lean_dec(v_h__1_513_);
v_a_530_ = lean_ctor_get(v_x_512_, 0);
lean_inc_ref(v_a_530_);
lean_dec_ref_known(v_x_512_, 1);
v___x_531_ = lean_apply_1(v_h__5_517_, v_a_530_);
return v___x_531_;
}
case 5:
{
lean_object* v_a_532_; lean_object* v_b_533_; lean_object* v___x_534_; 
lean_dec(v_h__9_521_);
lean_dec(v_h__8_520_);
lean_dec(v_h__7_519_);
lean_dec(v_h__5_517_);
lean_dec(v_h__4_516_);
lean_dec(v_h__3_515_);
lean_dec(v_h__2_514_);
lean_dec(v_h__1_513_);
v_a_532_ = lean_ctor_get(v_x_512_, 0);
lean_inc_ref(v_a_532_);
v_b_533_ = lean_ctor_get(v_x_512_, 1);
lean_inc_ref(v_b_533_);
lean_dec_ref_known(v_x_512_, 2);
v___x_534_ = lean_apply_2(v_h__6_518_, v_a_532_, v_b_533_);
return v___x_534_;
}
case 6:
{
lean_object* v_a_535_; lean_object* v_b_536_; lean_object* v___x_537_; 
lean_dec(v_h__9_521_);
lean_dec(v_h__8_520_);
lean_dec(v_h__6_518_);
lean_dec(v_h__5_517_);
lean_dec(v_h__4_516_);
lean_dec(v_h__3_515_);
lean_dec(v_h__2_514_);
lean_dec(v_h__1_513_);
v_a_535_ = lean_ctor_get(v_x_512_, 0);
lean_inc_ref(v_a_535_);
v_b_536_ = lean_ctor_get(v_x_512_, 1);
lean_inc_ref(v_b_536_);
lean_dec_ref_known(v_x_512_, 2);
v___x_537_ = lean_apply_2(v_h__7_519_, v_a_535_, v_b_536_);
return v___x_537_;
}
case 7:
{
lean_object* v_a_538_; lean_object* v_b_539_; lean_object* v___x_540_; 
lean_dec(v_h__9_521_);
lean_dec(v_h__7_519_);
lean_dec(v_h__6_518_);
lean_dec(v_h__5_517_);
lean_dec(v_h__4_516_);
lean_dec(v_h__3_515_);
lean_dec(v_h__2_514_);
lean_dec(v_h__1_513_);
v_a_538_ = lean_ctor_get(v_x_512_, 0);
lean_inc_ref(v_a_538_);
v_b_539_ = lean_ctor_get(v_x_512_, 1);
lean_inc_ref(v_b_539_);
lean_dec_ref_known(v_x_512_, 2);
v___x_540_ = lean_apply_2(v_h__8_520_, v_a_538_, v_b_539_);
return v___x_540_;
}
default: 
{
lean_object* v_a_541_; lean_object* v_k_542_; lean_object* v___x_543_; 
lean_dec(v_h__8_520_);
lean_dec(v_h__7_519_);
lean_dec(v_h__6_518_);
lean_dec(v_h__5_517_);
lean_dec(v_h__4_516_);
lean_dec(v_h__3_515_);
lean_dec(v_h__2_514_);
lean_dec(v_h__1_513_);
v_a_541_ = lean_ctor_get(v_x_512_, 0);
lean_inc_ref(v_a_541_);
v_k_542_ = lean_ctor_get(v_x_512_, 1);
lean_inc(v_k_542_);
lean_dec_ref_known(v_x_512_, 2);
v___x_543_ = lean_apply_2(v_h__9_521_, v_a_541_, v_k_542_);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_toPPQ_match__1_splitter___redArg(lean_object* v_x_544_, lean_object* v_h__1_545_, lean_object* v_h__2_546_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_h__1_545_);
v___x_547_ = lean_box(0);
v___x_548_ = lean_apply_1(v_h__2_546_, v___x_547_);
return v___x_548_;
}
else
{
lean_object* v_val_549_; lean_object* v___x_550_; 
lean_dec(v_h__2_546_);
v_val_549_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_val_549_);
lean_dec_ref_known(v_x_544_, 1);
v___x_550_ = lean_apply_1(v_h__1_545_, v_val_549_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_toPPQ_match__1_splitter(lean_object* v_motive_551_, lean_object* v_x_552_, lean_object* v_h__1_553_, lean_object* v_h__2_554_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v_h__1_553_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_apply_1(v_h__2_554_, v___x_555_);
return v___x_556_;
}
else
{
lean_object* v_val_557_; lean_object* v___x_558_; 
lean_dec(v_h__2_554_);
v_val_557_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_val_557_);
lean_dec_ref_known(v_x_552_, 1);
v___x_558_ = lean_apply_1(v_h__1_553_, v_val_557_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL(lean_object* v_k_559_, lean_object* v_d_560_, lean_object* v_v_561_, lean_object* v_x_562_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
lean_object* v_k_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_k_563_ = lean_ctor_get(v_x_562_, 0);
lean_inc(v_k_563_);
lean_dec_ref_known(v_x_562_, 1);
v___x_564_ = lean_int_mul(v_k_559_, v_k_563_);
lean_dec(v_k_563_);
v___x_565_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_removeCode___closed__0, &l_Lean_Grind_CommRing_PPoly_removeCode___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_removeCode___closed__0);
v___x_566_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v_d_560_);
lean_ctor_set(v___x_566_, 2, v_v_561_);
lean_ctor_set(v___x_566_, 3, v___x_565_);
return v___x_566_;
}
else
{
lean_object* v_k_567_; lean_object* v_d_568_; lean_object* v_v_569_; lean_object* v_p_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_581_; 
v_k_567_ = lean_ctor_get(v_x_562_, 0);
v_d_568_ = lean_ctor_get(v_x_562_, 1);
v_v_569_ = lean_ctor_get(v_x_562_, 2);
v_p_570_ = lean_ctor_get(v_x_562_, 3);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_581_ == 0)
{
v___x_572_ = v_x_562_;
v_isShared_573_ = v_isSharedCheck_581_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_p_570_);
lean_inc(v_v_569_);
lean_inc(v_d_568_);
lean_inc(v_k_567_);
lean_dec(v_x_562_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_581_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_574_ = lean_int_mul(v_k_559_, v_k_567_);
lean_dec(v_k_567_);
v___x_575_ = lean_nat_add(v_d_560_, v_d_568_);
lean_dec(v_d_568_);
v___x_576_ = lean_nat_add(v_v_561_, v_v_569_);
lean_dec(v_v_569_);
v___x_577_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_559_, v_d_560_, v_v_561_, v_p_570_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 3, v___x_577_);
lean_ctor_set(v___x_572_, 2, v___x_576_);
lean_ctor_set(v___x_572_, 1, v___x_575_);
lean_ctor_set(v___x_572_, 0, v___x_574_);
v___x_579_ = v___x_572_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL___boxed(lean_object* v_k_582_, lean_object* v_d_583_, lean_object* v_v_584_, lean_object* v_x_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_582_, v_d_583_, v_v_584_, v_x_585_);
lean_dec(v_k_582_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTL(lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
lean_object* v_k_589_; lean_object* v___x_590_; 
v_k_589_ = lean_ctor_get(v_x_587_, 0);
lean_inc(v_k_589_);
lean_dec_ref_known(v_x_587_, 1);
v___x_590_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_589_, v_x_588_);
lean_dec(v_k_589_);
return v___x_590_;
}
else
{
lean_object* v_k_591_; lean_object* v_d_592_; lean_object* v_v_593_; lean_object* v_p_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_k_591_ = lean_ctor_get(v_x_587_, 0);
lean_inc(v_k_591_);
v_d_592_ = lean_ctor_get(v_x_587_, 1);
lean_inc(v_d_592_);
v_v_593_ = lean_ctor_get(v_x_587_, 2);
lean_inc(v_v_593_);
v_p_594_ = lean_ctor_get(v_x_587_, 3);
lean_inc_ref(v_p_594_);
lean_dec_ref_known(v_x_587_, 4);
lean_inc_ref(v_x_588_);
v___x_595_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_591_, v_d_592_, v_v_593_, v_x_588_);
lean_dec(v_k_591_);
v___x_596_ = l_Lean_Grind_CommRing_PPoly_mulTL(v_p_594_, v_x_588_);
v___x_597_ = l_Lean_Grind_CommRing_PPoly_append(v___x_595_, v___x_596_);
return v___x_597_;
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__0(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_to_int(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__1(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_powTL___closed__0, &l_Lean_Grind_CommRing_PPoly_powTL___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__0);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL(lean_object* v_p_602_, lean_object* v_x_603_){
_start:
{
lean_object* v_zero_604_; uint8_t v_isZero_605_; 
v_zero_604_ = lean_unsigned_to_nat(0u);
v_isZero_605_ = lean_nat_dec_eq(v_x_603_, v_zero_604_);
if (v_isZero_605_ == 1)
{
lean_object* v___x_606_; 
lean_dec_ref(v_p_602_);
v___x_606_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_powTL___closed__1, &l_Lean_Grind_CommRing_PPoly_powTL___closed__1_once, _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__1);
return v___x_606_;
}
else
{
lean_object* v_one_607_; lean_object* v_n_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_one_607_ = lean_unsigned_to_nat(1u);
v_n_608_ = lean_nat_sub(v_x_603_, v_one_607_);
lean_inc_ref(v_p_602_);
v___x_609_ = l_Lean_Grind_CommRing_PPoly_powTL(v_p_602_, v_n_608_);
lean_dec(v_n_608_);
v___x_610_ = l_Lean_Grind_CommRing_PPoly_mulTL(v___x_609_, v_p_602_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL___boxed(lean_object* v_p_611_, lean_object* v_x_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Grind_CommRing_PPoly_powTL(v_p_611_, v_x_612_);
lean_dec(v_x_612_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___redArg(lean_object* v_x_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_){
_start:
{
lean_object* v_zero_617_; uint8_t v_isZero_618_; 
v_zero_617_ = lean_unsigned_to_nat(0u);
v_isZero_618_ = lean_nat_dec_eq(v_x_614_, v_zero_617_);
if (v_isZero_618_ == 1)
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v_h__2_616_);
v___x_619_ = lean_box(0);
v___x_620_ = lean_apply_1(v_h__1_615_, v___x_619_);
return v___x_620_;
}
else
{
lean_object* v_one_621_; lean_object* v_n_622_; lean_object* v___x_623_; 
lean_dec(v_h__1_615_);
v_one_621_ = lean_unsigned_to_nat(1u);
v_n_622_ = lean_nat_sub(v_x_614_, v_one_621_);
v___x_623_ = lean_apply_1(v_h__2_616_, v_n_622_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___redArg___boxed(lean_object* v_x_624_, lean_object* v_h__1_625_, lean_object* v_h__2_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___redArg(v_x_624_, v_h__1_625_, v_h__2_626_);
lean_dec(v_x_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter(lean_object* v_motive_628_, lean_object* v_x_629_, lean_object* v_h__1_630_, lean_object* v_h__2_631_){
_start:
{
lean_object* v_zero_632_; uint8_t v_isZero_633_; 
v_zero_632_ = lean_unsigned_to_nat(0u);
v_isZero_633_ = lean_nat_dec_eq(v_x_629_, v_zero_632_);
if (v_isZero_633_ == 1)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec(v_h__2_631_);
v___x_634_ = lean_box(0);
v___x_635_ = lean_apply_1(v_h__1_630_, v___x_634_);
return v___x_635_;
}
else
{
lean_object* v_one_636_; lean_object* v_n_637_; lean_object* v___x_638_; 
lean_dec(v_h__1_630_);
v_one_636_ = lean_unsigned_to_nat(1u);
v_n_637_ = lean_nat_sub(v_x_629_, v_one_636_);
v___x_638_ = lean_apply_1(v_h__2_631_, v_n_637_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___boxed(lean_object* v_motive_639_, lean_object* v_x_640_, lean_object* v_h__1_641_, lean_object* v_h__2_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter(v_motive_639_, v_x_640_, v_h__1_641_, v_h__2_642_);
lean_dec(v_x_640_);
return v_res_643_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_Packed(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_FieldSolver(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ring_Kronecker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ring_Packed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_FieldSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Ring_Kronecker(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_Packed(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_FieldSolver(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ring_Kronecker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Packed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_FieldSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Kronecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Ring_Kronecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Ring_Kronecker(builtin);
}
#ifdef __cplusplus
}
#endif
