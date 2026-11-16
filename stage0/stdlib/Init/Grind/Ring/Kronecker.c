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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append_addConst(lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
if (lean_obj_tag(v_a_116_) == 0)
{
lean_object* v_k_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
v_k_118_ = lean_ctor_get(v_a_116_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v_a_116_);
if (v_isSharedCheck_126_ == 0)
{
v___x_120_ = v_a_116_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_k_118_);
lean_dec(v_a_116_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = lean_int_add(v_k_118_, v_a_117_);
lean_dec(v_k_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
else
{
lean_object* v_k_127_; lean_object* v_d_128_; lean_object* v_v_129_; lean_object* v_p_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_138_; 
v_k_127_ = lean_ctor_get(v_a_116_, 0);
v_d_128_ = lean_ctor_get(v_a_116_, 1);
v_v_129_ = lean_ctor_get(v_a_116_, 2);
v_p_130_ = lean_ctor_get(v_a_116_, 3);
v_isSharedCheck_138_ = !lean_is_exclusive(v_a_116_);
if (v_isSharedCheck_138_ == 0)
{
v___x_132_ = v_a_116_;
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_p_130_);
lean_inc(v_v_129_);
lean_inc(v_d_128_);
lean_inc(v_k_127_);
lean_dec(v_a_116_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_138_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_134_ = l_Lean_Grind_CommRing_PPoly_append_addConst(v_p_130_, v_a_117_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 3, v___x_134_);
v___x_136_ = v___x_132_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_d_128_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_v_129_);
lean_ctor_set(v_reuseFailAlloc_137_, 3, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append_addConst___boxed(lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Grind_CommRing_PPoly_append_addConst(v_a_139_, v_a_140_);
lean_dec(v_a_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v_k_144_; lean_object* v___x_145_; 
v_k_144_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_k_144_);
lean_dec_ref_known(v_x_142_, 1);
v___x_145_ = l_Lean_Grind_CommRing_PPoly_append_addConst(v_x_143_, v_k_144_);
lean_dec(v_k_144_);
return v___x_145_;
}
else
{
lean_object* v_k_146_; lean_object* v_d_147_; lean_object* v_v_148_; lean_object* v_p_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
v_k_146_ = lean_ctor_get(v_x_142_, 0);
v_d_147_ = lean_ctor_get(v_x_142_, 1);
v_v_148_ = lean_ctor_get(v_x_142_, 2);
v_p_149_ = lean_ctor_get(v_x_142_, 3);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_157_ == 0)
{
v___x_151_ = v_x_142_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_p_149_);
lean_inc(v_v_148_);
lean_inc(v_d_147_);
lean_inc(v_k_146_);
lean_dec(v_x_142_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = l_Lean_Grind_CommRing_PPoly_append(v_p_149_, v_x_143_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 3, v___x_153_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_d_147_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_v_148_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_neg(lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v_k_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_167_; 
v_k_159_ = lean_ctor_get(v_x_158_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_167_ == 0)
{
v___x_161_ = v_x_158_;
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_k_159_);
lean_dec(v_x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = lean_int_neg(v_k_159_);
lean_dec(v_k_159_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v_k_168_; lean_object* v_d_169_; lean_object* v_v_170_; lean_object* v_p_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_180_; 
v_k_168_ = lean_ctor_get(v_x_158_, 0);
v_d_169_ = lean_ctor_get(v_x_158_, 1);
v_v_170_ = lean_ctor_get(v_x_158_, 2);
v_p_171_ = lean_ctor_get(v_x_158_, 3);
v_isSharedCheck_180_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_180_ == 0)
{
v___x_173_ = v_x_158_;
v_isShared_174_ = v_isSharedCheck_180_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_p_171_);
lean_inc(v_v_170_);
lean_inc(v_d_169_);
lean_inc(v_k_168_);
lean_dec(v_x_158_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_180_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_175_ = lean_int_neg(v_k_168_);
lean_dec(v_k_168_);
v___x_176_ = l_Lean_Grind_CommRing_PPoly_neg(v_p_171_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 3, v___x_176_);
lean_ctor_set(v___x_173_, 0, v___x_175_);
v___x_178_ = v___x_173_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_d_169_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_v_170_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_addConst_match__1_splitter___redArg(lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_h__1_183_, lean_object* v_h__2_184_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v_k_185_; lean_object* v___x_186_; 
lean_dec(v_h__2_184_);
v_k_185_ = lean_ctor_get(v_x_181_, 0);
lean_inc(v_k_185_);
lean_dec_ref_known(v_x_181_, 1);
v___x_186_ = lean_apply_2(v_h__1_183_, v_k_185_, v_x_182_);
return v___x_186_;
}
else
{
lean_object* v_k_187_; lean_object* v_d_188_; lean_object* v_v_189_; lean_object* v_p_190_; lean_object* v___x_191_; 
lean_dec(v_h__1_183_);
v_k_187_ = lean_ctor_get(v_x_181_, 0);
lean_inc(v_k_187_);
v_d_188_ = lean_ctor_get(v_x_181_, 1);
lean_inc(v_d_188_);
v_v_189_ = lean_ctor_get(v_x_181_, 2);
lean_inc(v_v_189_);
v_p_190_ = lean_ctor_get(v_x_181_, 3);
lean_inc_ref(v_p_190_);
lean_dec_ref_known(v_x_181_, 4);
v___x_191_ = lean_apply_5(v_h__2_184_, v_k_187_, v_d_188_, v_v_189_, v_p_190_, v_x_182_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_addConst_match__1_splitter(lean_object* v_motive_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_h__1_195_, lean_object* v_h__2_196_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v_k_197_; lean_object* v___x_198_; 
lean_dec(v_h__2_196_);
v_k_197_ = lean_ctor_get(v_x_193_, 0);
lean_inc(v_k_197_);
lean_dec_ref_known(v_x_193_, 1);
v___x_198_ = lean_apply_2(v_h__1_195_, v_k_197_, v_x_194_);
return v___x_198_;
}
else
{
lean_object* v_k_199_; lean_object* v_d_200_; lean_object* v_v_201_; lean_object* v_p_202_; lean_object* v___x_203_; 
lean_dec(v_h__1_195_);
v_k_199_ = lean_ctor_get(v_x_193_, 0);
lean_inc(v_k_199_);
v_d_200_ = lean_ctor_get(v_x_193_, 1);
lean_inc(v_d_200_);
v_v_201_ = lean_ctor_get(v_x_193_, 2);
lean_inc(v_v_201_);
v_p_202_ = lean_ctor_get(v_x_193_, 3);
lean_inc_ref(v_p_202_);
lean_dec_ref_known(v_x_193_, 4);
v___x_203_ = lean_apply_5(v_h__2_196_, v_k_199_, v_d_200_, v_v_201_, v_p_202_, v_x_194_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_match__1_splitter___redArg(lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_h__1_206_, lean_object* v_h__2_207_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
lean_object* v_k_208_; lean_object* v___x_209_; 
lean_dec(v_h__2_207_);
v_k_208_ = lean_ctor_get(v_x_204_, 0);
lean_inc(v_k_208_);
lean_dec_ref_known(v_x_204_, 1);
v___x_209_ = lean_apply_2(v_h__1_206_, v_k_208_, v_x_205_);
return v___x_209_;
}
else
{
lean_object* v_k_210_; lean_object* v_d_211_; lean_object* v_v_212_; lean_object* v_p_213_; lean_object* v___x_214_; 
lean_dec(v_h__1_206_);
v_k_210_ = lean_ctor_get(v_x_204_, 0);
lean_inc(v_k_210_);
v_d_211_ = lean_ctor_get(v_x_204_, 1);
lean_inc(v_d_211_);
v_v_212_ = lean_ctor_get(v_x_204_, 2);
lean_inc(v_v_212_);
v_p_213_ = lean_ctor_get(v_x_204_, 3);
lean_inc_ref(v_p_213_);
lean_dec_ref_known(v_x_204_, 4);
v___x_214_ = lean_apply_5(v_h__2_207_, v_k_210_, v_d_211_, v_v_212_, v_p_213_, v_x_205_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_append_match__1_splitter(lean_object* v_motive_215_, lean_object* v_x_216_, lean_object* v_x_217_, lean_object* v_h__1_218_, lean_object* v_h__2_219_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v_k_220_; lean_object* v___x_221_; 
lean_dec(v_h__2_219_);
v_k_220_ = lean_ctor_get(v_x_216_, 0);
lean_inc(v_k_220_);
lean_dec_ref_known(v_x_216_, 1);
v___x_221_ = lean_apply_2(v_h__1_218_, v_k_220_, v_x_217_);
return v___x_221_;
}
else
{
lean_object* v_k_222_; lean_object* v_d_223_; lean_object* v_v_224_; lean_object* v_p_225_; lean_object* v___x_226_; 
lean_dec(v_h__1_218_);
v_k_222_ = lean_ctor_get(v_x_216_, 0);
lean_inc(v_k_222_);
v_d_223_ = lean_ctor_get(v_x_216_, 1);
lean_inc(v_d_223_);
v_v_224_ = lean_ctor_get(v_x_216_, 2);
lean_inc(v_v_224_);
v_p_225_ = lean_ctor_get(v_x_216_, 3);
lean_inc_ref(v_p_225_);
lean_dec_ref_known(v_x_216_, 4);
v___x_226_ = lean_apply_5(v_h__2_219_, v_k_222_, v_d_223_, v_v_224_, v_p_225_, v_x_217_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0_spec__0(lean_object* v_as_227_, size_t v_i_228_, size_t v_stop_229_, lean_object* v_b_230_){
_start:
{
uint8_t v___x_231_; 
v___x_231_ = lean_usize_dec_eq(v_i_228_, v_stop_229_);
if (v___x_231_ == 0)
{
size_t v___x_232_; size_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_sub(v_i_228_, v___x_232_);
v___x_234_ = lean_array_uget_borrowed(v_as_227_, v___x_233_);
v___x_235_ = l_Lean_Grind_CommRing_PPoly_norm1(v___x_234_);
v___x_236_ = lean_nat_add(v___x_235_, v_b_230_);
lean_dec(v_b_230_);
lean_dec(v___x_235_);
v_i_228_ = v___x_233_;
v_b_230_ = v___x_236_;
goto _start;
}
else
{
return v_b_230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0_spec__0___boxed(lean_object* v_as_238_, lean_object* v_i_239_, lean_object* v_stop_240_, lean_object* v_b_241_){
_start:
{
size_t v_i_boxed_242_; size_t v_stop_boxed_243_; lean_object* v_res_244_; 
v_i_boxed_242_ = lean_unbox_usize(v_i_239_);
lean_dec(v_i_239_);
v_stop_boxed_243_ = lean_unbox_usize(v_stop_240_);
lean_dec(v_stop_240_);
v_res_244_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0_spec__0(v_as_238_, v_i_boxed_242_, v_stop_boxed_243_, v_b_241_);
lean_dec_ref(v_as_238_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(lean_object* v_init_245_, lean_object* v_l_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_247_ = lean_array_mk(v_l_246_);
v___x_248_ = lean_array_get_size(v___x_247_);
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_nat_dec_lt(v___x_249_, v___x_248_);
if (v___x_250_ == 0)
{
lean_dec_ref(v___x_247_);
return v_init_245_;
}
else
{
size_t v___x_251_; size_t v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_usize_of_nat(v___x_248_);
v___x_252_ = ((size_t)0ULL);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0_spec__0(v___x_247_, v___x_251_, v___x_252_, v_init_245_);
lean_dec_ref(v___x_247_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1List(lean_object* v_ps_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = l_List_foldrTR___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(v___x_255_, v_ps_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_denoteG___redArg(lean_object* v_inst_257_, lean_object* v_g_258_, lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v_intCast_260_; lean_object* v_k_261_; lean_object* v___x_262_; 
lean_dec(v_g_258_);
v_intCast_260_ = lean_ctor_get(v_inst_257_, 3);
lean_inc(v_intCast_260_);
lean_dec_ref(v_inst_257_);
v_k_261_ = lean_ctor_get(v_x_259_, 0);
lean_inc(v_k_261_);
lean_dec_ref_known(v_x_259_, 1);
v___x_262_ = lean_apply_1(v_intCast_260_, v_k_261_);
return v___x_262_;
}
else
{
lean_object* v_toSemiring_263_; lean_object* v_intCast_264_; lean_object* v_toAdd_265_; lean_object* v_toMul_266_; lean_object* v_k_267_; lean_object* v_v_268_; lean_object* v_p_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_toSemiring_263_ = lean_ctor_get(v_inst_257_, 0);
v_intCast_264_ = lean_ctor_get(v_inst_257_, 3);
v_toAdd_265_ = lean_ctor_get(v_toSemiring_263_, 0);
lean_inc(v_toAdd_265_);
v_toMul_266_ = lean_ctor_get(v_toSemiring_263_, 1);
v_k_267_ = lean_ctor_get(v_x_259_, 0);
lean_inc(v_k_267_);
v_v_268_ = lean_ctor_get(v_x_259_, 2);
lean_inc(v_v_268_);
v_p_269_ = lean_ctor_get(v_x_259_, 3);
lean_inc_ref(v_p_269_);
lean_dec_ref_known(v_x_259_, 4);
lean_inc(v_intCast_264_);
v___x_270_ = lean_apply_1(v_intCast_264_, v_k_267_);
lean_inc(v_g_258_);
v___x_271_ = lean_apply_1(v_g_258_, v_v_268_);
lean_inc(v_toMul_266_);
v___x_272_ = lean_apply_2(v_toMul_266_, v___x_270_, v___x_271_);
v___x_273_ = l_Lean_Grind_CommRing_PPoly_denoteG___redArg(v_inst_257_, v_g_258_, v_p_269_);
v___x_274_ = lean_apply_2(v_toAdd_265_, v___x_272_, v___x_273_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_denoteG(lean_object* v_00_u03b1_275_, lean_object* v_inst_276_, lean_object* v_g_277_, lean_object* v_x_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Grind_CommRing_PPoly_denoteG___redArg(v_inst_276_, v_g_277_, v_x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_scale(lean_object* v_k_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_k_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_290_; 
v_k_282_ = lean_ctor_get(v_x_281_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_290_ == 0)
{
v___x_284_ = v_x_281_;
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_k_282_);
lean_dec(v_x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_290_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = lean_int_mul(v_k_280_, v_k_282_);
lean_dec(v_k_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_286_);
v___x_288_ = v___x_284_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
else
{
lean_object* v_k_291_; lean_object* v_d_292_; lean_object* v_v_293_; lean_object* v_p_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_303_; 
v_k_291_ = lean_ctor_get(v_x_281_, 0);
v_d_292_ = lean_ctor_get(v_x_281_, 1);
v_v_293_ = lean_ctor_get(v_x_281_, 2);
v_p_294_ = lean_ctor_get(v_x_281_, 3);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_303_ == 0)
{
v___x_296_ = v_x_281_;
v_isShared_297_ = v_isSharedCheck_303_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_p_294_);
lean_inc(v_v_293_);
lean_inc(v_d_292_);
lean_inc(v_k_291_);
lean_dec(v_x_281_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_303_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_298_ = lean_int_mul(v_k_280_, v_k_291_);
lean_dec(v_k_291_);
v___x_299_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_280_, v_p_294_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 3, v___x_299_);
lean_ctor_set(v___x_296_, 0, v___x_298_);
v___x_301_ = v___x_296_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_d_292_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_v_293_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_scale___boxed(lean_object* v_k_304_, lean_object* v_x_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_304_, v_x_305_);
lean_dec(v_k_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Expr_evalConst_spec__0(lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lean_nat_to_int(v_a_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_evalConst(lean_object* v_x_309_){
_start:
{
switch(lean_obj_tag(v_x_309_))
{
case 1:
{
lean_object* v_k_310_; lean_object* v___x_311_; 
v_k_310_ = lean_ctor_get(v_x_309_, 0);
lean_inc(v_k_310_);
lean_dec_ref_known(v_x_309_, 1);
v___x_311_ = lean_nat_to_int(v_k_310_);
return v___x_311_;
}
case 3:
{
lean_object* v___x_312_; 
lean_dec_ref_known(v_x_309_, 1);
v___x_312_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_coeff___closed__0, &l_Lean_Grind_CommRing_PPoly_coeff___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_coeff___closed__0);
return v___x_312_;
}
case 4:
{
lean_object* v_a_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_a_313_ = lean_ctor_get(v_x_309_, 0);
lean_inc_ref(v_a_313_);
lean_dec_ref_known(v_x_309_, 1);
v___x_314_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_313_);
v___x_315_ = lean_int_neg(v___x_314_);
lean_dec(v___x_314_);
return v___x_315_;
}
case 5:
{
lean_object* v_a_316_; lean_object* v_b_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_a_316_ = lean_ctor_get(v_x_309_, 0);
lean_inc_ref(v_a_316_);
v_b_317_ = lean_ctor_get(v_x_309_, 1);
lean_inc_ref(v_b_317_);
lean_dec_ref_known(v_x_309_, 2);
v___x_318_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_316_);
v___x_319_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_317_);
v___x_320_ = lean_int_add(v___x_318_, v___x_319_);
lean_dec(v___x_319_);
lean_dec(v___x_318_);
return v___x_320_;
}
case 6:
{
lean_object* v_a_321_; lean_object* v_b_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_a_321_ = lean_ctor_get(v_x_309_, 0);
lean_inc_ref(v_a_321_);
v_b_322_ = lean_ctor_get(v_x_309_, 1);
lean_inc_ref(v_b_322_);
lean_dec_ref_known(v_x_309_, 2);
v___x_323_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_321_);
v___x_324_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_322_);
v___x_325_ = lean_int_sub(v___x_323_, v___x_324_);
lean_dec(v___x_324_);
lean_dec(v___x_323_);
return v___x_325_;
}
case 7:
{
lean_object* v_a_326_; lean_object* v_b_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_a_326_ = lean_ctor_get(v_x_309_, 0);
lean_inc_ref(v_a_326_);
v_b_327_ = lean_ctor_get(v_x_309_, 1);
lean_inc_ref(v_b_327_);
lean_dec_ref_known(v_x_309_, 2);
v___x_328_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_326_);
v___x_329_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_327_);
v___x_330_ = lean_int_mul(v___x_328_, v___x_329_);
lean_dec(v___x_329_);
lean_dec(v___x_328_);
return v___x_330_;
}
case 8:
{
lean_object* v_a_331_; lean_object* v_k_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_a_331_ = lean_ctor_get(v_x_309_, 0);
lean_inc_ref(v_a_331_);
v_k_332_ = lean_ctor_get(v_x_309_, 1);
lean_inc(v_k_332_);
lean_dec_ref_known(v_x_309_, 2);
v___x_333_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_331_);
v___x_334_ = l_Int_pow(v___x_333_, v_k_332_);
lean_dec(v_k_332_);
lean_dec(v___x_333_);
return v___x_334_;
}
default: 
{
lean_object* v_k_335_; 
v_k_335_ = lean_ctor_get(v_x_309_, 0);
lean_inc(v_k_335_);
lean_dec_ref(v_x_309_);
return v_k_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___redArg(lean_object* v_inst_336_, lean_object* v_f_337_, lean_object* v_v_338_){
_start:
{
lean_object* v_toSemiring_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_toSemiring_339_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toSemiring_339_);
lean_dec_ref(v_inst_336_);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_nat_dec_eq(v_v_338_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec_ref(v_toSemiring_339_);
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_sub(v_v_338_, v___x_342_);
v___x_344_ = lean_apply_1(v_f_337_, v___x_343_);
return v___x_344_;
}
else
{
lean_object* v_ofNat_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec(v_f_337_);
v_ofNat_345_ = lean_ctor_get(v_toSemiring_339_, 3);
lean_inc(v_ofNat_345_);
lean_dec_ref(v_toSemiring_339_);
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_apply_1(v_ofNat_345_, v___x_346_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___redArg___boxed(lean_object* v_inst_348_, lean_object* v_f_349_, lean_object* v_v_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Grind_CommRing_PPoly_linVal___redArg(v_inst_348_, v_f_349_, v_v_350_);
lean_dec(v_v_350_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal(lean_object* v_00_u03b1_352_, lean_object* v_inst_353_, lean_object* v_f_354_, lean_object* v_v_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Grind_CommRing_PPoly_linVal___redArg(v_inst_353_, v_f_354_, v_v_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___boxed(lean_object* v_00_u03b1_357_, lean_object* v_inst_358_, lean_object* v_f_359_, lean_object* v_v_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Grind_CommRing_PPoly_linVal(v_00_u03b1_357_, v_inst_358_, v_f_359_, v_v_360_);
lean_dec(v_v_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorIdx___impl(lean_object* v_x_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_obj_tag_nat(v_x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorIdx___impl___boxed(lean_object* v_x_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Grind_CommRing_KList_ctorIdx___impl(v_x_364_);
lean_dec(v_x_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim___redArg(lean_object* v_t_366_, lean_object* v_k_367_){
_start:
{
if (lean_obj_tag(v_t_366_) == 0)
{
return v_k_367_;
}
else
{
lean_object* v_k_368_; lean_object* v_m_369_; lean_object* v_q_370_; lean_object* v_ls_371_; lean_object* v___x_372_; 
v_k_368_ = lean_ctor_get(v_t_366_, 0);
lean_inc(v_k_368_);
v_m_369_ = lean_ctor_get(v_t_366_, 1);
lean_inc(v_m_369_);
v_q_370_ = lean_ctor_get(v_t_366_, 2);
lean_inc_ref(v_q_370_);
v_ls_371_ = lean_ctor_get(v_t_366_, 3);
lean_inc(v_ls_371_);
lean_dec_ref_known(v_t_366_, 4);
v___x_372_ = lean_apply_4(v_k_367_, v_k_368_, v_m_369_, v_q_370_, v_ls_371_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim(lean_object* v_motive_373_, lean_object* v_ctorIdx_374_, lean_object* v_t_375_, lean_object* v_h_376_, lean_object* v_k_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_375_, v_k_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim___boxed(lean_object* v_motive_379_, lean_object* v_ctorIdx_380_, lean_object* v_t_381_, lean_object* v_h_382_, lean_object* v_k_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Grind_CommRing_KList_ctorElim(v_motive_379_, v_ctorIdx_380_, v_t_381_, v_h_382_, v_k_383_);
lean_dec(v_ctorIdx_380_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_nil_elim___redArg(lean_object* v_t_385_, lean_object* v_nil_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_385_, v_nil_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_nil_elim(lean_object* v_motive_388_, lean_object* v_t_389_, lean_object* v_h_390_, lean_object* v_nil_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_389_, v_nil_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_cons_elim___redArg(lean_object* v_t_393_, lean_object* v_cons_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_393_, v_cons_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_cons_elim(lean_object* v_motive_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_cons_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_397_, v_cons_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorIdx___impl(lean_object* v_x_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lean_obj_tag_nat(v_x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorIdx___impl___boxed(lean_object* v_x_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Grind_CommRing_MList_ctorIdx___impl(v_x_403_);
lean_dec(v_x_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim___redArg(lean_object* v_t_405_, lean_object* v_k_406_){
_start:
{
if (lean_obj_tag(v_t_405_) == 0)
{
return v_k_406_;
}
else
{
lean_object* v_M_407_; lean_object* v_q_408_; lean_object* v_ls_409_; lean_object* v___x_410_; 
v_M_407_ = lean_ctor_get(v_t_405_, 0);
lean_inc_ref(v_M_407_);
v_q_408_ = lean_ctor_get(v_t_405_, 1);
lean_inc_ref(v_q_408_);
v_ls_409_ = lean_ctor_get(v_t_405_, 2);
lean_inc(v_ls_409_);
lean_dec_ref_known(v_t_405_, 3);
v___x_410_ = lean_apply_3(v_k_406_, v_M_407_, v_q_408_, v_ls_409_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim(lean_object* v_motive_411_, lean_object* v_ctorIdx_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_k_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_413_, v_k_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim___boxed(lean_object* v_motive_417_, lean_object* v_ctorIdx_418_, lean_object* v_t_419_, lean_object* v_h_420_, lean_object* v_k_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Grind_CommRing_MList_ctorElim(v_motive_417_, v_ctorIdx_418_, v_t_419_, v_h_420_, v_k_421_);
lean_dec(v_ctorIdx_418_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_nil_elim___redArg(lean_object* v_t_423_, lean_object* v_nil_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_423_, v_nil_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_nil_elim(lean_object* v_motive_426_, lean_object* v_t_427_, lean_object* v_h_428_, lean_object* v_nil_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_427_, v_nil_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_cons_elim___redArg(lean_object* v_t_431_, lean_object* v_cons_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_431_, v_cons_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_cons_elim(lean_object* v_motive_434_, lean_object* v_t_435_, lean_object* v_h_436_, lean_object* v_cons_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_435_, v_cons_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_evalConst_match__1_splitter___redArg(lean_object* v_x_439_, lean_object* v_h__1_440_, lean_object* v_h__2_441_, lean_object* v_h__3_442_, lean_object* v_h__4_443_, lean_object* v_h__5_444_, lean_object* v_h__6_445_, lean_object* v_h__7_446_, lean_object* v_h__8_447_, lean_object* v_h__9_448_){
_start:
{
switch(lean_obj_tag(v_x_439_))
{
case 0:
{
lean_object* v_k_449_; lean_object* v___x_450_; 
lean_dec(v_h__9_448_);
lean_dec(v_h__8_447_);
lean_dec(v_h__7_446_);
lean_dec(v_h__6_445_);
lean_dec(v_h__5_444_);
lean_dec(v_h__4_443_);
lean_dec(v_h__3_442_);
lean_dec(v_h__2_441_);
v_k_449_ = lean_ctor_get(v_x_439_, 0);
lean_inc(v_k_449_);
lean_dec_ref_known(v_x_439_, 1);
v___x_450_ = lean_apply_1(v_h__1_440_, v_k_449_);
return v___x_450_;
}
case 1:
{
lean_object* v_k_451_; lean_object* v___x_452_; 
lean_dec(v_h__9_448_);
lean_dec(v_h__8_447_);
lean_dec(v_h__7_446_);
lean_dec(v_h__6_445_);
lean_dec(v_h__5_444_);
lean_dec(v_h__4_443_);
lean_dec(v_h__2_441_);
lean_dec(v_h__1_440_);
v_k_451_ = lean_ctor_get(v_x_439_, 0);
lean_inc(v_k_451_);
lean_dec_ref_known(v_x_439_, 1);
v___x_452_ = lean_apply_1(v_h__3_442_, v_k_451_);
return v___x_452_;
}
case 2:
{
lean_object* v_k_453_; lean_object* v___x_454_; 
lean_dec(v_h__9_448_);
lean_dec(v_h__8_447_);
lean_dec(v_h__7_446_);
lean_dec(v_h__6_445_);
lean_dec(v_h__5_444_);
lean_dec(v_h__4_443_);
lean_dec(v_h__3_442_);
lean_dec(v_h__1_440_);
v_k_453_ = lean_ctor_get(v_x_439_, 0);
lean_inc(v_k_453_);
lean_dec_ref_known(v_x_439_, 1);
v___x_454_ = lean_apply_1(v_h__2_441_, v_k_453_);
return v___x_454_;
}
case 3:
{
lean_object* v_i_455_; lean_object* v___x_456_; 
lean_dec(v_h__9_448_);
lean_dec(v_h__8_447_);
lean_dec(v_h__7_446_);
lean_dec(v_h__6_445_);
lean_dec(v_h__5_444_);
lean_dec(v_h__3_442_);
lean_dec(v_h__2_441_);
lean_dec(v_h__1_440_);
v_i_455_ = lean_ctor_get(v_x_439_, 0);
lean_inc(v_i_455_);
lean_dec_ref_known(v_x_439_, 1);
v___x_456_ = lean_apply_1(v_h__4_443_, v_i_455_);
return v___x_456_;
}
case 4:
{
lean_object* v_a_457_; lean_object* v___x_458_; 
lean_dec(v_h__9_448_);
lean_dec(v_h__8_447_);
lean_dec(v_h__7_446_);
lean_dec(v_h__6_445_);
lean_dec(v_h__4_443_);
lean_dec(v_h__3_442_);
lean_dec(v_h__2_441_);
lean_dec(v_h__1_440_);
v_a_457_ = lean_ctor_get(v_x_439_, 0);
lean_inc_ref(v_a_457_);
lean_dec_ref_known(v_x_439_, 1);
v___x_458_ = lean_apply_1(v_h__5_444_, v_a_457_);
return v___x_458_;
}
case 5:
{
lean_object* v_a_459_; lean_object* v_b_460_; lean_object* v___x_461_; 
lean_dec(v_h__9_448_);
lean_dec(v_h__8_447_);
lean_dec(v_h__7_446_);
lean_dec(v_h__5_444_);
lean_dec(v_h__4_443_);
lean_dec(v_h__3_442_);
lean_dec(v_h__2_441_);
lean_dec(v_h__1_440_);
v_a_459_ = lean_ctor_get(v_x_439_, 0);
lean_inc_ref(v_a_459_);
v_b_460_ = lean_ctor_get(v_x_439_, 1);
lean_inc_ref(v_b_460_);
lean_dec_ref_known(v_x_439_, 2);
v___x_461_ = lean_apply_2(v_h__6_445_, v_a_459_, v_b_460_);
return v___x_461_;
}
case 6:
{
lean_object* v_a_462_; lean_object* v_b_463_; lean_object* v___x_464_; 
lean_dec(v_h__9_448_);
lean_dec(v_h__8_447_);
lean_dec(v_h__6_445_);
lean_dec(v_h__5_444_);
lean_dec(v_h__4_443_);
lean_dec(v_h__3_442_);
lean_dec(v_h__2_441_);
lean_dec(v_h__1_440_);
v_a_462_ = lean_ctor_get(v_x_439_, 0);
lean_inc_ref(v_a_462_);
v_b_463_ = lean_ctor_get(v_x_439_, 1);
lean_inc_ref(v_b_463_);
lean_dec_ref_known(v_x_439_, 2);
v___x_464_ = lean_apply_2(v_h__7_446_, v_a_462_, v_b_463_);
return v___x_464_;
}
case 7:
{
lean_object* v_a_465_; lean_object* v_b_466_; lean_object* v___x_467_; 
lean_dec(v_h__9_448_);
lean_dec(v_h__7_446_);
lean_dec(v_h__6_445_);
lean_dec(v_h__5_444_);
lean_dec(v_h__4_443_);
lean_dec(v_h__3_442_);
lean_dec(v_h__2_441_);
lean_dec(v_h__1_440_);
v_a_465_ = lean_ctor_get(v_x_439_, 0);
lean_inc_ref(v_a_465_);
v_b_466_ = lean_ctor_get(v_x_439_, 1);
lean_inc_ref(v_b_466_);
lean_dec_ref_known(v_x_439_, 2);
v___x_467_ = lean_apply_2(v_h__8_447_, v_a_465_, v_b_466_);
return v___x_467_;
}
default: 
{
lean_object* v_a_468_; lean_object* v_k_469_; lean_object* v___x_470_; 
lean_dec(v_h__8_447_);
lean_dec(v_h__7_446_);
lean_dec(v_h__6_445_);
lean_dec(v_h__5_444_);
lean_dec(v_h__4_443_);
lean_dec(v_h__3_442_);
lean_dec(v_h__2_441_);
lean_dec(v_h__1_440_);
v_a_468_ = lean_ctor_get(v_x_439_, 0);
lean_inc_ref(v_a_468_);
v_k_469_ = lean_ctor_get(v_x_439_, 1);
lean_inc(v_k_469_);
lean_dec_ref_known(v_x_439_, 2);
v___x_470_ = lean_apply_2(v_h__9_448_, v_a_468_, v_k_469_);
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_evalConst_match__1_splitter(lean_object* v_motive_471_, lean_object* v_x_472_, lean_object* v_h__1_473_, lean_object* v_h__2_474_, lean_object* v_h__3_475_, lean_object* v_h__4_476_, lean_object* v_h__5_477_, lean_object* v_h__6_478_, lean_object* v_h__7_479_, lean_object* v_h__8_480_, lean_object* v_h__9_481_){
_start:
{
switch(lean_obj_tag(v_x_472_))
{
case 0:
{
lean_object* v_k_482_; lean_object* v___x_483_; 
lean_dec(v_h__9_481_);
lean_dec(v_h__8_480_);
lean_dec(v_h__7_479_);
lean_dec(v_h__6_478_);
lean_dec(v_h__5_477_);
lean_dec(v_h__4_476_);
lean_dec(v_h__3_475_);
lean_dec(v_h__2_474_);
v_k_482_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_k_482_);
lean_dec_ref_known(v_x_472_, 1);
v___x_483_ = lean_apply_1(v_h__1_473_, v_k_482_);
return v___x_483_;
}
case 1:
{
lean_object* v_k_484_; lean_object* v___x_485_; 
lean_dec(v_h__9_481_);
lean_dec(v_h__8_480_);
lean_dec(v_h__7_479_);
lean_dec(v_h__6_478_);
lean_dec(v_h__5_477_);
lean_dec(v_h__4_476_);
lean_dec(v_h__2_474_);
lean_dec(v_h__1_473_);
v_k_484_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_k_484_);
lean_dec_ref_known(v_x_472_, 1);
v___x_485_ = lean_apply_1(v_h__3_475_, v_k_484_);
return v___x_485_;
}
case 2:
{
lean_object* v_k_486_; lean_object* v___x_487_; 
lean_dec(v_h__9_481_);
lean_dec(v_h__8_480_);
lean_dec(v_h__7_479_);
lean_dec(v_h__6_478_);
lean_dec(v_h__5_477_);
lean_dec(v_h__4_476_);
lean_dec(v_h__3_475_);
lean_dec(v_h__1_473_);
v_k_486_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_k_486_);
lean_dec_ref_known(v_x_472_, 1);
v___x_487_ = lean_apply_1(v_h__2_474_, v_k_486_);
return v___x_487_;
}
case 3:
{
lean_object* v_i_488_; lean_object* v___x_489_; 
lean_dec(v_h__9_481_);
lean_dec(v_h__8_480_);
lean_dec(v_h__7_479_);
lean_dec(v_h__6_478_);
lean_dec(v_h__5_477_);
lean_dec(v_h__3_475_);
lean_dec(v_h__2_474_);
lean_dec(v_h__1_473_);
v_i_488_ = lean_ctor_get(v_x_472_, 0);
lean_inc(v_i_488_);
lean_dec_ref_known(v_x_472_, 1);
v___x_489_ = lean_apply_1(v_h__4_476_, v_i_488_);
return v___x_489_;
}
case 4:
{
lean_object* v_a_490_; lean_object* v___x_491_; 
lean_dec(v_h__9_481_);
lean_dec(v_h__8_480_);
lean_dec(v_h__7_479_);
lean_dec(v_h__6_478_);
lean_dec(v_h__4_476_);
lean_dec(v_h__3_475_);
lean_dec(v_h__2_474_);
lean_dec(v_h__1_473_);
v_a_490_ = lean_ctor_get(v_x_472_, 0);
lean_inc_ref(v_a_490_);
lean_dec_ref_known(v_x_472_, 1);
v___x_491_ = lean_apply_1(v_h__5_477_, v_a_490_);
return v___x_491_;
}
case 5:
{
lean_object* v_a_492_; lean_object* v_b_493_; lean_object* v___x_494_; 
lean_dec(v_h__9_481_);
lean_dec(v_h__8_480_);
lean_dec(v_h__7_479_);
lean_dec(v_h__5_477_);
lean_dec(v_h__4_476_);
lean_dec(v_h__3_475_);
lean_dec(v_h__2_474_);
lean_dec(v_h__1_473_);
v_a_492_ = lean_ctor_get(v_x_472_, 0);
lean_inc_ref(v_a_492_);
v_b_493_ = lean_ctor_get(v_x_472_, 1);
lean_inc_ref(v_b_493_);
lean_dec_ref_known(v_x_472_, 2);
v___x_494_ = lean_apply_2(v_h__6_478_, v_a_492_, v_b_493_);
return v___x_494_;
}
case 6:
{
lean_object* v_a_495_; lean_object* v_b_496_; lean_object* v___x_497_; 
lean_dec(v_h__9_481_);
lean_dec(v_h__8_480_);
lean_dec(v_h__6_478_);
lean_dec(v_h__5_477_);
lean_dec(v_h__4_476_);
lean_dec(v_h__3_475_);
lean_dec(v_h__2_474_);
lean_dec(v_h__1_473_);
v_a_495_ = lean_ctor_get(v_x_472_, 0);
lean_inc_ref(v_a_495_);
v_b_496_ = lean_ctor_get(v_x_472_, 1);
lean_inc_ref(v_b_496_);
lean_dec_ref_known(v_x_472_, 2);
v___x_497_ = lean_apply_2(v_h__7_479_, v_a_495_, v_b_496_);
return v___x_497_;
}
case 7:
{
lean_object* v_a_498_; lean_object* v_b_499_; lean_object* v___x_500_; 
lean_dec(v_h__9_481_);
lean_dec(v_h__7_479_);
lean_dec(v_h__6_478_);
lean_dec(v_h__5_477_);
lean_dec(v_h__4_476_);
lean_dec(v_h__3_475_);
lean_dec(v_h__2_474_);
lean_dec(v_h__1_473_);
v_a_498_ = lean_ctor_get(v_x_472_, 0);
lean_inc_ref(v_a_498_);
v_b_499_ = lean_ctor_get(v_x_472_, 1);
lean_inc_ref(v_b_499_);
lean_dec_ref_known(v_x_472_, 2);
v___x_500_ = lean_apply_2(v_h__8_480_, v_a_498_, v_b_499_);
return v___x_500_;
}
default: 
{
lean_object* v_a_501_; lean_object* v_k_502_; lean_object* v___x_503_; 
lean_dec(v_h__8_480_);
lean_dec(v_h__7_479_);
lean_dec(v_h__6_478_);
lean_dec(v_h__5_477_);
lean_dec(v_h__4_476_);
lean_dec(v_h__3_475_);
lean_dec(v_h__2_474_);
lean_dec(v_h__1_473_);
v_a_501_ = lean_ctor_get(v_x_472_, 0);
lean_inc_ref(v_a_501_);
v_k_502_ = lean_ctor_get(v_x_472_, 1);
lean_inc(v_k_502_);
lean_dec_ref_known(v_x_472_, 2);
v___x_503_ = lean_apply_2(v_h__9_481_, v_a_501_, v_k_502_);
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_toPPQ_match__1_splitter___redArg(lean_object* v_x_504_, lean_object* v_h__1_505_, lean_object* v_h__2_506_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v_h__1_505_);
v___x_507_ = lean_box(0);
v___x_508_ = lean_apply_1(v_h__2_506_, v___x_507_);
return v___x_508_;
}
else
{
lean_object* v_val_509_; lean_object* v___x_510_; 
lean_dec(v_h__2_506_);
v_val_509_ = lean_ctor_get(v_x_504_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v_x_504_, 1);
v___x_510_ = lean_apply_1(v_h__1_505_, v_val_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_toPPQ_match__1_splitter(lean_object* v_motive_511_, lean_object* v_x_512_, lean_object* v_h__1_513_, lean_object* v_h__2_514_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v_h__1_513_);
v___x_515_ = lean_box(0);
v___x_516_ = lean_apply_1(v_h__2_514_, v___x_515_);
return v___x_516_;
}
else
{
lean_object* v_val_517_; lean_object* v___x_518_; 
lean_dec(v_h__2_514_);
v_val_517_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v_x_512_, 1);
v___x_518_ = lean_apply_1(v_h__1_513_, v_val_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL(lean_object* v_k_519_, lean_object* v_d_520_, lean_object* v_v_521_, lean_object* v_x_522_){
_start:
{
if (lean_obj_tag(v_x_522_) == 0)
{
lean_object* v_k_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_k_523_ = lean_ctor_get(v_x_522_, 0);
lean_inc(v_k_523_);
lean_dec_ref_known(v_x_522_, 1);
v___x_524_ = lean_int_mul(v_k_519_, v_k_523_);
lean_dec(v_k_523_);
v___x_525_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_removeCode___closed__0, &l_Lean_Grind_CommRing_PPoly_removeCode___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_removeCode___closed__0);
v___x_526_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v_d_520_);
lean_ctor_set(v___x_526_, 2, v_v_521_);
lean_ctor_set(v___x_526_, 3, v___x_525_);
return v___x_526_;
}
else
{
lean_object* v_k_527_; lean_object* v_d_528_; lean_object* v_v_529_; lean_object* v_p_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_541_; 
v_k_527_ = lean_ctor_get(v_x_522_, 0);
v_d_528_ = lean_ctor_get(v_x_522_, 1);
v_v_529_ = lean_ctor_get(v_x_522_, 2);
v_p_530_ = lean_ctor_get(v_x_522_, 3);
v_isSharedCheck_541_ = !lean_is_exclusive(v_x_522_);
if (v_isSharedCheck_541_ == 0)
{
v___x_532_ = v_x_522_;
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_p_530_);
lean_inc(v_v_529_);
lean_inc(v_d_528_);
lean_inc(v_k_527_);
lean_dec(v_x_522_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_534_ = lean_int_mul(v_k_519_, v_k_527_);
lean_dec(v_k_527_);
v___x_535_ = lean_nat_add(v_d_520_, v_d_528_);
lean_dec(v_d_528_);
v___x_536_ = lean_nat_add(v_v_521_, v_v_529_);
lean_dec(v_v_529_);
v___x_537_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_519_, v_d_520_, v_v_521_, v_p_530_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 3, v___x_537_);
lean_ctor_set(v___x_532_, 2, v___x_536_);
lean_ctor_set(v___x_532_, 1, v___x_535_);
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_539_ = v___x_532_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_540_, 3, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL___boxed(lean_object* v_k_542_, lean_object* v_d_543_, lean_object* v_v_544_, lean_object* v_x_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_542_, v_d_543_, v_v_544_, v_x_545_);
lean_dec(v_k_542_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTL(lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
lean_object* v_k_549_; lean_object* v___x_550_; 
v_k_549_ = lean_ctor_get(v_x_547_, 0);
lean_inc(v_k_549_);
lean_dec_ref_known(v_x_547_, 1);
v___x_550_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_549_, v_x_548_);
lean_dec(v_k_549_);
return v___x_550_;
}
else
{
lean_object* v_k_551_; lean_object* v_d_552_; lean_object* v_v_553_; lean_object* v_p_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_k_551_ = lean_ctor_get(v_x_547_, 0);
lean_inc(v_k_551_);
v_d_552_ = lean_ctor_get(v_x_547_, 1);
lean_inc(v_d_552_);
v_v_553_ = lean_ctor_get(v_x_547_, 2);
lean_inc(v_v_553_);
v_p_554_ = lean_ctor_get(v_x_547_, 3);
lean_inc_ref(v_p_554_);
lean_dec_ref_known(v_x_547_, 4);
lean_inc_ref(v_x_548_);
v___x_555_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_551_, v_d_552_, v_v_553_, v_x_548_);
lean_dec(v_k_551_);
v___x_556_ = l_Lean_Grind_CommRing_PPoly_mulTL(v_p_554_, v_x_548_);
v___x_557_ = l_Lean_Grind_CommRing_PPoly_append(v___x_555_, v___x_556_);
return v___x_557_;
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__0(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_to_int(v___x_558_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__1(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_powTL___closed__0, &l_Lean_Grind_CommRing_PPoly_powTL___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__0);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL(lean_object* v_p_562_, lean_object* v_x_563_){
_start:
{
lean_object* v_zero_564_; uint8_t v_isZero_565_; 
v_zero_564_ = lean_unsigned_to_nat(0u);
v_isZero_565_ = lean_nat_dec_eq(v_x_563_, v_zero_564_);
if (v_isZero_565_ == 1)
{
lean_object* v___x_566_; 
lean_dec_ref(v_p_562_);
v___x_566_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_powTL___closed__1, &l_Lean_Grind_CommRing_PPoly_powTL___closed__1_once, _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__1);
return v___x_566_;
}
else
{
lean_object* v_one_567_; lean_object* v_n_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_one_567_ = lean_unsigned_to_nat(1u);
v_n_568_ = lean_nat_sub(v_x_563_, v_one_567_);
lean_inc_ref(v_p_562_);
v___x_569_ = l_Lean_Grind_CommRing_PPoly_powTL(v_p_562_, v_n_568_);
lean_dec(v_n_568_);
v___x_570_ = l_Lean_Grind_CommRing_PPoly_mulTL(v___x_569_, v_p_562_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL___boxed(lean_object* v_p_571_, lean_object* v_x_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Grind_CommRing_PPoly_powTL(v_p_571_, v_x_572_);
lean_dec(v_x_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___redArg(lean_object* v_x_574_, lean_object* v_h__1_575_, lean_object* v_h__2_576_){
_start:
{
lean_object* v_zero_577_; uint8_t v_isZero_578_; 
v_zero_577_ = lean_unsigned_to_nat(0u);
v_isZero_578_ = lean_nat_dec_eq(v_x_574_, v_zero_577_);
if (v_isZero_578_ == 1)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_h__2_576_);
v___x_579_ = lean_box(0);
v___x_580_ = lean_apply_1(v_h__1_575_, v___x_579_);
return v___x_580_;
}
else
{
lean_object* v_one_581_; lean_object* v_n_582_; lean_object* v___x_583_; 
lean_dec(v_h__1_575_);
v_one_581_ = lean_unsigned_to_nat(1u);
v_n_582_ = lean_nat_sub(v_x_574_, v_one_581_);
v___x_583_ = lean_apply_1(v_h__2_576_, v_n_582_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___redArg___boxed(lean_object* v_x_584_, lean_object* v_h__1_585_, lean_object* v_h__2_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___redArg(v_x_584_, v_h__1_585_, v_h__2_586_);
lean_dec(v_x_584_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter(lean_object* v_motive_588_, lean_object* v_x_589_, lean_object* v_h__1_590_, lean_object* v_h__2_591_){
_start:
{
lean_object* v_zero_592_; uint8_t v_isZero_593_; 
v_zero_592_ = lean_unsigned_to_nat(0u);
v_isZero_593_ = lean_nat_dec_eq(v_x_589_, v_zero_592_);
if (v_isZero_593_ == 1)
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v_h__2_591_);
v___x_594_ = lean_box(0);
v___x_595_ = lean_apply_1(v_h__1_590_, v___x_594_);
return v___x_595_;
}
else
{
lean_object* v_one_596_; lean_object* v_n_597_; lean_object* v___x_598_; 
lean_dec(v_h__1_590_);
v_one_596_ = lean_unsigned_to_nat(1u);
v_n_597_ = lean_nat_sub(v_x_589_, v_one_596_);
v___x_598_ = lean_apply_1(v_h__2_591_, v_n_597_);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___boxed(lean_object* v_motive_599_, lean_object* v_x_600_, lean_object* v_h__1_601_, lean_object* v_h__2_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter(v_motive_599_, v_x_600_, v_h__1_601_, v_h__2_602_);
lean_dec(v_x_600_);
return v_res_603_;
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
