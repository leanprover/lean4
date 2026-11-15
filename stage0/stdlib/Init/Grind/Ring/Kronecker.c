// Lean compiler output
// Module: Init.Grind.Ring.Kronecker
// Imports: public import Init.Grind.Ring.Packed public import Init.Grind.Ring.FieldSolver import Init.Omega import Init.ByCases import Init.Data.Int.Order import Init.Data.Int.LemmasAux import Init.Data.Nat.Lemmas import Init.Data.Nat.Bitwise.Lemmas
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
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1List(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1List___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Option_elim_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Option_elim_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(lean_object* v_init_227_, lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_inc(v_init_227_);
return v_init_227_;
}
else
{
lean_object* v_head_229_; lean_object* v_tail_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_head_229_ = lean_ctor_get(v_x_228_, 0);
v_tail_230_ = lean_ctor_get(v_x_228_, 1);
v___x_231_ = l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(v_init_227_, v_tail_230_);
v___x_232_ = l_Lean_Grind_CommRing_PPoly_norm1(v_head_229_);
v___x_233_ = lean_nat_add(v___x_232_, v___x_231_);
lean_dec(v___x_231_);
lean_dec(v___x_232_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0___boxed(lean_object* v_init_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(v_init_234_, v_x_235_);
lean_dec(v_x_235_);
lean_dec(v_init_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1List(lean_object* v_ps_237_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(v___x_238_, v_ps_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1List___boxed(lean_object* v_ps_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Grind_CommRing_PPoly_norm1List(v_ps_240_);
lean_dec(v_ps_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Option_elim_match__1_splitter___redArg(lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_h__1_245_, lean_object* v_h__2_246_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_object* v___x_247_; 
lean_dec(v_h__1_245_);
v___x_247_ = lean_apply_2(v_h__2_246_, v_x_243_, v_x_244_);
return v___x_247_;
}
else
{
lean_object* v_val_248_; lean_object* v___x_249_; 
lean_dec(v_h__2_246_);
v_val_248_ = lean_ctor_get(v_x_242_, 0);
lean_inc(v_val_248_);
lean_dec_ref_known(v_x_242_, 1);
v___x_249_ = lean_apply_3(v_h__1_245_, v_val_248_, v_x_243_, v_x_244_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Option_elim_match__1_splitter(lean_object* v_00_u03b1_250_, lean_object* v_00_u03b2_251_, lean_object* v_motive_252_, lean_object* v_x_253_, lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v_h__1_256_, lean_object* v_h__2_257_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
lean_object* v___x_258_; 
lean_dec(v_h__1_256_);
v___x_258_ = lean_apply_2(v_h__2_257_, v_x_254_, v_x_255_);
return v___x_258_;
}
else
{
lean_object* v_val_259_; lean_object* v___x_260_; 
lean_dec(v_h__2_257_);
v_val_259_ = lean_ctor_get(v_x_253_, 0);
lean_inc(v_val_259_);
lean_dec_ref_known(v_x_253_, 1);
v___x_260_ = lean_apply_3(v_h__1_256_, v_val_259_, v_x_254_, v_x_255_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_denoteG___redArg(lean_object* v_inst_261_, lean_object* v_g_262_, lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v_intCast_264_; lean_object* v_k_265_; lean_object* v___x_266_; 
lean_dec(v_g_262_);
v_intCast_264_ = lean_ctor_get(v_inst_261_, 3);
lean_inc(v_intCast_264_);
lean_dec_ref(v_inst_261_);
v_k_265_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_k_265_);
lean_dec_ref_known(v_x_263_, 1);
v___x_266_ = lean_apply_1(v_intCast_264_, v_k_265_);
return v___x_266_;
}
else
{
lean_object* v_toSemiring_267_; lean_object* v_intCast_268_; lean_object* v_toAdd_269_; lean_object* v_toMul_270_; lean_object* v_k_271_; lean_object* v_v_272_; lean_object* v_p_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_toSemiring_267_ = lean_ctor_get(v_inst_261_, 0);
v_intCast_268_ = lean_ctor_get(v_inst_261_, 3);
v_toAdd_269_ = lean_ctor_get(v_toSemiring_267_, 0);
lean_inc(v_toAdd_269_);
v_toMul_270_ = lean_ctor_get(v_toSemiring_267_, 1);
v_k_271_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_k_271_);
v_v_272_ = lean_ctor_get(v_x_263_, 2);
lean_inc(v_v_272_);
v_p_273_ = lean_ctor_get(v_x_263_, 3);
lean_inc_ref(v_p_273_);
lean_dec_ref_known(v_x_263_, 4);
lean_inc(v_intCast_268_);
v___x_274_ = lean_apply_1(v_intCast_268_, v_k_271_);
lean_inc(v_g_262_);
v___x_275_ = lean_apply_1(v_g_262_, v_v_272_);
lean_inc(v_toMul_270_);
v___x_276_ = lean_apply_2(v_toMul_270_, v___x_274_, v___x_275_);
v___x_277_ = l_Lean_Grind_CommRing_PPoly_denoteG___redArg(v_inst_261_, v_g_262_, v_p_273_);
v___x_278_ = lean_apply_2(v_toAdd_269_, v___x_276_, v___x_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_denoteG(lean_object* v_00_u03b1_279_, lean_object* v_inst_280_, lean_object* v_g_281_, lean_object* v_x_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Grind_CommRing_PPoly_denoteG___redArg(v_inst_280_, v_g_281_, v_x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_scale(lean_object* v_k_284_, lean_object* v_x_285_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
lean_object* v_k_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_294_; 
v_k_286_ = lean_ctor_get(v_x_285_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_285_);
if (v_isSharedCheck_294_ == 0)
{
v___x_288_ = v_x_285_;
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_k_286_);
lean_dec(v_x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_int_mul(v_k_284_, v_k_286_);
lean_dec(v_k_286_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_290_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v_k_295_; lean_object* v_d_296_; lean_object* v_v_297_; lean_object* v_p_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_307_; 
v_k_295_ = lean_ctor_get(v_x_285_, 0);
v_d_296_ = lean_ctor_get(v_x_285_, 1);
v_v_297_ = lean_ctor_get(v_x_285_, 2);
v_p_298_ = lean_ctor_get(v_x_285_, 3);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_285_);
if (v_isSharedCheck_307_ == 0)
{
v___x_300_ = v_x_285_;
v_isShared_301_ = v_isSharedCheck_307_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_p_298_);
lean_inc(v_v_297_);
lean_inc(v_d_296_);
lean_inc(v_k_295_);
lean_dec(v_x_285_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_307_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_302_ = lean_int_mul(v_k_284_, v_k_295_);
lean_dec(v_k_295_);
v___x_303_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_284_, v_p_298_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 3, v___x_303_);
lean_ctor_set(v___x_300_, 0, v___x_302_);
v___x_305_ = v___x_300_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_d_296_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_v_297_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_scale___boxed(lean_object* v_k_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_308_, v_x_309_);
lean_dec(v_k_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Expr_evalConst_spec__0(lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_nat_to_int(v_a_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_evalConst(lean_object* v_x_313_){
_start:
{
switch(lean_obj_tag(v_x_313_))
{
case 1:
{
lean_object* v_k_314_; lean_object* v___x_315_; 
v_k_314_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_k_314_);
lean_dec_ref_known(v_x_313_, 1);
v___x_315_ = lean_nat_to_int(v_k_314_);
return v___x_315_;
}
case 3:
{
lean_object* v___x_316_; 
lean_dec_ref_known(v_x_313_, 1);
v___x_316_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_coeff___closed__0, &l_Lean_Grind_CommRing_PPoly_coeff___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_coeff___closed__0);
return v___x_316_;
}
case 4:
{
lean_object* v_a_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_a_317_ = lean_ctor_get(v_x_313_, 0);
lean_inc_ref(v_a_317_);
lean_dec_ref_known(v_x_313_, 1);
v___x_318_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_317_);
v___x_319_ = lean_int_neg(v___x_318_);
lean_dec(v___x_318_);
return v___x_319_;
}
case 5:
{
lean_object* v_a_320_; lean_object* v_b_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_a_320_ = lean_ctor_get(v_x_313_, 0);
lean_inc_ref(v_a_320_);
v_b_321_ = lean_ctor_get(v_x_313_, 1);
lean_inc_ref(v_b_321_);
lean_dec_ref_known(v_x_313_, 2);
v___x_322_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_320_);
v___x_323_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_321_);
v___x_324_ = lean_int_add(v___x_322_, v___x_323_);
lean_dec(v___x_323_);
lean_dec(v___x_322_);
return v___x_324_;
}
case 6:
{
lean_object* v_a_325_; lean_object* v_b_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_a_325_ = lean_ctor_get(v_x_313_, 0);
lean_inc_ref(v_a_325_);
v_b_326_ = lean_ctor_get(v_x_313_, 1);
lean_inc_ref(v_b_326_);
lean_dec_ref_known(v_x_313_, 2);
v___x_327_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_325_);
v___x_328_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_326_);
v___x_329_ = lean_int_sub(v___x_327_, v___x_328_);
lean_dec(v___x_328_);
lean_dec(v___x_327_);
return v___x_329_;
}
case 7:
{
lean_object* v_a_330_; lean_object* v_b_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_a_330_ = lean_ctor_get(v_x_313_, 0);
lean_inc_ref(v_a_330_);
v_b_331_ = lean_ctor_get(v_x_313_, 1);
lean_inc_ref(v_b_331_);
lean_dec_ref_known(v_x_313_, 2);
v___x_332_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_330_);
v___x_333_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_331_);
v___x_334_ = lean_int_mul(v___x_332_, v___x_333_);
lean_dec(v___x_333_);
lean_dec(v___x_332_);
return v___x_334_;
}
case 8:
{
lean_object* v_a_335_; lean_object* v_k_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_a_335_ = lean_ctor_get(v_x_313_, 0);
lean_inc_ref(v_a_335_);
v_k_336_ = lean_ctor_get(v_x_313_, 1);
lean_inc(v_k_336_);
lean_dec_ref_known(v_x_313_, 2);
v___x_337_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_335_);
v___x_338_ = l_Int_pow(v___x_337_, v_k_336_);
lean_dec(v_k_336_);
lean_dec(v___x_337_);
return v___x_338_;
}
default: 
{
lean_object* v_k_339_; 
v_k_339_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_k_339_);
lean_dec_ref(v_x_313_);
return v_k_339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___redArg(lean_object* v_inst_340_, lean_object* v_f_341_, lean_object* v_v_342_){
_start:
{
lean_object* v_toSemiring_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_toSemiring_343_ = lean_ctor_get(v_inst_340_, 0);
lean_inc_ref(v_toSemiring_343_);
lean_dec_ref(v_inst_340_);
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_nat_dec_eq(v_v_342_, v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec_ref(v_toSemiring_343_);
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_sub(v_v_342_, v___x_346_);
v___x_348_ = lean_apply_1(v_f_341_, v___x_347_);
return v___x_348_;
}
else
{
lean_object* v_ofNat_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_f_341_);
v_ofNat_349_ = lean_ctor_get(v_toSemiring_343_, 3);
lean_inc(v_ofNat_349_);
lean_dec_ref(v_toSemiring_343_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_apply_1(v_ofNat_349_, v___x_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___redArg___boxed(lean_object* v_inst_352_, lean_object* v_f_353_, lean_object* v_v_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Grind_CommRing_PPoly_linVal___redArg(v_inst_352_, v_f_353_, v_v_354_);
lean_dec(v_v_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal(lean_object* v_00_u03b1_356_, lean_object* v_inst_357_, lean_object* v_f_358_, lean_object* v_v_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Grind_CommRing_PPoly_linVal___redArg(v_inst_357_, v_f_358_, v_v_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___boxed(lean_object* v_00_u03b1_361_, lean_object* v_inst_362_, lean_object* v_f_363_, lean_object* v_v_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Grind_CommRing_PPoly_linVal(v_00_u03b1_361_, v_inst_362_, v_f_363_, v_v_364_);
lean_dec(v_v_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorIdx___impl(lean_object* v_x_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_tag_nat(v_x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorIdx___impl___boxed(lean_object* v_x_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Grind_CommRing_KList_ctorIdx___impl(v_x_368_);
lean_dec(v_x_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim___redArg(lean_object* v_t_370_, lean_object* v_k_371_){
_start:
{
if (lean_obj_tag(v_t_370_) == 0)
{
return v_k_371_;
}
else
{
lean_object* v_k_372_; lean_object* v_m_373_; lean_object* v_q_374_; lean_object* v_ls_375_; lean_object* v___x_376_; 
v_k_372_ = lean_ctor_get(v_t_370_, 0);
lean_inc(v_k_372_);
v_m_373_ = lean_ctor_get(v_t_370_, 1);
lean_inc(v_m_373_);
v_q_374_ = lean_ctor_get(v_t_370_, 2);
lean_inc_ref(v_q_374_);
v_ls_375_ = lean_ctor_get(v_t_370_, 3);
lean_inc(v_ls_375_);
lean_dec_ref_known(v_t_370_, 4);
v___x_376_ = lean_apply_4(v_k_371_, v_k_372_, v_m_373_, v_q_374_, v_ls_375_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim(lean_object* v_motive_377_, lean_object* v_ctorIdx_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_k_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_379_, v_k_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim___boxed(lean_object* v_motive_383_, lean_object* v_ctorIdx_384_, lean_object* v_t_385_, lean_object* v_h_386_, lean_object* v_k_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Grind_CommRing_KList_ctorElim(v_motive_383_, v_ctorIdx_384_, v_t_385_, v_h_386_, v_k_387_);
lean_dec(v_ctorIdx_384_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_nil_elim___redArg(lean_object* v_t_389_, lean_object* v_nil_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_389_, v_nil_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_nil_elim(lean_object* v_motive_392_, lean_object* v_t_393_, lean_object* v_h_394_, lean_object* v_nil_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_393_, v_nil_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_cons_elim___redArg(lean_object* v_t_397_, lean_object* v_cons_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_397_, v_cons_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_cons_elim(lean_object* v_motive_400_, lean_object* v_t_401_, lean_object* v_h_402_, lean_object* v_cons_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_401_, v_cons_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorIdx___impl(lean_object* v_x_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_obj_tag_nat(v_x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorIdx___impl___boxed(lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Grind_CommRing_MList_ctorIdx___impl(v_x_407_);
lean_dec(v_x_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim___redArg(lean_object* v_t_409_, lean_object* v_k_410_){
_start:
{
if (lean_obj_tag(v_t_409_) == 0)
{
return v_k_410_;
}
else
{
lean_object* v_M_411_; lean_object* v_q_412_; lean_object* v_ls_413_; lean_object* v___x_414_; 
v_M_411_ = lean_ctor_get(v_t_409_, 0);
lean_inc_ref(v_M_411_);
v_q_412_ = lean_ctor_get(v_t_409_, 1);
lean_inc_ref(v_q_412_);
v_ls_413_ = lean_ctor_get(v_t_409_, 2);
lean_inc(v_ls_413_);
lean_dec_ref_known(v_t_409_, 3);
v___x_414_ = lean_apply_3(v_k_410_, v_M_411_, v_q_412_, v_ls_413_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim(lean_object* v_motive_415_, lean_object* v_ctorIdx_416_, lean_object* v_t_417_, lean_object* v_h_418_, lean_object* v_k_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_417_, v_k_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim___boxed(lean_object* v_motive_421_, lean_object* v_ctorIdx_422_, lean_object* v_t_423_, lean_object* v_h_424_, lean_object* v_k_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Grind_CommRing_MList_ctorElim(v_motive_421_, v_ctorIdx_422_, v_t_423_, v_h_424_, v_k_425_);
lean_dec(v_ctorIdx_422_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_nil_elim___redArg(lean_object* v_t_427_, lean_object* v_nil_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_427_, v_nil_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_nil_elim(lean_object* v_motive_430_, lean_object* v_t_431_, lean_object* v_h_432_, lean_object* v_nil_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_431_, v_nil_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_cons_elim___redArg(lean_object* v_t_435_, lean_object* v_cons_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_435_, v_cons_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_cons_elim(lean_object* v_motive_438_, lean_object* v_t_439_, lean_object* v_h_440_, lean_object* v_cons_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_439_, v_cons_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_evalConst_match__1_splitter___redArg(lean_object* v_x_443_, lean_object* v_h__1_444_, lean_object* v_h__2_445_, lean_object* v_h__3_446_, lean_object* v_h__4_447_, lean_object* v_h__5_448_, lean_object* v_h__6_449_, lean_object* v_h__7_450_, lean_object* v_h__8_451_, lean_object* v_h__9_452_){
_start:
{
switch(lean_obj_tag(v_x_443_))
{
case 0:
{
lean_object* v_k_453_; lean_object* v___x_454_; 
lean_dec(v_h__9_452_);
lean_dec(v_h__8_451_);
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
v_k_453_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_k_453_);
lean_dec_ref_known(v_x_443_, 1);
v___x_454_ = lean_apply_1(v_h__1_444_, v_k_453_);
return v___x_454_;
}
case 1:
{
lean_object* v_k_455_; lean_object* v___x_456_; 
lean_dec(v_h__9_452_);
lean_dec(v_h__8_451_);
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v_k_455_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_k_455_);
lean_dec_ref_known(v_x_443_, 1);
v___x_456_ = lean_apply_1(v_h__3_446_, v_k_455_);
return v___x_456_;
}
case 2:
{
lean_object* v_k_457_; lean_object* v___x_458_; 
lean_dec(v_h__9_452_);
lean_dec(v_h__8_451_);
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__1_444_);
v_k_457_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_k_457_);
lean_dec_ref_known(v_x_443_, 1);
v___x_458_ = lean_apply_1(v_h__2_445_, v_k_457_);
return v___x_458_;
}
case 3:
{
lean_object* v_i_459_; lean_object* v___x_460_; 
lean_dec(v_h__9_452_);
lean_dec(v_h__8_451_);
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v_i_459_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_i_459_);
lean_dec_ref_known(v_x_443_, 1);
v___x_460_ = lean_apply_1(v_h__4_447_, v_i_459_);
return v___x_460_;
}
case 4:
{
lean_object* v_a_461_; lean_object* v___x_462_; 
lean_dec(v_h__9_452_);
lean_dec(v_h__8_451_);
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v_a_461_ = lean_ctor_get(v_x_443_, 0);
lean_inc_ref(v_a_461_);
lean_dec_ref_known(v_x_443_, 1);
v___x_462_ = lean_apply_1(v_h__5_448_, v_a_461_);
return v___x_462_;
}
case 5:
{
lean_object* v_a_463_; lean_object* v_b_464_; lean_object* v___x_465_; 
lean_dec(v_h__9_452_);
lean_dec(v_h__8_451_);
lean_dec(v_h__7_450_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v_a_463_ = lean_ctor_get(v_x_443_, 0);
lean_inc_ref(v_a_463_);
v_b_464_ = lean_ctor_get(v_x_443_, 1);
lean_inc_ref(v_b_464_);
lean_dec_ref_known(v_x_443_, 2);
v___x_465_ = lean_apply_2(v_h__6_449_, v_a_463_, v_b_464_);
return v___x_465_;
}
case 6:
{
lean_object* v_a_466_; lean_object* v_b_467_; lean_object* v___x_468_; 
lean_dec(v_h__9_452_);
lean_dec(v_h__8_451_);
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v_a_466_ = lean_ctor_get(v_x_443_, 0);
lean_inc_ref(v_a_466_);
v_b_467_ = lean_ctor_get(v_x_443_, 1);
lean_inc_ref(v_b_467_);
lean_dec_ref_known(v_x_443_, 2);
v___x_468_ = lean_apply_2(v_h__7_450_, v_a_466_, v_b_467_);
return v___x_468_;
}
case 7:
{
lean_object* v_a_469_; lean_object* v_b_470_; lean_object* v___x_471_; 
lean_dec(v_h__9_452_);
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v_a_469_ = lean_ctor_get(v_x_443_, 0);
lean_inc_ref(v_a_469_);
v_b_470_ = lean_ctor_get(v_x_443_, 1);
lean_inc_ref(v_b_470_);
lean_dec_ref_known(v_x_443_, 2);
v___x_471_ = lean_apply_2(v_h__8_451_, v_a_469_, v_b_470_);
return v___x_471_;
}
default: 
{
lean_object* v_a_472_; lean_object* v_k_473_; lean_object* v___x_474_; 
lean_dec(v_h__8_451_);
lean_dec(v_h__7_450_);
lean_dec(v_h__6_449_);
lean_dec(v_h__5_448_);
lean_dec(v_h__4_447_);
lean_dec(v_h__3_446_);
lean_dec(v_h__2_445_);
lean_dec(v_h__1_444_);
v_a_472_ = lean_ctor_get(v_x_443_, 0);
lean_inc_ref(v_a_472_);
v_k_473_ = lean_ctor_get(v_x_443_, 1);
lean_inc(v_k_473_);
lean_dec_ref_known(v_x_443_, 2);
v___x_474_ = lean_apply_2(v_h__9_452_, v_a_472_, v_k_473_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_evalConst_match__1_splitter(lean_object* v_motive_475_, lean_object* v_x_476_, lean_object* v_h__1_477_, lean_object* v_h__2_478_, lean_object* v_h__3_479_, lean_object* v_h__4_480_, lean_object* v_h__5_481_, lean_object* v_h__6_482_, lean_object* v_h__7_483_, lean_object* v_h__8_484_, lean_object* v_h__9_485_){
_start:
{
switch(lean_obj_tag(v_x_476_))
{
case 0:
{
lean_object* v_k_486_; lean_object* v___x_487_; 
lean_dec(v_h__9_485_);
lean_dec(v_h__8_484_);
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
v_k_486_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_k_486_);
lean_dec_ref_known(v_x_476_, 1);
v___x_487_ = lean_apply_1(v_h__1_477_, v_k_486_);
return v___x_487_;
}
case 1:
{
lean_object* v_k_488_; lean_object* v___x_489_; 
lean_dec(v_h__9_485_);
lean_dec(v_h__8_484_);
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v_k_488_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_k_488_);
lean_dec_ref_known(v_x_476_, 1);
v___x_489_ = lean_apply_1(v_h__3_479_, v_k_488_);
return v___x_489_;
}
case 2:
{
lean_object* v_k_490_; lean_object* v___x_491_; 
lean_dec(v_h__9_485_);
lean_dec(v_h__8_484_);
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__1_477_);
v_k_490_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_k_490_);
lean_dec_ref_known(v_x_476_, 1);
v___x_491_ = lean_apply_1(v_h__2_478_, v_k_490_);
return v___x_491_;
}
case 3:
{
lean_object* v_i_492_; lean_object* v___x_493_; 
lean_dec(v_h__9_485_);
lean_dec(v_h__8_484_);
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v_i_492_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_i_492_);
lean_dec_ref_known(v_x_476_, 1);
v___x_493_ = lean_apply_1(v_h__4_480_, v_i_492_);
return v___x_493_;
}
case 4:
{
lean_object* v_a_494_; lean_object* v___x_495_; 
lean_dec(v_h__9_485_);
lean_dec(v_h__8_484_);
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v_a_494_ = lean_ctor_get(v_x_476_, 0);
lean_inc_ref(v_a_494_);
lean_dec_ref_known(v_x_476_, 1);
v___x_495_ = lean_apply_1(v_h__5_481_, v_a_494_);
return v___x_495_;
}
case 5:
{
lean_object* v_a_496_; lean_object* v_b_497_; lean_object* v___x_498_; 
lean_dec(v_h__9_485_);
lean_dec(v_h__8_484_);
lean_dec(v_h__7_483_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v_a_496_ = lean_ctor_get(v_x_476_, 0);
lean_inc_ref(v_a_496_);
v_b_497_ = lean_ctor_get(v_x_476_, 1);
lean_inc_ref(v_b_497_);
lean_dec_ref_known(v_x_476_, 2);
v___x_498_ = lean_apply_2(v_h__6_482_, v_a_496_, v_b_497_);
return v___x_498_;
}
case 6:
{
lean_object* v_a_499_; lean_object* v_b_500_; lean_object* v___x_501_; 
lean_dec(v_h__9_485_);
lean_dec(v_h__8_484_);
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v_a_499_ = lean_ctor_get(v_x_476_, 0);
lean_inc_ref(v_a_499_);
v_b_500_ = lean_ctor_get(v_x_476_, 1);
lean_inc_ref(v_b_500_);
lean_dec_ref_known(v_x_476_, 2);
v___x_501_ = lean_apply_2(v_h__7_483_, v_a_499_, v_b_500_);
return v___x_501_;
}
case 7:
{
lean_object* v_a_502_; lean_object* v_b_503_; lean_object* v___x_504_; 
lean_dec(v_h__9_485_);
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v_a_502_ = lean_ctor_get(v_x_476_, 0);
lean_inc_ref(v_a_502_);
v_b_503_ = lean_ctor_get(v_x_476_, 1);
lean_inc_ref(v_b_503_);
lean_dec_ref_known(v_x_476_, 2);
v___x_504_ = lean_apply_2(v_h__8_484_, v_a_502_, v_b_503_);
return v___x_504_;
}
default: 
{
lean_object* v_a_505_; lean_object* v_k_506_; lean_object* v___x_507_; 
lean_dec(v_h__8_484_);
lean_dec(v_h__7_483_);
lean_dec(v_h__6_482_);
lean_dec(v_h__5_481_);
lean_dec(v_h__4_480_);
lean_dec(v_h__3_479_);
lean_dec(v_h__2_478_);
lean_dec(v_h__1_477_);
v_a_505_ = lean_ctor_get(v_x_476_, 0);
lean_inc_ref(v_a_505_);
v_k_506_ = lean_ctor_get(v_x_476_, 1);
lean_inc(v_k_506_);
lean_dec_ref_known(v_x_476_, 2);
v___x_507_ = lean_apply_2(v_h__9_485_, v_a_505_, v_k_506_);
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_toPPQ_match__1_splitter___redArg(lean_object* v_x_508_, lean_object* v_h__1_509_, lean_object* v_h__2_510_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_h__1_509_);
v___x_511_ = lean_box(0);
v___x_512_ = lean_apply_1(v_h__2_510_, v___x_511_);
return v___x_512_;
}
else
{
lean_object* v_val_513_; lean_object* v___x_514_; 
lean_dec(v_h__2_510_);
v_val_513_ = lean_ctor_get(v_x_508_, 0);
lean_inc(v_val_513_);
lean_dec_ref_known(v_x_508_, 1);
v___x_514_ = lean_apply_1(v_h__1_509_, v_val_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_Expr_toPPQ_match__1_splitter(lean_object* v_motive_515_, lean_object* v_x_516_, lean_object* v_h__1_517_, lean_object* v_h__2_518_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v_h__1_517_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_apply_1(v_h__2_518_, v___x_519_);
return v___x_520_;
}
else
{
lean_object* v_val_521_; lean_object* v___x_522_; 
lean_dec(v_h__2_518_);
v_val_521_ = lean_ctor_get(v_x_516_, 0);
lean_inc(v_val_521_);
lean_dec_ref_known(v_x_516_, 1);
v___x_522_ = lean_apply_1(v_h__1_517_, v_val_521_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL(lean_object* v_k_523_, lean_object* v_d_524_, lean_object* v_v_525_, lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_object* v_k_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_k_527_ = lean_ctor_get(v_x_526_, 0);
lean_inc(v_k_527_);
lean_dec_ref_known(v_x_526_, 1);
v___x_528_ = lean_int_mul(v_k_523_, v_k_527_);
lean_dec(v_k_527_);
v___x_529_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_removeCode___closed__0, &l_Lean_Grind_CommRing_PPoly_removeCode___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_removeCode___closed__0);
v___x_530_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v_d_524_);
lean_ctor_set(v___x_530_, 2, v_v_525_);
lean_ctor_set(v___x_530_, 3, v___x_529_);
return v___x_530_;
}
else
{
lean_object* v_k_531_; lean_object* v_d_532_; lean_object* v_v_533_; lean_object* v_p_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_545_; 
v_k_531_ = lean_ctor_get(v_x_526_, 0);
v_d_532_ = lean_ctor_get(v_x_526_, 1);
v_v_533_ = lean_ctor_get(v_x_526_, 2);
v_p_534_ = lean_ctor_get(v_x_526_, 3);
v_isSharedCheck_545_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_545_ == 0)
{
v___x_536_ = v_x_526_;
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_p_534_);
lean_inc(v_v_533_);
lean_inc(v_d_532_);
lean_inc(v_k_531_);
lean_dec(v_x_526_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_545_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_538_ = lean_int_mul(v_k_523_, v_k_531_);
lean_dec(v_k_531_);
v___x_539_ = lean_nat_add(v_d_524_, v_d_532_);
lean_dec(v_d_532_);
v___x_540_ = lean_nat_add(v_v_525_, v_v_533_);
lean_dec(v_v_533_);
v___x_541_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_523_, v_d_524_, v_v_525_, v_p_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 3, v___x_541_);
lean_ctor_set(v___x_536_, 2, v___x_540_);
lean_ctor_set(v___x_536_, 1, v___x_539_);
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_543_ = v___x_536_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL___boxed(lean_object* v_k_546_, lean_object* v_d_547_, lean_object* v_v_548_, lean_object* v_x_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_546_, v_d_547_, v_v_548_, v_x_549_);
lean_dec(v_k_546_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTL(lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v_k_553_; lean_object* v___x_554_; 
v_k_553_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_k_553_);
lean_dec_ref_known(v_x_551_, 1);
v___x_554_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_553_, v_x_552_);
lean_dec(v_k_553_);
return v___x_554_;
}
else
{
lean_object* v_k_555_; lean_object* v_d_556_; lean_object* v_v_557_; lean_object* v_p_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_k_555_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_k_555_);
v_d_556_ = lean_ctor_get(v_x_551_, 1);
lean_inc(v_d_556_);
v_v_557_ = lean_ctor_get(v_x_551_, 2);
lean_inc(v_v_557_);
v_p_558_ = lean_ctor_get(v_x_551_, 3);
lean_inc_ref(v_p_558_);
lean_dec_ref_known(v_x_551_, 4);
lean_inc_ref(v_x_552_);
v___x_559_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_555_, v_d_556_, v_v_557_, v_x_552_);
lean_dec(v_k_555_);
v___x_560_ = l_Lean_Grind_CommRing_PPoly_mulTL(v_p_558_, v_x_552_);
v___x_561_ = l_Lean_Grind_CommRing_PPoly_append(v___x_559_, v___x_560_);
return v___x_561_;
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__0(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_to_int(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__1(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_powTL___closed__0, &l_Lean_Grind_CommRing_PPoly_powTL___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__0);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL(lean_object* v_p_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_zero_568_; uint8_t v_isZero_569_; 
v_zero_568_ = lean_unsigned_to_nat(0u);
v_isZero_569_ = lean_nat_dec_eq(v_x_567_, v_zero_568_);
if (v_isZero_569_ == 1)
{
lean_object* v___x_570_; 
lean_dec_ref(v_p_566_);
v___x_570_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_powTL___closed__1, &l_Lean_Grind_CommRing_PPoly_powTL___closed__1_once, _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__1);
return v___x_570_;
}
else
{
lean_object* v_one_571_; lean_object* v_n_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_one_571_ = lean_unsigned_to_nat(1u);
v_n_572_ = lean_nat_sub(v_x_567_, v_one_571_);
lean_inc_ref(v_p_566_);
v___x_573_ = l_Lean_Grind_CommRing_PPoly_powTL(v_p_566_, v_n_572_);
lean_dec(v_n_572_);
v___x_574_ = l_Lean_Grind_CommRing_PPoly_mulTL(v___x_573_, v_p_566_);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL___boxed(lean_object* v_p_575_, lean_object* v_x_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Grind_CommRing_PPoly_powTL(v_p_575_, v_x_576_);
lean_dec(v_x_576_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___redArg(lean_object* v_x_578_, lean_object* v_h__1_579_, lean_object* v_h__2_580_){
_start:
{
lean_object* v_zero_581_; uint8_t v_isZero_582_; 
v_zero_581_ = lean_unsigned_to_nat(0u);
v_isZero_582_ = lean_nat_dec_eq(v_x_578_, v_zero_581_);
if (v_isZero_582_ == 1)
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v_h__2_580_);
v___x_583_ = lean_box(0);
v___x_584_ = lean_apply_1(v_h__1_579_, v___x_583_);
return v___x_584_;
}
else
{
lean_object* v_one_585_; lean_object* v_n_586_; lean_object* v___x_587_; 
lean_dec(v_h__1_579_);
v_one_585_ = lean_unsigned_to_nat(1u);
v_n_586_ = lean_nat_sub(v_x_578_, v_one_585_);
v___x_587_ = lean_apply_1(v_h__2_580_, v_n_586_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___redArg___boxed(lean_object* v_x_588_, lean_object* v_h__1_589_, lean_object* v_h__2_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___redArg(v_x_588_, v_h__1_589_, v_h__2_590_);
lean_dec(v_x_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter(lean_object* v_motive_592_, lean_object* v_x_593_, lean_object* v_h__1_594_, lean_object* v_h__2_595_){
_start:
{
lean_object* v_zero_596_; uint8_t v_isZero_597_; 
v_zero_596_ = lean_unsigned_to_nat(0u);
v_isZero_597_ = lean_nat_dec_eq(v_x_593_, v_zero_596_);
if (v_isZero_597_ == 1)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_h__2_595_);
v___x_598_ = lean_box(0);
v___x_599_ = lean_apply_1(v_h__1_594_, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v_one_600_; lean_object* v_n_601_; lean_object* v___x_602_; 
lean_dec(v_h__1_594_);
v_one_600_ = lean_unsigned_to_nat(1u);
v_n_601_ = lean_nat_sub(v_x_593_, v_one_600_);
v___x_602_ = lean_apply_1(v_h__2_595_, v_n_601_);
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter___boxed(lean_object* v_motive_603_, lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Init_Grind_Ring_Kronecker_0__Lean_Grind_CommRing_PPoly_powTL_match__1_splitter(v_motive_603_, v_x_604_, v_h__1_605_, v_h__2_606_);
lean_dec(v_x_604_);
return v_res_607_;
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
