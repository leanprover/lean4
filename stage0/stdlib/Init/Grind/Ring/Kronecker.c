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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append_addConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append_addConst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_neg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1List(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1List___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTL(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_PPoly_powTL___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_PPoly_powTL___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_PPoly_powTL___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_PPoly_powTL___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append_addConst(lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
if (lean_obj_tag(v_a_95_) == 0)
{
lean_object* v_k_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_105_; 
v_k_97_ = lean_ctor_get(v_a_95_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v_a_95_);
if (v_isSharedCheck_105_ == 0)
{
v___x_99_ = v_a_95_;
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_k_97_);
lean_dec(v_a_95_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_int_add(v_k_97_, v_a_96_);
lean_dec(v_k_97_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_101_);
v___x_103_ = v___x_99_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
else
{
lean_object* v_k_106_; lean_object* v_d_107_; lean_object* v_v_108_; lean_object* v_p_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_117_; 
v_k_106_ = lean_ctor_get(v_a_95_, 0);
v_d_107_ = lean_ctor_get(v_a_95_, 1);
v_v_108_ = lean_ctor_get(v_a_95_, 2);
v_p_109_ = lean_ctor_get(v_a_95_, 3);
v_isSharedCheck_117_ = !lean_is_exclusive(v_a_95_);
if (v_isSharedCheck_117_ == 0)
{
v___x_111_ = v_a_95_;
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_p_109_);
lean_inc(v_v_108_);
lean_inc(v_d_107_);
lean_inc(v_k_106_);
lean_dec(v_a_95_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = l_Lean_Grind_CommRing_PPoly_append_addConst(v_p_109_, v_a_96_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 3, v___x_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_k_106_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_d_107_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_v_108_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append_addConst___boxed(lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Grind_CommRing_PPoly_append_addConst(v_a_118_, v_a_119_);
lean_dec(v_a_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_append(lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v_k_123_; lean_object* v___x_124_; 
v_k_123_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_k_123_);
lean_dec_ref_known(v_x_121_, 1);
v___x_124_ = l_Lean_Grind_CommRing_PPoly_append_addConst(v_x_122_, v_k_123_);
lean_dec(v_k_123_);
return v___x_124_;
}
else
{
lean_object* v_k_125_; lean_object* v_d_126_; lean_object* v_v_127_; lean_object* v_p_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_136_; 
v_k_125_ = lean_ctor_get(v_x_121_, 0);
v_d_126_ = lean_ctor_get(v_x_121_, 1);
v_v_127_ = lean_ctor_get(v_x_121_, 2);
v_p_128_ = lean_ctor_get(v_x_121_, 3);
v_isSharedCheck_136_ = !lean_is_exclusive(v_x_121_);
if (v_isSharedCheck_136_ == 0)
{
v___x_130_ = v_x_121_;
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_p_128_);
lean_inc(v_v_127_);
lean_inc(v_d_126_);
lean_inc(v_k_125_);
lean_dec(v_x_121_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = l_Lean_Grind_CommRing_PPoly_append(v_p_128_, v_x_122_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 3, v___x_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_k_125_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_d_126_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_v_127_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_neg(lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v_k_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_146_; 
v_k_138_ = lean_ctor_get(v_x_137_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_146_ == 0)
{
v___x_140_ = v_x_137_;
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_k_138_);
lean_dec(v_x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_int_neg(v_k_138_);
lean_dec(v_k_138_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_142_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
else
{
lean_object* v_k_147_; lean_object* v_d_148_; lean_object* v_v_149_; lean_object* v_p_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_159_; 
v_k_147_ = lean_ctor_get(v_x_137_, 0);
v_d_148_ = lean_ctor_get(v_x_137_, 1);
v_v_149_ = lean_ctor_get(v_x_137_, 2);
v_p_150_ = lean_ctor_get(v_x_137_, 3);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_159_ == 0)
{
v___x_152_ = v_x_137_;
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_p_150_);
lean_inc(v_v_149_);
lean_inc(v_d_148_);
lean_inc(v_k_147_);
lean_dec(v_x_137_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_154_ = lean_int_neg(v_k_147_);
lean_dec(v_k_147_);
v___x_155_ = l_Lean_Grind_CommRing_PPoly_neg(v_p_150_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 3, v___x_155_);
lean_ctor_set(v___x_152_, 0, v___x_154_);
v___x_157_ = v___x_152_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_d_148_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_v_149_);
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
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(lean_object* v_init_160_, lean_object* v_x_161_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
lean_inc(v_init_160_);
return v_init_160_;
}
else
{
lean_object* v_head_162_; lean_object* v_tail_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_head_162_ = lean_ctor_get(v_x_161_, 0);
v_tail_163_ = lean_ctor_get(v_x_161_, 1);
v___x_164_ = l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(v_init_160_, v_tail_163_);
v___x_165_ = l_Lean_Grind_CommRing_PPoly_norm1(v_head_162_);
v___x_166_ = lean_nat_add(v___x_165_, v___x_164_);
lean_dec(v___x_164_);
lean_dec(v___x_165_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0___boxed(lean_object* v_init_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(v_init_167_, v_x_168_);
lean_dec(v_x_168_);
lean_dec(v_init_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1List(lean_object* v_ps_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = l_List_foldr___at___00Lean_Grind_CommRing_PPoly_norm1List_spec__0(v___x_171_, v_ps_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_norm1List___boxed(lean_object* v_ps_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Grind_CommRing_PPoly_norm1List(v_ps_173_);
lean_dec(v_ps_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_denoteG___redArg(lean_object* v_inst_175_, lean_object* v_g_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v_intCast_178_; lean_object* v_k_179_; lean_object* v___x_180_; 
lean_dec(v_g_176_);
v_intCast_178_ = lean_ctor_get(v_inst_175_, 3);
lean_inc(v_intCast_178_);
lean_dec_ref(v_inst_175_);
v_k_179_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_k_179_);
lean_dec_ref_known(v_x_177_, 1);
v___x_180_ = lean_apply_1(v_intCast_178_, v_k_179_);
return v___x_180_;
}
else
{
lean_object* v_toSemiring_181_; lean_object* v_intCast_182_; lean_object* v_toAdd_183_; lean_object* v_toMul_184_; lean_object* v_k_185_; lean_object* v_v_186_; lean_object* v_p_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_toSemiring_181_ = lean_ctor_get(v_inst_175_, 0);
v_intCast_182_ = lean_ctor_get(v_inst_175_, 3);
v_toAdd_183_ = lean_ctor_get(v_toSemiring_181_, 0);
lean_inc(v_toAdd_183_);
v_toMul_184_ = lean_ctor_get(v_toSemiring_181_, 1);
v_k_185_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_k_185_);
v_v_186_ = lean_ctor_get(v_x_177_, 2);
lean_inc(v_v_186_);
v_p_187_ = lean_ctor_get(v_x_177_, 3);
lean_inc_ref(v_p_187_);
lean_dec_ref_known(v_x_177_, 4);
lean_inc(v_intCast_182_);
v___x_188_ = lean_apply_1(v_intCast_182_, v_k_185_);
lean_inc(v_g_176_);
v___x_189_ = lean_apply_1(v_g_176_, v_v_186_);
lean_inc(v_toMul_184_);
v___x_190_ = lean_apply_2(v_toMul_184_, v___x_188_, v___x_189_);
v___x_191_ = l_Lean_Grind_CommRing_PPoly_denoteG___redArg(v_inst_175_, v_g_176_, v_p_187_);
v___x_192_ = lean_apply_2(v_toAdd_183_, v___x_190_, v___x_191_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_denoteG(lean_object* v_00_u03b1_193_, lean_object* v_inst_194_, lean_object* v_g_195_, lean_object* v_x_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Grind_CommRing_PPoly_denoteG___redArg(v_inst_194_, v_g_195_, v_x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_scale(lean_object* v_k_198_, lean_object* v_x_199_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v_k_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
v_k_200_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_208_ == 0)
{
v___x_202_ = v_x_199_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_k_200_);
lean_dec(v_x_199_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = lean_int_mul(v_k_198_, v_k_200_);
lean_dec(v_k_200_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_204_);
v___x_206_ = v___x_202_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
lean_object* v_k_209_; lean_object* v_d_210_; lean_object* v_v_211_; lean_object* v_p_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_221_; 
v_k_209_ = lean_ctor_get(v_x_199_, 0);
v_d_210_ = lean_ctor_get(v_x_199_, 1);
v_v_211_ = lean_ctor_get(v_x_199_, 2);
v_p_212_ = lean_ctor_get(v_x_199_, 3);
v_isSharedCheck_221_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_221_ == 0)
{
v___x_214_ = v_x_199_;
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_p_212_);
lean_inc(v_v_211_);
lean_inc(v_d_210_);
lean_inc(v_k_209_);
lean_dec(v_x_199_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_216_ = lean_int_mul(v_k_198_, v_k_209_);
lean_dec(v_k_209_);
v___x_217_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_198_, v_p_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 3, v___x_217_);
lean_ctor_set(v___x_214_, 0, v___x_216_);
v___x_219_ = v___x_214_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_d_210_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_v_211_);
lean_ctor_set(v_reuseFailAlloc_220_, 3, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_scale___boxed(lean_object* v_k_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_222_, v_x_223_);
lean_dec(v_k_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Expr_evalConst_spec__0(lean_object* v_a_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_nat_to_int(v_a_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_evalConst(lean_object* v_x_227_){
_start:
{
switch(lean_obj_tag(v_x_227_))
{
case 1:
{
lean_object* v_k_228_; lean_object* v___x_229_; 
v_k_228_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_k_228_);
lean_dec_ref_known(v_x_227_, 1);
v___x_229_ = lean_nat_to_int(v_k_228_);
return v___x_229_;
}
case 3:
{
lean_object* v___x_230_; 
lean_dec_ref_known(v_x_227_, 1);
v___x_230_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_coeff___closed__0, &l_Lean_Grind_CommRing_PPoly_coeff___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_coeff___closed__0);
return v___x_230_;
}
case 4:
{
lean_object* v_a_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_a_231_ = lean_ctor_get(v_x_227_, 0);
lean_inc_ref(v_a_231_);
lean_dec_ref_known(v_x_227_, 1);
v___x_232_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_231_);
v___x_233_ = lean_int_neg(v___x_232_);
lean_dec(v___x_232_);
return v___x_233_;
}
case 5:
{
lean_object* v_a_234_; lean_object* v_b_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_a_234_ = lean_ctor_get(v_x_227_, 0);
lean_inc_ref(v_a_234_);
v_b_235_ = lean_ctor_get(v_x_227_, 1);
lean_inc_ref(v_b_235_);
lean_dec_ref_known(v_x_227_, 2);
v___x_236_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_234_);
v___x_237_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_235_);
v___x_238_ = lean_int_add(v___x_236_, v___x_237_);
lean_dec(v___x_237_);
lean_dec(v___x_236_);
return v___x_238_;
}
case 6:
{
lean_object* v_a_239_; lean_object* v_b_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_a_239_ = lean_ctor_get(v_x_227_, 0);
lean_inc_ref(v_a_239_);
v_b_240_ = lean_ctor_get(v_x_227_, 1);
lean_inc_ref(v_b_240_);
lean_dec_ref_known(v_x_227_, 2);
v___x_241_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_239_);
v___x_242_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_240_);
v___x_243_ = lean_int_sub(v___x_241_, v___x_242_);
lean_dec(v___x_242_);
lean_dec(v___x_241_);
return v___x_243_;
}
case 7:
{
lean_object* v_a_244_; lean_object* v_b_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_a_244_ = lean_ctor_get(v_x_227_, 0);
lean_inc_ref(v_a_244_);
v_b_245_ = lean_ctor_get(v_x_227_, 1);
lean_inc_ref(v_b_245_);
lean_dec_ref_known(v_x_227_, 2);
v___x_246_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_244_);
v___x_247_ = l_Lean_Grind_CommRing_Expr_evalConst(v_b_245_);
v___x_248_ = lean_int_mul(v___x_246_, v___x_247_);
lean_dec(v___x_247_);
lean_dec(v___x_246_);
return v___x_248_;
}
case 8:
{
lean_object* v_a_249_; lean_object* v_k_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_a_249_ = lean_ctor_get(v_x_227_, 0);
lean_inc_ref(v_a_249_);
v_k_250_ = lean_ctor_get(v_x_227_, 1);
lean_inc(v_k_250_);
lean_dec_ref_known(v_x_227_, 2);
v___x_251_ = l_Lean_Grind_CommRing_Expr_evalConst(v_a_249_);
v___x_252_ = l_Int_pow(v___x_251_, v_k_250_);
lean_dec(v_k_250_);
lean_dec(v___x_251_);
return v___x_252_;
}
default: 
{
lean_object* v_k_253_; 
v_k_253_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_k_253_);
lean_dec_ref(v_x_227_);
return v_k_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___redArg(lean_object* v_inst_254_, lean_object* v_f_255_, lean_object* v_v_256_){
_start:
{
lean_object* v_toSemiring_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_toSemiring_257_ = lean_ctor_get(v_inst_254_, 0);
lean_inc_ref(v_toSemiring_257_);
lean_dec_ref(v_inst_254_);
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = lean_nat_dec_eq(v_v_256_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec_ref(v_toSemiring_257_);
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_sub(v_v_256_, v___x_260_);
v___x_262_ = lean_apply_1(v_f_255_, v___x_261_);
return v___x_262_;
}
else
{
lean_object* v_ofNat_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_f_255_);
v_ofNat_263_ = lean_ctor_get(v_toSemiring_257_, 3);
lean_inc(v_ofNat_263_);
lean_dec_ref(v_toSemiring_257_);
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_apply_1(v_ofNat_263_, v___x_264_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___redArg___boxed(lean_object* v_inst_266_, lean_object* v_f_267_, lean_object* v_v_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Grind_CommRing_PPoly_linVal___redArg(v_inst_266_, v_f_267_, v_v_268_);
lean_dec(v_v_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal(lean_object* v_00_u03b1_270_, lean_object* v_inst_271_, lean_object* v_f_272_, lean_object* v_v_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Grind_CommRing_PPoly_linVal___redArg(v_inst_271_, v_f_272_, v_v_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_linVal___boxed(lean_object* v_00_u03b1_275_, lean_object* v_inst_276_, lean_object* v_f_277_, lean_object* v_v_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Grind_CommRing_PPoly_linVal(v_00_u03b1_275_, v_inst_276_, v_f_277_, v_v_278_);
lean_dec(v_v_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorIdx___impl(lean_object* v_x_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_tag_nat(v_x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorIdx___impl___boxed(lean_object* v_x_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Grind_CommRing_KList_ctorIdx___impl(v_x_282_);
lean_dec(v_x_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim___redArg(lean_object* v_t_284_, lean_object* v_k_285_){
_start:
{
if (lean_obj_tag(v_t_284_) == 0)
{
return v_k_285_;
}
else
{
lean_object* v_k_286_; lean_object* v_m_287_; lean_object* v_q_288_; lean_object* v_ls_289_; lean_object* v___x_290_; 
v_k_286_ = lean_ctor_get(v_t_284_, 0);
lean_inc(v_k_286_);
v_m_287_ = lean_ctor_get(v_t_284_, 1);
lean_inc(v_m_287_);
v_q_288_ = lean_ctor_get(v_t_284_, 2);
lean_inc_ref(v_q_288_);
v_ls_289_ = lean_ctor_get(v_t_284_, 3);
lean_inc(v_ls_289_);
lean_dec_ref_known(v_t_284_, 4);
v___x_290_ = lean_apply_4(v_k_285_, v_k_286_, v_m_287_, v_q_288_, v_ls_289_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim(lean_object* v_motive_291_, lean_object* v_ctorIdx_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_k_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_293_, v_k_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_ctorElim___boxed(lean_object* v_motive_297_, lean_object* v_ctorIdx_298_, lean_object* v_t_299_, lean_object* v_h_300_, lean_object* v_k_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Grind_CommRing_KList_ctorElim(v_motive_297_, v_ctorIdx_298_, v_t_299_, v_h_300_, v_k_301_);
lean_dec(v_ctorIdx_298_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_nil_elim___redArg(lean_object* v_t_303_, lean_object* v_nil_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_303_, v_nil_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_nil_elim(lean_object* v_motive_306_, lean_object* v_t_307_, lean_object* v_h_308_, lean_object* v_nil_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_307_, v_nil_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_cons_elim___redArg(lean_object* v_t_311_, lean_object* v_cons_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_311_, v_cons_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_KList_cons_elim(lean_object* v_motive_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_cons_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Grind_CommRing_KList_ctorElim___redArg(v_t_315_, v_cons_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorIdx___impl(lean_object* v_x_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = lean_obj_tag_nat(v_x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorIdx___impl___boxed(lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Grind_CommRing_MList_ctorIdx___impl(v_x_321_);
lean_dec(v_x_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim___redArg(lean_object* v_t_323_, lean_object* v_k_324_){
_start:
{
if (lean_obj_tag(v_t_323_) == 0)
{
return v_k_324_;
}
else
{
lean_object* v_M_325_; lean_object* v_q_326_; lean_object* v_ls_327_; lean_object* v___x_328_; 
v_M_325_ = lean_ctor_get(v_t_323_, 0);
lean_inc_ref(v_M_325_);
v_q_326_ = lean_ctor_get(v_t_323_, 1);
lean_inc_ref(v_q_326_);
v_ls_327_ = lean_ctor_get(v_t_323_, 2);
lean_inc(v_ls_327_);
lean_dec_ref_known(v_t_323_, 3);
v___x_328_ = lean_apply_3(v_k_324_, v_M_325_, v_q_326_, v_ls_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim(lean_object* v_motive_329_, lean_object* v_ctorIdx_330_, lean_object* v_t_331_, lean_object* v_h_332_, lean_object* v_k_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_331_, v_k_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_ctorElim___boxed(lean_object* v_motive_335_, lean_object* v_ctorIdx_336_, lean_object* v_t_337_, lean_object* v_h_338_, lean_object* v_k_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Grind_CommRing_MList_ctorElim(v_motive_335_, v_ctorIdx_336_, v_t_337_, v_h_338_, v_k_339_);
lean_dec(v_ctorIdx_336_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_nil_elim___redArg(lean_object* v_t_341_, lean_object* v_nil_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_341_, v_nil_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_nil_elim(lean_object* v_motive_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_nil_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_345_, v_nil_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_cons_elim___redArg(lean_object* v_t_349_, lean_object* v_cons_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_349_, v_cons_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_MList_cons_elim(lean_object* v_motive_352_, lean_object* v_t_353_, lean_object* v_h_354_, lean_object* v_cons_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Grind_CommRing_MList_ctorElim___redArg(v_t_353_, v_cons_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL(lean_object* v_k_357_, lean_object* v_d_358_, lean_object* v_v_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
lean_object* v_k_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_k_361_ = lean_ctor_get(v_x_360_, 0);
lean_inc(v_k_361_);
lean_dec_ref_known(v_x_360_, 1);
v___x_362_ = lean_int_mul(v_k_357_, v_k_361_);
lean_dec(v_k_361_);
v___x_363_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_removeCode___closed__0, &l_Lean_Grind_CommRing_PPoly_removeCode___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_removeCode___closed__0);
v___x_364_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v_d_358_);
lean_ctor_set(v___x_364_, 2, v_v_359_);
lean_ctor_set(v___x_364_, 3, v___x_363_);
return v___x_364_;
}
else
{
lean_object* v_k_365_; lean_object* v_d_366_; lean_object* v_v_367_; lean_object* v_p_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_379_; 
v_k_365_ = lean_ctor_get(v_x_360_, 0);
v_d_366_ = lean_ctor_get(v_x_360_, 1);
v_v_367_ = lean_ctor_get(v_x_360_, 2);
v_p_368_ = lean_ctor_get(v_x_360_, 3);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_379_ == 0)
{
v___x_370_ = v_x_360_;
v_isShared_371_ = v_isSharedCheck_379_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_p_368_);
lean_inc(v_v_367_);
lean_inc(v_d_366_);
lean_inc(v_k_365_);
lean_dec(v_x_360_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_379_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_372_ = lean_int_mul(v_k_357_, v_k_365_);
lean_dec(v_k_365_);
v___x_373_ = lean_nat_add(v_d_358_, v_d_366_);
lean_dec(v_d_366_);
v___x_374_ = lean_nat_add(v_v_359_, v_v_367_);
lean_dec(v_v_367_);
v___x_375_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_357_, v_d_358_, v_v_359_, v_p_368_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 3, v___x_375_);
lean_ctor_set(v___x_370_, 2, v___x_374_);
lean_ctor_set(v___x_370_, 1, v___x_373_);
lean_ctor_set(v___x_370_, 0, v___x_372_);
v___x_377_ = v___x_370_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTermTL___boxed(lean_object* v_k_380_, lean_object* v_d_381_, lean_object* v_v_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_380_, v_d_381_, v_v_382_, v_x_383_);
lean_dec(v_k_380_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_mulTL(lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
if (lean_obj_tag(v_x_385_) == 0)
{
lean_object* v_k_387_; lean_object* v___x_388_; 
v_k_387_ = lean_ctor_get(v_x_385_, 0);
lean_inc(v_k_387_);
lean_dec_ref_known(v_x_385_, 1);
v___x_388_ = l_Lean_Grind_CommRing_PPoly_scale(v_k_387_, v_x_386_);
lean_dec(v_k_387_);
return v___x_388_;
}
else
{
lean_object* v_k_389_; lean_object* v_d_390_; lean_object* v_v_391_; lean_object* v_p_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_k_389_ = lean_ctor_get(v_x_385_, 0);
lean_inc(v_k_389_);
v_d_390_ = lean_ctor_get(v_x_385_, 1);
lean_inc(v_d_390_);
v_v_391_ = lean_ctor_get(v_x_385_, 2);
lean_inc(v_v_391_);
v_p_392_ = lean_ctor_get(v_x_385_, 3);
lean_inc_ref(v_p_392_);
lean_dec_ref_known(v_x_385_, 4);
lean_inc_ref(v_x_386_);
v___x_393_ = l_Lean_Grind_CommRing_PPoly_mulTermTL(v_k_389_, v_d_390_, v_v_391_, v_x_386_);
lean_dec(v_k_389_);
v___x_394_ = l_Lean_Grind_CommRing_PPoly_mulTL(v_p_392_, v_x_386_);
v___x_395_ = l_Lean_Grind_CommRing_PPoly_append(v___x_393_, v___x_394_);
return v___x_395_;
}
}
}
static lean_object* _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__0(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_to_int(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__1(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_powTL___closed__0, &l_Lean_Grind_CommRing_PPoly_powTL___closed__0_once, _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__0);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL(lean_object* v_p_400_, lean_object* v_x_401_){
_start:
{
lean_object* v_zero_402_; uint8_t v_isZero_403_; 
v_zero_402_ = lean_unsigned_to_nat(0u);
v_isZero_403_ = lean_nat_dec_eq(v_x_401_, v_zero_402_);
if (v_isZero_403_ == 1)
{
lean_object* v___x_404_; 
lean_dec_ref(v_p_400_);
v___x_404_ = lean_obj_once(&l_Lean_Grind_CommRing_PPoly_powTL___closed__1, &l_Lean_Grind_CommRing_PPoly_powTL___closed__1_once, _init_l_Lean_Grind_CommRing_PPoly_powTL___closed__1);
return v___x_404_;
}
else
{
lean_object* v_one_405_; lean_object* v_n_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_one_405_ = lean_unsigned_to_nat(1u);
v_n_406_ = lean_nat_sub(v_x_401_, v_one_405_);
lean_inc_ref(v_p_400_);
v___x_407_ = l_Lean_Grind_CommRing_PPoly_powTL(v_p_400_, v_n_406_);
lean_dec(v_n_406_);
v___x_408_ = l_Lean_Grind_CommRing_PPoly_mulTL(v___x_407_, v_p_400_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_PPoly_powTL___boxed(lean_object* v_p_409_, lean_object* v_x_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Grind_CommRing_PPoly_powTL(v_p_409_, v_x_410_);
lean_dec(v_x_410_);
return v_res_411_;
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
