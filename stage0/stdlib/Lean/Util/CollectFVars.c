// Lean compiler output
// Module: Lean.Util.CollectFVars
// Imports: public import Lean.LocalContext
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_CollectFVars_instInhabitedState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectFVars_instInhabitedState_default___closed__0;
static lean_once_cell_t l_Lean_CollectFVars_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectFVars_instInhabitedState_default___closed__1;
static lean_once_cell_t l_Lean_CollectFVars_instInhabitedState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectFVars_instInhabitedState_default___closed__2;
static const lean_array_object l_Lean_CollectFVars_instInhabitedState_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CollectFVars_instInhabitedState_default___closed__3 = (const lean_object*)&l_Lean_CollectFVars_instInhabitedState_default___closed__3_value;
static lean_once_cell_t l_Lean_CollectFVars_instInhabitedState_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectFVars_instInhabitedState_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l_Lean_CollectFVars_instInhabitedState_default___closed__1, &l_Lean_CollectFVars_instInhabitedState_default___closed__1_once, _init_l_Lean_CollectFVars_instInhabitedState_default___closed__1);
v___x_6_ = lean_obj_once(&l_Lean_CollectFVars_instInhabitedState_default___closed__0, &l_Lean_CollectFVars_instInhabitedState_default___closed__0_once, _init_l_Lean_CollectFVars_instInhabitedState_default___closed__0);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState_default___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_11_ = ((lean_object*)(l_Lean_CollectFVars_instInhabitedState_default___closed__3));
v___x_12_ = lean_box(1);
v___x_13_ = lean_obj_once(&l_Lean_CollectFVars_instInhabitedState_default___closed__2, &l_Lean_CollectFVars_instInhabitedState_default___closed__2_once, _init_l_Lean_CollectFVars_instInhabitedState_default___closed__2);
v___x_14_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
lean_ctor_set(v___x_14_, 2, v___x_11_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState_default(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_CollectFVars_instInhabitedState_default___closed__4, &l_Lean_CollectFVars_instInhabitedState_default___closed__4_once, _init_l_Lean_CollectFVars_instInhabitedState_default___closed__4);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_CollectFVars_instInhabitedState(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_CollectFVars_instInhabitedState_default;
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_State_add(lean_object* v_s_17_, lean_object* v_fvarId_18_){
_start:
{
lean_object* v_visitedExpr_19_; lean_object* v_fvarSet_20_; lean_object* v_fvarIds_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_30_; 
v_visitedExpr_19_ = lean_ctor_get(v_s_17_, 0);
v_fvarSet_20_ = lean_ctor_get(v_s_17_, 1);
v_fvarIds_21_ = lean_ctor_get(v_s_17_, 2);
v_isSharedCheck_30_ = !lean_is_exclusive(v_s_17_);
if (v_isSharedCheck_30_ == 0)
{
v___x_23_ = v_s_17_;
v_isShared_24_ = v_isSharedCheck_30_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_fvarIds_21_);
lean_inc(v_fvarSet_20_);
lean_inc(v_visitedExpr_19_);
lean_dec(v_s_17_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_30_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
lean_inc(v_fvarId_18_);
v___x_25_ = l_Lean_FVarIdSet_insert(v_fvarSet_20_, v_fvarId_18_);
v___x_26_ = lean_array_push(v_fvarIds_21_, v_fvarId_18_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 2, v___x_26_);
lean_ctor_set(v___x_23_, 1, v___x_25_);
v___x_28_ = v___x_23_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_visitedExpr_19_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v___x_25_);
lean_ctor_set(v_reuseFailAlloc_29_, 2, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(lean_object* v_m_31_, lean_object* v_query_32_, lean_object* v_x_33_, lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_zero_36_; uint8_t v_isZero_37_; 
v_zero_36_ = lean_unsigned_to_nat(0u);
v_isZero_37_ = lean_nat_dec_eq(v_x_34_, v_zero_36_);
if (v_isZero_37_ == 1)
{
lean_dec(v_x_35_);
lean_dec(v_x_34_);
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(2);
return v___x_38_;
}
else
{
lean_object* v_val_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_val_39_ = lean_ctor_get(v_x_33_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v_x_33_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v_x_33_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_val_39_);
lean_dec(v_x_33_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_val_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
else
{
lean_object* v_keyArray_47_; lean_object* v_valueArray_48_; lean_object* v___x_49_; uint8_t v_isSome_50_; 
v_keyArray_47_ = lean_ctor_get(v_m_31_, 1);
v_valueArray_48_ = lean_ctor_get(v_m_31_, 2);
v___x_49_ = lean_array_fget_borrowed(v_keyArray_47_, v_x_35_);
v_isSome_50_ = lean_noption_is_some(v___x_49_);
if (v_isSome_50_ == 0)
{
lean_dec(v_x_34_);
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v___x_51_; 
v___x_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_51_, 0, v_x_35_);
return v___x_51_;
}
else
{
lean_object* v_val_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
lean_dec(v_x_35_);
v_val_52_ = lean_ctor_get(v_x_33_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v_x_33_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v_x_33_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_val_52_);
lean_dec(v_x_33_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_val_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
else
{
lean_object* v_one_60_; lean_object* v_n_61_; lean_object* v___y_63_; 
v_one_60_ = lean_unsigned_to_nat(1u);
v_n_61_ = lean_nat_sub(v_x_34_, v_one_60_);
lean_dec(v_x_34_);
if (v_isSome_50_ == 0)
{
goto v___jp_69_;
}
else
{
lean_object* v___x_71_; uint8_t v_isSome_72_; 
v___x_71_ = lean_array_fget_borrowed(v_valueArray_48_, v_x_35_);
v_isSome_72_ = lean_noption_is_some(v___x_71_);
if (v_isSome_72_ == 0)
{
goto v___jp_69_;
}
else
{
lean_object* v_val_73_; uint8_t v___x_74_; 
lean_inc(v___x_49_);
v_val_73_ = lean_noption_get(v___x_49_);
v___x_74_ = lean_expr_eqv(v_val_73_, v_query_32_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
lean_dec(v_val_73_);
v___x_75_ = lean_array_get_size(v_keyArray_47_);
v___x_76_ = lean_nat_add(v_x_35_, v_one_60_);
lean_dec(v_x_35_);
v___x_77_ = lean_nat_dec_lt(v___x_76_, v___x_75_);
if (v___x_77_ == 0)
{
lean_dec(v___x_76_);
v_x_34_ = v_n_61_;
v_x_35_ = v_zero_36_;
goto _start;
}
else
{
v_x_34_ = v_n_61_;
v_x_35_ = v___x_76_;
goto _start;
}
}
else
{
lean_object* v_val_80_; lean_object* v___x_81_; 
lean_dec(v_n_61_);
lean_dec(v_x_33_);
lean_inc(v___x_71_);
v_val_80_ = lean_noption_get(v___x_71_);
v___x_81_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_81_, 0, v_x_35_);
lean_ctor_set(v___x_81_, 1, v_val_73_);
lean_ctor_set(v___x_81_, 2, v_val_80_);
return v___x_81_;
}
}
}
v___jp_62_:
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_64_ = lean_array_get_size(v_keyArray_47_);
v___x_65_ = lean_nat_add(v_x_35_, v_one_60_);
lean_dec(v_x_35_);
v___x_66_ = lean_nat_dec_lt(v___x_65_, v___x_64_);
if (v___x_66_ == 0)
{
lean_dec(v___x_65_);
v_x_33_ = v___y_63_;
v_x_34_ = v_n_61_;
v_x_35_ = v_zero_36_;
goto _start;
}
else
{
v_x_33_ = v___y_63_;
v_x_34_ = v_n_61_;
v_x_35_ = v___x_65_;
goto _start;
}
}
v___jp_69_:
{
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v___x_70_; 
lean_inc(v_x_35_);
v___x_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_70_, 0, v_x_35_);
v___y_63_ = v___x_70_;
goto v___jp_62_;
}
else
{
v___y_63_ = v_x_33_;
goto v___jp_62_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg___boxed(lean_object* v_m_82_, lean_object* v_query_83_, lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(v_m_82_, v_query_83_, v_x_84_, v_x_85_, v_x_86_);
lean_dec_ref(v_query_83_);
lean_dec_ref(v_m_82_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___redArg(lean_object* v_m_88_, lean_object* v_query_89_){
_start:
{
lean_object* v_keyArray_90_; lean_object* v___x_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; uint64_t v_fold_95_; uint64_t v___x_96_; uint64_t v___x_97_; uint64_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; size_t v___x_102_; size_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_keyArray_90_ = lean_ctor_get(v_m_88_, 1);
v___x_91_ = lean_array_get_size(v_keyArray_90_);
v___x_92_ = l_Lean_Expr_hash(v_query_89_);
v___x_93_ = 32ULL;
v___x_94_ = lean_uint64_shift_right(v___x_92_, v___x_93_);
v_fold_95_ = lean_uint64_xor(v___x_92_, v___x_94_);
v___x_96_ = 16ULL;
v___x_97_ = lean_uint64_shift_right(v_fold_95_, v___x_96_);
v___x_98_ = lean_uint64_xor(v_fold_95_, v___x_97_);
v___x_99_ = lean_uint64_to_usize(v___x_98_);
v___x_100_ = lean_usize_of_nat(v___x_91_);
v___x_101_ = ((size_t)1ULL);
v___x_102_ = lean_usize_sub(v___x_100_, v___x_101_);
v___x_103_ = lean_usize_land(v___x_99_, v___x_102_);
v___x_104_ = lean_usize_to_nat(v___x_103_);
v___x_105_ = lean_box(0);
v___x_106_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(v_m_88_, v_query_89_, v___x_105_, v___x_91_, v___x_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___redArg___boxed(lean_object* v_m_107_, lean_object* v_query_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___redArg(v_m_107_, v_query_108_);
lean_dec_ref(v_query_108_);
lean_dec_ref(v_m_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6___redArg(lean_object* v_b_110_, lean_object* v_acc_111_, lean_object* v_i_112_){
_start:
{
lean_object* v___y_114_; lean_object* v_keyArray_122_; lean_object* v_valueArray_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_keyArray_122_ = lean_ctor_get(v_b_110_, 1);
v_valueArray_123_ = lean_ctor_get(v_b_110_, 2);
v___x_124_ = lean_array_get_size(v_keyArray_122_);
v___x_125_ = lean_nat_dec_lt(v_i_112_, v___x_124_);
if (v___x_125_ == 0)
{
lean_dec(v_i_112_);
return v_acc_111_;
}
else
{
lean_object* v___x_126_; uint8_t v_isSome_127_; 
v___x_126_ = lean_array_fget_borrowed(v_keyArray_122_, v_i_112_);
v_isSome_127_ = lean_noption_is_some(v___x_126_);
if (v_isSome_127_ == 0)
{
goto v___jp_118_;
}
else
{
lean_object* v___x_128_; uint8_t v_isSome_129_; 
v___x_128_ = lean_array_fget_borrowed(v_valueArray_123_, v_i_112_);
v_isSome_129_ = lean_noption_is_some(v___x_128_);
if (v_isSome_129_ == 0)
{
goto v___jp_118_;
}
else
{
lean_object* v_val_130_; lean_object* v_val_131_; lean_object* v_i_133_; lean_object* v___x_138_; 
lean_inc(v___x_126_);
v_val_130_ = lean_noption_get(v___x_126_);
lean_inc(v___x_128_);
v_val_131_ = lean_noption_get(v___x_128_);
v___x_138_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___redArg(v_acc_111_, v_val_130_);
switch(lean_obj_tag(v___x_138_))
{
case 0:
{
lean_object* v_index_139_; lean_object* v_size_140_; lean_object* v___x_141_; 
v_index_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_index_139_);
lean_dec_ref_known(v___x_138_, 3);
v_size_140_ = lean_ctor_get(v_acc_111_, 0);
lean_inc(v_size_140_);
v___x_141_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_111_, v_size_140_, v_index_139_, v_val_130_, v_val_131_);
lean_dec(v_index_139_);
v___y_114_ = v___x_141_;
goto v___jp_113_;
}
case 1:
{
lean_object* v_index_142_; 
v_index_142_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_index_142_);
lean_dec_ref_known(v___x_138_, 1);
v_i_133_ = v_index_142_;
goto v___jp_132_;
}
default: 
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_111_, v___x_143_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_index_145_; 
v_index_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_index_145_);
lean_dec_ref_known(v___x_144_, 1);
v_i_133_ = v_index_145_;
goto v___jp_132_;
}
else
{
lean_dec(v_val_131_);
lean_dec(v_val_130_);
v___y_114_ = v_acc_111_;
goto v___jp_113_;
}
}
}
v___jp_132_:
{
lean_object* v_size_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_size_134_ = lean_ctor_get(v_acc_111_, 0);
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = lean_nat_add(v_size_134_, v___x_135_);
v___x_137_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_111_, v___x_136_, v_i_133_, v_val_130_, v_val_131_);
lean_dec(v_i_133_);
v___y_114_ = v___x_137_;
goto v___jp_113_;
}
}
}
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_nat_add(v_i_112_, v___x_115_);
lean_dec(v_i_112_);
v_acc_111_ = v___y_114_;
v_i_112_ = v___x_116_;
goto _start;
}
v___jp_118_:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_i_112_, v___x_119_);
lean_dec(v_i_112_);
v_i_112_ = v___x_120_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_b_146_, lean_object* v_acc_147_, lean_object* v_i_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6___redArg(v_b_146_, v_acc_147_, v_i_148_);
lean_dec_ref(v_b_146_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5___redArg(lean_object* v_init_150_, lean_object* v_b_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6___redArg(v_b_151_, v_init_150_, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5___redArg___boxed(lean_object* v_init_154_, lean_object* v_b_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5___redArg(v_init_154_, v_b_155_);
lean_dec_ref(v_b_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2___redArg(lean_object* v_m_157_){
_start:
{
lean_object* v_keyArray_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_cellCount_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_target_165_; lean_object* v___x_166_; 
v_keyArray_158_ = lean_ctor_get(v_m_157_, 1);
v___x_159_ = lean_array_get_size(v_keyArray_158_);
v___x_160_ = lean_unsigned_to_nat(2u);
v_cellCount_161_ = lean_nat_mul(v___x_159_, v___x_160_);
v___x_162_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_161_);
v___x_163_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_161_);
v___x_164_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_161_);
v_target_165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_165_, 0, v___x_162_);
lean_ctor_set(v_target_165_, 1, v___x_163_);
lean_ctor_set(v_target_165_, 2, v___x_164_);
v___x_166_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5___redArg(v_target_165_, v_m_157_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2___redArg___boxed(lean_object* v_m_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2___redArg(v_m_167_);
lean_dec_ref(v_m_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(lean_object* v_m_169_, lean_object* v_query_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___redArg(v_m_169_, v_query_170_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_index_172_; lean_object* v_key_173_; lean_object* v_value_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
v_index_172_ = lean_ctor_get(v___x_171_, 0);
v_key_173_ = lean_ctor_get(v___x_171_, 1);
v_value_174_ = lean_ctor_get(v___x_171_, 2);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_171_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_value_174_);
lean_inc(v_key_173_);
lean_inc(v_index_172_);
lean_dec(v___x_171_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_index_172_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_key_173_);
lean_ctor_set(v_reuseFailAlloc_180_, 2, v_value_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_object* v___x_182_; 
lean_dec(v___x_171_);
v___x_182_ = lean_box(1);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg___boxed(lean_object* v_m_183_, lean_object* v_query_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_m_183_, v_query_184_);
lean_dec_ref(v_query_184_);
lean_dec_ref(v_m_183_);
return v_res_185_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(lean_object* v_m_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_m_186_, v_a_187_);
if (lean_obj_tag(v___x_188_) == 0)
{
uint8_t v___x_189_; 
lean_dec_ref_known(v___x_188_, 3);
v___x_189_ = 1;
return v___x_189_;
}
else
{
uint8_t v___x_190_; 
v___x_190_ = 0;
return v___x_190_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg___boxed(lean_object* v_m_191_, lean_object* v_a_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_191_, v_a_192_);
lean_dec_ref(v_a_192_);
lean_dec_ref(v_m_191_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_visit(lean_object* v_e_195_, lean_object* v_s_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = l_Lean_Expr_hasFVar(v_e_195_);
if (v___x_197_ == 0)
{
lean_dec_ref(v_e_195_);
return v_s_196_;
}
else
{
lean_object* v_visitedExpr_198_; lean_object* v_fvarSet_199_; lean_object* v_fvarIds_200_; lean_object* v___y_202_; uint8_t v___x_205_; 
v_visitedExpr_198_ = lean_ctor_get(v_s_196_, 0);
v_fvarSet_199_ = lean_ctor_get(v_s_196_, 1);
v_fvarIds_200_ = lean_ctor_get(v_s_196_, 2);
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_visitedExpr_198_, v_e_195_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___y_208_; lean_object* v_i_209_; lean_object* v___y_215_; lean_object* v___y_225_; lean_object* v_i_226_; lean_object* v___x_241_; 
lean_inc_ref(v_fvarIds_200_);
lean_inc(v_fvarSet_199_);
lean_inc_ref(v_visitedExpr_198_);
lean_dec_ref(v_s_196_);
v___x_206_ = lean_box(0);
v___x_241_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___redArg(v_visitedExpr_198_, v_e_195_);
switch(lean_obj_tag(v___x_241_))
{
case 0:
{
lean_dec_ref_known(v___x_241_, 3);
v___y_202_ = v_visitedExpr_198_;
goto v___jp_201_;
}
case 1:
{
lean_object* v_index_242_; lean_object* v_size_243_; lean_object* v_keyArray_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_index_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_index_242_);
lean_dec_ref_known(v___x_241_, 1);
v_size_243_ = lean_ctor_get(v_visitedExpr_198_, 0);
v_keyArray_244_ = lean_ctor_get(v_visitedExpr_198_, 1);
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_nat_add(v_size_243_, v___x_245_);
v___x_247_ = lean_array_get_size(v_keyArray_244_);
v___x_248_ = lean_nat_dec_lt(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v___x_246_);
lean_dec(v_index_242_);
goto v___jp_231_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_249_ = lean_unsigned_to_nat(4u);
v___x_250_ = lean_nat_mul(v___x_246_, v___x_249_);
v___x_251_ = lean_unsigned_to_nat(3u);
v___x_252_ = lean_nat_mul(v___x_247_, v___x_251_);
v___x_253_ = lean_nat_dec_le(v___x_250_, v___x_252_);
lean_dec(v___x_252_);
lean_dec(v___x_250_);
if (v___x_253_ == 0)
{
lean_dec(v___x_246_);
lean_dec(v_index_242_);
goto v___jp_231_;
}
else
{
lean_object* v___x_254_; 
lean_inc_ref(v_e_195_);
v___x_254_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedExpr_198_, v___x_246_, v_index_242_, v_e_195_, v___x_206_);
lean_dec(v_index_242_);
v___y_202_ = v___x_254_;
goto v___jp_201_;
}
}
}
default: 
{
lean_object* v_size_255_; lean_object* v_keyArray_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_size_255_ = lean_ctor_get(v_visitedExpr_198_, 0);
v_keyArray_256_ = lean_ctor_get(v_visitedExpr_198_, 1);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_size_255_, v___x_257_);
v___x_259_ = lean_array_get_size(v_keyArray_256_);
v___x_260_ = lean_nat_dec_lt(v___x_258_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec(v___x_258_);
v___x_261_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2___redArg(v_visitedExpr_198_);
lean_dec_ref(v_visitedExpr_198_);
v___y_215_ = v___x_261_;
goto v___jp_214_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_262_ = lean_unsigned_to_nat(4u);
v___x_263_ = lean_nat_mul(v___x_258_, v___x_262_);
lean_dec(v___x_258_);
v___x_264_ = lean_unsigned_to_nat(3u);
v___x_265_ = lean_nat_mul(v___x_259_, v___x_264_);
v___x_266_ = lean_nat_dec_le(v___x_263_, v___x_265_);
lean_dec(v___x_265_);
lean_dec(v___x_263_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2___redArg(v_visitedExpr_198_);
lean_dec_ref(v_visitedExpr_198_);
v___y_215_ = v___x_267_;
goto v___jp_214_;
}
else
{
v___y_215_ = v_visitedExpr_198_;
goto v___jp_214_;
}
}
}
}
v___jp_207_:
{
lean_object* v_size_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_size_210_ = lean_ctor_get(v___y_208_, 0);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_size_210_, v___x_211_);
lean_inc_ref(v_e_195_);
v___x_213_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_208_, v___x_212_, v_i_209_, v_e_195_, v___x_206_);
lean_dec(v_i_209_);
v___y_202_ = v___x_213_;
goto v___jp_201_;
}
v___jp_214_:
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___redArg(v___y_215_, v_e_195_);
switch(lean_obj_tag(v___x_216_))
{
case 0:
{
lean_object* v_index_217_; lean_object* v_size_218_; lean_object* v___x_219_; 
v_index_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_index_217_);
lean_dec_ref_known(v___x_216_, 3);
v_size_218_ = lean_ctor_get(v___y_215_, 0);
lean_inc(v_size_218_);
lean_inc_ref(v_e_195_);
v___x_219_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_215_, v_size_218_, v_index_217_, v_e_195_, v___x_206_);
lean_dec(v_index_217_);
v___y_202_ = v___x_219_;
goto v___jp_201_;
}
case 1:
{
lean_object* v_index_220_; 
v_index_220_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_index_220_);
lean_dec_ref_known(v___x_216_, 1);
v___y_208_ = v___y_215_;
v_i_209_ = v_index_220_;
goto v___jp_207_;
}
default: 
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_215_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_index_223_; 
v_index_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_index_223_);
lean_dec_ref_known(v___x_222_, 1);
v___y_208_ = v___y_215_;
v_i_209_ = v_index_223_;
goto v___jp_207_;
}
else
{
v___y_202_ = v___y_215_;
goto v___jp_201_;
}
}
}
}
v___jp_224_:
{
lean_object* v_size_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_size_227_ = lean_ctor_get(v___y_225_, 0);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_add(v_size_227_, v___x_228_);
lean_inc_ref(v_e_195_);
v___x_230_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_225_, v___x_229_, v_i_226_, v_e_195_, v___x_206_);
lean_dec(v_i_226_);
v___y_202_ = v___x_230_;
goto v___jp_201_;
}
v___jp_231_:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2___redArg(v_visitedExpr_198_);
lean_dec_ref(v_visitedExpr_198_);
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___redArg(v___x_232_, v_e_195_);
switch(lean_obj_tag(v___x_233_))
{
case 0:
{
lean_object* v_index_234_; lean_object* v_size_235_; lean_object* v___x_236_; 
v_index_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_index_234_);
lean_dec_ref_known(v___x_233_, 3);
v_size_235_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_size_235_);
lean_inc_ref(v_e_195_);
v___x_236_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_232_, v_size_235_, v_index_234_, v_e_195_, v___x_206_);
lean_dec(v_index_234_);
v___y_202_ = v___x_236_;
goto v___jp_201_;
}
case 1:
{
lean_object* v_index_237_; 
v_index_237_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_index_237_);
lean_dec_ref_known(v___x_233_, 1);
v___y_225_ = v___x_232_;
v_i_226_ = v_index_237_;
goto v___jp_224_;
}
default: 
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_232_, v___x_238_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_index_240_; 
v_index_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_index_240_);
lean_dec_ref_known(v___x_239_, 1);
v___y_225_ = v___x_232_;
v_i_226_ = v_index_240_;
goto v___jp_224_;
}
else
{
v___y_202_ = v___x_232_;
goto v___jp_201_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_195_);
return v_s_196_;
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_203_, 0, v___y_202_);
lean_ctor_set(v___x_203_, 1, v_fvarSet_199_);
lean_ctor_set(v___x_203_, 2, v_fvarIds_200_);
v___x_204_ = l_Lean_CollectFVars_main(v_e_195_, v___x_203_);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectFVars_main(lean_object* v_x_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_d_271_; lean_object* v_b_272_; lean_object* v___y_273_; 
switch(lean_obj_tag(v_x_268_))
{
case 11:
{
lean_object* v_struct_276_; lean_object* v___x_277_; 
v_struct_276_ = lean_ctor_get(v_x_268_, 2);
lean_inc_ref(v_struct_276_);
lean_dec_ref_known(v_x_268_, 3);
v___x_277_ = l_Lean_CollectFVars_visit(v_struct_276_, v_a_269_);
return v___x_277_;
}
case 7:
{
lean_object* v_binderType_278_; lean_object* v_body_279_; 
v_binderType_278_ = lean_ctor_get(v_x_268_, 1);
lean_inc_ref(v_binderType_278_);
v_body_279_ = lean_ctor_get(v_x_268_, 2);
lean_inc_ref(v_body_279_);
lean_dec_ref_known(v_x_268_, 3);
v_d_271_ = v_binderType_278_;
v_b_272_ = v_body_279_;
v___y_273_ = v_a_269_;
goto v___jp_270_;
}
case 6:
{
lean_object* v_binderType_280_; lean_object* v_body_281_; 
v_binderType_280_ = lean_ctor_get(v_x_268_, 1);
lean_inc_ref(v_binderType_280_);
v_body_281_ = lean_ctor_get(v_x_268_, 2);
lean_inc_ref(v_body_281_);
lean_dec_ref_known(v_x_268_, 3);
v_d_271_ = v_binderType_280_;
v_b_272_ = v_body_281_;
v___y_273_ = v_a_269_;
goto v___jp_270_;
}
case 8:
{
lean_object* v_type_282_; lean_object* v_value_283_; lean_object* v_body_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_type_282_ = lean_ctor_get(v_x_268_, 1);
lean_inc_ref(v_type_282_);
v_value_283_ = lean_ctor_get(v_x_268_, 2);
lean_inc_ref(v_value_283_);
v_body_284_ = lean_ctor_get(v_x_268_, 3);
lean_inc_ref(v_body_284_);
lean_dec_ref_known(v_x_268_, 4);
v___x_285_ = l_Lean_CollectFVars_visit(v_type_282_, v_a_269_);
v___x_286_ = l_Lean_CollectFVars_visit(v_value_283_, v___x_285_);
v___x_287_ = l_Lean_CollectFVars_visit(v_body_284_, v___x_286_);
return v___x_287_;
}
case 5:
{
lean_object* v_fn_288_; lean_object* v_arg_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_fn_288_ = lean_ctor_get(v_x_268_, 0);
lean_inc_ref(v_fn_288_);
v_arg_289_ = lean_ctor_get(v_x_268_, 1);
lean_inc_ref(v_arg_289_);
lean_dec_ref_known(v_x_268_, 2);
v___x_290_ = l_Lean_CollectFVars_visit(v_fn_288_, v_a_269_);
v___x_291_ = l_Lean_CollectFVars_visit(v_arg_289_, v___x_290_);
return v___x_291_;
}
case 10:
{
lean_object* v_expr_292_; lean_object* v___x_293_; 
v_expr_292_ = lean_ctor_get(v_x_268_, 1);
lean_inc_ref(v_expr_292_);
lean_dec_ref_known(v_x_268_, 2);
v___x_293_ = l_Lean_CollectFVars_visit(v_expr_292_, v_a_269_);
return v___x_293_;
}
case 1:
{
lean_object* v_fvarId_294_; lean_object* v___x_295_; 
v_fvarId_294_ = lean_ctor_get(v_x_268_, 0);
lean_inc(v_fvarId_294_);
lean_dec_ref_known(v_x_268_, 1);
v___x_295_ = l_Lean_CollectFVars_State_add(v_a_269_, v_fvarId_294_);
return v___x_295_;
}
default: 
{
lean_dec_ref(v_x_268_);
return v_a_269_;
}
}
v___jp_270_:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = l_Lean_CollectFVars_visit(v_d_271_, v___y_273_);
v___x_275_ = l_Lean_CollectFVars_visit(v_b_272_, v___x_274_);
return v___x_275_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(lean_object* v_00_u03b2_296_, lean_object* v_m_297_, lean_object* v_a_298_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___redArg(v_m_297_, v_a_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0___boxed(lean_object* v_00_u03b2_300_, lean_object* v_m_301_, lean_object* v_a_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0(v_00_u03b2_300_, v_m_301_, v_a_302_);
lean_dec_ref(v_a_302_);
lean_dec_ref(v_m_301_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1(lean_object* v_00_u03b2_305_, lean_object* v_m_306_, lean_object* v_query_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___redArg(v_m_306_, v_query_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1___boxed(lean_object* v_00_u03b2_309_, lean_object* v_m_310_, lean_object* v_query_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1(v_00_u03b2_309_, v_m_310_, v_query_311_);
lean_dec_ref(v_query_311_);
lean_dec_ref(v_m_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2(lean_object* v_00_u03b2_313_, lean_object* v_m_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2___redArg(v_m_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2___boxed(lean_object* v_00_u03b2_316_, lean_object* v_m_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2(v_00_u03b2_316_, v_m_317_);
lean_dec_ref(v_m_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1(lean_object* v_00_u03b2_319_, lean_object* v_m_320_, lean_object* v_query_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___redArg(v_m_320_, v_query_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1___boxed(lean_object* v_00_u03b2_323_, lean_object* v_m_324_, lean_object* v_query_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectFVars_visit_spec__0_spec__1(v_00_u03b2_323_, v_m_324_, v_query_325_);
lean_dec_ref(v_query_325_);
lean_dec_ref(v_m_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3(lean_object* v_00_u03b2_327_, lean_object* v_m_328_, lean_object* v_query_329_, lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3___redArg(v_m_328_, v_query_329_, v_x_330_, v_x_331_, v_x_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3___boxed(lean_object* v_00_u03b2_335_, lean_object* v_m_336_, lean_object* v_query_337_, lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectFVars_visit_spec__1_spec__3(v_00_u03b2_335_, v_m_336_, v_query_337_, v_x_338_, v_x_339_, v_x_340_, v_x_341_);
lean_dec_ref(v_query_337_);
lean_dec_ref(v_m_336_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5(lean_object* v_00_u03b2_343_, lean_object* v_init_344_, lean_object* v_b_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5___redArg(v_init_344_, v_b_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5___boxed(lean_object* v_00_u03b2_347_, lean_object* v_init_348_, lean_object* v_b_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5(v_00_u03b2_347_, v_init_348_, v_b_349_);
lean_dec_ref(v_b_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_351_, lean_object* v_b_352_, lean_object* v_acc_353_, lean_object* v_i_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6___redArg(v_b_352_, v_acc_353_, v_i_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6___boxed(lean_object* v_00_u03b2_356_, lean_object* v_b_357_, lean_object* v_acc_358_, lean_object* v_i_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectFVars_visit_spec__2_spec__5_spec__6(v_00_u03b2_356_, v_b_357_, v_acc_358_, v_i_359_);
lean_dec_ref(v_b_357_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectFVars(lean_object* v_s_361_, lean_object* v_e_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_CollectFVars_main(v_e_362_, v_s_361_);
return v___x_363_;
}
}
lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectFVars_instInhabitedState_default = _init_l_Lean_CollectFVars_instInhabitedState_default();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState_default);
l_Lean_CollectFVars_instInhabitedState = _init_l_Lean_CollectFVars_instInhabitedState();
lean_mark_persistent(l_Lean_CollectFVars_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_LocalContext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectFVars(builtin);
}
#ifdef __cplusplus
}
#endif
