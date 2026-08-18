// Lean compiler output
// Module: Lean.Util.CollectMVars
// Imports: public import Lean.Expr
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_CollectMVars_instInhabitedState___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectMVars_instInhabitedState___closed__0;
static lean_once_cell_t l_Lean_CollectMVars_instInhabitedState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectMVars_instInhabitedState___closed__1;
static lean_once_cell_t l_Lean_CollectMVars_instInhabitedState___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectMVars_instInhabitedState___closed__2;
static const lean_array_object l_Lean_CollectMVars_instInhabitedState___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CollectMVars_instInhabitedState___closed__3 = (const lean_object*)&l_Lean_CollectMVars_instInhabitedState___closed__3_value;
static lean_once_cell_t l_Lean_CollectMVars_instInhabitedState___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectMVars_instInhabitedState___closed__4;
LEAN_EXPORT lean_object* l_Lean_CollectMVars_instInhabitedState;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectMVars_visit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectMVars_main(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_collectMVars(lean_object*, lean_object*);
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState___closed__0(void){
_start:
{
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState___closed__1(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l_Lean_CollectMVars_instInhabitedState___closed__1, &l_Lean_CollectMVars_instInhabitedState___closed__1_once, _init_l_Lean_CollectMVars_instInhabitedState___closed__1);
v___x_6_ = lean_obj_once(&l_Lean_CollectMVars_instInhabitedState___closed__0, &l_Lean_CollectMVars_instInhabitedState___closed__0_once, _init_l_Lean_CollectMVars_instInhabitedState___closed__0);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = ((lean_object*)(l_Lean_CollectMVars_instInhabitedState___closed__3));
v___x_12_ = lean_obj_once(&l_Lean_CollectMVars_instInhabitedState___closed__2, &l_Lean_CollectMVars_instInhabitedState___closed__2_once, _init_l_Lean_CollectMVars_instInhabitedState___closed__2);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_CollectMVars_instInhabitedState(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Lean_CollectMVars_instInhabitedState___closed__4, &l_Lean_CollectMVars_instInhabitedState___closed__4_once, _init_l_Lean_CollectMVars_instInhabitedState___closed__4);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(lean_object* v_m_15_, lean_object* v_query_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_zero_20_; uint8_t v_isZero_21_; 
v_zero_20_ = lean_unsigned_to_nat(0u);
v_isZero_21_ = lean_nat_dec_eq(v_x_18_, v_zero_20_);
if (v_isZero_21_ == 1)
{
lean_dec(v_x_19_);
lean_dec(v_x_18_);
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_22_; 
v___x_22_ = lean_box(2);
return v___x_22_;
}
else
{
lean_object* v_val_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
v_val_23_ = lean_ctor_get(v_x_17_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v_x_17_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v_x_17_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_val_23_);
lean_dec(v_x_17_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_val_23_);
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
else
{
lean_object* v_keyArray_31_; lean_object* v_valueArray_32_; lean_object* v___x_33_; uint8_t v_isSome_34_; 
v_keyArray_31_ = lean_ctor_get(v_m_15_, 1);
v_valueArray_32_ = lean_ctor_get(v_m_15_, 2);
v___x_33_ = lean_array_fget_borrowed(v_keyArray_31_, v_x_19_);
v_isSome_34_ = lean_noption_is_some(v___x_33_);
if (v_isSome_34_ == 0)
{
lean_dec(v_x_18_);
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v_x_19_);
return v___x_35_;
}
else
{
lean_object* v_val_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
lean_dec(v_x_19_);
v_val_36_ = lean_ctor_get(v_x_17_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v_x_17_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v_x_17_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_val_36_);
lean_dec(v_x_17_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_val_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
else
{
lean_object* v_one_44_; lean_object* v_n_45_; lean_object* v___y_47_; 
v_one_44_ = lean_unsigned_to_nat(1u);
v_n_45_ = lean_nat_sub(v_x_18_, v_one_44_);
lean_dec(v_x_18_);
if (v_isSome_34_ == 0)
{
goto v___jp_53_;
}
else
{
lean_object* v___x_55_; uint8_t v_isSome_56_; 
v___x_55_ = lean_array_fget_borrowed(v_valueArray_32_, v_x_19_);
v_isSome_56_ = lean_noption_is_some(v___x_55_);
if (v_isSome_56_ == 0)
{
goto v___jp_53_;
}
else
{
lean_object* v_val_57_; uint8_t v___x_58_; 
lean_inc(v___x_33_);
v_val_57_ = lean_noption_get(v___x_33_);
v___x_58_ = lean_expr_eqv(v_val_57_, v_query_16_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
lean_dec(v_val_57_);
v___x_59_ = lean_array_get_size(v_keyArray_31_);
v___x_60_ = lean_nat_add(v_x_19_, v_one_44_);
lean_dec(v_x_19_);
v___x_61_ = lean_nat_dec_lt(v___x_60_, v___x_59_);
if (v___x_61_ == 0)
{
lean_dec(v___x_60_);
v_x_18_ = v_n_45_;
v_x_19_ = v_zero_20_;
goto _start;
}
else
{
v_x_18_ = v_n_45_;
v_x_19_ = v___x_60_;
goto _start;
}
}
else
{
lean_object* v_val_64_; lean_object* v___x_65_; 
lean_dec(v_n_45_);
lean_dec(v_x_17_);
lean_inc(v___x_55_);
v_val_64_ = lean_noption_get(v___x_55_);
v___x_65_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_65_, 0, v_x_19_);
lean_ctor_set(v___x_65_, 1, v_val_57_);
lean_ctor_set(v___x_65_, 2, v_val_64_);
return v___x_65_;
}
}
}
v___jp_46_:
{
lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_48_ = lean_array_get_size(v_keyArray_31_);
v___x_49_ = lean_nat_add(v_x_19_, v_one_44_);
lean_dec(v_x_19_);
v___x_50_ = lean_nat_dec_lt(v___x_49_, v___x_48_);
if (v___x_50_ == 0)
{
lean_dec(v___x_49_);
v_x_17_ = v___y_47_;
v_x_18_ = v_n_45_;
v_x_19_ = v_zero_20_;
goto _start;
}
else
{
v_x_17_ = v___y_47_;
v_x_18_ = v_n_45_;
v_x_19_ = v___x_49_;
goto _start;
}
}
v___jp_53_:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_54_; 
lean_inc(v_x_19_);
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v_x_19_);
v___y_47_ = v___x_54_;
goto v___jp_46_;
}
else
{
v___y_47_ = v_x_17_;
goto v___jp_46_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg___boxed(lean_object* v_m_66_, lean_object* v_query_67_, lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(v_m_66_, v_query_67_, v_x_68_, v_x_69_, v_x_70_);
lean_dec_ref(v_query_67_);
lean_dec_ref(v_m_66_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___redArg(lean_object* v_m_72_, lean_object* v_query_73_){
_start:
{
lean_object* v_keyArray_74_; lean_object* v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v___x_78_; uint64_t v_fold_79_; uint64_t v___x_80_; uint64_t v___x_81_; uint64_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_keyArray_74_ = lean_ctor_get(v_m_72_, 1);
v___x_75_ = lean_array_get_size(v_keyArray_74_);
v___x_76_ = l_Lean_Expr_hash(v_query_73_);
v___x_77_ = 32ULL;
v___x_78_ = lean_uint64_shift_right(v___x_76_, v___x_77_);
v_fold_79_ = lean_uint64_xor(v___x_76_, v___x_78_);
v___x_80_ = 16ULL;
v___x_81_ = lean_uint64_shift_right(v_fold_79_, v___x_80_);
v___x_82_ = lean_uint64_xor(v_fold_79_, v___x_81_);
v___x_83_ = lean_uint64_to_usize(v___x_82_);
v___x_84_ = lean_usize_of_nat(v___x_75_);
v___x_85_ = ((size_t)1ULL);
v___x_86_ = lean_usize_sub(v___x_84_, v___x_85_);
v___x_87_ = lean_usize_land(v___x_83_, v___x_86_);
v___x_88_ = lean_usize_to_nat(v___x_87_);
v___x_89_ = lean_box(0);
v___x_90_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(v_m_72_, v_query_73_, v___x_89_, v___x_75_, v___x_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___redArg___boxed(lean_object* v_m_91_, lean_object* v_query_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___redArg(v_m_91_, v_query_92_);
lean_dec_ref(v_query_92_);
lean_dec_ref(v_m_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(lean_object* v_m_94_, lean_object* v_query_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___redArg(v_m_94_, v_query_95_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_index_97_; lean_object* v_key_98_; lean_object* v_value_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
v_index_97_ = lean_ctor_get(v___x_96_, 0);
v_key_98_ = lean_ctor_get(v___x_96_, 1);
v_value_99_ = lean_ctor_get(v___x_96_, 2);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_96_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_value_99_);
lean_inc(v_key_98_);
lean_inc(v_index_97_);
lean_dec(v___x_96_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_index_97_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_key_98_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v_value_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
else
{
lean_object* v___x_107_; 
lean_dec(v___x_96_);
v___x_107_ = lean_box(1);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg___boxed(lean_object* v_m_108_, lean_object* v_query_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_m_108_, v_query_109_);
lean_dec_ref(v_query_109_);
lean_dec_ref(v_m_108_);
return v_res_110_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(lean_object* v_m_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_m_111_, v_a_112_);
if (lean_obj_tag(v___x_113_) == 0)
{
uint8_t v___x_114_; 
lean_dec_ref_known(v___x_113_, 3);
v___x_114_ = 1;
return v___x_114_;
}
else
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg___boxed(lean_object* v_m_116_, lean_object* v_a_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_m_116_, v_a_117_);
lean_dec_ref(v_a_117_);
lean_dec_ref(v_m_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6___redArg(lean_object* v_b_120_, lean_object* v_acc_121_, lean_object* v_i_122_){
_start:
{
lean_object* v___y_124_; lean_object* v_keyArray_132_; lean_object* v_valueArray_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_keyArray_132_ = lean_ctor_get(v_b_120_, 1);
v_valueArray_133_ = lean_ctor_get(v_b_120_, 2);
v___x_134_ = lean_array_get_size(v_keyArray_132_);
v___x_135_ = lean_nat_dec_lt(v_i_122_, v___x_134_);
if (v___x_135_ == 0)
{
lean_dec(v_i_122_);
return v_acc_121_;
}
else
{
lean_object* v___x_136_; uint8_t v_isSome_137_; 
v___x_136_ = lean_array_fget_borrowed(v_keyArray_132_, v_i_122_);
v_isSome_137_ = lean_noption_is_some(v___x_136_);
if (v_isSome_137_ == 0)
{
goto v___jp_128_;
}
else
{
lean_object* v___x_138_; uint8_t v_isSome_139_; 
v___x_138_ = lean_array_fget_borrowed(v_valueArray_133_, v_i_122_);
v_isSome_139_ = lean_noption_is_some(v___x_138_);
if (v_isSome_139_ == 0)
{
goto v___jp_128_;
}
else
{
lean_object* v_val_140_; lean_object* v_val_141_; lean_object* v_i_143_; lean_object* v___x_148_; 
lean_inc(v___x_136_);
v_val_140_ = lean_noption_get(v___x_136_);
lean_inc(v___x_138_);
v_val_141_ = lean_noption_get(v___x_138_);
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___redArg(v_acc_121_, v_val_140_);
switch(lean_obj_tag(v___x_148_))
{
case 0:
{
lean_object* v_index_149_; lean_object* v_size_150_; lean_object* v___x_151_; 
v_index_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_index_149_);
lean_dec_ref_known(v___x_148_, 3);
v_size_150_ = lean_ctor_get(v_acc_121_, 0);
lean_inc(v_size_150_);
v___x_151_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_121_, v_size_150_, v_index_149_, v_val_140_, v_val_141_);
lean_dec(v_index_149_);
v___y_124_ = v___x_151_;
goto v___jp_123_;
}
case 1:
{
lean_object* v_index_152_; 
v_index_152_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_index_152_);
lean_dec_ref_known(v___x_148_, 1);
v_i_143_ = v_index_152_;
goto v___jp_142_;
}
default: 
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_121_, v___x_153_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_index_155_; 
v_index_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_index_155_);
lean_dec_ref_known(v___x_154_, 1);
v_i_143_ = v_index_155_;
goto v___jp_142_;
}
else
{
lean_dec(v_val_141_);
lean_dec(v_val_140_);
v___y_124_ = v_acc_121_;
goto v___jp_123_;
}
}
}
v___jp_142_:
{
lean_object* v_size_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_size_144_ = lean_ctor_get(v_acc_121_, 0);
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = lean_nat_add(v_size_144_, v___x_145_);
v___x_147_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_121_, v___x_146_, v_i_143_, v_val_140_, v_val_141_);
lean_dec(v_i_143_);
v___y_124_ = v___x_147_;
goto v___jp_123_;
}
}
}
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = lean_nat_add(v_i_122_, v___x_125_);
lean_dec(v_i_122_);
v_acc_121_ = v___y_124_;
v_i_122_ = v___x_126_;
goto _start;
}
v___jp_128_:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_add(v_i_122_, v___x_129_);
lean_dec(v_i_122_);
v_i_122_ = v___x_130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_b_156_, lean_object* v_acc_157_, lean_object* v_i_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6___redArg(v_b_156_, v_acc_157_, v_i_158_);
lean_dec_ref(v_b_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5___redArg(lean_object* v_init_160_, lean_object* v_b_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6___redArg(v_b_161_, v_init_160_, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5___redArg___boxed(lean_object* v_init_164_, lean_object* v_b_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5___redArg(v_init_164_, v_b_165_);
lean_dec_ref(v_b_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2___redArg(lean_object* v_m_167_){
_start:
{
lean_object* v_keyArray_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_cellCount_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_target_175_; lean_object* v___x_176_; 
v_keyArray_168_ = lean_ctor_get(v_m_167_, 1);
v___x_169_ = lean_array_get_size(v_keyArray_168_);
v___x_170_ = lean_unsigned_to_nat(2u);
v_cellCount_171_ = lean_nat_mul(v___x_169_, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_171_);
v___x_173_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_171_);
v___x_174_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_171_);
v_target_175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_175_, 0, v___x_172_);
lean_ctor_set(v_target_175_, 1, v___x_173_);
lean_ctor_set(v_target_175_, 2, v___x_174_);
v___x_176_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5___redArg(v_target_175_, v_m_167_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2___redArg___boxed(lean_object* v_m_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2___redArg(v_m_177_);
lean_dec_ref(v_m_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectMVars_visit(lean_object* v_e_179_, lean_object* v_s_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = l_Lean_Expr_hasExprMVar(v_e_179_);
if (v___x_181_ == 0)
{
lean_dec_ref(v_e_179_);
return v_s_180_;
}
else
{
lean_object* v_visitedExpr_182_; lean_object* v_result_183_; lean_object* v___y_185_; uint8_t v___x_188_; 
v_visitedExpr_182_ = lean_ctor_get(v_s_180_, 0);
v_result_183_ = lean_ctor_get(v_s_180_, 1);
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_visitedExpr_182_, v_e_179_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___y_191_; lean_object* v_i_192_; lean_object* v___y_198_; lean_object* v___y_208_; lean_object* v_i_209_; lean_object* v___x_224_; 
lean_inc_ref(v_result_183_);
lean_inc_ref(v_visitedExpr_182_);
lean_dec_ref(v_s_180_);
v___x_189_ = lean_box(0);
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___redArg(v_visitedExpr_182_, v_e_179_);
switch(lean_obj_tag(v___x_224_))
{
case 0:
{
lean_dec_ref_known(v___x_224_, 3);
v___y_185_ = v_visitedExpr_182_;
goto v___jp_184_;
}
case 1:
{
lean_object* v_index_225_; lean_object* v_size_226_; lean_object* v_keyArray_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_index_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_index_225_);
lean_dec_ref_known(v___x_224_, 1);
v_size_226_ = lean_ctor_get(v_visitedExpr_182_, 0);
v_keyArray_227_ = lean_ctor_get(v_visitedExpr_182_, 1);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_add(v_size_226_, v___x_228_);
v___x_230_ = lean_array_get_size(v_keyArray_227_);
v___x_231_ = lean_nat_dec_lt(v___x_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_dec(v___x_229_);
lean_dec(v_index_225_);
goto v___jp_214_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_232_ = lean_unsigned_to_nat(4u);
v___x_233_ = lean_nat_mul(v___x_229_, v___x_232_);
v___x_234_ = lean_unsigned_to_nat(3u);
v___x_235_ = lean_nat_mul(v___x_230_, v___x_234_);
v___x_236_ = lean_nat_dec_le(v___x_233_, v___x_235_);
lean_dec(v___x_235_);
lean_dec(v___x_233_);
if (v___x_236_ == 0)
{
lean_dec(v___x_229_);
lean_dec(v_index_225_);
goto v___jp_214_;
}
else
{
lean_object* v___x_237_; 
lean_inc_ref(v_e_179_);
v___x_237_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedExpr_182_, v___x_229_, v_index_225_, v_e_179_, v___x_189_);
lean_dec(v_index_225_);
v___y_185_ = v___x_237_;
goto v___jp_184_;
}
}
}
default: 
{
lean_object* v_size_238_; lean_object* v_keyArray_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_size_238_ = lean_ctor_get(v_visitedExpr_182_, 0);
v_keyArray_239_ = lean_ctor_get(v_visitedExpr_182_, 1);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_size_238_, v___x_240_);
v___x_242_ = lean_array_get_size(v_keyArray_239_);
v___x_243_ = lean_nat_dec_lt(v___x_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
lean_dec(v___x_241_);
v___x_244_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2___redArg(v_visitedExpr_182_);
lean_dec_ref(v_visitedExpr_182_);
v___y_198_ = v___x_244_;
goto v___jp_197_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_245_ = lean_unsigned_to_nat(4u);
v___x_246_ = lean_nat_mul(v___x_241_, v___x_245_);
lean_dec(v___x_241_);
v___x_247_ = lean_unsigned_to_nat(3u);
v___x_248_ = lean_nat_mul(v___x_242_, v___x_247_);
v___x_249_ = lean_nat_dec_le(v___x_246_, v___x_248_);
lean_dec(v___x_248_);
lean_dec(v___x_246_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2___redArg(v_visitedExpr_182_);
lean_dec_ref(v_visitedExpr_182_);
v___y_198_ = v___x_250_;
goto v___jp_197_;
}
else
{
v___y_198_ = v_visitedExpr_182_;
goto v___jp_197_;
}
}
}
}
v___jp_190_:
{
lean_object* v_size_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_size_193_ = lean_ctor_get(v___y_191_, 0);
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_add(v_size_193_, v___x_194_);
lean_inc_ref(v_e_179_);
v___x_196_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_191_, v___x_195_, v_i_192_, v_e_179_, v___x_189_);
lean_dec(v_i_192_);
v___y_185_ = v___x_196_;
goto v___jp_184_;
}
v___jp_197_:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___redArg(v___y_198_, v_e_179_);
switch(lean_obj_tag(v___x_199_))
{
case 0:
{
lean_object* v_index_200_; lean_object* v_size_201_; lean_object* v___x_202_; 
v_index_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_index_200_);
lean_dec_ref_known(v___x_199_, 3);
v_size_201_ = lean_ctor_get(v___y_198_, 0);
lean_inc(v_size_201_);
lean_inc_ref(v_e_179_);
v___x_202_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_198_, v_size_201_, v_index_200_, v_e_179_, v___x_189_);
lean_dec(v_index_200_);
v___y_185_ = v___x_202_;
goto v___jp_184_;
}
case 1:
{
lean_object* v_index_203_; 
v_index_203_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_index_203_);
lean_dec_ref_known(v___x_199_, 1);
v___y_191_ = v___y_198_;
v_i_192_ = v_index_203_;
goto v___jp_190_;
}
default: 
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_198_, v___x_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_index_206_; 
v_index_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_index_206_);
lean_dec_ref_known(v___x_205_, 1);
v___y_191_ = v___y_198_;
v_i_192_ = v_index_206_;
goto v___jp_190_;
}
else
{
v___y_185_ = v___y_198_;
goto v___jp_184_;
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
lean_inc_ref(v_e_179_);
v___x_213_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_208_, v___x_212_, v_i_209_, v_e_179_, v___x_189_);
lean_dec(v_i_209_);
v___y_185_ = v___x_213_;
goto v___jp_184_;
}
v___jp_214_:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2___redArg(v_visitedExpr_182_);
lean_dec_ref(v_visitedExpr_182_);
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___redArg(v___x_215_, v_e_179_);
switch(lean_obj_tag(v___x_216_))
{
case 0:
{
lean_object* v_index_217_; lean_object* v_size_218_; lean_object* v___x_219_; 
v_index_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_index_217_);
lean_dec_ref_known(v___x_216_, 3);
v_size_218_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_size_218_);
lean_inc_ref(v_e_179_);
v___x_219_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_215_, v_size_218_, v_index_217_, v_e_179_, v___x_189_);
lean_dec(v_index_217_);
v___y_185_ = v___x_219_;
goto v___jp_184_;
}
case 1:
{
lean_object* v_index_220_; 
v_index_220_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_index_220_);
lean_dec_ref_known(v___x_216_, 1);
v___y_208_ = v___x_215_;
v_i_209_ = v_index_220_;
goto v___jp_207_;
}
default: 
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_215_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_index_223_; 
v_index_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_index_223_);
lean_dec_ref_known(v___x_222_, 1);
v___y_208_ = v___x_215_;
v_i_209_ = v_index_223_;
goto v___jp_207_;
}
else
{
v___y_185_ = v___x_215_;
goto v___jp_184_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_179_);
return v_s_180_;
}
v___jp_184_:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___y_185_);
lean_ctor_set(v___x_186_, 1, v_result_183_);
v___x_187_ = l_Lean_CollectMVars_main(v_e_179_, v___x_186_);
return v___x_187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectMVars_main(lean_object* v_x_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_d_254_; lean_object* v_b_255_; lean_object* v___y_256_; 
switch(lean_obj_tag(v_x_251_))
{
case 11:
{
lean_object* v_struct_259_; lean_object* v___x_260_; 
v_struct_259_ = lean_ctor_get(v_x_251_, 2);
lean_inc_ref(v_struct_259_);
lean_dec_ref_known(v_x_251_, 3);
v___x_260_ = l_Lean_CollectMVars_visit(v_struct_259_, v_a_252_);
return v___x_260_;
}
case 7:
{
lean_object* v_binderType_261_; lean_object* v_body_262_; 
v_binderType_261_ = lean_ctor_get(v_x_251_, 1);
lean_inc_ref(v_binderType_261_);
v_body_262_ = lean_ctor_get(v_x_251_, 2);
lean_inc_ref(v_body_262_);
lean_dec_ref_known(v_x_251_, 3);
v_d_254_ = v_binderType_261_;
v_b_255_ = v_body_262_;
v___y_256_ = v_a_252_;
goto v___jp_253_;
}
case 6:
{
lean_object* v_binderType_263_; lean_object* v_body_264_; 
v_binderType_263_ = lean_ctor_get(v_x_251_, 1);
lean_inc_ref(v_binderType_263_);
v_body_264_ = lean_ctor_get(v_x_251_, 2);
lean_inc_ref(v_body_264_);
lean_dec_ref_known(v_x_251_, 3);
v_d_254_ = v_binderType_263_;
v_b_255_ = v_body_264_;
v___y_256_ = v_a_252_;
goto v___jp_253_;
}
case 8:
{
lean_object* v_type_265_; lean_object* v_value_266_; lean_object* v_body_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_type_265_ = lean_ctor_get(v_x_251_, 1);
lean_inc_ref(v_type_265_);
v_value_266_ = lean_ctor_get(v_x_251_, 2);
lean_inc_ref(v_value_266_);
v_body_267_ = lean_ctor_get(v_x_251_, 3);
lean_inc_ref(v_body_267_);
lean_dec_ref_known(v_x_251_, 4);
v___x_268_ = l_Lean_CollectMVars_visit(v_type_265_, v_a_252_);
v___x_269_ = l_Lean_CollectMVars_visit(v_value_266_, v___x_268_);
v___x_270_ = l_Lean_CollectMVars_visit(v_body_267_, v___x_269_);
return v___x_270_;
}
case 5:
{
lean_object* v_fn_271_; lean_object* v_arg_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_fn_271_ = lean_ctor_get(v_x_251_, 0);
lean_inc_ref(v_fn_271_);
v_arg_272_ = lean_ctor_get(v_x_251_, 1);
lean_inc_ref(v_arg_272_);
lean_dec_ref_known(v_x_251_, 2);
v___x_273_ = l_Lean_CollectMVars_visit(v_fn_271_, v_a_252_);
v___x_274_ = l_Lean_CollectMVars_visit(v_arg_272_, v___x_273_);
return v___x_274_;
}
case 10:
{
lean_object* v_expr_275_; lean_object* v___x_276_; 
v_expr_275_ = lean_ctor_get(v_x_251_, 1);
lean_inc_ref(v_expr_275_);
lean_dec_ref_known(v_x_251_, 2);
v___x_276_ = l_Lean_CollectMVars_visit(v_expr_275_, v_a_252_);
return v___x_276_;
}
case 2:
{
lean_object* v_mvarId_277_; lean_object* v_visitedExpr_278_; lean_object* v_result_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_mvarId_277_ = lean_ctor_get(v_x_251_, 0);
lean_inc(v_mvarId_277_);
lean_dec_ref_known(v_x_251_, 1);
v_visitedExpr_278_ = lean_ctor_get(v_a_252_, 0);
v_result_279_ = lean_ctor_get(v_a_252_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_a_252_);
if (v_isSharedCheck_287_ == 0)
{
v___x_281_ = v_a_252_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_result_279_);
lean_inc(v_visitedExpr_278_);
lean_dec(v_a_252_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_array_push(v_result_279_, v_mvarId_277_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v___x_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_visitedExpr_278_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
default: 
{
lean_dec_ref(v_x_251_);
return v_a_252_;
}
}
v___jp_253_:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = l_Lean_CollectMVars_visit(v_d_254_, v___y_256_);
v___x_258_ = l_Lean_CollectMVars_visit(v_b_255_, v___x_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0(lean_object* v_00_u03b2_288_, lean_object* v_m_289_, lean_object* v_a_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___redArg(v_m_289_, v_a_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0___boxed(lean_object* v_00_u03b2_292_, lean_object* v_m_293_, lean_object* v_a_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0(v_00_u03b2_292_, v_m_293_, v_a_294_);
lean_dec_ref(v_a_294_);
lean_dec_ref(v_m_293_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1(lean_object* v_00_u03b2_297_, lean_object* v_m_298_, lean_object* v_query_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___redArg(v_m_298_, v_query_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1___boxed(lean_object* v_00_u03b2_301_, lean_object* v_m_302_, lean_object* v_query_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1(v_00_u03b2_301_, v_m_302_, v_query_303_);
lean_dec_ref(v_query_303_);
lean_dec_ref(v_m_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2(lean_object* v_00_u03b2_305_, lean_object* v_m_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2___redArg(v_m_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2___boxed(lean_object* v_00_u03b2_308_, lean_object* v_m_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2(v_00_u03b2_308_, v_m_309_);
lean_dec_ref(v_m_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1(lean_object* v_00_u03b2_311_, lean_object* v_m_312_, lean_object* v_query_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___redArg(v_m_312_, v_query_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1___boxed(lean_object* v_00_u03b2_315_, lean_object* v_m_316_, lean_object* v_query_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectMVars_visit_spec__0_spec__1(v_00_u03b2_315_, v_m_316_, v_query_317_);
lean_dec_ref(v_query_317_);
lean_dec_ref(v_m_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3(lean_object* v_00_u03b2_319_, lean_object* v_m_320_, lean_object* v_query_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3___redArg(v_m_320_, v_query_321_, v_x_322_, v_x_323_, v_x_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3___boxed(lean_object* v_00_u03b2_327_, lean_object* v_m_328_, lean_object* v_query_329_, lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectMVars_visit_spec__1_spec__3(v_00_u03b2_327_, v_m_328_, v_query_329_, v_x_330_, v_x_331_, v_x_332_, v_x_333_);
lean_dec_ref(v_query_329_);
lean_dec_ref(v_m_328_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5(lean_object* v_00_u03b2_335_, lean_object* v_init_336_, lean_object* v_b_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5___redArg(v_init_336_, v_b_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5___boxed(lean_object* v_00_u03b2_339_, lean_object* v_init_340_, lean_object* v_b_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5(v_00_u03b2_339_, v_init_340_, v_b_341_);
lean_dec_ref(v_b_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_343_, lean_object* v_b_344_, lean_object* v_acc_345_, lean_object* v_i_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6___redArg(v_b_344_, v_acc_345_, v_i_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6___boxed(lean_object* v_00_u03b2_348_, lean_object* v_b_349_, lean_object* v_acc_350_, lean_object* v_i_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectMVars_visit_spec__2_spec__5_spec__6(v_00_u03b2_348_, v_b_349_, v_acc_350_, v_i_351_);
lean_dec_ref(v_b_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectMVars(lean_object* v_s_353_, lean_object* v_e_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_CollectMVars_visit(v_e_354_, v_s_353_);
return v___x_355_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectMVars_instInhabitedState = _init_l_Lean_CollectMVars_instInhabitedState();
lean_mark_persistent(l_Lean_CollectMVars_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectMVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectMVars(builtin);
}
#ifdef __cplusplus
}
#endif
