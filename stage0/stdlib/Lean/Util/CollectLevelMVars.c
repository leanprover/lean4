// Lean compiler output
// Module: Lean.Util.CollectLevelMVars
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
uint64_t l_Lean_Level_hash(lean_object*);
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
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_CollectLevelMVars_instInhabitedState___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__0;
static lean_once_cell_t l_Lean_CollectLevelMVars_instInhabitedState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__1;
static lean_once_cell_t l_Lean_CollectLevelMVars_instInhabitedState___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__2;
static const lean_array_object l_Lean_CollectLevelMVars_instInhabitedState___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__3 = (const lean_object*)&l_Lean_CollectLevelMVars_instInhabitedState___closed__3_value;
static lean_once_cell_t l_Lean_CollectLevelMVars_instInhabitedState___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelMVars_instInhabitedState___closed__4;
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_instInhabitedState;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_collect(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_main(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectLevelMVars(lean_object*, lean_object*);
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__0(void){
_start:
{
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__1(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l_Lean_CollectLevelMVars_instInhabitedState___closed__1, &l_Lean_CollectLevelMVars_instInhabitedState___closed__1_once, _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__1);
v___x_6_ = lean_obj_once(&l_Lean_CollectLevelMVars_instInhabitedState___closed__0, &l_Lean_CollectLevelMVars_instInhabitedState___closed__0_once, _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__0);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = ((lean_object*)(l_Lean_CollectLevelMVars_instInhabitedState___closed__3));
v___x_12_ = lean_obj_once(&l_Lean_CollectLevelMVars_instInhabitedState___closed__2, &l_Lean_CollectLevelMVars_instInhabitedState___closed__2_once, _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__2);
v___x_13_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
lean_ctor_set(v___x_13_, 2, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_CollectLevelMVars_instInhabitedState(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Lean_CollectLevelMVars_instInhabitedState___closed__4, &l_Lean_CollectLevelMVars_instInhabitedState___closed__4_once, _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__4);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(lean_object* v_m_15_, lean_object* v_query_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_x_19_){
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
v___x_58_ = lean_level_eq(v_val_57_, v_query_16_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg___boxed(lean_object* v_m_66_, lean_object* v_query_67_, lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(v_m_66_, v_query_67_, v_x_68_, v_x_69_, v_x_70_);
lean_dec(v_query_67_);
lean_dec_ref(v_m_66_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(lean_object* v_m_72_, lean_object* v_query_73_){
_start:
{
lean_object* v_keyArray_74_; lean_object* v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v___x_78_; uint64_t v_fold_79_; uint64_t v___x_80_; uint64_t v___x_81_; uint64_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; size_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_keyArray_74_ = lean_ctor_get(v_m_72_, 1);
v___x_75_ = lean_array_get_size(v_keyArray_74_);
v___x_76_ = l_Lean_Level_hash(v_query_73_);
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
v___x_90_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(v_m_72_, v_query_73_, v___x_89_, v___x_75_, v___x_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg___boxed(lean_object* v_m_91_, lean_object* v_query_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_m_91_, v_query_92_);
lean_dec(v_query_92_);
lean_dec_ref(v_m_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6___redArg(lean_object* v_b_94_, lean_object* v_acc_95_, lean_object* v_i_96_){
_start:
{
lean_object* v___y_98_; lean_object* v_keyArray_106_; lean_object* v_valueArray_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_keyArray_106_ = lean_ctor_get(v_b_94_, 1);
v_valueArray_107_ = lean_ctor_get(v_b_94_, 2);
v___x_108_ = lean_array_get_size(v_keyArray_106_);
v___x_109_ = lean_nat_dec_lt(v_i_96_, v___x_108_);
if (v___x_109_ == 0)
{
lean_dec(v_i_96_);
return v_acc_95_;
}
else
{
lean_object* v___x_110_; uint8_t v_isSome_111_; 
v___x_110_ = lean_array_fget_borrowed(v_keyArray_106_, v_i_96_);
v_isSome_111_ = lean_noption_is_some(v___x_110_);
if (v_isSome_111_ == 0)
{
goto v___jp_102_;
}
else
{
lean_object* v___x_112_; uint8_t v_isSome_113_; 
v___x_112_ = lean_array_fget_borrowed(v_valueArray_107_, v_i_96_);
v_isSome_113_ = lean_noption_is_some(v___x_112_);
if (v_isSome_113_ == 0)
{
goto v___jp_102_;
}
else
{
lean_object* v_val_114_; lean_object* v_val_115_; lean_object* v_i_117_; lean_object* v___x_122_; 
lean_inc(v___x_110_);
v_val_114_ = lean_noption_get(v___x_110_);
lean_inc(v___x_112_);
v_val_115_ = lean_noption_get(v___x_112_);
v___x_122_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_acc_95_, v_val_114_);
switch(lean_obj_tag(v___x_122_))
{
case 0:
{
lean_object* v_index_123_; lean_object* v_size_124_; lean_object* v___x_125_; 
v_index_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_index_123_);
lean_dec_ref_known(v___x_122_, 3);
v_size_124_ = lean_ctor_get(v_acc_95_, 0);
lean_inc(v_size_124_);
v___x_125_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_95_, v_size_124_, v_index_123_, v_val_114_, v_val_115_);
lean_dec(v_index_123_);
v___y_98_ = v___x_125_;
goto v___jp_97_;
}
case 1:
{
lean_object* v_index_126_; 
v_index_126_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_index_126_);
lean_dec_ref_known(v___x_122_, 1);
v_i_117_ = v_index_126_;
goto v___jp_116_;
}
default: 
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_95_, v___x_127_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_index_129_; 
v_index_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_index_129_);
lean_dec_ref_known(v___x_128_, 1);
v_i_117_ = v_index_129_;
goto v___jp_116_;
}
else
{
lean_dec(v_val_115_);
lean_dec(v_val_114_);
v___y_98_ = v_acc_95_;
goto v___jp_97_;
}
}
}
v___jp_116_:
{
lean_object* v_size_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_size_118_ = lean_ctor_get(v_acc_95_, 0);
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_size_118_, v___x_119_);
v___x_121_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_95_, v___x_120_, v_i_117_, v_val_114_, v_val_115_);
lean_dec(v_i_117_);
v___y_98_ = v___x_121_;
goto v___jp_97_;
}
}
}
}
v___jp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_i_96_, v___x_99_);
lean_dec(v_i_96_);
v_acc_95_ = v___y_98_;
v_i_96_ = v___x_100_;
goto _start;
}
v___jp_102_:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_add(v_i_96_, v___x_103_);
lean_dec(v_i_96_);
v_i_96_ = v___x_104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_b_130_, lean_object* v_acc_131_, lean_object* v_i_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6___redArg(v_b_130_, v_acc_131_, v_i_132_);
lean_dec_ref(v_b_130_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5___redArg(lean_object* v_init_134_, lean_object* v_b_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6___redArg(v_b_135_, v_init_134_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5___redArg___boxed(lean_object* v_init_138_, lean_object* v_b_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5___redArg(v_init_138_, v_b_139_);
lean_dec_ref(v_b_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2___redArg(lean_object* v_m_141_){
_start:
{
lean_object* v_keyArray_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v_cellCount_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v_target_149_; lean_object* v___x_150_; 
v_keyArray_142_ = lean_ctor_get(v_m_141_, 1);
v___x_143_ = lean_array_get_size(v_keyArray_142_);
v___x_144_ = lean_unsigned_to_nat(2u);
v_cellCount_145_ = lean_nat_mul(v___x_143_, v___x_144_);
v___x_146_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_145_);
v___x_147_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_145_);
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_145_);
v_target_149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_149_, 0, v___x_146_);
lean_ctor_set(v_target_149_, 1, v___x_147_);
lean_ctor_set(v_target_149_, 2, v___x_148_);
v___x_150_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5___redArg(v_target_149_, v_m_141_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2___redArg___boxed(lean_object* v_m_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2___redArg(v_m_151_);
lean_dec_ref(v_m_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(lean_object* v_m_153_, lean_object* v_query_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_m_153_, v_query_154_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_index_156_; lean_object* v_key_157_; lean_object* v_value_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_index_156_ = lean_ctor_get(v___x_155_, 0);
v_key_157_ = lean_ctor_get(v___x_155_, 1);
v_value_158_ = lean_ctor_get(v___x_155_, 2);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_155_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_value_158_);
lean_inc(v_key_157_);
lean_inc(v_index_156_);
lean_dec(v___x_155_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_index_156_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_key_157_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_value_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
else
{
lean_object* v___x_166_; 
lean_dec(v___x_155_);
v___x_166_ = lean_box(1);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg___boxed(lean_object* v_m_167_, lean_object* v_query_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_m_167_, v_query_168_);
lean_dec(v_query_168_);
lean_dec_ref(v_m_167_);
return v_res_169_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(lean_object* v_m_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_m_170_, v_a_171_);
if (lean_obj_tag(v___x_172_) == 0)
{
uint8_t v___x_173_; 
lean_dec_ref_known(v___x_172_, 3);
v___x_173_ = 1;
return v___x_173_;
}
else
{
uint8_t v___x_174_; 
v___x_174_ = 0;
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg___boxed(lean_object* v_m_175_, lean_object* v_a_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_m_175_, v_a_176_);
lean_dec(v_a_176_);
lean_dec_ref(v_m_175_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitLevel(lean_object* v_u_179_, lean_object* v_s_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = l_Lean_Level_hasMVar(v_u_179_);
if (v___x_181_ == 0)
{
lean_dec(v_u_179_);
return v_s_180_;
}
else
{
lean_object* v_visitedLevel_182_; lean_object* v_visitedExpr_183_; lean_object* v_result_184_; lean_object* v___y_186_; uint8_t v___x_189_; 
v_visitedLevel_182_ = lean_ctor_get(v_s_180_, 0);
v_visitedExpr_183_ = lean_ctor_get(v_s_180_, 1);
v_result_184_ = lean_ctor_get(v_s_180_, 2);
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_visitedLevel_182_, v_u_179_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___y_192_; lean_object* v_i_193_; lean_object* v___y_199_; lean_object* v___y_209_; lean_object* v_i_210_; lean_object* v___x_225_; 
lean_inc_ref(v_result_184_);
lean_inc_ref(v_visitedExpr_183_);
lean_inc_ref(v_visitedLevel_182_);
lean_dec_ref(v_s_180_);
v___x_190_ = lean_box(0);
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_visitedLevel_182_, v_u_179_);
switch(lean_obj_tag(v___x_225_))
{
case 0:
{
lean_dec_ref_known(v___x_225_, 3);
v___y_186_ = v_visitedLevel_182_;
goto v___jp_185_;
}
case 1:
{
lean_object* v_index_226_; lean_object* v_size_227_; lean_object* v_keyArray_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v_index_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_index_226_);
lean_dec_ref_known(v___x_225_, 1);
v_size_227_ = lean_ctor_get(v_visitedLevel_182_, 0);
v_keyArray_228_ = lean_ctor_get(v_visitedLevel_182_, 1);
v___x_229_ = lean_unsigned_to_nat(1u);
v___x_230_ = lean_nat_add(v_size_227_, v___x_229_);
v___x_231_ = lean_array_get_size(v_keyArray_228_);
v___x_232_ = lean_nat_dec_lt(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
lean_dec(v___x_230_);
lean_dec(v_index_226_);
goto v___jp_215_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_233_ = lean_unsigned_to_nat(4u);
v___x_234_ = lean_nat_mul(v___x_230_, v___x_233_);
v___x_235_ = lean_unsigned_to_nat(3u);
v___x_236_ = lean_nat_mul(v___x_231_, v___x_235_);
v___x_237_ = lean_nat_dec_le(v___x_234_, v___x_236_);
lean_dec(v___x_236_);
lean_dec(v___x_234_);
if (v___x_237_ == 0)
{
lean_dec(v___x_230_);
lean_dec(v_index_226_);
goto v___jp_215_;
}
else
{
lean_object* v___x_238_; 
lean_inc(v_u_179_);
v___x_238_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedLevel_182_, v___x_230_, v_index_226_, v_u_179_, v___x_190_);
lean_dec(v_index_226_);
v___y_186_ = v___x_238_;
goto v___jp_185_;
}
}
}
default: 
{
lean_object* v_size_239_; lean_object* v_keyArray_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_size_239_ = lean_ctor_get(v_visitedLevel_182_, 0);
v_keyArray_240_ = lean_ctor_get(v_visitedLevel_182_, 1);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_size_239_, v___x_241_);
v___x_243_ = lean_array_get_size(v_keyArray_240_);
v___x_244_ = lean_nat_dec_lt(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; 
lean_dec(v___x_242_);
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2___redArg(v_visitedLevel_182_);
lean_dec_ref(v_visitedLevel_182_);
v___y_199_ = v___x_245_;
goto v___jp_198_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_246_ = lean_unsigned_to_nat(4u);
v___x_247_ = lean_nat_mul(v___x_242_, v___x_246_);
lean_dec(v___x_242_);
v___x_248_ = lean_unsigned_to_nat(3u);
v___x_249_ = lean_nat_mul(v___x_243_, v___x_248_);
v___x_250_ = lean_nat_dec_le(v___x_247_, v___x_249_);
lean_dec(v___x_249_);
lean_dec(v___x_247_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2___redArg(v_visitedLevel_182_);
lean_dec_ref(v_visitedLevel_182_);
v___y_199_ = v___x_251_;
goto v___jp_198_;
}
else
{
v___y_199_ = v_visitedLevel_182_;
goto v___jp_198_;
}
}
}
}
v___jp_191_:
{
lean_object* v_size_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_size_194_ = lean_ctor_get(v___y_192_, 0);
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = lean_nat_add(v_size_194_, v___x_195_);
lean_inc(v_u_179_);
v___x_197_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_192_, v___x_196_, v_i_193_, v_u_179_, v___x_190_);
lean_dec(v_i_193_);
v___y_186_ = v___x_197_;
goto v___jp_185_;
}
v___jp_198_:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v___y_199_, v_u_179_);
switch(lean_obj_tag(v___x_200_))
{
case 0:
{
lean_object* v_index_201_; lean_object* v_size_202_; lean_object* v___x_203_; 
v_index_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_index_201_);
lean_dec_ref_known(v___x_200_, 3);
v_size_202_ = lean_ctor_get(v___y_199_, 0);
lean_inc(v_size_202_);
lean_inc(v_u_179_);
v___x_203_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_199_, v_size_202_, v_index_201_, v_u_179_, v___x_190_);
lean_dec(v_index_201_);
v___y_186_ = v___x_203_;
goto v___jp_185_;
}
case 1:
{
lean_object* v_index_204_; 
v_index_204_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_index_204_);
lean_dec_ref_known(v___x_200_, 1);
v___y_192_ = v___y_199_;
v_i_193_ = v_index_204_;
goto v___jp_191_;
}
default: 
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_199_, v___x_205_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_index_207_; 
v_index_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_index_207_);
lean_dec_ref_known(v___x_206_, 1);
v___y_192_ = v___y_199_;
v_i_193_ = v_index_207_;
goto v___jp_191_;
}
else
{
v___y_186_ = v___y_199_;
goto v___jp_185_;
}
}
}
}
v___jp_208_:
{
lean_object* v_size_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_size_211_ = lean_ctor_get(v___y_209_, 0);
v___x_212_ = lean_unsigned_to_nat(1u);
v___x_213_ = lean_nat_add(v_size_211_, v___x_212_);
lean_inc(v_u_179_);
v___x_214_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_209_, v___x_213_, v_i_210_, v_u_179_, v___x_190_);
lean_dec(v_i_210_);
v___y_186_ = v___x_214_;
goto v___jp_185_;
}
v___jp_215_:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2___redArg(v_visitedLevel_182_);
lean_dec_ref(v_visitedLevel_182_);
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v___x_216_, v_u_179_);
switch(lean_obj_tag(v___x_217_))
{
case 0:
{
lean_object* v_index_218_; lean_object* v_size_219_; lean_object* v___x_220_; 
v_index_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_index_218_);
lean_dec_ref_known(v___x_217_, 3);
v_size_219_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_size_219_);
lean_inc(v_u_179_);
v___x_220_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_216_, v_size_219_, v_index_218_, v_u_179_, v___x_190_);
lean_dec(v_index_218_);
v___y_186_ = v___x_220_;
goto v___jp_185_;
}
case 1:
{
lean_object* v_index_221_; 
v_index_221_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_index_221_);
lean_dec_ref_known(v___x_217_, 1);
v___y_209_ = v___x_216_;
v_i_210_ = v_index_221_;
goto v___jp_208_;
}
default: 
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_216_, v___x_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_index_224_; 
v_index_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_index_224_);
lean_dec_ref_known(v___x_223_, 1);
v___y_209_ = v___x_216_;
v_i_210_ = v_index_224_;
goto v___jp_208_;
}
else
{
v___y_186_ = v___x_216_;
goto v___jp_185_;
}
}
}
}
}
else
{
lean_dec(v_u_179_);
return v_s_180_;
}
v___jp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_187_, 0, v___y_186_);
lean_ctor_set(v___x_187_, 1, v_visitedExpr_183_);
lean_ctor_set(v___x_187_, 2, v_result_184_);
v___x_188_ = l_Lean_CollectLevelMVars_collect(v_u_179_, v___x_187_);
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_collect(lean_object* v_x_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_u_255_; lean_object* v_v_256_; lean_object* v___y_257_; 
switch(lean_obj_tag(v_x_252_))
{
case 1:
{
lean_object* v_a_260_; lean_object* v___x_261_; 
v_a_260_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v_x_252_, 1);
v___x_261_ = l_Lean_CollectLevelMVars_visitLevel(v_a_260_, v_a_253_);
return v___x_261_;
}
case 2:
{
lean_object* v_a_262_; lean_object* v_a_263_; 
v_a_262_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_a_262_);
v_a_263_ = lean_ctor_get(v_x_252_, 1);
lean_inc(v_a_263_);
lean_dec_ref_known(v_x_252_, 2);
v_u_255_ = v_a_262_;
v_v_256_ = v_a_263_;
v___y_257_ = v_a_253_;
goto v___jp_254_;
}
case 3:
{
lean_object* v_a_264_; lean_object* v_a_265_; 
v_a_264_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_a_264_);
v_a_265_ = lean_ctor_get(v_x_252_, 1);
lean_inc(v_a_265_);
lean_dec_ref_known(v_x_252_, 2);
v_u_255_ = v_a_264_;
v_v_256_ = v_a_265_;
v___y_257_ = v_a_253_;
goto v___jp_254_;
}
case 5:
{
lean_object* v_a_266_; lean_object* v_visitedLevel_267_; lean_object* v_visitedExpr_268_; lean_object* v_result_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_a_266_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v_x_252_, 1);
v_visitedLevel_267_ = lean_ctor_get(v_a_253_, 0);
v_visitedExpr_268_ = lean_ctor_get(v_a_253_, 1);
v_result_269_ = lean_ctor_get(v_a_253_, 2);
v_isSharedCheck_277_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v_a_253_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_result_269_);
lean_inc(v_visitedExpr_268_);
lean_inc(v_visitedLevel_267_);
lean_dec(v_a_253_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_array_push(v_result_269_, v_a_266_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 2, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_visitedLevel_267_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_visitedExpr_268_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
default: 
{
lean_dec(v_x_252_);
return v_a_253_;
}
}
v___jp_254_:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = l_Lean_CollectLevelMVars_visitLevel(v_u_255_, v___y_257_);
v___x_259_ = l_Lean_CollectLevelMVars_visitLevel(v_v_256_, v___x_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(lean_object* v_00_u03b2_278_, lean_object* v_m_279_, lean_object* v_a_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_m_279_, v_a_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___boxed(lean_object* v_00_u03b2_282_, lean_object* v_m_283_, lean_object* v_a_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(v_00_u03b2_282_, v_m_283_, v_a_284_);
lean_dec(v_a_284_);
lean_dec_ref(v_m_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1(lean_object* v_00_u03b2_287_, lean_object* v_m_288_, lean_object* v_query_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_m_288_, v_query_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1___boxed(lean_object* v_00_u03b2_291_, lean_object* v_m_292_, lean_object* v_query_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1(v_00_u03b2_291_, v_m_292_, v_query_293_);
lean_dec(v_query_293_);
lean_dec_ref(v_m_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2(lean_object* v_00_u03b2_295_, lean_object* v_m_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2___redArg(v_m_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2___boxed(lean_object* v_00_u03b2_298_, lean_object* v_m_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2(v_00_u03b2_298_, v_m_299_);
lean_dec_ref(v_m_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(lean_object* v_00_u03b2_301_, lean_object* v_m_302_, lean_object* v_query_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_m_302_, v_query_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___boxed(lean_object* v_00_u03b2_305_, lean_object* v_m_306_, lean_object* v_query_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(v_00_u03b2_305_, v_m_306_, v_query_307_);
lean_dec(v_query_307_);
lean_dec_ref(v_m_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3(lean_object* v_00_u03b2_309_, lean_object* v_m_310_, lean_object* v_query_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(v_m_310_, v_query_311_, v_x_312_, v_x_313_, v_x_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___boxed(lean_object* v_00_u03b2_317_, lean_object* v_m_318_, lean_object* v_query_319_, lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3(v_00_u03b2_317_, v_m_318_, v_query_319_, v_x_320_, v_x_321_, v_x_322_, v_x_323_);
lean_dec(v_query_319_);
lean_dec_ref(v_m_318_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5(lean_object* v_00_u03b2_325_, lean_object* v_init_326_, lean_object* v_b_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5___redArg(v_init_326_, v_b_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5___boxed(lean_object* v_00_u03b2_329_, lean_object* v_init_330_, lean_object* v_b_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5(v_00_u03b2_329_, v_init_330_, v_b_331_);
lean_dec_ref(v_b_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_333_, lean_object* v_b_334_, lean_object* v_acc_335_, lean_object* v_i_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6___redArg(v_b_334_, v_acc_335_, v_i_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6___boxed(lean_object* v_00_u03b2_338_, lean_object* v_b_339_, lean_object* v_acc_340_, lean_object* v_i_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitLevel_spec__2_spec__5_spec__6(v_00_u03b2_338_, v_b_339_, v_acc_340_, v_i_341_);
lean_dec_ref(v_b_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(lean_object* v_m_343_, lean_object* v_query_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v_zero_348_; uint8_t v_isZero_349_; 
v_zero_348_ = lean_unsigned_to_nat(0u);
v_isZero_349_ = lean_nat_dec_eq(v_x_346_, v_zero_348_);
if (v_isZero_349_ == 1)
{
lean_dec(v_x_347_);
lean_dec(v_x_346_);
if (lean_obj_tag(v_x_345_) == 0)
{
lean_object* v___x_350_; 
v___x_350_ = lean_box(2);
return v___x_350_;
}
else
{
lean_object* v_val_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_val_351_ = lean_ctor_get(v_x_345_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v_x_345_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v_x_345_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_val_351_);
lean_dec(v_x_345_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_val_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v_keyArray_359_; lean_object* v_valueArray_360_; lean_object* v___x_361_; uint8_t v_isSome_362_; 
v_keyArray_359_ = lean_ctor_get(v_m_343_, 1);
v_valueArray_360_ = lean_ctor_get(v_m_343_, 2);
v___x_361_ = lean_array_fget_borrowed(v_keyArray_359_, v_x_347_);
v_isSome_362_ = lean_noption_is_some(v___x_361_);
if (v_isSome_362_ == 0)
{
lean_dec(v_x_346_);
if (lean_obj_tag(v_x_345_) == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v_x_347_);
return v___x_363_;
}
else
{
lean_object* v_val_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec(v_x_347_);
v_val_364_ = lean_ctor_get(v_x_345_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v_x_345_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v_x_345_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_val_364_);
lean_dec(v_x_345_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_val_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v_one_372_; lean_object* v_n_373_; lean_object* v___y_375_; 
v_one_372_ = lean_unsigned_to_nat(1u);
v_n_373_ = lean_nat_sub(v_x_346_, v_one_372_);
lean_dec(v_x_346_);
if (v_isSome_362_ == 0)
{
goto v___jp_381_;
}
else
{
lean_object* v___x_383_; uint8_t v_isSome_384_; 
v___x_383_ = lean_array_fget_borrowed(v_valueArray_360_, v_x_347_);
v_isSome_384_ = lean_noption_is_some(v___x_383_);
if (v_isSome_384_ == 0)
{
goto v___jp_381_;
}
else
{
lean_object* v_val_385_; uint8_t v___x_386_; 
lean_inc(v___x_361_);
v_val_385_ = lean_noption_get(v___x_361_);
v___x_386_ = lean_expr_eqv(v_val_385_, v_query_344_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
lean_dec(v_val_385_);
v___x_387_ = lean_array_get_size(v_keyArray_359_);
v___x_388_ = lean_nat_add(v_x_347_, v_one_372_);
lean_dec(v_x_347_);
v___x_389_ = lean_nat_dec_lt(v___x_388_, v___x_387_);
if (v___x_389_ == 0)
{
lean_dec(v___x_388_);
v_x_346_ = v_n_373_;
v_x_347_ = v_zero_348_;
goto _start;
}
else
{
v_x_346_ = v_n_373_;
v_x_347_ = v___x_388_;
goto _start;
}
}
else
{
lean_object* v_val_392_; lean_object* v___x_393_; 
lean_dec(v_n_373_);
lean_dec(v_x_345_);
lean_inc(v___x_383_);
v_val_392_ = lean_noption_get(v___x_383_);
v___x_393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_393_, 0, v_x_347_);
lean_ctor_set(v___x_393_, 1, v_val_385_);
lean_ctor_set(v___x_393_, 2, v_val_392_);
return v___x_393_;
}
}
}
v___jp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_376_ = lean_array_get_size(v_keyArray_359_);
v___x_377_ = lean_nat_add(v_x_347_, v_one_372_);
lean_dec(v_x_347_);
v___x_378_ = lean_nat_dec_lt(v___x_377_, v___x_376_);
if (v___x_378_ == 0)
{
lean_dec(v___x_377_);
v_x_345_ = v___y_375_;
v_x_346_ = v_n_373_;
v_x_347_ = v_zero_348_;
goto _start;
}
else
{
v_x_345_ = v___y_375_;
v_x_346_ = v_n_373_;
v_x_347_ = v___x_377_;
goto _start;
}
}
v___jp_381_:
{
if (lean_obj_tag(v_x_345_) == 0)
{
lean_object* v___x_382_; 
lean_inc(v_x_347_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v_x_347_);
v___y_375_ = v___x_382_;
goto v___jp_374_;
}
else
{
v___y_375_ = v_x_345_;
goto v___jp_374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg___boxed(lean_object* v_m_394_, lean_object* v_query_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_m_394_, v_query_395_, v_x_396_, v_x_397_, v_x_398_);
lean_dec_ref(v_query_395_);
lean_dec_ref(v_m_394_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(lean_object* v_m_400_, lean_object* v_query_401_){
_start:
{
lean_object* v_keyArray_402_; lean_object* v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v_fold_407_; uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_keyArray_402_ = lean_ctor_get(v_m_400_, 1);
v___x_403_ = lean_array_get_size(v_keyArray_402_);
v___x_404_ = l_Lean_Expr_hash(v_query_401_);
v___x_405_ = 32ULL;
v___x_406_ = lean_uint64_shift_right(v___x_404_, v___x_405_);
v_fold_407_ = lean_uint64_xor(v___x_404_, v___x_406_);
v___x_408_ = 16ULL;
v___x_409_ = lean_uint64_shift_right(v_fold_407_, v___x_408_);
v___x_410_ = lean_uint64_xor(v_fold_407_, v___x_409_);
v___x_411_ = lean_uint64_to_usize(v___x_410_);
v___x_412_ = lean_usize_of_nat(v___x_403_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_sub(v___x_412_, v___x_413_);
v___x_415_ = lean_usize_land(v___x_411_, v___x_414_);
v___x_416_ = lean_usize_to_nat(v___x_415_);
v___x_417_ = lean_box(0);
v___x_418_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_m_400_, v_query_401_, v___x_417_, v___x_403_, v___x_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg___boxed(lean_object* v_m_419_, lean_object* v_query_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_m_419_, v_query_420_);
lean_dec_ref(v_query_420_);
lean_dec_ref(v_m_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6___redArg(lean_object* v_b_422_, lean_object* v_acc_423_, lean_object* v_i_424_){
_start:
{
lean_object* v___y_426_; lean_object* v_keyArray_434_; lean_object* v_valueArray_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_keyArray_434_ = lean_ctor_get(v_b_422_, 1);
v_valueArray_435_ = lean_ctor_get(v_b_422_, 2);
v___x_436_ = lean_array_get_size(v_keyArray_434_);
v___x_437_ = lean_nat_dec_lt(v_i_424_, v___x_436_);
if (v___x_437_ == 0)
{
lean_dec(v_i_424_);
return v_acc_423_;
}
else
{
lean_object* v___x_438_; uint8_t v_isSome_439_; 
v___x_438_ = lean_array_fget_borrowed(v_keyArray_434_, v_i_424_);
v_isSome_439_ = lean_noption_is_some(v___x_438_);
if (v_isSome_439_ == 0)
{
goto v___jp_430_;
}
else
{
lean_object* v___x_440_; uint8_t v_isSome_441_; 
v___x_440_ = lean_array_fget_borrowed(v_valueArray_435_, v_i_424_);
v_isSome_441_ = lean_noption_is_some(v___x_440_);
if (v_isSome_441_ == 0)
{
goto v___jp_430_;
}
else
{
lean_object* v_val_442_; lean_object* v_val_443_; lean_object* v_i_445_; lean_object* v___x_450_; 
lean_inc(v___x_438_);
v_val_442_ = lean_noption_get(v___x_438_);
lean_inc(v___x_440_);
v_val_443_ = lean_noption_get(v___x_440_);
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_acc_423_, v_val_442_);
switch(lean_obj_tag(v___x_450_))
{
case 0:
{
lean_object* v_index_451_; lean_object* v_size_452_; lean_object* v___x_453_; 
v_index_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_index_451_);
lean_dec_ref_known(v___x_450_, 3);
v_size_452_ = lean_ctor_get(v_acc_423_, 0);
lean_inc(v_size_452_);
v___x_453_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_423_, v_size_452_, v_index_451_, v_val_442_, v_val_443_);
lean_dec(v_index_451_);
v___y_426_ = v___x_453_;
goto v___jp_425_;
}
case 1:
{
lean_object* v_index_454_; 
v_index_454_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_index_454_);
lean_dec_ref_known(v___x_450_, 1);
v_i_445_ = v_index_454_;
goto v___jp_444_;
}
default: 
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_423_, v___x_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_index_457_; 
v_index_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_index_457_);
lean_dec_ref_known(v___x_456_, 1);
v_i_445_ = v_index_457_;
goto v___jp_444_;
}
else
{
lean_dec(v_val_443_);
lean_dec(v_val_442_);
v___y_426_ = v_acc_423_;
goto v___jp_425_;
}
}
}
v___jp_444_:
{
lean_object* v_size_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_size_446_ = lean_ctor_get(v_acc_423_, 0);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_add(v_size_446_, v___x_447_);
v___x_449_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_423_, v___x_448_, v_i_445_, v_val_442_, v_val_443_);
lean_dec(v_i_445_);
v___y_426_ = v___x_449_;
goto v___jp_425_;
}
}
}
}
v___jp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_add(v_i_424_, v___x_427_);
lean_dec(v_i_424_);
v_acc_423_ = v___y_426_;
v_i_424_ = v___x_428_;
goto _start;
}
v___jp_430_:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = lean_nat_add(v_i_424_, v___x_431_);
lean_dec(v_i_424_);
v_i_424_ = v___x_432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_b_458_, lean_object* v_acc_459_, lean_object* v_i_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6___redArg(v_b_458_, v_acc_459_, v_i_460_);
lean_dec_ref(v_b_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4___redArg(lean_object* v_init_462_, lean_object* v_b_463_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6___redArg(v_b_463_, v_init_462_, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4___redArg___boxed(lean_object* v_init_466_, lean_object* v_b_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4___redArg(v_init_466_, v_b_467_);
lean_dec_ref(v_b_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2___redArg(lean_object* v_m_469_){
_start:
{
lean_object* v_keyArray_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_cellCount_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_target_477_; lean_object* v___x_478_; 
v_keyArray_470_ = lean_ctor_get(v_m_469_, 1);
v___x_471_ = lean_array_get_size(v_keyArray_470_);
v___x_472_ = lean_unsigned_to_nat(2u);
v_cellCount_473_ = lean_nat_mul(v___x_471_, v___x_472_);
v___x_474_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_473_);
v___x_475_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_473_);
v___x_476_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_473_);
v_target_477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_477_, 0, v___x_474_);
lean_ctor_set(v_target_477_, 1, v___x_475_);
lean_ctor_set(v_target_477_, 2, v___x_476_);
v___x_478_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4___redArg(v_target_477_, v_m_469_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2___redArg___boxed(lean_object* v_m_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2___redArg(v_m_479_);
lean_dec_ref(v_m_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(lean_object* v_m_481_, lean_object* v_query_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_m_481_, v_query_482_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_index_484_; lean_object* v_key_485_; lean_object* v_value_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_index_484_ = lean_ctor_get(v___x_483_, 0);
v_key_485_ = lean_ctor_get(v___x_483_, 1);
v_value_486_ = lean_ctor_get(v___x_483_, 2);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_483_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_value_486_);
lean_inc(v_key_485_);
lean_inc(v_index_484_);
lean_dec(v___x_483_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_index_484_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_key_485_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v_value_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
else
{
lean_object* v___x_494_; 
lean_dec(v___x_483_);
v___x_494_ = lean_box(1);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg___boxed(lean_object* v_m_495_, lean_object* v_query_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_m_495_, v_query_496_);
lean_dec_ref(v_query_496_);
lean_dec_ref(v_m_495_);
return v_res_497_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(lean_object* v_m_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_m_498_, v_a_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
uint8_t v___x_501_; 
lean_dec_ref_known(v___x_500_, 3);
v___x_501_ = 1;
return v___x_501_;
}
else
{
uint8_t v___x_502_; 
v___x_502_ = 0;
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg___boxed(lean_object* v_m_503_, lean_object* v_a_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_503_, v_a_504_);
lean_dec_ref(v_a_504_);
lean_dec_ref(v_m_503_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__4(lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
return v_x_507_;
}
else
{
lean_object* v_head_509_; lean_object* v_tail_510_; lean_object* v___x_511_; 
v_head_509_ = lean_ctor_get(v_x_508_, 0);
lean_inc(v_head_509_);
v_tail_510_ = lean_ctor_get(v_x_508_, 1);
lean_inc(v_tail_510_);
lean_dec_ref_known(v_x_508_, 2);
v___x_511_ = l_Lean_CollectLevelMVars_visitLevel(v_head_509_, v_x_507_);
v_x_507_ = v___x_511_;
v_x_508_ = v_tail_510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_visitExpr(lean_object* v_e_513_, lean_object* v_s_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_Expr_hasMVar(v_e_513_);
if (v___x_515_ == 0)
{
lean_dec_ref(v_e_513_);
return v_s_514_;
}
else
{
lean_object* v_visitedLevel_516_; lean_object* v_visitedExpr_517_; lean_object* v_result_518_; lean_object* v___y_520_; uint8_t v___x_523_; 
v_visitedLevel_516_ = lean_ctor_get(v_s_514_, 0);
v_visitedExpr_517_ = lean_ctor_get(v_s_514_, 1);
v_result_518_ = lean_ctor_get(v_s_514_, 2);
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_visitedExpr_517_, v_e_513_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___y_526_; lean_object* v_i_527_; lean_object* v___y_533_; lean_object* v___y_543_; lean_object* v_i_544_; lean_object* v___x_559_; 
lean_inc_ref(v_result_518_);
lean_inc_ref(v_visitedExpr_517_);
lean_inc_ref(v_visitedLevel_516_);
lean_dec_ref(v_s_514_);
v___x_524_ = lean_box(0);
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_visitedExpr_517_, v_e_513_);
switch(lean_obj_tag(v___x_559_))
{
case 0:
{
lean_dec_ref_known(v___x_559_, 3);
v___y_520_ = v_visitedExpr_517_;
goto v___jp_519_;
}
case 1:
{
lean_object* v_index_560_; lean_object* v_size_561_; lean_object* v_keyArray_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_index_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_index_560_);
lean_dec_ref_known(v___x_559_, 1);
v_size_561_ = lean_ctor_get(v_visitedExpr_517_, 0);
v_keyArray_562_ = lean_ctor_get(v_visitedExpr_517_, 1);
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_add(v_size_561_, v___x_563_);
v___x_565_ = lean_array_get_size(v_keyArray_562_);
v___x_566_ = lean_nat_dec_lt(v___x_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_dec(v___x_564_);
lean_dec(v_index_560_);
goto v___jp_549_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_567_ = lean_unsigned_to_nat(4u);
v___x_568_ = lean_nat_mul(v___x_564_, v___x_567_);
v___x_569_ = lean_unsigned_to_nat(3u);
v___x_570_ = lean_nat_mul(v___x_565_, v___x_569_);
v___x_571_ = lean_nat_dec_le(v___x_568_, v___x_570_);
lean_dec(v___x_570_);
lean_dec(v___x_568_);
if (v___x_571_ == 0)
{
lean_dec(v___x_564_);
lean_dec(v_index_560_);
goto v___jp_549_;
}
else
{
lean_object* v___x_572_; 
lean_inc_ref(v_e_513_);
v___x_572_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedExpr_517_, v___x_564_, v_index_560_, v_e_513_, v___x_524_);
lean_dec(v_index_560_);
v___y_520_ = v___x_572_;
goto v___jp_519_;
}
}
}
default: 
{
lean_object* v_size_573_; lean_object* v_keyArray_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_size_573_ = lean_ctor_get(v_visitedExpr_517_, 0);
v_keyArray_574_ = lean_ctor_get(v_visitedExpr_517_, 1);
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_add(v_size_573_, v___x_575_);
v___x_577_ = lean_array_get_size(v_keyArray_574_);
v___x_578_ = lean_nat_dec_lt(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_dec(v___x_576_);
v___x_579_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2___redArg(v_visitedExpr_517_);
lean_dec_ref(v_visitedExpr_517_);
v___y_533_ = v___x_579_;
goto v___jp_532_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_580_ = lean_unsigned_to_nat(4u);
v___x_581_ = lean_nat_mul(v___x_576_, v___x_580_);
lean_dec(v___x_576_);
v___x_582_ = lean_unsigned_to_nat(3u);
v___x_583_ = lean_nat_mul(v___x_577_, v___x_582_);
v___x_584_ = lean_nat_dec_le(v___x_581_, v___x_583_);
lean_dec(v___x_583_);
lean_dec(v___x_581_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2___redArg(v_visitedExpr_517_);
lean_dec_ref(v_visitedExpr_517_);
v___y_533_ = v___x_585_;
goto v___jp_532_;
}
else
{
v___y_533_ = v_visitedExpr_517_;
goto v___jp_532_;
}
}
}
}
v___jp_525_:
{
lean_object* v_size_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_size_528_ = lean_ctor_get(v___y_526_, 0);
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = lean_nat_add(v_size_528_, v___x_529_);
lean_inc_ref(v_e_513_);
v___x_531_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_526_, v___x_530_, v_i_527_, v_e_513_, v___x_524_);
lean_dec(v_i_527_);
v___y_520_ = v___x_531_;
goto v___jp_519_;
}
v___jp_532_:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v___y_533_, v_e_513_);
switch(lean_obj_tag(v___x_534_))
{
case 0:
{
lean_object* v_index_535_; lean_object* v_size_536_; lean_object* v___x_537_; 
v_index_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_index_535_);
lean_dec_ref_known(v___x_534_, 3);
v_size_536_ = lean_ctor_get(v___y_533_, 0);
lean_inc(v_size_536_);
lean_inc_ref(v_e_513_);
v___x_537_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_533_, v_size_536_, v_index_535_, v_e_513_, v___x_524_);
lean_dec(v_index_535_);
v___y_520_ = v___x_537_;
goto v___jp_519_;
}
case 1:
{
lean_object* v_index_538_; 
v_index_538_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_index_538_);
lean_dec_ref_known(v___x_534_, 1);
v___y_526_ = v___y_533_;
v_i_527_ = v_index_538_;
goto v___jp_525_;
}
default: 
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_533_, v___x_539_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_index_541_; 
v_index_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_index_541_);
lean_dec_ref_known(v___x_540_, 1);
v___y_526_ = v___y_533_;
v_i_527_ = v_index_541_;
goto v___jp_525_;
}
else
{
v___y_520_ = v___y_533_;
goto v___jp_519_;
}
}
}
}
v___jp_542_:
{
lean_object* v_size_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_size_545_ = lean_ctor_get(v___y_543_, 0);
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = lean_nat_add(v_size_545_, v___x_546_);
lean_inc_ref(v_e_513_);
v___x_548_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_543_, v___x_547_, v_i_544_, v_e_513_, v___x_524_);
lean_dec(v_i_544_);
v___y_520_ = v___x_548_;
goto v___jp_519_;
}
v___jp_549_:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2___redArg(v_visitedExpr_517_);
lean_dec_ref(v_visitedExpr_517_);
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v___x_550_, v_e_513_);
switch(lean_obj_tag(v___x_551_))
{
case 0:
{
lean_object* v_index_552_; lean_object* v_size_553_; lean_object* v___x_554_; 
v_index_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_index_552_);
lean_dec_ref_known(v___x_551_, 3);
v_size_553_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_size_553_);
lean_inc_ref(v_e_513_);
v___x_554_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_550_, v_size_553_, v_index_552_, v_e_513_, v___x_524_);
lean_dec(v_index_552_);
v___y_520_ = v___x_554_;
goto v___jp_519_;
}
case 1:
{
lean_object* v_index_555_; 
v_index_555_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_index_555_);
lean_dec_ref_known(v___x_551_, 1);
v___y_543_ = v___x_550_;
v_i_544_ = v_index_555_;
goto v___jp_542_;
}
default: 
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_550_, v___x_556_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_index_558_; 
v_index_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_index_558_);
lean_dec_ref_known(v___x_557_, 1);
v___y_543_ = v___x_550_;
v_i_544_ = v_index_558_;
goto v___jp_542_;
}
else
{
v___y_520_ = v___x_550_;
goto v___jp_519_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_513_);
return v_s_514_;
}
v___jp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_521_, 0, v_visitedLevel_516_);
lean_ctor_set(v___x_521_, 1, v___y_520_);
lean_ctor_set(v___x_521_, 2, v_result_518_);
v___x_522_ = l_Lean_CollectLevelMVars_main(v_e_513_, v___x_521_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelMVars_main(lean_object* v_x_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_d_589_; lean_object* v_b_590_; lean_object* v___y_591_; 
switch(lean_obj_tag(v_x_586_))
{
case 11:
{
lean_object* v_struct_594_; lean_object* v___x_595_; 
v_struct_594_ = lean_ctor_get(v_x_586_, 2);
lean_inc_ref(v_struct_594_);
lean_dec_ref_known(v_x_586_, 3);
v___x_595_ = l_Lean_CollectLevelMVars_visitExpr(v_struct_594_, v_a_587_);
return v___x_595_;
}
case 7:
{
lean_object* v_binderType_596_; lean_object* v_body_597_; 
v_binderType_596_ = lean_ctor_get(v_x_586_, 1);
lean_inc_ref(v_binderType_596_);
v_body_597_ = lean_ctor_get(v_x_586_, 2);
lean_inc_ref(v_body_597_);
lean_dec_ref_known(v_x_586_, 3);
v_d_589_ = v_binderType_596_;
v_b_590_ = v_body_597_;
v___y_591_ = v_a_587_;
goto v___jp_588_;
}
case 6:
{
lean_object* v_binderType_598_; lean_object* v_body_599_; 
v_binderType_598_ = lean_ctor_get(v_x_586_, 1);
lean_inc_ref(v_binderType_598_);
v_body_599_ = lean_ctor_get(v_x_586_, 2);
lean_inc_ref(v_body_599_);
lean_dec_ref_known(v_x_586_, 3);
v_d_589_ = v_binderType_598_;
v_b_590_ = v_body_599_;
v___y_591_ = v_a_587_;
goto v___jp_588_;
}
case 8:
{
lean_object* v_type_600_; lean_object* v_value_601_; lean_object* v_body_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_type_600_ = lean_ctor_get(v_x_586_, 1);
lean_inc_ref(v_type_600_);
v_value_601_ = lean_ctor_get(v_x_586_, 2);
lean_inc_ref(v_value_601_);
v_body_602_ = lean_ctor_get(v_x_586_, 3);
lean_inc_ref(v_body_602_);
lean_dec_ref_known(v_x_586_, 4);
v___x_603_ = l_Lean_CollectLevelMVars_visitExpr(v_type_600_, v_a_587_);
v___x_604_ = l_Lean_CollectLevelMVars_visitExpr(v_value_601_, v___x_603_);
v___x_605_ = l_Lean_CollectLevelMVars_visitExpr(v_body_602_, v___x_604_);
return v___x_605_;
}
case 5:
{
lean_object* v_fn_606_; lean_object* v_arg_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_fn_606_ = lean_ctor_get(v_x_586_, 0);
lean_inc_ref(v_fn_606_);
v_arg_607_ = lean_ctor_get(v_x_586_, 1);
lean_inc_ref(v_arg_607_);
lean_dec_ref_known(v_x_586_, 2);
v___x_608_ = l_Lean_CollectLevelMVars_visitExpr(v_fn_606_, v_a_587_);
v___x_609_ = l_Lean_CollectLevelMVars_visitExpr(v_arg_607_, v___x_608_);
return v___x_609_;
}
case 10:
{
lean_object* v_expr_610_; lean_object* v___x_611_; 
v_expr_610_ = lean_ctor_get(v_x_586_, 1);
lean_inc_ref(v_expr_610_);
lean_dec_ref_known(v_x_586_, 2);
v___x_611_ = l_Lean_CollectLevelMVars_visitExpr(v_expr_610_, v_a_587_);
return v___x_611_;
}
case 4:
{
lean_object* v_us_612_; lean_object* v___x_613_; 
v_us_612_ = lean_ctor_get(v_x_586_, 1);
lean_inc(v_us_612_);
lean_dec_ref_known(v_x_586_, 2);
v___x_613_ = l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__4(v_a_587_, v_us_612_);
return v___x_613_;
}
case 3:
{
lean_object* v_u_614_; lean_object* v___x_615_; 
v_u_614_ = lean_ctor_get(v_x_586_, 0);
lean_inc(v_u_614_);
lean_dec_ref_known(v_x_586_, 1);
v___x_615_ = l_Lean_CollectLevelMVars_visitLevel(v_u_614_, v_a_587_);
return v___x_615_;
}
default: 
{
lean_dec_ref(v_x_586_);
return v_a_587_;
}
}
v___jp_588_:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = l_Lean_CollectLevelMVars_visitExpr(v_d_589_, v___y_591_);
v___x_593_ = l_Lean_CollectLevelMVars_visitExpr(v_b_590_, v___x_592_);
return v___x_593_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(lean_object* v_00_u03b2_616_, lean_object* v_m_617_, lean_object* v_a_618_){
_start:
{
uint8_t v___x_619_; 
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_617_, v_a_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___boxed(lean_object* v_00_u03b2_620_, lean_object* v_m_621_, lean_object* v_a_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(v_00_u03b2_620_, v_m_621_, v_a_622_);
lean_dec_ref(v_a_622_);
lean_dec_ref(v_m_621_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1(lean_object* v_00_u03b2_625_, lean_object* v_m_626_, lean_object* v_query_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_m_626_, v_query_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1___boxed(lean_object* v_00_u03b2_629_, lean_object* v_m_630_, lean_object* v_query_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1(v_00_u03b2_629_, v_m_630_, v_query_631_);
lean_dec_ref(v_query_631_);
lean_dec_ref(v_m_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2(lean_object* v_00_u03b2_633_, lean_object* v_m_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2___redArg(v_m_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2___boxed(lean_object* v_00_u03b2_636_, lean_object* v_m_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2(v_00_u03b2_636_, v_m_637_);
lean_dec_ref(v_m_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(lean_object* v_00_u03b2_639_, lean_object* v_m_640_, lean_object* v_query_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_m_640_, v_query_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_643_, lean_object* v_m_644_, lean_object* v_query_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(v_00_u03b2_643_, v_m_644_, v_query_645_);
lean_dec_ref(v_query_645_);
lean_dec_ref(v_m_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2(lean_object* v_00_u03b2_647_, lean_object* v_m_648_, lean_object* v_query_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_m_648_, v_query_649_, v_x_650_, v_x_651_, v_x_652_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___boxed(lean_object* v_00_u03b2_655_, lean_object* v_m_656_, lean_object* v_query_657_, lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2(v_00_u03b2_655_, v_m_656_, v_query_657_, v_x_658_, v_x_659_, v_x_660_, v_x_661_);
lean_dec_ref(v_query_657_);
lean_dec_ref(v_m_656_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4(lean_object* v_00_u03b2_663_, lean_object* v_init_664_, lean_object* v_b_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4___redArg(v_init_664_, v_b_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4___boxed(lean_object* v_00_u03b2_667_, lean_object* v_init_668_, lean_object* v_b_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4(v_00_u03b2_667_, v_init_668_, v_b_669_);
lean_dec_ref(v_b_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_671_, lean_object* v_b_672_, lean_object* v_acc_673_, lean_object* v_i_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6___redArg(v_b_672_, v_acc_673_, v_i_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_676_, lean_object* v_b_677_, lean_object* v_acc_678_, lean_object* v_i_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelMVars_visitExpr_spec__2_spec__4_spec__6(v_00_u03b2_676_, v_b_677_, v_acc_678_, v_i_679_);
lean_dec_ref(v_b_677_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectLevelMVars(lean_object* v_s_681_, lean_object* v_e_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_CollectLevelMVars_main(v_e_682_, v_s_681_);
return v___x_683_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectLevelMVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectLevelMVars_instInhabitedState = _init_l_Lean_CollectLevelMVars_instInhabitedState();
lean_mark_persistent(l_Lean_CollectLevelMVars_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectLevelMVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectLevelMVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectLevelMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectLevelMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectLevelMVars(builtin);
}
#ifdef __cplusplus
}
#endif
