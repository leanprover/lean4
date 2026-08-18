// Lean compiler output
// Module: Lean.Util.CollectLevelParams
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
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
static lean_once_cell_t l_Lean_CollectLevelParams_instInhabitedState___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelParams_instInhabitedState___closed__0;
static lean_once_cell_t l_Lean_CollectLevelParams_instInhabitedState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelParams_instInhabitedState___closed__1;
static lean_once_cell_t l_Lean_CollectLevelParams_instInhabitedState___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelParams_instInhabitedState___closed__2;
static const lean_array_object l_Lean_CollectLevelParams_instInhabitedState___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_CollectLevelParams_instInhabitedState___closed__3 = (const lean_object*)&l_Lean_CollectLevelParams_instInhabitedState___closed__3_value;
static lean_once_cell_t l_Lean_CollectLevelParams_instInhabitedState___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_CollectLevelParams_instInhabitedState___closed__4;
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_instInhabitedState;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_collect(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevels(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_collect(lean_object*, lean_object*);
static lean_object* _init_l_Lean_CollectLevelParams_instInhabitedState___closed__0(void){
_start:
{
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_CollectLevelParams_instInhabitedState___closed__1(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_CollectLevelParams_instInhabitedState___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l_Lean_CollectLevelParams_instInhabitedState___closed__1, &l_Lean_CollectLevelParams_instInhabitedState___closed__1_once, _init_l_Lean_CollectLevelParams_instInhabitedState___closed__1);
v___x_6_ = lean_obj_once(&l_Lean_CollectLevelParams_instInhabitedState___closed__0, &l_Lean_CollectLevelParams_instInhabitedState___closed__0_once, _init_l_Lean_CollectLevelParams_instInhabitedState___closed__0);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_CollectLevelParams_instInhabitedState___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = ((lean_object*)(l_Lean_CollectLevelParams_instInhabitedState___closed__3));
v___x_12_ = lean_obj_once(&l_Lean_CollectLevelParams_instInhabitedState___closed__2, &l_Lean_CollectLevelParams_instInhabitedState___closed__2_once, _init_l_Lean_CollectLevelParams_instInhabitedState___closed__2);
v___x_13_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
lean_ctor_set(v___x_13_, 2, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_CollectLevelParams_instInhabitedState(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Lean_CollectLevelParams_instInhabitedState___closed__4, &l_Lean_CollectLevelParams_instInhabitedState___closed__4_once, _init_l_Lean_CollectLevelParams_instInhabitedState___closed__4);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(lean_object* v_m_15_, lean_object* v_query_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_x_19_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg___boxed(lean_object* v_m_66_, lean_object* v_query_67_, lean_object* v_x_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(v_m_66_, v_query_67_, v_x_68_, v_x_69_, v_x_70_);
lean_dec(v_query_67_);
lean_dec_ref(v_m_66_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(lean_object* v_m_72_, lean_object* v_query_73_){
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
v___x_90_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(v_m_72_, v_query_73_, v___x_89_, v___x_75_, v___x_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg___boxed(lean_object* v_m_91_, lean_object* v_query_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_m_91_, v_query_92_);
lean_dec(v_query_92_);
lean_dec_ref(v_m_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6___redArg(lean_object* v_b_94_, lean_object* v_acc_95_, lean_object* v_i_96_){
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
v___x_122_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_acc_95_, v_val_114_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_b_130_, lean_object* v_acc_131_, lean_object* v_i_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6___redArg(v_b_130_, v_acc_131_, v_i_132_);
lean_dec_ref(v_b_130_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5___redArg(lean_object* v_init_134_, lean_object* v_b_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6___redArg(v_b_135_, v_init_134_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5___redArg___boxed(lean_object* v_init_138_, lean_object* v_b_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5___redArg(v_init_138_, v_b_139_);
lean_dec_ref(v_b_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2___redArg(lean_object* v_m_141_){
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
v___x_150_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5___redArg(v_target_149_, v_m_141_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2___redArg___boxed(lean_object* v_m_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2___redArg(v_m_151_);
lean_dec_ref(v_m_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(lean_object* v_m_153_, lean_object* v_query_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_m_153_, v_query_154_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg___boxed(lean_object* v_m_167_, lean_object* v_query_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_m_167_, v_query_168_);
lean_dec(v_query_168_);
lean_dec_ref(v_m_167_);
return v_res_169_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(lean_object* v_m_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_m_170_, v_a_171_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg___boxed(lean_object* v_m_175_, lean_object* v_a_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_m_175_, v_a_176_);
lean_dec(v_a_176_);
lean_dec_ref(v_m_175_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object* v_u_179_, lean_object* v_s_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = l_Lean_Level_hasParam(v_u_179_);
if (v___x_181_ == 0)
{
lean_dec(v_u_179_);
return v_s_180_;
}
else
{
lean_object* v_visitedLevel_182_; lean_object* v_visitedExpr_183_; lean_object* v_params_184_; lean_object* v___y_186_; uint8_t v___x_189_; 
v_visitedLevel_182_ = lean_ctor_get(v_s_180_, 0);
v_visitedExpr_183_ = lean_ctor_get(v_s_180_, 1);
v_params_184_ = lean_ctor_get(v_s_180_, 2);
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_182_, v_u_179_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___y_192_; lean_object* v_i_193_; lean_object* v___y_199_; lean_object* v___y_209_; lean_object* v_i_210_; lean_object* v___x_225_; 
lean_inc_ref(v_params_184_);
lean_inc_ref(v_visitedExpr_183_);
lean_inc_ref(v_visitedLevel_182_);
lean_dec_ref(v_s_180_);
v___x_190_ = lean_box(0);
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_visitedLevel_182_, v_u_179_);
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
v___x_245_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2___redArg(v_visitedLevel_182_);
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
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2___redArg(v_visitedLevel_182_);
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
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v___y_199_, v_u_179_);
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
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2___redArg(v_visitedLevel_182_);
lean_dec_ref(v_visitedLevel_182_);
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v___x_216_, v_u_179_);
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
lean_ctor_set(v___x_187_, 2, v_params_184_);
v___x_188_ = l_Lean_CollectLevelParams_collect(v_u_179_, v___x_187_);
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_collect(lean_object* v_x_252_, lean_object* v_a_253_){
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
v___x_261_ = l_Lean_CollectLevelParams_visitLevel(v_a_260_, v_a_253_);
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
case 4:
{
lean_object* v_a_266_; lean_object* v_visitedLevel_267_; lean_object* v_visitedExpr_268_; lean_object* v_params_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_a_266_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_a_266_);
lean_dec_ref_known(v_x_252_, 1);
v_visitedLevel_267_ = lean_ctor_get(v_a_253_, 0);
v_visitedExpr_268_ = lean_ctor_get(v_a_253_, 1);
v_params_269_ = lean_ctor_get(v_a_253_, 2);
v_isSharedCheck_277_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v_a_253_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_params_269_);
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
v___x_273_ = lean_array_push(v_params_269_, v_a_266_);
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
v___x_258_ = l_Lean_CollectLevelParams_visitLevel(v_u_255_, v___y_257_);
v___x_259_ = l_Lean_CollectLevelParams_visitLevel(v_v_256_, v___x_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0(lean_object* v_00_u03b2_278_, lean_object* v_m_279_, lean_object* v_a_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_m_279_, v_a_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___boxed(lean_object* v_00_u03b2_282_, lean_object* v_m_283_, lean_object* v_a_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0(v_00_u03b2_282_, v_m_283_, v_a_284_);
lean_dec(v_a_284_);
lean_dec_ref(v_m_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1(lean_object* v_00_u03b2_287_, lean_object* v_m_288_, lean_object* v_query_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_m_288_, v_query_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1___boxed(lean_object* v_00_u03b2_291_, lean_object* v_m_292_, lean_object* v_query_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1(v_00_u03b2_291_, v_m_292_, v_query_293_);
lean_dec(v_query_293_);
lean_dec_ref(v_m_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2(lean_object* v_00_u03b2_295_, lean_object* v_m_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2___redArg(v_m_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2___boxed(lean_object* v_00_u03b2_298_, lean_object* v_m_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2(v_00_u03b2_298_, v_m_299_);
lean_dec_ref(v_m_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(lean_object* v_00_u03b2_301_, lean_object* v_m_302_, lean_object* v_query_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_m_302_, v_query_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___boxed(lean_object* v_00_u03b2_305_, lean_object* v_m_306_, lean_object* v_query_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(v_00_u03b2_305_, v_m_306_, v_query_307_);
lean_dec(v_query_307_);
lean_dec_ref(v_m_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3(lean_object* v_00_u03b2_309_, lean_object* v_m_310_, lean_object* v_query_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(v_m_310_, v_query_311_, v_x_312_, v_x_313_, v_x_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___boxed(lean_object* v_00_u03b2_317_, lean_object* v_m_318_, lean_object* v_query_319_, lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3(v_00_u03b2_317_, v_m_318_, v_query_319_, v_x_320_, v_x_321_, v_x_322_, v_x_323_);
lean_dec(v_query_319_);
lean_dec_ref(v_m_318_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5(lean_object* v_00_u03b2_325_, lean_object* v_init_326_, lean_object* v_b_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5___redArg(v_init_326_, v_b_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5___boxed(lean_object* v_00_u03b2_329_, lean_object* v_init_330_, lean_object* v_b_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5(v_00_u03b2_329_, v_init_330_, v_b_331_);
lean_dec_ref(v_b_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_333_, lean_object* v_b_334_, lean_object* v_acc_335_, lean_object* v_i_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6___redArg(v_b_334_, v_acc_335_, v_i_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6___boxed(lean_object* v_00_u03b2_338_, lean_object* v_b_339_, lean_object* v_acc_340_, lean_object* v_i_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitLevel_spec__2_spec__5_spec__6(v_00_u03b2_338_, v_b_339_, v_acc_340_, v_i_341_);
lean_dec_ref(v_b_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_344_) == 0)
{
return v_x_343_;
}
else
{
lean_object* v_head_345_; lean_object* v_tail_346_; lean_object* v___x_347_; 
v_head_345_ = lean_ctor_get(v_x_344_, 0);
lean_inc(v_head_345_);
v_tail_346_ = lean_ctor_get(v_x_344_, 1);
lean_inc(v_tail_346_);
lean_dec_ref_known(v_x_344_, 2);
v___x_347_ = l_Lean_CollectLevelParams_visitLevel(v_head_345_, v_x_343_);
v_x_343_ = v___x_347_;
v_x_344_ = v_tail_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitLevels(lean_object* v_us_349_, lean_object* v_s_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(v_s_350_, v_us_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(lean_object* v_m_352_, lean_object* v_query_353_, lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
lean_object* v_zero_357_; uint8_t v_isZero_358_; 
v_zero_357_ = lean_unsigned_to_nat(0u);
v_isZero_358_ = lean_nat_dec_eq(v_x_355_, v_zero_357_);
if (v_isZero_358_ == 1)
{
lean_dec(v_x_356_);
lean_dec(v_x_355_);
if (lean_obj_tag(v_x_354_) == 0)
{
lean_object* v___x_359_; 
v___x_359_ = lean_box(2);
return v___x_359_;
}
else
{
lean_object* v_val_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_val_360_ = lean_ctor_get(v_x_354_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v_x_354_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_val_360_);
lean_dec(v_x_354_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_val_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
else
{
lean_object* v_keyArray_368_; lean_object* v_valueArray_369_; lean_object* v___x_370_; uint8_t v_isSome_371_; 
v_keyArray_368_ = lean_ctor_get(v_m_352_, 1);
v_valueArray_369_ = lean_ctor_get(v_m_352_, 2);
v___x_370_ = lean_array_fget_borrowed(v_keyArray_368_, v_x_356_);
v_isSome_371_ = lean_noption_is_some(v___x_370_);
if (v_isSome_371_ == 0)
{
lean_dec(v_x_355_);
if (lean_obj_tag(v_x_354_) == 0)
{
lean_object* v___x_372_; 
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v_x_356_);
return v___x_372_;
}
else
{
lean_object* v_val_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec(v_x_356_);
v_val_373_ = lean_ctor_get(v_x_354_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v_x_354_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_val_373_);
lean_dec(v_x_354_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
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
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_val_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v_one_381_; lean_object* v_n_382_; lean_object* v___y_384_; 
v_one_381_ = lean_unsigned_to_nat(1u);
v_n_382_ = lean_nat_sub(v_x_355_, v_one_381_);
lean_dec(v_x_355_);
if (v_isSome_371_ == 0)
{
goto v___jp_390_;
}
else
{
lean_object* v___x_392_; uint8_t v_isSome_393_; 
v___x_392_ = lean_array_fget_borrowed(v_valueArray_369_, v_x_356_);
v_isSome_393_ = lean_noption_is_some(v___x_392_);
if (v_isSome_393_ == 0)
{
goto v___jp_390_;
}
else
{
lean_object* v_val_394_; uint8_t v___x_395_; 
lean_inc(v___x_370_);
v_val_394_ = lean_noption_get(v___x_370_);
v___x_395_ = lean_expr_eqv(v_val_394_, v_query_353_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
lean_dec(v_val_394_);
v___x_396_ = lean_array_get_size(v_keyArray_368_);
v___x_397_ = lean_nat_add(v_x_356_, v_one_381_);
lean_dec(v_x_356_);
v___x_398_ = lean_nat_dec_lt(v___x_397_, v___x_396_);
if (v___x_398_ == 0)
{
lean_dec(v___x_397_);
v_x_355_ = v_n_382_;
v_x_356_ = v_zero_357_;
goto _start;
}
else
{
v_x_355_ = v_n_382_;
v_x_356_ = v___x_397_;
goto _start;
}
}
else
{
lean_object* v_val_401_; lean_object* v___x_402_; 
lean_dec(v_n_382_);
lean_dec(v_x_354_);
lean_inc(v___x_392_);
v_val_401_ = lean_noption_get(v___x_392_);
v___x_402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_402_, 0, v_x_356_);
lean_ctor_set(v___x_402_, 1, v_val_394_);
lean_ctor_set(v___x_402_, 2, v_val_401_);
return v___x_402_;
}
}
}
v___jp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_385_ = lean_array_get_size(v_keyArray_368_);
v___x_386_ = lean_nat_add(v_x_356_, v_one_381_);
lean_dec(v_x_356_);
v___x_387_ = lean_nat_dec_lt(v___x_386_, v___x_385_);
if (v___x_387_ == 0)
{
lean_dec(v___x_386_);
v_x_354_ = v___y_384_;
v_x_355_ = v_n_382_;
v_x_356_ = v_zero_357_;
goto _start;
}
else
{
v_x_354_ = v___y_384_;
v_x_355_ = v_n_382_;
v_x_356_ = v___x_386_;
goto _start;
}
}
v___jp_390_:
{
if (lean_obj_tag(v_x_354_) == 0)
{
lean_object* v___x_391_; 
lean_inc(v_x_356_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v_x_356_);
v___y_384_ = v___x_391_;
goto v___jp_383_;
}
else
{
v___y_384_ = v_x_354_;
goto v___jp_383_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg___boxed(lean_object* v_m_403_, lean_object* v_query_404_, lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(v_m_403_, v_query_404_, v_x_405_, v_x_406_, v_x_407_);
lean_dec_ref(v_query_404_);
lean_dec_ref(v_m_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(lean_object* v_m_409_, lean_object* v_query_410_){
_start:
{
lean_object* v_keyArray_411_; lean_object* v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v_fold_416_; uint64_t v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; size_t v___x_420_; size_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_keyArray_411_ = lean_ctor_get(v_m_409_, 1);
v___x_412_ = lean_array_get_size(v_keyArray_411_);
v___x_413_ = l_Lean_Expr_hash(v_query_410_);
v___x_414_ = 32ULL;
v___x_415_ = lean_uint64_shift_right(v___x_413_, v___x_414_);
v_fold_416_ = lean_uint64_xor(v___x_413_, v___x_415_);
v___x_417_ = 16ULL;
v___x_418_ = lean_uint64_shift_right(v_fold_416_, v___x_417_);
v___x_419_ = lean_uint64_xor(v_fold_416_, v___x_418_);
v___x_420_ = lean_uint64_to_usize(v___x_419_);
v___x_421_ = lean_usize_of_nat(v___x_412_);
v___x_422_ = ((size_t)1ULL);
v___x_423_ = lean_usize_sub(v___x_421_, v___x_422_);
v___x_424_ = lean_usize_land(v___x_420_, v___x_423_);
v___x_425_ = lean_usize_to_nat(v___x_424_);
v___x_426_ = lean_box(0);
v___x_427_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(v_m_409_, v_query_410_, v___x_426_, v___x_412_, v___x_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg___boxed(lean_object* v_m_428_, lean_object* v_query_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_m_428_, v_query_429_);
lean_dec_ref(v_query_429_);
lean_dec_ref(v_m_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(lean_object* v_m_431_, lean_object* v_query_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_m_431_, v_query_432_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_index_434_; lean_object* v_key_435_; lean_object* v_value_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
v_index_434_ = lean_ctor_get(v___x_433_, 0);
v_key_435_ = lean_ctor_get(v___x_433_, 1);
v_value_436_ = lean_ctor_get(v___x_433_, 2);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_433_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_value_436_);
lean_inc(v_key_435_);
lean_inc(v_index_434_);
lean_dec(v___x_433_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_index_434_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_key_435_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_value_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
else
{
lean_object* v___x_444_; 
lean_dec(v___x_433_);
v___x_444_ = lean_box(1);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg___boxed(lean_object* v_m_445_, lean_object* v_query_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_m_445_, v_query_446_);
lean_dec_ref(v_query_446_);
lean_dec_ref(v_m_445_);
return v_res_447_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(lean_object* v_m_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_m_448_, v_a_449_);
if (lean_obj_tag(v___x_450_) == 0)
{
uint8_t v___x_451_; 
lean_dec_ref_known(v___x_450_, 3);
v___x_451_ = 1;
return v___x_451_;
}
else
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg___boxed(lean_object* v_m_453_, lean_object* v_a_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_m_453_, v_a_454_);
lean_dec_ref(v_a_454_);
lean_dec_ref(v_m_453_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6___redArg(lean_object* v_b_457_, lean_object* v_acc_458_, lean_object* v_i_459_){
_start:
{
lean_object* v___y_461_; lean_object* v_keyArray_469_; lean_object* v_valueArray_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v_keyArray_469_ = lean_ctor_get(v_b_457_, 1);
v_valueArray_470_ = lean_ctor_get(v_b_457_, 2);
v___x_471_ = lean_array_get_size(v_keyArray_469_);
v___x_472_ = lean_nat_dec_lt(v_i_459_, v___x_471_);
if (v___x_472_ == 0)
{
lean_dec(v_i_459_);
return v_acc_458_;
}
else
{
lean_object* v___x_473_; uint8_t v_isSome_474_; 
v___x_473_ = lean_array_fget_borrowed(v_keyArray_469_, v_i_459_);
v_isSome_474_ = lean_noption_is_some(v___x_473_);
if (v_isSome_474_ == 0)
{
goto v___jp_465_;
}
else
{
lean_object* v___x_475_; uint8_t v_isSome_476_; 
v___x_475_ = lean_array_fget_borrowed(v_valueArray_470_, v_i_459_);
v_isSome_476_ = lean_noption_is_some(v___x_475_);
if (v_isSome_476_ == 0)
{
goto v___jp_465_;
}
else
{
lean_object* v_val_477_; lean_object* v_val_478_; lean_object* v_i_480_; lean_object* v___x_485_; 
lean_inc(v___x_473_);
v_val_477_ = lean_noption_get(v___x_473_);
lean_inc(v___x_475_);
v_val_478_ = lean_noption_get(v___x_475_);
v___x_485_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_acc_458_, v_val_477_);
switch(lean_obj_tag(v___x_485_))
{
case 0:
{
lean_object* v_index_486_; lean_object* v_size_487_; lean_object* v___x_488_; 
v_index_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_index_486_);
lean_dec_ref_known(v___x_485_, 3);
v_size_487_ = lean_ctor_get(v_acc_458_, 0);
lean_inc(v_size_487_);
v___x_488_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_458_, v_size_487_, v_index_486_, v_val_477_, v_val_478_);
lean_dec(v_index_486_);
v___y_461_ = v___x_488_;
goto v___jp_460_;
}
case 1:
{
lean_object* v_index_489_; 
v_index_489_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_index_489_);
lean_dec_ref_known(v___x_485_, 1);
v_i_480_ = v_index_489_;
goto v___jp_479_;
}
default: 
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_458_, v___x_490_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_index_492_; 
v_index_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_index_492_);
lean_dec_ref_known(v___x_491_, 1);
v_i_480_ = v_index_492_;
goto v___jp_479_;
}
else
{
lean_dec(v_val_478_);
lean_dec(v_val_477_);
v___y_461_ = v_acc_458_;
goto v___jp_460_;
}
}
}
v___jp_479_:
{
lean_object* v_size_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_size_481_ = lean_ctor_get(v_acc_458_, 0);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_add(v_size_481_, v___x_482_);
v___x_484_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_458_, v___x_483_, v_i_480_, v_val_477_, v_val_478_);
lean_dec(v_i_480_);
v___y_461_ = v___x_484_;
goto v___jp_460_;
}
}
}
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(1u);
v___x_463_ = lean_nat_add(v_i_459_, v___x_462_);
lean_dec(v_i_459_);
v_acc_458_ = v___y_461_;
v_i_459_ = v___x_463_;
goto _start;
}
v___jp_465_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v_i_459_, v___x_466_);
lean_dec(v_i_459_);
v_i_459_ = v___x_467_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_b_493_, lean_object* v_acc_494_, lean_object* v_i_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6___redArg(v_b_493_, v_acc_494_, v_i_495_);
lean_dec_ref(v_b_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5___redArg(lean_object* v_init_497_, lean_object* v_b_498_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6___redArg(v_b_498_, v_init_497_, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5___redArg___boxed(lean_object* v_init_501_, lean_object* v_b_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5___redArg(v_init_501_, v_b_502_);
lean_dec_ref(v_b_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2___redArg(lean_object* v_m_504_){
_start:
{
lean_object* v_keyArray_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_cellCount_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_target_512_; lean_object* v___x_513_; 
v_keyArray_505_ = lean_ctor_get(v_m_504_, 1);
v___x_506_ = lean_array_get_size(v_keyArray_505_);
v___x_507_ = lean_unsigned_to_nat(2u);
v_cellCount_508_ = lean_nat_mul(v___x_506_, v___x_507_);
v___x_509_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_508_);
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_508_);
v___x_511_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_508_);
v_target_512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_512_, 0, v___x_509_);
lean_ctor_set(v_target_512_, 1, v___x_510_);
lean_ctor_set(v_target_512_, 2, v___x_511_);
v___x_513_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5___redArg(v_target_512_, v_m_504_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2___redArg___boxed(lean_object* v_m_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2___redArg(v_m_514_);
lean_dec_ref(v_m_514_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object* v_e_516_, lean_object* v_s_517_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = l_Lean_Expr_hasLevelParam(v_e_516_);
if (v___x_518_ == 0)
{
lean_dec_ref(v_e_516_);
return v_s_517_;
}
else
{
lean_object* v_visitedLevel_519_; lean_object* v_visitedExpr_520_; lean_object* v_params_521_; lean_object* v___y_523_; uint8_t v___x_526_; 
v_visitedLevel_519_ = lean_ctor_get(v_s_517_, 0);
v_visitedExpr_520_ = lean_ctor_get(v_s_517_, 1);
v_params_521_ = lean_ctor_get(v_s_517_, 2);
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_visitedExpr_520_, v_e_516_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___y_529_; lean_object* v_i_530_; lean_object* v___y_536_; lean_object* v___y_546_; lean_object* v_i_547_; lean_object* v___x_562_; 
lean_inc_ref(v_params_521_);
lean_inc_ref(v_visitedExpr_520_);
lean_inc_ref(v_visitedLevel_519_);
lean_dec_ref(v_s_517_);
v___x_527_ = lean_box(0);
v___x_562_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_visitedExpr_520_, v_e_516_);
switch(lean_obj_tag(v___x_562_))
{
case 0:
{
lean_dec_ref_known(v___x_562_, 3);
v___y_523_ = v_visitedExpr_520_;
goto v___jp_522_;
}
case 1:
{
lean_object* v_index_563_; lean_object* v_size_564_; lean_object* v_keyArray_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_index_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_index_563_);
lean_dec_ref_known(v___x_562_, 1);
v_size_564_ = lean_ctor_get(v_visitedExpr_520_, 0);
v_keyArray_565_ = lean_ctor_get(v_visitedExpr_520_, 1);
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_nat_add(v_size_564_, v___x_566_);
v___x_568_ = lean_array_get_size(v_keyArray_565_);
v___x_569_ = lean_nat_dec_lt(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_dec(v___x_567_);
lean_dec(v_index_563_);
goto v___jp_552_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_570_ = lean_unsigned_to_nat(4u);
v___x_571_ = lean_nat_mul(v___x_567_, v___x_570_);
v___x_572_ = lean_unsigned_to_nat(3u);
v___x_573_ = lean_nat_mul(v___x_568_, v___x_572_);
v___x_574_ = lean_nat_dec_le(v___x_571_, v___x_573_);
lean_dec(v___x_573_);
lean_dec(v___x_571_);
if (v___x_574_ == 0)
{
lean_dec(v___x_567_);
lean_dec(v_index_563_);
goto v___jp_552_;
}
else
{
lean_object* v___x_575_; 
lean_inc_ref(v_e_516_);
v___x_575_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visitedExpr_520_, v___x_567_, v_index_563_, v_e_516_, v___x_527_);
lean_dec(v_index_563_);
v___y_523_ = v___x_575_;
goto v___jp_522_;
}
}
}
default: 
{
lean_object* v_size_576_; lean_object* v_keyArray_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_size_576_ = lean_ctor_get(v_visitedExpr_520_, 0);
v_keyArray_577_ = lean_ctor_get(v_visitedExpr_520_, 1);
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_size_576_, v___x_578_);
v___x_580_ = lean_array_get_size(v_keyArray_577_);
v___x_581_ = lean_nat_dec_lt(v___x_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec(v___x_579_);
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2___redArg(v_visitedExpr_520_);
lean_dec_ref(v_visitedExpr_520_);
v___y_536_ = v___x_582_;
goto v___jp_535_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_583_ = lean_unsigned_to_nat(4u);
v___x_584_ = lean_nat_mul(v___x_579_, v___x_583_);
lean_dec(v___x_579_);
v___x_585_ = lean_unsigned_to_nat(3u);
v___x_586_ = lean_nat_mul(v___x_580_, v___x_585_);
v___x_587_ = lean_nat_dec_le(v___x_584_, v___x_586_);
lean_dec(v___x_586_);
lean_dec(v___x_584_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2___redArg(v_visitedExpr_520_);
lean_dec_ref(v_visitedExpr_520_);
v___y_536_ = v___x_588_;
goto v___jp_535_;
}
else
{
v___y_536_ = v_visitedExpr_520_;
goto v___jp_535_;
}
}
}
}
v___jp_528_:
{
lean_object* v_size_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_size_531_ = lean_ctor_get(v___y_529_, 0);
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = lean_nat_add(v_size_531_, v___x_532_);
lean_inc_ref(v_e_516_);
v___x_534_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_529_, v___x_533_, v_i_530_, v_e_516_, v___x_527_);
lean_dec(v_i_530_);
v___y_523_ = v___x_534_;
goto v___jp_522_;
}
v___jp_535_:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v___y_536_, v_e_516_);
switch(lean_obj_tag(v___x_537_))
{
case 0:
{
lean_object* v_index_538_; lean_object* v_size_539_; lean_object* v___x_540_; 
v_index_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_index_538_);
lean_dec_ref_known(v___x_537_, 3);
v_size_539_ = lean_ctor_get(v___y_536_, 0);
lean_inc(v_size_539_);
lean_inc_ref(v_e_516_);
v___x_540_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_536_, v_size_539_, v_index_538_, v_e_516_, v___x_527_);
lean_dec(v_index_538_);
v___y_523_ = v___x_540_;
goto v___jp_522_;
}
case 1:
{
lean_object* v_index_541_; 
v_index_541_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_index_541_);
lean_dec_ref_known(v___x_537_, 1);
v___y_529_ = v___y_536_;
v_i_530_ = v_index_541_;
goto v___jp_528_;
}
default: 
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_536_, v___x_542_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_index_544_; 
v_index_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_index_544_);
lean_dec_ref_known(v___x_543_, 1);
v___y_529_ = v___y_536_;
v_i_530_ = v_index_544_;
goto v___jp_528_;
}
else
{
v___y_523_ = v___y_536_;
goto v___jp_522_;
}
}
}
}
v___jp_545_:
{
lean_object* v_size_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_size_548_ = lean_ctor_get(v___y_546_, 0);
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_add(v_size_548_, v___x_549_);
lean_inc_ref(v_e_516_);
v___x_551_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_546_, v___x_550_, v_i_547_, v_e_516_, v___x_527_);
lean_dec(v_i_547_);
v___y_523_ = v___x_551_;
goto v___jp_522_;
}
v___jp_552_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2___redArg(v_visitedExpr_520_);
lean_dec_ref(v_visitedExpr_520_);
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v___x_553_, v_e_516_);
switch(lean_obj_tag(v___x_554_))
{
case 0:
{
lean_object* v_index_555_; lean_object* v_size_556_; lean_object* v___x_557_; 
v_index_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_index_555_);
lean_dec_ref_known(v___x_554_, 3);
v_size_556_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_size_556_);
lean_inc_ref(v_e_516_);
v___x_557_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_553_, v_size_556_, v_index_555_, v_e_516_, v___x_527_);
lean_dec(v_index_555_);
v___y_523_ = v___x_557_;
goto v___jp_522_;
}
case 1:
{
lean_object* v_index_558_; 
v_index_558_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_index_558_);
lean_dec_ref_known(v___x_554_, 1);
v___y_546_ = v___x_553_;
v_i_547_ = v_index_558_;
goto v___jp_545_;
}
default: 
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_553_, v___x_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_index_561_; 
v_index_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_index_561_);
lean_dec_ref_known(v___x_560_, 1);
v___y_546_ = v___x_553_;
v_i_547_ = v_index_561_;
goto v___jp_545_;
}
else
{
v___y_523_ = v___x_553_;
goto v___jp_522_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_516_);
return v_s_517_;
}
v___jp_522_:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_524_, 0, v_visitedLevel_519_);
lean_ctor_set(v___x_524_, 1, v___y_523_);
lean_ctor_set(v___x_524_, 2, v_params_521_);
v___x_525_ = l_Lean_CollectLevelParams_main(v_e_516_, v___x_524_);
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_main(lean_object* v_x_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_d_592_; lean_object* v_b_593_; lean_object* v___y_594_; 
switch(lean_obj_tag(v_x_589_))
{
case 11:
{
lean_object* v_struct_597_; lean_object* v___x_598_; 
v_struct_597_ = lean_ctor_get(v_x_589_, 2);
lean_inc_ref(v_struct_597_);
lean_dec_ref_known(v_x_589_, 3);
v___x_598_ = l_Lean_CollectLevelParams_visitExpr(v_struct_597_, v_a_590_);
return v___x_598_;
}
case 7:
{
lean_object* v_binderType_599_; lean_object* v_body_600_; 
v_binderType_599_ = lean_ctor_get(v_x_589_, 1);
lean_inc_ref(v_binderType_599_);
v_body_600_ = lean_ctor_get(v_x_589_, 2);
lean_inc_ref(v_body_600_);
lean_dec_ref_known(v_x_589_, 3);
v_d_592_ = v_binderType_599_;
v_b_593_ = v_body_600_;
v___y_594_ = v_a_590_;
goto v___jp_591_;
}
case 6:
{
lean_object* v_binderType_601_; lean_object* v_body_602_; 
v_binderType_601_ = lean_ctor_get(v_x_589_, 1);
lean_inc_ref(v_binderType_601_);
v_body_602_ = lean_ctor_get(v_x_589_, 2);
lean_inc_ref(v_body_602_);
lean_dec_ref_known(v_x_589_, 3);
v_d_592_ = v_binderType_601_;
v_b_593_ = v_body_602_;
v___y_594_ = v_a_590_;
goto v___jp_591_;
}
case 8:
{
lean_object* v_type_603_; lean_object* v_value_604_; lean_object* v_body_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_type_603_ = lean_ctor_get(v_x_589_, 1);
lean_inc_ref(v_type_603_);
v_value_604_ = lean_ctor_get(v_x_589_, 2);
lean_inc_ref(v_value_604_);
v_body_605_ = lean_ctor_get(v_x_589_, 3);
lean_inc_ref(v_body_605_);
lean_dec_ref_known(v_x_589_, 4);
v___x_606_ = l_Lean_CollectLevelParams_visitExpr(v_type_603_, v_a_590_);
v___x_607_ = l_Lean_CollectLevelParams_visitExpr(v_value_604_, v___x_606_);
v___x_608_ = l_Lean_CollectLevelParams_visitExpr(v_body_605_, v___x_607_);
return v___x_608_;
}
case 5:
{
lean_object* v_fn_609_; lean_object* v_arg_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_fn_609_ = lean_ctor_get(v_x_589_, 0);
lean_inc_ref(v_fn_609_);
v_arg_610_ = lean_ctor_get(v_x_589_, 1);
lean_inc_ref(v_arg_610_);
lean_dec_ref_known(v_x_589_, 2);
v___x_611_ = l_Lean_CollectLevelParams_visitExpr(v_fn_609_, v_a_590_);
v___x_612_ = l_Lean_CollectLevelParams_visitExpr(v_arg_610_, v___x_611_);
return v___x_612_;
}
case 10:
{
lean_object* v_expr_613_; lean_object* v___x_614_; 
v_expr_613_ = lean_ctor_get(v_x_589_, 1);
lean_inc_ref(v_expr_613_);
lean_dec_ref_known(v_x_589_, 2);
v___x_614_ = l_Lean_CollectLevelParams_visitExpr(v_expr_613_, v_a_590_);
return v___x_614_;
}
case 4:
{
lean_object* v_us_615_; lean_object* v___x_616_; 
v_us_615_ = lean_ctor_get(v_x_589_, 1);
lean_inc(v_us_615_);
lean_dec_ref_known(v_x_589_, 2);
v___x_616_ = l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(v_a_590_, v_us_615_);
return v___x_616_;
}
case 3:
{
lean_object* v_u_617_; lean_object* v___x_618_; 
v_u_617_ = lean_ctor_get(v_x_589_, 0);
lean_inc(v_u_617_);
lean_dec_ref_known(v_x_589_, 1);
v___x_618_ = l_Lean_CollectLevelParams_visitLevel(v_u_617_, v_a_590_);
return v___x_618_;
}
default: 
{
lean_dec_ref(v_x_589_);
return v_a_590_;
}
}
v___jp_591_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = l_Lean_CollectLevelParams_visitExpr(v_d_592_, v___y_594_);
v___x_596_ = l_Lean_CollectLevelParams_visitExpr(v_b_593_, v___x_595_);
return v___x_596_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(lean_object* v_00_u03b2_619_, lean_object* v_m_620_, lean_object* v_a_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_m_620_, v_a_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___boxed(lean_object* v_00_u03b2_623_, lean_object* v_m_624_, lean_object* v_a_625_){
_start:
{
uint8_t v_res_626_; lean_object* v_r_627_; 
v_res_626_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(v_00_u03b2_623_, v_m_624_, v_a_625_);
lean_dec_ref(v_a_625_);
lean_dec_ref(v_m_624_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1(lean_object* v_00_u03b2_628_, lean_object* v_m_629_, lean_object* v_query_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_m_629_, v_query_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1___boxed(lean_object* v_00_u03b2_632_, lean_object* v_m_633_, lean_object* v_query_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1(v_00_u03b2_632_, v_m_633_, v_query_634_);
lean_dec_ref(v_query_634_);
lean_dec_ref(v_m_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2(lean_object* v_00_u03b2_636_, lean_object* v_m_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2___redArg(v_m_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2___boxed(lean_object* v_00_u03b2_639_, lean_object* v_m_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2(v_00_u03b2_639_, v_m_640_);
lean_dec_ref(v_m_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(lean_object* v_00_u03b2_642_, lean_object* v_m_643_, lean_object* v_query_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_m_643_, v_query_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___boxed(lean_object* v_00_u03b2_646_, lean_object* v_m_647_, lean_object* v_query_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(v_00_u03b2_646_, v_m_647_, v_query_648_);
lean_dec_ref(v_query_648_);
lean_dec_ref(v_m_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3(lean_object* v_00_u03b2_650_, lean_object* v_m_651_, lean_object* v_query_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(v_m_651_, v_query_652_, v_x_653_, v_x_654_, v_x_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___boxed(lean_object* v_00_u03b2_658_, lean_object* v_m_659_, lean_object* v_query_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3(v_00_u03b2_658_, v_m_659_, v_query_660_, v_x_661_, v_x_662_, v_x_663_, v_x_664_);
lean_dec_ref(v_query_660_);
lean_dec_ref(v_m_659_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5(lean_object* v_00_u03b2_666_, lean_object* v_init_667_, lean_object* v_b_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5___redArg(v_init_667_, v_b_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_670_, lean_object* v_init_671_, lean_object* v_b_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5(v_00_u03b2_670_, v_init_671_, v_b_672_);
lean_dec_ref(v_b_672_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_674_, lean_object* v_b_675_, lean_object* v_acc_676_, lean_object* v_i_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6___redArg(v_b_675_, v_acc_676_, v_i_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6___boxed(lean_object* v_00_u03b2_679_, lean_object* v_b_680_, lean_object* v_acc_681_, lean_object* v_i_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_CollectLevelParams_visitExpr_spec__2_spec__5_spec__6(v_00_u03b2_679_, v_b_680_, v_acc_681_, v_i_682_);
lean_dec_ref(v_b_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(lean_object* v_s_684_, lean_object* v_pre_685_, lean_object* v_i_686_){
_start:
{
lean_object* v_visitedLevel_687_; lean_object* v___x_688_; lean_object* v_v_689_; uint8_t v___x_690_; 
v_visitedLevel_687_ = lean_ctor_get(v_s_684_, 0);
lean_inc(v_i_686_);
lean_inc(v_pre_685_);
v___x_688_ = lean_name_append_index_after(v_pre_685_, v_i_686_);
v_v_689_ = l_Lean_mkLevelParam(v___x_688_);
v___x_690_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_687_, v_v_689_);
if (v___x_690_ == 0)
{
lean_dec(v_i_686_);
lean_dec(v_pre_685_);
return v_v_689_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v_v_689_);
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_nat_add(v_i_686_, v___x_691_);
lean_dec(v_i_686_);
v_i_686_ = v___x_692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop___boxed(lean_object* v_s_694_, lean_object* v_pre_695_, lean_object* v_i_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(v_s_694_, v_pre_695_, v_i_696_);
lean_dec_ref(v_s_694_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam(lean_object* v_s_698_, lean_object* v_pre_699_){
_start:
{
lean_object* v_visitedLevel_700_; lean_object* v_v_701_; uint8_t v___x_702_; 
v_visitedLevel_700_ = lean_ctor_get(v_s_698_, 0);
lean_inc(v_pre_699_);
v_v_701_ = l_Lean_mkLevelParam(v_pre_699_);
v___x_702_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_700_, v_v_701_);
if (v___x_702_ == 0)
{
lean_dec(v_pre_699_);
return v_v_701_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v_v_701_);
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(v_s_698_, v_pre_699_, v___x_703_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_getUnusedLevelParam___boxed(lean_object* v_s_705_, lean_object* v_pre_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_CollectLevelParams_State_getUnusedLevelParam(v_s_705_, v_pre_706_);
lean_dec_ref(v_s_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_collectLevelParams(lean_object* v_s_708_, lean_object* v_e_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_CollectLevelParams_main(v_e_709_, v_s_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectLevelParams_State_collect(lean_object* v_s_711_, lean_object* v_e_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_CollectLevelParams_main(v_e_712_, v_s_711_);
return v___x_713_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectLevelParams(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectLevelParams_instInhabitedState = _init_l_Lean_CollectLevelParams_instInhabitedState();
lean_mark_persistent(l_Lean_CollectLevelParams_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectLevelParams(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectLevelParams(builtin);
}
#ifdef __cplusplus
}
#endif
