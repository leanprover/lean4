// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.RevertAll
// Imports: public import Lean.Meta.Tactic.Revert import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getAt_x3f(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "__grind_mark"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getOriginalName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getOriginalName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markGrindName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_MVarId_revertAll___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_revertAll___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_revertAll___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_revertAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "revertAll"};
static const lean_object* l_Lean_MVarId_revertAll___closed__0 = (const lean_object*)&l_Lean_MVarId_revertAll___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_revertAll___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_revertAll___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 62, 121, 47, 113, 229, 251, 224)}};
static const lean_object* l_Lean_MVarId_revertAll___closed__1 = (const lean_object*)&l_Lean_MVarId_revertAll___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getOriginalName_x3f(lean_object* v_name_3_){
_start:
{
if (lean_obj_tag(v_name_3_) == 1)
{
lean_object* v_pre_4_; lean_object* v_str_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v_pre_4_ = lean_ctor_get(v_name_3_, 0);
v_str_5_ = lean_ctor_get(v_name_3_, 1);
v___x_6_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0));
v___x_7_ = lean_string_dec_eq(v_str_5_, v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
else
{
lean_object* v___x_9_; 
lean_inc(v_pre_4_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_pre_4_);
return v___x_9_;
}
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getOriginalName_x3f___boxed(lean_object* v_name_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_11_);
lean_dec(v_name_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markGrindName(lean_object* v_userName_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0));
v___x_15_ = l_Lean_Name_str___override(v_userName_13_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(lean_object* v_mvarId_16_, lean_object* v_x_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_16_, v_x_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_31_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_31_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_27_ == 0)
{
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_24_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
else
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_a_32_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_23_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_23_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg___boxed(lean_object* v_mvarId_40_, lean_object* v_x_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_40_, v_x_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2(lean_object* v_00_u03b1_48_, lean_object* v_mvarId_49_, lean_object* v_x_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_49_, v_x_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___boxed(lean_object* v_00_u03b1_57_, lean_object* v_mvarId_58_, lean_object* v_x_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2(v_00_u03b1_57_, v_mvarId_58_, v_x_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_66_, lean_object* v_x_67_, lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
lean_object* v_ks_70_; lean_object* v_vs_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_95_; 
v_ks_70_ = lean_ctor_get(v_x_66_, 0);
v_vs_71_ = lean_ctor_get(v_x_66_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v_x_66_);
if (v_isSharedCheck_95_ == 0)
{
v___x_73_ = v_x_66_;
v_isShared_74_ = v_isSharedCheck_95_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_vs_71_);
lean_inc(v_ks_70_);
lean_dec(v_x_66_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_95_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_array_get_size(v_ks_70_);
v___x_76_ = lean_nat_dec_lt(v_x_67_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
lean_dec(v_x_67_);
v___x_77_ = lean_array_push(v_ks_70_, v_x_68_);
v___x_78_ = lean_array_push(v_vs_71_, v_x_69_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_78_);
lean_ctor_set(v___x_73_, 0, v___x_77_);
v___x_80_ = v___x_73_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
else
{
lean_object* v_k_x27_82_; uint8_t v___x_83_; 
v_k_x27_82_ = lean_array_fget_borrowed(v_ks_70_, v_x_67_);
v___x_83_ = l_Lean_instBEqMVarId_beq(v_x_68_, v_k_x27_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_85_; 
if (v_isShared_74_ == 0)
{
v___x_85_ = v___x_73_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_ks_70_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_vs_71_);
v___x_85_ = v_reuseFailAlloc_89_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_add(v_x_67_, v___x_86_);
lean_dec(v_x_67_);
v_x_66_ = v___x_85_;
v_x_67_ = v___x_87_;
goto _start;
}
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_90_ = lean_array_fset(v_ks_70_, v_x_67_, v_x_68_);
v___x_91_ = lean_array_fset(v_vs_71_, v_x_67_, v_x_69_);
lean_dec(v_x_67_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_91_);
lean_ctor_set(v___x_73_, 0, v___x_90_);
v___x_93_ = v___x_73_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_96_, lean_object* v_k_97_, lean_object* v_v_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_96_, v___x_99_, v_k_97_, v_v_98_);
return v___x_100_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_101_; size_t v___x_102_; size_t v___x_103_; 
v___x_101_ = ((size_t)5ULL);
v___x_102_ = ((size_t)1ULL);
v___x_103_ = lean_usize_shift_left(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_104_; size_t v___x_105_; size_t v___x_106_; 
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_106_ = lean_usize_sub(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(lean_object* v_x_108_, size_t v_x_109_, size_t v_x_110_, lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_object* v_es_113_; size_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; lean_object* v_j_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v_es_113_ = lean_ctor_get(v_x_108_, 0);
v___x_114_ = ((size_t)5ULL);
v___x_115_ = ((size_t)1ULL);
v___x_116_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_117_ = lean_usize_land(v_x_109_, v___x_116_);
v_j_118_ = lean_usize_to_nat(v___x_117_);
v___x_119_ = lean_array_get_size(v_es_113_);
v___x_120_ = lean_nat_dec_lt(v_j_118_, v___x_119_);
if (v___x_120_ == 0)
{
lean_dec(v_j_118_);
lean_dec(v_x_112_);
lean_dec(v_x_111_);
return v_x_108_;
}
else
{
lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_157_; 
lean_inc_ref(v_es_113_);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v_x_108_, 0);
lean_dec(v_unused_158_);
v___x_122_ = v_x_108_;
v_isShared_123_ = v_isSharedCheck_157_;
goto v_resetjp_121_;
}
else
{
lean_dec(v_x_108_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_157_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_v_124_; lean_object* v___x_125_; lean_object* v_xs_x27_126_; lean_object* v___y_128_; 
v_v_124_ = lean_array_fget(v_es_113_, v_j_118_);
v___x_125_ = lean_box(0);
v_xs_x27_126_ = lean_array_fset(v_es_113_, v_j_118_, v___x_125_);
switch(lean_obj_tag(v_v_124_))
{
case 0:
{
lean_object* v_key_133_; lean_object* v_val_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_144_; 
v_key_133_ = lean_ctor_get(v_v_124_, 0);
v_val_134_ = lean_ctor_get(v_v_124_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_v_124_);
if (v_isSharedCheck_144_ == 0)
{
v___x_136_ = v_v_124_;
v_isShared_137_ = v_isSharedCheck_144_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_val_134_);
lean_inc(v_key_133_);
lean_dec(v_v_124_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_144_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
uint8_t v___x_138_; 
v___x_138_ = l_Lean_instBEqMVarId_beq(v_x_111_, v_key_133_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; 
lean_del_object(v___x_136_);
v___x_139_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_133_, v_val_134_, v_x_111_, v_x_112_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
v___y_128_ = v___x_140_;
goto v___jp_127_;
}
else
{
lean_object* v___x_142_; 
lean_dec(v_val_134_);
lean_dec(v_key_133_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v_x_112_);
lean_ctor_set(v___x_136_, 0, v_x_111_);
v___x_142_ = v___x_136_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_x_111_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_x_112_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
v___y_128_ = v___x_142_;
goto v___jp_127_;
}
}
}
}
case 1:
{
lean_object* v_node_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_155_; 
v_node_145_ = lean_ctor_get(v_v_124_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v_v_124_);
if (v_isSharedCheck_155_ == 0)
{
v___x_147_ = v_v_124_;
v_isShared_148_ = v_isSharedCheck_155_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_node_145_);
lean_dec(v_v_124_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_155_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_149_ = lean_usize_shift_right(v_x_109_, v___x_114_);
v___x_150_ = lean_usize_add(v_x_110_, v___x_115_);
v___x_151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_node_145_, v___x_149_, v___x_150_, v_x_111_, v_x_112_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_151_);
v___x_153_ = v___x_147_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
v___y_128_ = v___x_153_;
goto v___jp_127_;
}
}
}
default: 
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v_x_111_);
lean_ctor_set(v___x_156_, 1, v_x_112_);
v___y_128_ = v___x_156_;
goto v___jp_127_;
}
}
v___jp_127_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = lean_array_fset(v_xs_x27_126_, v_j_118_, v___y_128_);
lean_dec(v_j_118_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_129_);
v___x_131_ = v___x_122_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
else
{
lean_object* v_ks_159_; lean_object* v_vs_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_180_; 
v_ks_159_ = lean_ctor_get(v_x_108_, 0);
v_vs_160_ = lean_ctor_get(v_x_108_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_180_ == 0)
{
v___x_162_ = v_x_108_;
v_isShared_163_ = v_isSharedCheck_180_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_vs_160_);
lean_inc(v_ks_159_);
lean_dec(v_x_108_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_180_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_ks_159_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_vs_160_);
v___x_165_ = v_reuseFailAlloc_179_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v_newNode_166_; uint8_t v___y_168_; size_t v___x_174_; uint8_t v___x_175_; 
v_newNode_166_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(v___x_165_, v_x_111_, v_x_112_);
v___x_174_ = ((size_t)7ULL);
v___x_175_ = lean_usize_dec_le(v___x_174_, v_x_110_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_166_);
v___x_177_ = lean_unsigned_to_nat(4u);
v___x_178_ = lean_nat_dec_lt(v___x_176_, v___x_177_);
lean_dec(v___x_176_);
v___y_168_ = v___x_178_;
goto v___jp_167_;
}
else
{
v___y_168_ = v___x_175_;
goto v___jp_167_;
}
v___jp_167_:
{
if (v___y_168_ == 0)
{
lean_object* v_ks_169_; lean_object* v_vs_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_ks_169_ = lean_ctor_get(v_newNode_166_, 0);
lean_inc_ref(v_ks_169_);
v_vs_170_ = lean_ctor_get(v_newNode_166_, 1);
lean_inc_ref(v_vs_170_);
lean_dec_ref(v_newNode_166_);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_173_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_x_110_, v_ks_169_, v_vs_170_, v___x_171_, v___x_172_);
lean_dec_ref(v_vs_170_);
lean_dec_ref(v_ks_169_);
return v___x_173_;
}
else
{
return v_newNode_166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_181_, lean_object* v_keys_182_, lean_object* v_vals_183_, lean_object* v_i_184_, lean_object* v_entries_185_){
_start:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_array_get_size(v_keys_182_);
v___x_187_ = lean_nat_dec_lt(v_i_184_, v___x_186_);
if (v___x_187_ == 0)
{
lean_dec(v_i_184_);
return v_entries_185_;
}
else
{
lean_object* v_k_188_; lean_object* v_v_189_; uint64_t v___x_190_; size_t v_h_191_; size_t v___x_192_; lean_object* v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v_h_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_k_188_ = lean_array_fget_borrowed(v_keys_182_, v_i_184_);
v_v_189_ = lean_array_fget_borrowed(v_vals_183_, v_i_184_);
v___x_190_ = l_Lean_instHashableMVarId_hash(v_k_188_);
v_h_191_ = lean_uint64_to_usize(v___x_190_);
v___x_192_ = ((size_t)5ULL);
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_sub(v_depth_181_, v___x_194_);
v___x_196_ = lean_usize_mul(v___x_192_, v___x_195_);
v_h_197_ = lean_usize_shift_right(v_h_191_, v___x_196_);
v___x_198_ = lean_nat_add(v_i_184_, v___x_193_);
lean_dec(v_i_184_);
lean_inc(v_v_189_);
lean_inc(v_k_188_);
v___x_199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_entries_185_, v_h_197_, v_depth_181_, v_k_188_, v_v_189_);
v_i_184_ = v___x_198_;
v_entries_185_ = v___x_199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_201_, lean_object* v_keys_202_, lean_object* v_vals_203_, lean_object* v_i_204_, lean_object* v_entries_205_){
_start:
{
size_t v_depth_boxed_206_; lean_object* v_res_207_; 
v_depth_boxed_206_ = lean_unbox_usize(v_depth_201_);
lean_dec(v_depth_201_);
v_res_207_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_206_, v_keys_202_, v_vals_203_, v_i_204_, v_entries_205_);
lean_dec_ref(v_vals_203_);
lean_dec_ref(v_keys_202_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_208_, lean_object* v_x_209_, lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
size_t v_x_3142__boxed_213_; size_t v_x_3143__boxed_214_; lean_object* v_res_215_; 
v_x_3142__boxed_213_ = lean_unbox_usize(v_x_209_);
lean_dec(v_x_209_);
v_x_3143__boxed_214_ = lean_unbox_usize(v_x_210_);
lean_dec(v_x_210_);
v_res_215_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_208_, v_x_3142__boxed_213_, v_x_3143__boxed_214_, v_x_211_, v_x_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(lean_object* v_x_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
uint64_t v___x_219_; size_t v___x_220_; size_t v___x_221_; lean_object* v___x_222_; 
v___x_219_ = l_Lean_instHashableMVarId_hash(v_x_217_);
v___x_220_ = lean_uint64_to_usize(v___x_219_);
v___x_221_ = ((size_t)1ULL);
v___x_222_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_216_, v___x_220_, v___x_221_, v_x_217_, v_x_218_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(lean_object* v_mvarId_223_, lean_object* v_val_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; lean_object* v_mctx_228_; lean_object* v_cache_229_; lean_object* v_zetaDeltaFVarIds_230_; lean_object* v_postponed_231_; lean_object* v_diag_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_259_; 
v___x_227_ = lean_st_ref_take(v___y_225_);
v_mctx_228_ = lean_ctor_get(v___x_227_, 0);
v_cache_229_ = lean_ctor_get(v___x_227_, 1);
v_zetaDeltaFVarIds_230_ = lean_ctor_get(v___x_227_, 2);
v_postponed_231_ = lean_ctor_get(v___x_227_, 3);
v_diag_232_ = lean_ctor_get(v___x_227_, 4);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_259_ == 0)
{
v___x_234_ = v___x_227_;
v_isShared_235_ = v_isSharedCheck_259_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_diag_232_);
lean_inc(v_postponed_231_);
lean_inc(v_zetaDeltaFVarIds_230_);
lean_inc(v_cache_229_);
lean_inc(v_mctx_228_);
lean_dec(v___x_227_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_259_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_depth_236_; lean_object* v_levelAssignDepth_237_; lean_object* v_mvarCounter_238_; lean_object* v_lDepth_239_; lean_object* v_decls_240_; lean_object* v_userNames_241_; lean_object* v_lAssignment_242_; lean_object* v_eAssignment_243_; lean_object* v_dAssignment_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_258_; 
v_depth_236_ = lean_ctor_get(v_mctx_228_, 0);
v_levelAssignDepth_237_ = lean_ctor_get(v_mctx_228_, 1);
v_mvarCounter_238_ = lean_ctor_get(v_mctx_228_, 2);
v_lDepth_239_ = lean_ctor_get(v_mctx_228_, 3);
v_decls_240_ = lean_ctor_get(v_mctx_228_, 4);
v_userNames_241_ = lean_ctor_get(v_mctx_228_, 5);
v_lAssignment_242_ = lean_ctor_get(v_mctx_228_, 6);
v_eAssignment_243_ = lean_ctor_get(v_mctx_228_, 7);
v_dAssignment_244_ = lean_ctor_get(v_mctx_228_, 8);
v_isSharedCheck_258_ = !lean_is_exclusive(v_mctx_228_);
if (v_isSharedCheck_258_ == 0)
{
v___x_246_ = v_mctx_228_;
v_isShared_247_ = v_isSharedCheck_258_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_dAssignment_244_);
lean_inc(v_eAssignment_243_);
lean_inc(v_lAssignment_242_);
lean_inc(v_userNames_241_);
lean_inc(v_decls_240_);
lean_inc(v_lDepth_239_);
lean_inc(v_mvarCounter_238_);
lean_inc(v_levelAssignDepth_237_);
lean_inc(v_depth_236_);
lean_dec(v_mctx_228_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_258_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(v_eAssignment_243_, v_mvarId_223_, v_val_224_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 7, v___x_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_depth_236_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_levelAssignDepth_237_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_mvarCounter_238_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v_lDepth_239_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v_decls_240_);
lean_ctor_set(v_reuseFailAlloc_257_, 5, v_userNames_241_);
lean_ctor_set(v_reuseFailAlloc_257_, 6, v_lAssignment_242_);
lean_ctor_set(v_reuseFailAlloc_257_, 7, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_257_, 8, v_dAssignment_244_);
v___x_250_ = v_reuseFailAlloc_257_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_250_);
v___x_252_ = v___x_234_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_cache_229_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_zetaDeltaFVarIds_230_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_postponed_231_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_diag_232_);
v___x_252_ = v_reuseFailAlloc_256_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_st_ref_set(v___y_225_, v___x_252_);
v___x_254_ = lean_box(0);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg___boxed(lean_object* v_mvarId_260_, lean_object* v_val_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_260_, v_val_261_, v___y_262_);
lean_dec(v___y_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(lean_object* v_upperBound_265_, lean_object* v___x_266_, lean_object* v_a_267_, lean_object* v_b_268_){
_start:
{
lean_object* v_a_271_; uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_lt(v_a_267_, v_upperBound_265_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec(v_a_267_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_b_268_);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = lean_nat_sub(v___x_266_, v_a_267_);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_sub(v___x_277_, v___x_278_);
lean_dec(v___x_277_);
lean_inc_ref(v_b_268_);
v___x_280_ = l_Lean_LocalContext_getAt_x3f(v_b_268_, v___x_279_);
lean_dec(v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
v_a_271_ = v_b_268_;
goto v___jp_270_;
}
else
{
lean_object* v_val_281_; uint8_t v___x_282_; 
v_val_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_281_);
lean_dec_ref(v___x_280_);
v___x_282_ = l_Lean_LocalDecl_isImplementationDetail(v_val_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = l_Lean_LocalDecl_userName(v_val_281_);
v___x_284_ = l_Lean_Name_hasMacroScopes(v___x_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_Meta_Grind_markGrindName(v___x_283_);
v___x_286_ = l_Lean_LocalDecl_fvarId(v_val_281_);
lean_dec(v_val_281_);
v___x_287_ = l_Lean_LocalContext_setUserName(v_b_268_, v___x_286_, v___x_285_);
v_a_271_ = v___x_287_;
goto v___jp_270_;
}
else
{
lean_dec(v___x_283_);
lean_dec(v_val_281_);
v_a_271_ = v_b_268_;
goto v___jp_270_;
}
}
else
{
lean_dec(v_val_281_);
v_a_271_ = v_b_268_;
goto v___jp_270_;
}
}
}
v___jp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_a_267_, v___x_272_);
lean_dec(v_a_267_);
v_a_267_ = v___x_273_;
v_b_268_ = v_a_271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg___boxed(lean_object* v_upperBound_288_, lean_object* v___x_289_, lean_object* v_a_290_, lean_object* v_b_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v_upperBound_288_, v___x_289_, v_a_290_, v_b_291_);
lean_dec(v___x_289_);
lean_dec(v_upperBound_288_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___lam__0(lean_object* v_mvarId_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; 
lean_inc(v_mvarId_294_);
v___x_300_ = l_Lean_MVarId_getDecl(v_mvarId_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v_userName_302_; lean_object* v_lctx_303_; lean_object* v_type_304_; lean_object* v_localInstances_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref(v___x_300_);
v_userName_302_ = lean_ctor_get(v_a_301_, 0);
lean_inc(v_userName_302_);
v_lctx_303_ = lean_ctor_get(v_a_301_, 1);
lean_inc_ref(v_lctx_303_);
v_type_304_ = lean_ctor_get(v_a_301_, 2);
lean_inc_ref(v_type_304_);
v_localInstances_305_ = lean_ctor_get(v_a_301_, 4);
lean_inc_ref(v_localInstances_305_);
lean_dec(v_a_301_);
lean_inc_ref(v_lctx_303_);
v___x_306_ = lean_local_ctx_num_indices(v_lctx_303_);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v___x_306_, v___x_306_, v___x_307_, v_lctx_303_);
lean_dec(v___x_306_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; uint8_t v___x_310_; lean_object* v___x_311_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v___x_308_);
v___x_310_ = 2;
v___x_311_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_309_, v_localInstances_305_, v_type_304_, v___x_310_, v_userName_302_, v___x_307_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref(v___x_311_);
lean_inc(v_a_312_);
v___x_313_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_294_, v_a_312_, v___y_296_);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v___x_313_, 0);
lean_dec(v_unused_322_);
v___x_315_ = v___x_313_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_dec(v___x_313_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = l_Lean_Expr_mvarId_x21(v_a_312_);
lean_dec(v_a_312_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_317_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec(v_mvarId_294_);
v_a_323_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_311_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_311_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v_localInstances_305_);
lean_dec_ref(v_type_304_);
lean_dec(v_userName_302_);
lean_dec(v_mvarId_294_);
v_a_331_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_308_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_308_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_mvarId_294_);
v_a_339_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_300_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_300_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___lam__0___boxed(lean_object* v_mvarId_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_MVarId_markAccessible___lam__0(v_mvarId_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible(lean_object* v_mvarId_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___f_360_; lean_object* v___x_361_; 
lean_inc(v_mvarId_354_);
v___f_360_ = lean_alloc_closure((void*)(l_Lean_MVarId_markAccessible___lam__0___boxed), 6, 1);
lean_closure_set(v___f_360_, 0, v_mvarId_354_);
v___x_361_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_354_, v___f_360_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___boxed(lean_object* v_mvarId_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_MVarId_markAccessible(v_mvarId_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(lean_object* v_mvarId_369_, lean_object* v_val_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_369_, v_val_370_, v___y_372_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___boxed(lean_object* v_mvarId_377_, lean_object* v_val_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(v_mvarId_377_, v_val_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(lean_object* v_upperBound_385_, lean_object* v___x_386_, lean_object* v_inst_387_, lean_object* v_R_388_, lean_object* v_a_389_, lean_object* v_b_390_, lean_object* v_c_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v_upperBound_385_, v___x_386_, v_a_389_, v_b_390_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___boxed(lean_object* v_upperBound_398_, lean_object* v___x_399_, lean_object* v_inst_400_, lean_object* v_R_401_, lean_object* v_a_402_, lean_object* v_b_403_, lean_object* v_c_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(v_upperBound_398_, v___x_399_, v_inst_400_, v_R_401_, v_a_402_, v_b_403_, v_c_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___x_399_);
lean_dec(v_upperBound_398_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0(lean_object* v_00_u03b2_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(v_x_412_, v_x_413_, v_x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_416_, lean_object* v_x_417_, size_t v_x_418_, size_t v_x_419_, lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_417_, v_x_418_, v_x_419_, v_x_420_, v_x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_423_, lean_object* v_x_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
size_t v_x_3580__boxed_429_; size_t v_x_3581__boxed_430_; lean_object* v_res_431_; 
v_x_3580__boxed_429_ = lean_unbox_usize(v_x_425_);
lean_dec(v_x_425_);
v_x_3581__boxed_430_ = lean_unbox_usize(v_x_426_);
lean_dec(v_x_426_);
v_res_431_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(v_00_u03b2_423_, v_x_424_, v_x_3580__boxed_429_, v_x_3581__boxed_430_, v_x_427_, v_x_428_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_432_, lean_object* v_n_433_, lean_object* v_k_434_, lean_object* v_v_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(v_n_433_, v_k_434_, v_v_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_437_, size_t v_depth_438_, lean_object* v_keys_439_, lean_object* v_vals_440_, lean_object* v_heq_441_, lean_object* v_i_442_, lean_object* v_entries_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_438_, v_keys_439_, v_vals_440_, v_i_442_, v_entries_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_445_, lean_object* v_depth_446_, lean_object* v_keys_447_, lean_object* v_vals_448_, lean_object* v_heq_449_, lean_object* v_i_450_, lean_object* v_entries_451_){
_start:
{
size_t v_depth_boxed_452_; lean_object* v_res_453_; 
v_depth_boxed_452_ = lean_unbox_usize(v_depth_446_);
lean_dec(v_depth_446_);
v_res_453_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_445_, v_depth_boxed_452_, v_keys_447_, v_vals_448_, v_heq_449_, v_i_450_, v_entries_451_);
lean_dec_ref(v_vals_448_);
lean_dec_ref(v_keys_447_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_454_, lean_object* v_x_455_, lean_object* v_x_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_455_, v_x_456_, v_x_457_, v_x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(lean_object* v_as_460_, size_t v_sz_461_, size_t v_i_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = lean_usize_dec_lt(v_i_462_, v_sz_461_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
lean_dec_ref(v___y_464_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v_b_463_);
return v___x_469_;
}
else
{
lean_object* v_a_470_; lean_object* v___x_471_; 
v_a_470_ = lean_array_uget_borrowed(v_as_460_, v_i_462_);
lean_inc_ref(v___y_464_);
lean_inc(v_a_470_);
v___x_471_ = l_Lean_FVarId_getDecl___redArg(v_a_470_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v_a_474_; uint8_t v___x_478_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v___x_471_);
v___x_478_ = l_Lean_LocalDecl_isAuxDecl(v_a_472_);
lean_dec(v_a_472_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_inc(v_a_470_);
v___x_479_ = lean_array_push(v_b_463_, v_a_470_);
v_a_474_ = v___x_479_;
goto v___jp_473_;
}
else
{
v_a_474_ = v_b_463_;
goto v___jp_473_;
}
v___jp_473_:
{
size_t v___x_475_; size_t v___x_476_; 
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_add(v_i_462_, v___x_475_);
v_i_462_ = v___x_476_;
v_b_463_ = v_a_474_;
goto _start;
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v___y_464_);
lean_dec_ref(v_b_463_);
v_a_480_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_471_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_471_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg___boxed(lean_object* v_as_488_, lean_object* v_sz_489_, lean_object* v_i_490_, lean_object* v_b_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
size_t v_sz_boxed_496_; size_t v_i_boxed_497_; lean_object* v_res_498_; 
v_sz_boxed_496_ = lean_unbox_usize(v_sz_489_);
lean_dec(v_sz_489_);
v_i_boxed_497_ = lean_unbox_usize(v_i_490_);
lean_dec(v_i_490_);
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_488_, v_sz_boxed_496_, v_i_boxed_497_, v_b_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec_ref(v_as_488_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lam__0(lean_object* v_mvarId_501_, lean_object* v___x_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; 
lean_inc(v_mvarId_501_);
v___x_508_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_501_, v___x_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_lctx_509_; lean_object* v___x_510_; lean_object* v___x_511_; size_t v_sz_512_; size_t v___x_513_; lean_object* v___x_514_; 
lean_dec_ref(v___x_508_);
v_lctx_509_ = lean_ctor_get(v___y_503_, 2);
v___x_510_ = ((lean_object*)(l_Lean_MVarId_revertAll___lam__0___closed__0));
v___x_511_ = l_Lean_LocalContext_getFVarIds(v_lctx_509_);
v_sz_512_ = lean_array_size(v___x_511_);
v___x_513_ = ((size_t)0ULL);
lean_inc_ref(v___y_503_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v___x_511_, v_sz_512_, v___x_513_, v___x_510_, v___y_503_, v___y_505_, v___y_506_);
lean_dec_ref(v___x_511_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; uint8_t v___x_516_; lean_object* v___x_517_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref(v___x_514_);
v___x_516_ = 0;
lean_inc(v_mvarId_501_);
v___x_517_ = l_Lean_MVarId_setKind___redArg(v_mvarId_501_, v___x_516_, v___y_504_);
if (lean_obj_tag(v___x_517_) == 0)
{
uint8_t v___x_518_; lean_object* v___x_519_; 
lean_dec_ref(v___x_517_);
v___x_518_ = 1;
v___x_519_ = l_Lean_MVarId_revert(v_mvarId_501_, v_a_515_, v___x_518_, v___x_518_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_528_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_528_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_snd_524_; lean_object* v___x_526_; 
v_snd_524_ = lean_ctor_get(v_a_520_, 1);
lean_inc(v_snd_524_);
lean_dec(v_a_520_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v_snd_524_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_snd_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
v_a_529_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_519_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_519_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_a_515_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v_mvarId_501_);
v_a_537_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_517_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_517_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v_mvarId_501_);
v_a_545_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_514_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_514_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v_mvarId_501_);
v_a_553_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_508_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_508_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lam__0___boxed(lean_object* v_mvarId_561_, lean_object* v___x_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_MVarId_revertAll___lam__0(v_mvarId_561_, v___x_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll(lean_object* v_mvarId_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___x_580_; 
v___x_578_ = ((lean_object*)(l_Lean_MVarId_revertAll___closed__1));
lean_inc(v_mvarId_572_);
v___f_579_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertAll___lam__0___boxed), 7, 2);
lean_closure_set(v___f_579_, 0, v_mvarId_572_);
lean_closure_set(v___f_579_, 1, v___x_578_);
v___x_580_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_572_, v___f_579_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___boxed(lean_object* v_mvarId_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_MVarId_revertAll(v_mvarId_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(lean_object* v_as_588_, size_t v_sz_589_, size_t v_i_590_, lean_object* v_b_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_588_, v_sz_589_, v_i_590_, v_b_591_, v___y_592_, v___y_594_, v___y_595_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___boxed(lean_object* v_as_598_, lean_object* v_sz_599_, lean_object* v_i_600_, lean_object* v_b_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
size_t v_sz_boxed_607_; size_t v_i_boxed_608_; lean_object* v_res_609_; 
v_sz_boxed_607_ = lean_unbox_usize(v_sz_599_);
lean_dec(v_sz_599_);
v_i_boxed_608_ = lean_unbox_usize(v_i_600_);
lean_dec(v_i_600_);
v_res_609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(v_as_598_, v_sz_boxed_607_, v_i_boxed_608_, v_b_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v_as_598_);
return v_res_609_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
}
#ifdef __cplusplus
}
#endif
