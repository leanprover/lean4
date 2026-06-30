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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
size_t lean_usize_sub(size_t, size_t);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0;
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
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
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
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(lean_object* v_x_102_, size_t v_x_103_, size_t v_x_104_, lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_object* v_es_107_; size_t v___x_108_; size_t v___x_109_; lean_object* v_j_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_es_107_ = lean_ctor_get(v_x_102_, 0);
v___x_108_ = ((size_t)31ULL);
v___x_109_ = lean_usize_land(v_x_103_, v___x_108_);
v_j_110_ = lean_usize_to_nat(v___x_109_);
v___x_111_ = lean_array_get_size(v_es_107_);
v___x_112_ = lean_nat_dec_lt(v_j_110_, v___x_111_);
if (v___x_112_ == 0)
{
lean_dec(v_j_110_);
lean_dec(v_x_106_);
lean_dec(v_x_105_);
return v_x_102_;
}
else
{
lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_151_; 
lean_inc_ref(v_es_107_);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_102_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v_x_102_, 0);
lean_dec(v_unused_152_);
v___x_114_ = v_x_102_;
v_isShared_115_ = v_isSharedCheck_151_;
goto v_resetjp_113_;
}
else
{
lean_dec(v_x_102_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_151_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v_v_116_; lean_object* v___x_117_; lean_object* v_xs_x27_118_; lean_object* v___y_120_; 
v_v_116_ = lean_array_fget(v_es_107_, v_j_110_);
v___x_117_ = lean_box(0);
v_xs_x27_118_ = lean_array_fset(v_es_107_, v_j_110_, v___x_117_);
switch(lean_obj_tag(v_v_116_))
{
case 0:
{
lean_object* v_key_125_; lean_object* v_val_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_136_; 
v_key_125_ = lean_ctor_get(v_v_116_, 0);
v_val_126_ = lean_ctor_get(v_v_116_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_v_116_);
if (v_isSharedCheck_136_ == 0)
{
v___x_128_ = v_v_116_;
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_val_126_);
lean_inc(v_key_125_);
lean_dec(v_v_116_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
uint8_t v___x_130_; 
v___x_130_ = l_Lean_instBEqMVarId_beq(v_x_105_, v_key_125_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_del_object(v___x_128_);
v___x_131_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_125_, v_val_126_, v_x_105_, v_x_106_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
v___y_120_ = v___x_132_;
goto v___jp_119_;
}
else
{
lean_object* v___x_134_; 
lean_dec(v_val_126_);
lean_dec(v_key_125_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_x_106_);
lean_ctor_set(v___x_128_, 0, v_x_105_);
v___x_134_ = v___x_128_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_x_105_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_x_106_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
v___y_120_ = v___x_134_;
goto v___jp_119_;
}
}
}
}
case 1:
{
lean_object* v_node_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_149_; 
v_node_137_ = lean_ctor_get(v_v_116_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_v_116_);
if (v_isSharedCheck_149_ == 0)
{
v___x_139_ = v_v_116_;
v_isShared_140_ = v_isSharedCheck_149_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_node_137_);
lean_dec(v_v_116_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_149_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_141_ = ((size_t)5ULL);
v___x_142_ = lean_usize_shift_right(v_x_103_, v___x_141_);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_add(v_x_104_, v___x_143_);
v___x_145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_node_137_, v___x_142_, v___x_144_, v_x_105_, v_x_106_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_145_);
v___x_147_ = v___x_139_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
v___y_120_ = v___x_147_;
goto v___jp_119_;
}
}
}
default: 
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v_x_105_);
lean_ctor_set(v___x_150_, 1, v_x_106_);
v___y_120_ = v___x_150_;
goto v___jp_119_;
}
}
v___jp_119_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = lean_array_fset(v_xs_x27_118_, v_j_110_, v___y_120_);
lean_dec(v_j_110_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_121_);
v___x_123_ = v___x_114_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
else
{
lean_object* v_ks_153_; lean_object* v_vs_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_174_; 
v_ks_153_ = lean_ctor_get(v_x_102_, 0);
v_vs_154_ = lean_ctor_get(v_x_102_, 1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_x_102_);
if (v_isSharedCheck_174_ == 0)
{
v___x_156_ = v_x_102_;
v_isShared_157_ = v_isSharedCheck_174_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_vs_154_);
lean_inc(v_ks_153_);
lean_dec(v_x_102_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_174_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_ks_153_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_vs_154_);
v___x_159_ = v_reuseFailAlloc_173_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v_newNode_160_; uint8_t v___y_162_; size_t v___x_168_; uint8_t v___x_169_; 
v_newNode_160_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(v___x_159_, v_x_105_, v_x_106_);
v___x_168_ = ((size_t)7ULL);
v___x_169_ = lean_usize_dec_le(v___x_168_, v_x_104_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_170_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_160_);
v___x_171_ = lean_unsigned_to_nat(4u);
v___x_172_ = lean_nat_dec_lt(v___x_170_, v___x_171_);
lean_dec(v___x_170_);
v___y_162_ = v___x_172_;
goto v___jp_161_;
}
else
{
v___y_162_ = v___x_169_;
goto v___jp_161_;
}
v___jp_161_:
{
if (v___y_162_ == 0)
{
lean_object* v_ks_163_; lean_object* v_vs_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_ks_163_ = lean_ctor_get(v_newNode_160_, 0);
lean_inc_ref(v_ks_163_);
v_vs_164_ = lean_ctor_get(v_newNode_160_, 1);
lean_inc_ref(v_vs_164_);
lean_dec_ref(v_newNode_160_);
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_167_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_x_104_, v_ks_163_, v_vs_164_, v___x_165_, v___x_166_);
lean_dec_ref(v_vs_164_);
lean_dec_ref(v_ks_163_);
return v___x_167_;
}
else
{
return v_newNode_160_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_175_, lean_object* v_keys_176_, lean_object* v_vals_177_, lean_object* v_i_178_, lean_object* v_entries_179_){
_start:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_array_get_size(v_keys_176_);
v___x_181_ = lean_nat_dec_lt(v_i_178_, v___x_180_);
if (v___x_181_ == 0)
{
lean_dec(v_i_178_);
return v_entries_179_;
}
else
{
lean_object* v_k_182_; lean_object* v_v_183_; uint64_t v___x_184_; size_t v_h_185_; size_t v___x_186_; lean_object* v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v_h_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_k_182_ = lean_array_fget_borrowed(v_keys_176_, v_i_178_);
v_v_183_ = lean_array_fget_borrowed(v_vals_177_, v_i_178_);
v___x_184_ = l_Lean_instHashableMVarId_hash(v_k_182_);
v_h_185_ = lean_uint64_to_usize(v___x_184_);
v___x_186_ = ((size_t)5ULL);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_sub(v_depth_175_, v___x_188_);
v___x_190_ = lean_usize_mul(v___x_186_, v___x_189_);
v_h_191_ = lean_usize_shift_right(v_h_185_, v___x_190_);
v___x_192_ = lean_nat_add(v_i_178_, v___x_187_);
lean_dec(v_i_178_);
lean_inc(v_v_183_);
lean_inc(v_k_182_);
v___x_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_entries_179_, v_h_191_, v_depth_175_, v_k_182_, v_v_183_);
v_i_178_ = v___x_192_;
v_entries_179_ = v___x_193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_195_, lean_object* v_keys_196_, lean_object* v_vals_197_, lean_object* v_i_198_, lean_object* v_entries_199_){
_start:
{
size_t v_depth_boxed_200_; lean_object* v_res_201_; 
v_depth_boxed_200_ = lean_unbox_usize(v_depth_195_);
lean_dec(v_depth_195_);
v_res_201_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_200_, v_keys_196_, v_vals_197_, v_i_198_, v_entries_199_);
lean_dec_ref(v_vals_197_);
lean_dec_ref(v_keys_196_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
size_t v_x_2942__boxed_207_; size_t v_x_2943__boxed_208_; lean_object* v_res_209_; 
v_x_2942__boxed_207_ = lean_unbox_usize(v_x_203_);
lean_dec(v_x_203_);
v_x_2943__boxed_208_ = lean_unbox_usize(v_x_204_);
lean_dec(v_x_204_);
v_res_209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_202_, v_x_2942__boxed_207_, v_x_2943__boxed_208_, v_x_205_, v_x_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
uint64_t v___x_213_; size_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_213_ = l_Lean_instHashableMVarId_hash(v_x_211_);
v___x_214_ = lean_uint64_to_usize(v___x_213_);
v___x_215_ = ((size_t)1ULL);
v___x_216_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_210_, v___x_214_, v___x_215_, v_x_211_, v_x_212_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(lean_object* v_mvarId_217_, lean_object* v_val_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; lean_object* v_mctx_222_; lean_object* v_cache_223_; lean_object* v_zetaDeltaFVarIds_224_; lean_object* v_postponed_225_; lean_object* v_diag_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_254_; 
v___x_221_ = lean_st_ref_take(v___y_219_);
v_mctx_222_ = lean_ctor_get(v___x_221_, 0);
v_cache_223_ = lean_ctor_get(v___x_221_, 1);
v_zetaDeltaFVarIds_224_ = lean_ctor_get(v___x_221_, 2);
v_postponed_225_ = lean_ctor_get(v___x_221_, 3);
v_diag_226_ = lean_ctor_get(v___x_221_, 4);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_254_ == 0)
{
v___x_228_ = v___x_221_;
v_isShared_229_ = v_isSharedCheck_254_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_diag_226_);
lean_inc(v_postponed_225_);
lean_inc(v_zetaDeltaFVarIds_224_);
lean_inc(v_cache_223_);
lean_inc(v_mctx_222_);
lean_dec(v___x_221_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_254_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_depth_230_; lean_object* v_levelAssignDepth_231_; lean_object* v_lmvarCounter_232_; lean_object* v_mvarCounter_233_; lean_object* v_lDecls_234_; lean_object* v_decls_235_; lean_object* v_userNames_236_; lean_object* v_lAssignment_237_; lean_object* v_eAssignment_238_; lean_object* v_dAssignment_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_253_; 
v_depth_230_ = lean_ctor_get(v_mctx_222_, 0);
v_levelAssignDepth_231_ = lean_ctor_get(v_mctx_222_, 1);
v_lmvarCounter_232_ = lean_ctor_get(v_mctx_222_, 2);
v_mvarCounter_233_ = lean_ctor_get(v_mctx_222_, 3);
v_lDecls_234_ = lean_ctor_get(v_mctx_222_, 4);
v_decls_235_ = lean_ctor_get(v_mctx_222_, 5);
v_userNames_236_ = lean_ctor_get(v_mctx_222_, 6);
v_lAssignment_237_ = lean_ctor_get(v_mctx_222_, 7);
v_eAssignment_238_ = lean_ctor_get(v_mctx_222_, 8);
v_dAssignment_239_ = lean_ctor_get(v_mctx_222_, 9);
v_isSharedCheck_253_ = !lean_is_exclusive(v_mctx_222_);
if (v_isSharedCheck_253_ == 0)
{
v___x_241_ = v_mctx_222_;
v_isShared_242_ = v_isSharedCheck_253_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_dAssignment_239_);
lean_inc(v_eAssignment_238_);
lean_inc(v_lAssignment_237_);
lean_inc(v_userNames_236_);
lean_inc(v_decls_235_);
lean_inc(v_lDecls_234_);
lean_inc(v_mvarCounter_233_);
lean_inc(v_lmvarCounter_232_);
lean_inc(v_levelAssignDepth_231_);
lean_inc(v_depth_230_);
lean_dec(v_mctx_222_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_253_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(v_eAssignment_238_, v_mvarId_217_, v_val_218_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 8, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_depth_230_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_levelAssignDepth_231_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_lmvarCounter_232_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v_mvarCounter_233_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_lDecls_234_);
lean_ctor_set(v_reuseFailAlloc_252_, 5, v_decls_235_);
lean_ctor_set(v_reuseFailAlloc_252_, 6, v_userNames_236_);
lean_ctor_set(v_reuseFailAlloc_252_, 7, v_lAssignment_237_);
lean_ctor_set(v_reuseFailAlloc_252_, 8, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_252_, 9, v_dAssignment_239_);
v___x_245_ = v_reuseFailAlloc_252_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; 
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_245_);
v___x_247_ = v___x_228_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_cache_223_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_zetaDeltaFVarIds_224_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v_postponed_225_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v_diag_226_);
v___x_247_ = v_reuseFailAlloc_251_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_st_ref_set(v___y_219_, v___x_247_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg___boxed(lean_object* v_mvarId_255_, lean_object* v_val_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_255_, v_val_256_, v___y_257_);
lean_dec(v___y_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(lean_object* v_upperBound_260_, lean_object* v___x_261_, lean_object* v_a_262_, lean_object* v_b_263_){
_start:
{
lean_object* v_a_266_; uint8_t v___x_270_; 
v___x_270_ = lean_nat_dec_lt(v_a_262_, v_upperBound_260_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
lean_dec(v_a_262_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v_b_263_);
return v___x_271_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = lean_nat_sub(v___x_261_, v_a_262_);
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_sub(v___x_272_, v___x_273_);
lean_dec(v___x_272_);
v___x_275_ = l_Lean_LocalContext_getAt_x3f(v_b_263_, v___x_274_);
lean_dec(v___x_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
v_a_266_ = v_b_263_;
goto v___jp_265_;
}
else
{
lean_object* v_val_276_; uint8_t v___x_277_; 
v_val_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_val_276_);
lean_dec_ref_known(v___x_275_, 1);
v___x_277_ = l_Lean_LocalDecl_isImplementationDetail(v_val_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = l_Lean_LocalDecl_userName(v_val_276_);
v___x_279_ = l_Lean_Name_hasMacroScopes(v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = l_Lean_Meta_Grind_markGrindName(v___x_278_);
v___x_281_ = l_Lean_LocalDecl_fvarId(v_val_276_);
lean_dec(v_val_276_);
v___x_282_ = l_Lean_LocalContext_setUserName(v_b_263_, v___x_281_, v___x_280_);
v_a_266_ = v___x_282_;
goto v___jp_265_;
}
else
{
lean_dec(v___x_278_);
lean_dec(v_val_276_);
v_a_266_ = v_b_263_;
goto v___jp_265_;
}
}
else
{
lean_dec(v_val_276_);
v_a_266_ = v_b_263_;
goto v___jp_265_;
}
}
}
v___jp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_add(v_a_262_, v___x_267_);
lean_dec(v_a_262_);
v_a_262_ = v___x_268_;
v_b_263_ = v_a_266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg___boxed(lean_object* v_upperBound_283_, lean_object* v___x_284_, lean_object* v_a_285_, lean_object* v_b_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v_upperBound_283_, v___x_284_, v_a_285_, v_b_286_);
lean_dec(v___x_284_);
lean_dec(v_upperBound_283_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___lam__0(lean_object* v_mvarId_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
lean_inc(v_mvarId_289_);
v___x_295_ = l_Lean_MVarId_getDecl(v_mvarId_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v_userName_297_; lean_object* v_lctx_298_; lean_object* v_type_299_; lean_object* v_localInstances_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_295_, 1);
v_userName_297_ = lean_ctor_get(v_a_296_, 0);
lean_inc(v_userName_297_);
v_lctx_298_ = lean_ctor_get(v_a_296_, 1);
lean_inc_ref_n(v_lctx_298_, 2);
v_type_299_ = lean_ctor_get(v_a_296_, 2);
lean_inc_ref(v_type_299_);
v_localInstances_300_ = lean_ctor_get(v_a_296_, 4);
lean_inc_ref(v_localInstances_300_);
lean_dec(v_a_296_);
v___x_301_ = lean_local_ctx_num_indices(v_lctx_298_);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v___x_301_, v___x_301_, v___x_302_, v_lctx_298_);
lean_dec(v___x_301_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; uint8_t v___x_305_; lean_object* v___x_306_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_303_, 1);
v___x_305_ = 2;
v___x_306_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_304_, v_localInstances_300_, v_type_299_, v___x_305_, v_userName_297_, v___x_302_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_316_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_n(v_a_307_, 2);
lean_dec_ref_known(v___x_306_, 1);
v___x_308_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_289_, v_a_307_, v___y_291_);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; 
v_unused_317_ = lean_ctor_get(v___x_308_, 0);
lean_dec(v_unused_317_);
v___x_310_ = v___x_308_;
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
else
{
lean_dec(v___x_308_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_316_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = l_Lean_Expr_mvarId_x21(v_a_307_);
lean_dec(v_a_307_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_312_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec(v_mvarId_289_);
v_a_318_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_306_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_306_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v_localInstances_300_);
lean_dec_ref(v_type_299_);
lean_dec(v_userName_297_);
lean_dec(v_mvarId_289_);
v_a_326_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_303_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_303_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec(v_mvarId_289_);
v_a_334_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_295_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_295_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___lam__0___boxed(lean_object* v_mvarId_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_MVarId_markAccessible___lam__0(v_mvarId_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible(lean_object* v_mvarId_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___f_355_; lean_object* v___x_356_; 
lean_inc(v_mvarId_349_);
v___f_355_ = lean_alloc_closure((void*)(l_Lean_MVarId_markAccessible___lam__0___boxed), 6, 1);
lean_closure_set(v___f_355_, 0, v_mvarId_349_);
v___x_356_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_349_, v___f_355_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_markAccessible___boxed(lean_object* v_mvarId_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_MVarId_markAccessible(v_mvarId_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(lean_object* v_mvarId_364_, lean_object* v_val_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_364_, v_val_365_, v___y_367_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___boxed(lean_object* v_mvarId_372_, lean_object* v_val_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(v_mvarId_372_, v_val_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(lean_object* v_upperBound_380_, lean_object* v___x_381_, lean_object* v_inst_382_, lean_object* v_R_383_, lean_object* v_a_384_, lean_object* v_b_385_, lean_object* v_c_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v_upperBound_380_, v___x_381_, v_a_384_, v_b_385_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___boxed(lean_object* v_upperBound_393_, lean_object* v___x_394_, lean_object* v_inst_395_, lean_object* v_R_396_, lean_object* v_a_397_, lean_object* v_b_398_, lean_object* v_c_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(v_upperBound_393_, v___x_394_, v_inst_395_, v_R_396_, v_a_397_, v_b_398_, v_c_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___x_394_);
lean_dec(v_upperBound_393_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0(lean_object* v_00_u03b2_406_, lean_object* v_x_407_, lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(v_x_407_, v_x_408_, v_x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_411_, lean_object* v_x_412_, size_t v_x_413_, size_t v_x_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_412_, v_x_413_, v_x_414_, v_x_415_, v_x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_418_, lean_object* v_x_419_, lean_object* v_x_420_, lean_object* v_x_421_, lean_object* v_x_422_, lean_object* v_x_423_){
_start:
{
size_t v_x_3362__boxed_424_; size_t v_x_3363__boxed_425_; lean_object* v_res_426_; 
v_x_3362__boxed_424_ = lean_unbox_usize(v_x_420_);
lean_dec(v_x_420_);
v_x_3363__boxed_425_ = lean_unbox_usize(v_x_421_);
lean_dec(v_x_421_);
v_res_426_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(v_00_u03b2_418_, v_x_419_, v_x_3362__boxed_424_, v_x_3363__boxed_425_, v_x_422_, v_x_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_427_, lean_object* v_n_428_, lean_object* v_k_429_, lean_object* v_v_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(v_n_428_, v_k_429_, v_v_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_432_, size_t v_depth_433_, lean_object* v_keys_434_, lean_object* v_vals_435_, lean_object* v_heq_436_, lean_object* v_i_437_, lean_object* v_entries_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_433_, v_keys_434_, v_vals_435_, v_i_437_, v_entries_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_440_, lean_object* v_depth_441_, lean_object* v_keys_442_, lean_object* v_vals_443_, lean_object* v_heq_444_, lean_object* v_i_445_, lean_object* v_entries_446_){
_start:
{
size_t v_depth_boxed_447_; lean_object* v_res_448_; 
v_depth_boxed_447_ = lean_unbox_usize(v_depth_441_);
lean_dec(v_depth_441_);
v_res_448_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_440_, v_depth_boxed_447_, v_keys_442_, v_vals_443_, v_heq_444_, v_i_445_, v_entries_446_);
lean_dec_ref(v_vals_443_);
lean_dec_ref(v_keys_442_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_449_, lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_450_, v_x_451_, v_x_452_, v_x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(lean_object* v_as_455_, size_t v_sz_456_, size_t v_i_457_, lean_object* v_b_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v___x_463_; 
v___x_463_ = lean_usize_dec_lt(v_i_457_, v_sz_456_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_b_458_);
return v___x_464_;
}
else
{
lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_465_ = lean_array_uget_borrowed(v_as_455_, v_i_457_);
lean_inc(v_a_465_);
v___x_466_ = l_Lean_FVarId_getDecl___redArg(v_a_465_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v_a_469_; uint8_t v___x_473_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
v___x_473_ = l_Lean_LocalDecl_isAuxDecl(v_a_467_);
lean_dec(v_a_467_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_inc(v_a_465_);
v___x_474_ = lean_array_push(v_b_458_, v_a_465_);
v_a_469_ = v___x_474_;
goto v___jp_468_;
}
else
{
v_a_469_ = v_b_458_;
goto v___jp_468_;
}
v___jp_468_:
{
size_t v___x_470_; size_t v___x_471_; 
v___x_470_ = ((size_t)1ULL);
v___x_471_ = lean_usize_add(v_i_457_, v___x_470_);
v_i_457_ = v___x_471_;
v_b_458_ = v_a_469_;
goto _start;
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v_b_458_);
v_a_475_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_466_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_466_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg___boxed(lean_object* v_as_483_, lean_object* v_sz_484_, lean_object* v_i_485_, lean_object* v_b_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
size_t v_sz_boxed_491_; size_t v_i_boxed_492_; lean_object* v_res_493_; 
v_sz_boxed_491_ = lean_unbox_usize(v_sz_484_);
lean_dec(v_sz_484_);
v_i_boxed_492_ = lean_unbox_usize(v_i_485_);
lean_dec(v_i_485_);
v_res_493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_483_, v_sz_boxed_491_, v_i_boxed_492_, v_b_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec_ref(v_as_483_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lam__0(lean_object* v_mvarId_496_, lean_object* v___x_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
lean_inc(v_mvarId_496_);
v___x_503_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_496_, v___x_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_lctx_504_; lean_object* v___x_505_; lean_object* v___x_506_; size_t v_sz_507_; size_t v___x_508_; lean_object* v___x_509_; 
lean_dec_ref_known(v___x_503_, 1);
v_lctx_504_ = lean_ctor_get(v___y_498_, 2);
v___x_505_ = ((lean_object*)(l_Lean_MVarId_revertAll___lam__0___closed__0));
v___x_506_ = l_Lean_LocalContext_getFVarIds(v_lctx_504_);
v_sz_507_ = lean_array_size(v___x_506_);
v___x_508_ = ((size_t)0ULL);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v___x_506_, v_sz_507_, v___x_508_, v___x_505_, v___y_498_, v___y_500_, v___y_501_);
lean_dec_ref(v___x_506_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; uint8_t v___x_511_; lean_object* v___x_512_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = 0;
lean_inc(v_mvarId_496_);
v___x_512_ = l_Lean_MVarId_setKind___redArg(v_mvarId_496_, v___x_511_, v___y_499_);
if (lean_obj_tag(v___x_512_) == 0)
{
uint8_t v___x_513_; lean_object* v___x_514_; 
lean_dec_ref_known(v___x_512_, 1);
v___x_513_ = 1;
v___x_514_ = l_Lean_MVarId_revert(v_mvarId_496_, v_a_510_, v___x_513_, v___x_513_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_523_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_snd_519_; lean_object* v___x_521_; 
v_snd_519_ = lean_ctor_get(v_a_515_, 1);
lean_inc(v_snd_519_);
lean_dec(v_a_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v_snd_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_snd_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_a_524_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_514_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_514_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_a_510_);
lean_dec(v_mvarId_496_);
v_a_532_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_512_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_512_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_mvarId_496_);
v_a_540_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_509_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_509_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v_mvarId_496_);
v_a_548_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_503_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_503_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lam__0___boxed(lean_object* v_mvarId_556_, lean_object* v___x_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_MVarId_revertAll___lam__0(v_mvarId_556_, v___x_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll(lean_object* v_mvarId_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_573_; lean_object* v___f_574_; lean_object* v___x_575_; 
v___x_573_ = ((lean_object*)(l_Lean_MVarId_revertAll___closed__1));
lean_inc(v_mvarId_567_);
v___f_574_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertAll___lam__0___boxed), 7, 2);
lean_closure_set(v___f_574_, 0, v_mvarId_567_);
lean_closure_set(v___f_574_, 1, v___x_573_);
v___x_575_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(v_mvarId_567_, v___f_574_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___boxed(lean_object* v_mvarId_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_MVarId_revertAll(v_mvarId_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(lean_object* v_as_583_, size_t v_sz_584_, size_t v_i_585_, lean_object* v_b_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_583_, v_sz_584_, v_i_585_, v_b_586_, v___y_587_, v___y_589_, v___y_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___boxed(lean_object* v_as_593_, lean_object* v_sz_594_, lean_object* v_i_595_, lean_object* v_b_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
size_t v_sz_boxed_602_; size_t v_i_boxed_603_; lean_object* v_res_604_; 
v_sz_boxed_602_ = lean_unbox_usize(v_sz_594_);
lean_dec(v_sz_594_);
v_i_boxed_603_ = lean_unbox_usize(v_i_595_);
lean_dec(v_i_595_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(v_as_593_, v_sz_boxed_602_, v_i_boxed_603_, v_b_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v_as_593_);
return v_res_604_;
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
