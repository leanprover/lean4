// Lean compiler output
// Module: Lean.Meta.Tactic.Revert
// Imports: public import Lean.Meta.Tactic.Clear
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Failed to revert `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 106, .m_capacity = 106, .m_length = 105, .m_data = "`: It is an auxiliary declaration created to represent a recursive reference to an in-progress definition"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_MVarId_revert___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_revert___lam__0___closed__0;
static lean_once_cell_t l_Lean_MVarId_revert___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_revert___lam__0___closed__1;
static const lean_string_object l_Lean_MVarId_revert___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "failed to create binder due to failure when reverting variable dependencies"};
static const lean_object* l_Lean_MVarId_revert___lam__0___closed__2 = (const lean_object*)&l_Lean_MVarId_revert___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_MVarId_revert___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_revert___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_revert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "revert"};
static const lean_object* l_Lean_MVarId_revert___closed__0 = (const lean_object*)&l_Lean_MVarId_revert___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_revert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_revert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 122, 252, 27, 38, 131, 244, 91)}};
static const lean_object* l_Lean_MVarId_revert___closed__1 = (const lean_object*)&l_Lean_MVarId_revert___closed__1_value;
static const lean_array_object l_Lean_MVarId_revert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_revert___closed__2 = (const lean_object*)&l_Lean_MVarId_revert___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(lean_object* v_mvarId_1_, lean_object* v_x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1_, v_x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v___x_8_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_a_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_a_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
else
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_24_; 
v_a_17_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_24_ == 0)
{
v___x_19_ = v___x_8_;
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_8_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_24_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_20_ == 0)
{
v___x_22_ = v___x_19_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg___boxed(lean_object* v_mvarId_25_, lean_object* v_x_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_25_, v_x_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5(lean_object* v_00_u03b1_33_, lean_object* v_mvarId_34_, lean_object* v_x_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_34_, v_x_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___boxed(lean_object* v_00_u03b1_42_, lean_object* v_mvarId_43_, lean_object* v_x_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5(v_00_u03b1_42_, v_mvarId_43_, v_x_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(lean_object* v_msgData_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; lean_object* v_env_58_; lean_object* v___x_59_; lean_object* v_mctx_60_; lean_object* v_lctx_61_; lean_object* v_options_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_57_ = lean_st_ref_get(v___y_55_);
v_env_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc_ref(v_env_58_);
lean_dec(v___x_57_);
v___x_59_ = lean_st_ref_get(v___y_53_);
v_mctx_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_mctx_60_);
lean_dec(v___x_59_);
v_lctx_61_ = lean_ctor_get(v___y_52_, 2);
v_options_62_ = lean_ctor_get(v___y_54_, 2);
lean_inc_ref(v_options_62_);
lean_inc_ref(v_lctx_61_);
v___x_63_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_63_, 0, v_env_58_);
lean_ctor_set(v___x_63_, 1, v_mctx_60_);
lean_ctor_set(v___x_63_, 2, v_lctx_61_);
lean_ctor_set(v___x_63_, 3, v_options_62_);
v___x_64_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v_msgData_51_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3___boxed(lean_object* v_msgData_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(v_msgData_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(lean_object* v_msg_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_ref_79_; lean_object* v___x_80_; lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_89_; 
v_ref_79_ = lean_ctor_get(v___y_76_, 5);
v___x_80_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(v_msg_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_89_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_89_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_89_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v___x_87_; 
lean_inc(v_ref_79_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v_ref_79_);
lean_ctor_set(v___x_85_, 1, v_a_81_);
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 1);
lean_ctor_set(v___x_83_, 0, v___x_85_);
v___x_87_ = v___x_83_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg___boxed(lean_object* v_msg_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v_msg_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_96_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0));
v___x_99_ = l_Lean_stringToMessageData(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2));
v___x_102_ = l_Lean_stringToMessageData(v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(lean_object* v_as_103_, size_t v_sz_104_, size_t v_i_105_, lean_object* v_b_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_a_113_; uint8_t v___x_117_; 
v___x_117_ = lean_usize_dec_lt(v_i_105_, v_sz_104_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v_b_106_);
return v___x_118_;
}
else
{
lean_object* v_a_119_; lean_object* v___x_120_; 
v_a_119_ = lean_array_uget_borrowed(v_as_103_, v_i_105_);
lean_inc(v_a_119_);
v___x_120_ = l_Lean_FVarId_getDecl___redArg(v_a_119_, v___y_107_, v___y_109_, v___y_110_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref_known(v___x_120_, 1);
v___x_122_ = lean_box(0);
v___x_123_ = l_Lean_LocalDecl_isAuxDecl(v_a_121_);
lean_dec(v_a_121_);
if (v___x_123_ == 0)
{
v_a_113_ = v___x_122_;
goto v___jp_112_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_124_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1);
lean_inc(v_a_119_);
v___x_125_ = l_Lean_mkFVar(v_a_119_);
v___x_126_ = l_Lean_MessageData_ofExpr(v___x_125_);
v___x_127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_124_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3);
v___x_129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v___x_129_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_dec_ref_known(v___x_130_, 1);
v_a_113_ = v___x_122_;
goto v___jp_112_;
}
else
{
return v___x_130_;
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
v_a_131_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_120_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_120_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
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
v___jp_112_:
{
size_t v___x_114_; size_t v___x_115_; 
v___x_114_ = ((size_t)1ULL);
v___x_115_ = lean_usize_add(v_i_105_, v___x_114_);
v_i_105_ = v___x_115_;
v_b_106_ = v_a_113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___boxed(lean_object* v_as_139_, lean_object* v_sz_140_, lean_object* v_i_141_, lean_object* v_b_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
size_t v_sz_boxed_148_; size_t v_i_boxed_149_; lean_object* v_res_150_; 
v_sz_boxed_148_ = lean_unbox_usize(v_sz_140_);
lean_dec(v_sz_140_);
v_i_boxed_149_ = lean_unbox_usize(v_i_141_);
lean_dec(v_i_141_);
v_res_150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_as_139_, v_sz_boxed_148_, v_i_boxed_149_, v_b_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec_ref(v_as_139_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(size_t v_sz_151_, size_t v_i_152_, lean_object* v_bs_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = lean_usize_dec_lt(v_i_152_, v_sz_151_);
if (v___x_154_ == 0)
{
return v_bs_153_;
}
else
{
lean_object* v_v_155_; lean_object* v___x_156_; lean_object* v_bs_x27_157_; lean_object* v___x_158_; size_t v___x_159_; size_t v___x_160_; lean_object* v___x_161_; 
v_v_155_ = lean_array_uget(v_bs_153_, v_i_152_);
v___x_156_ = lean_unsigned_to_nat(0u);
v_bs_x27_157_ = lean_array_uset(v_bs_153_, v_i_152_, v___x_156_);
v___x_158_ = l_Lean_mkFVar(v_v_155_);
v___x_159_ = ((size_t)1ULL);
v___x_160_ = lean_usize_add(v_i_152_, v___x_159_);
v___x_161_ = lean_array_uset(v_bs_x27_157_, v_i_152_, v___x_158_);
v_i_152_ = v___x_160_;
v_bs_153_ = v___x_161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0___boxed(lean_object* v_sz_163_, lean_object* v_i_164_, lean_object* v_bs_165_){
_start:
{
size_t v_sz_boxed_166_; size_t v_i_boxed_167_; lean_object* v_res_168_; 
v_sz_boxed_166_ = lean_unbox_usize(v_sz_163_);
lean_dec(v_sz_163_);
v_i_boxed_167_ = lean_unbox_usize(v_i_164_);
lean_dec(v_i_164_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(v_sz_boxed_166_, v_i_boxed_167_, v_bs_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(size_t v_sz_169_, size_t v_i_170_, lean_object* v_bs_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = lean_usize_dec_lt(v_i_170_, v_sz_169_);
if (v___x_172_ == 0)
{
return v_bs_171_;
}
else
{
lean_object* v_v_173_; lean_object* v___x_174_; lean_object* v_bs_x27_175_; lean_object* v___x_176_; size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v_v_173_ = lean_array_uget(v_bs_171_, v_i_170_);
v___x_174_ = lean_unsigned_to_nat(0u);
v_bs_x27_175_ = lean_array_uset(v_bs_171_, v_i_170_, v___x_174_);
v___x_176_ = l_Lean_Expr_fvarId_x21(v_v_173_);
lean_dec(v_v_173_);
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_add(v_i_170_, v___x_177_);
v___x_179_ = lean_array_uset(v_bs_x27_175_, v_i_170_, v___x_176_);
v_i_170_ = v___x_178_;
v_bs_171_ = v___x_179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2___boxed(lean_object* v_sz_181_, lean_object* v_i_182_, lean_object* v_bs_183_){
_start:
{
size_t v_sz_boxed_184_; size_t v_i_boxed_185_; lean_object* v_res_186_; 
v_sz_boxed_184_ = lean_unbox_usize(v_sz_181_);
lean_dec(v_sz_181_);
v_i_boxed_185_ = lean_unbox_usize(v_i_182_);
lean_dec(v_i_182_);
v_res_186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(v_sz_boxed_184_, v_i_boxed_185_, v_bs_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(lean_object* v_as_187_, size_t v_sz_188_, size_t v_i_189_, lean_object* v_b_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_a_197_; uint8_t v___x_201_; 
v___x_201_ = lean_usize_dec_lt(v_i_189_, v_sz_188_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v_b_190_);
return v___x_202_;
}
else
{
lean_object* v_a_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_a_203_ = lean_array_uget_borrowed(v_as_187_, v_i_189_);
v___x_204_ = l_Lean_Expr_fvarId_x21(v_a_203_);
lean_inc(v___x_204_);
v___x_205_ = l_Lean_FVarId_getDecl___redArg(v___x_204_, v___y_191_, v___y_193_, v___y_194_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v_fst_207_; lean_object* v_snd_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_230_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
v_fst_207_ = lean_ctor_get(v_b_190_, 0);
v_snd_208_ = lean_ctor_get(v_b_190_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v_b_190_);
if (v_isSharedCheck_230_ == 0)
{
v___x_210_ = v_b_190_;
v_isShared_211_ = v_isSharedCheck_230_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_snd_208_);
lean_inc(v_fst_207_);
lean_dec(v_b_190_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_230_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
uint8_t v___x_212_; 
v___x_212_ = l_Lean_LocalDecl_isAuxDecl(v_a_206_);
lean_dec(v_a_206_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_215_; 
lean_dec(v___x_204_);
lean_inc(v_a_203_);
v___x_213_ = lean_array_push(v_snd_208_, v_a_203_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_213_);
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_fst_207_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
v_a_197_ = v___x_215_;
goto v___jp_196_;
}
}
else
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_MVarId_clear(v_fst_207_, v___x_204_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 1);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v_a_218_);
v___x_220_ = v___x_210_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_218_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_snd_208_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
v_a_197_ = v___x_220_;
goto v___jp_196_;
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_del_object(v___x_210_);
lean_dec(v_snd_208_);
v_a_222_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_217_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_217_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec(v___x_204_);
lean_dec_ref(v_b_190_);
v_a_231_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_205_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_205_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
v___jp_196_:
{
size_t v___x_198_; size_t v___x_199_; 
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_add(v_i_189_, v___x_198_);
v_i_189_ = v___x_199_;
v_b_190_ = v_a_197_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1___boxed(lean_object* v_as_239_, lean_object* v_sz_240_, lean_object* v_i_241_, lean_object* v_b_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
size_t v_sz_boxed_248_; size_t v_i_boxed_249_; lean_object* v_res_250_; 
v_sz_boxed_248_ = lean_unbox_usize(v_sz_240_);
lean_dec(v_sz_240_);
v_i_boxed_249_ = lean_unbox_usize(v_i_241_);
lean_dec(v_i_241_);
v_res_250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_as_239_, v_sz_boxed_248_, v_i_boxed_249_, v_b_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec_ref(v_as_239_);
return v_res_250_;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lam__0___closed__0(void){
_start:
{
lean_object* v_cellCount_251_; lean_object* v___x_252_; 
v_cellCount_251_ = lean_unsigned_to_nat(16u);
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lam__0___closed__1(void){
_start:
{
lean_object* v_cellCount_253_; lean_object* v___x_254_; 
v_cellCount_253_ = lean_unsigned_to_nat(16u);
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_253_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lam__0___closed__3(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l_Lean_MVarId_revert___lam__0___closed__2));
v___x_257_ = l_Lean_stringToMessageData(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0(lean_object* v_mvarId_258_, lean_object* v___x_259_, lean_object* v_fvarIds_260_, uint8_t v_preserveOrder_261_, uint8_t v___x_262_, lean_object* v___x_263_, uint8_t v_clearAuxDeclsInsteadOfRevert_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; uint8_t v___y_274_; size_t v___y_275_; lean_object* v_a_276_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___x_492_; 
lean_inc(v_mvarId_258_);
v___x_492_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_258_, v___x_259_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_dec_ref_known(v___x_492_, 1);
if (v_clearAuxDeclsInsteadOfRevert_264_ == 0)
{
lean_object* v___x_493_; size_t v_sz_494_; size_t v___x_495_; lean_object* v___x_496_; 
v___x_493_ = lean_box(0);
v_sz_494_ = lean_array_size(v_fvarIds_260_);
v___x_495_ = ((size_t)0ULL);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_fvarIds_260_, v_sz_494_, v___x_495_, v___x_493_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_dec_ref_known(v___x_496_, 1);
v___y_326_ = v___y_265_;
v___y_327_ = v___y_266_;
v___y_328_ = v___y_267_;
v___y_329_ = v___y_268_;
goto v___jp_325_;
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v___x_263_);
lean_dec_ref(v_fvarIds_260_);
lean_dec(v_mvarId_258_);
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
v___y_326_ = v___y_265_;
v___y_327_ = v___y_266_;
v___y_328_ = v___y_267_;
v___y_329_ = v___y_268_;
goto v___jp_325_;
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v___x_263_);
lean_dec_ref(v_fvarIds_260_);
lean_dec(v_mvarId_258_);
v_a_505_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_492_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_492_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
v___jp_270_:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_MVarId_setKind___redArg(v___y_273_, v___y_274_, v___y_272_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref_known(v___x_277_, 1);
v_fst_278_ = lean_ctor_get(v_a_276_, 0);
v_snd_279_ = lean_ctor_get(v_a_276_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_a_276_);
if (v_isSharedCheck_316_ == 0)
{
v___x_281_ = v_a_276_;
v_isShared_282_ = v_isSharedCheck_316_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_snd_279_);
lean_inc(v_fst_278_);
lean_dec(v_a_276_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_316_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = l_Lean_Expr_getAppFn(v_fst_278_);
lean_dec(v_fst_278_);
v___x_284_ = l_Lean_Expr_mvarId_x21(v___x_283_);
lean_dec_ref(v___x_283_);
lean_inc(v___x_284_);
v___x_285_ = l_Lean_MVarId_setKind___redArg(v___x_284_, v___y_274_, v___y_272_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v___x_286_; 
lean_dec_ref_known(v___x_285_, 1);
lean_inc(v___x_284_);
v___x_286_ = l_Lean_MVarId_setTag___redArg(v___x_284_, v___y_271_, v___y_272_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_298_; 
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_286_, 0);
lean_dec(v_unused_299_);
v___x_288_ = v___x_286_;
v_isShared_289_ = v_isSharedCheck_298_;
goto v_resetjp_287_;
}
else
{
lean_dec(v___x_286_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_298_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
size_t v_sz_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v_sz_290_ = lean_array_size(v_snd_279_);
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(v_sz_290_, v___y_275_, v_snd_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v___x_284_);
lean_ctor_set(v___x_281_, 0, v___x_291_);
v___x_293_ = v___x_281_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_284_);
v___x_293_ = v_reuseFailAlloc_297_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_293_);
v___x_295_ = v___x_288_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec(v___x_284_);
lean_del_object(v___x_281_);
lean_dec(v_snd_279_);
v_a_300_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_286_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_286_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
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
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec(v___x_284_);
lean_del_object(v___x_281_);
lean_dec(v_snd_279_);
lean_dec(v___y_271_);
v_a_308_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_285_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_285_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_a_276_);
lean_dec(v___y_271_);
v_a_317_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_277_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_277_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
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
v___jp_325_:
{
size_t v_sz_330_; size_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_sz_330_ = lean_array_size(v_fvarIds_260_);
v___x_331_ = ((size_t)0ULL);
v___x_332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(v_sz_330_, v___x_331_, v_fvarIds_260_);
v___x_333_ = l_Lean_Meta_collectForwardDeps(v___x_332_, v_preserveOrder_261_, v___x_262_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; lean_object* v___x_336_; size_t v_sz_337_; lean_object* v___x_338_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = lean_mk_empty_array_with_capacity(v___x_263_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v_mvarId_258_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v_sz_337_ = lean_array_size(v_a_334_);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_a_334_, v_sz_337_, v___x_331_, v___x_336_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v_a_334_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v_fst_340_; lean_object* v_snd_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_475_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_338_, 1);
v_fst_340_ = lean_ctor_get(v_a_339_, 0);
v_snd_341_ = lean_ctor_get(v_a_339_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_a_339_);
if (v_isSharedCheck_475_ == 0)
{
v___x_343_ = v_a_339_;
v_isShared_344_ = v_isSharedCheck_475_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_snd_341_);
lean_inc(v_fst_340_);
lean_dec(v_a_339_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_475_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; 
lean_inc(v_fst_340_);
v___x_345_ = l_Lean_MVarId_getTag(v_fst_340_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; uint8_t v___x_347_; lean_object* v___x_348_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v___x_347_ = 0;
lean_inc(v_fst_340_);
v___x_348_ = l_Lean_MVarId_setKind___redArg(v_fst_340_, v___x_347_, v___y_327_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_lctx_352_; lean_object* v_mctx_353_; lean_object* v_ngen_354_; lean_object* v_quotContext_355_; lean_object* v_nextMacroScope_356_; uint8_t v___x_357_; lean_object* v___x_359_; 
lean_dec_ref_known(v___x_348_, 1);
v___x_349_ = lean_st_ref_get(v___y_327_);
v___x_350_ = lean_st_ref_get(v___y_329_);
v___x_351_ = lean_st_ref_get(v___y_329_);
v_lctx_352_ = lean_ctor_get(v___y_326_, 2);
v_mctx_353_ = lean_ctor_get(v___x_349_, 0);
lean_inc_ref(v_mctx_353_);
lean_dec(v___x_349_);
v_ngen_354_ = lean_ctor_get(v___x_350_, 2);
lean_inc_ref(v_ngen_354_);
lean_dec(v___x_350_);
v_quotContext_355_ = lean_ctor_get(v___y_328_, 10);
v_nextMacroScope_356_ = lean_ctor_get(v___x_351_, 1);
lean_inc(v_nextMacroScope_356_);
lean_dec(v___x_351_);
v___x_357_ = 2;
lean_inc_ref(v_lctx_352_);
lean_inc(v_quotContext_355_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v_lctx_352_);
lean_ctor_set(v___x_343_, 0, v_quotContext_355_);
v___x_359_ = v___x_343_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_quotContext_355_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_lctx_352_);
v___x_359_ = v_reuseFailAlloc_458_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_360_ = lean_obj_once(&l_Lean_MVarId_revert___lam__0___closed__0, &l_Lean_MVarId_revert___lam__0___closed__0_once, _init_l_Lean_MVarId_revert___lam__0___closed__0);
v___x_361_ = lean_obj_once(&l_Lean_MVarId_revert___lam__0___closed__1, &l_Lean_MVarId_revert___lam__0___closed__1_once, _init_l_Lean_MVarId_revert___lam__0___closed__1);
v___x_362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_362_, 0, v___x_263_);
lean_ctor_set(v___x_362_, 1, v___x_360_);
lean_ctor_set(v___x_362_, 2, v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_363_, 0, v_mctx_353_);
lean_ctor_set(v___x_363_, 1, v_nextMacroScope_356_);
lean_ctor_set(v___x_363_, 2, v_ngen_354_);
lean_ctor_set(v___x_363_, 3, v___x_362_);
lean_inc(v_fst_340_);
v___x_364_ = l_Lean_MetavarContext_revert(v_snd_341_, v_fst_340_, v_preserveOrder_261_, v___x_359_, v___x_363_);
lean_dec_ref(v___x_359_);
lean_dec(v_snd_341_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v_a_366_; lean_object* v___x_367_; lean_object* v_mctx_368_; lean_object* v_nextMacroScope_369_; lean_object* v_ngen_370_; lean_object* v_cache_371_; lean_object* v_zetaDeltaFVarIds_372_; lean_object* v_postponed_373_; lean_object* v_diag_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_400_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
v_a_366_ = lean_ctor_get(v___x_364_, 1);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_364_, 2);
v___x_367_ = lean_st_ref_take(v___y_327_);
v_mctx_368_ = lean_ctor_get(v_a_366_, 0);
lean_inc_ref(v_mctx_368_);
v_nextMacroScope_369_ = lean_ctor_get(v_a_366_, 1);
lean_inc(v_nextMacroScope_369_);
v_ngen_370_ = lean_ctor_get(v_a_366_, 2);
lean_inc_ref(v_ngen_370_);
lean_dec(v_a_366_);
v_cache_371_ = lean_ctor_get(v___x_367_, 1);
v_zetaDeltaFVarIds_372_ = lean_ctor_get(v___x_367_, 2);
v_postponed_373_ = lean_ctor_get(v___x_367_, 3);
v_diag_374_ = lean_ctor_get(v___x_367_, 4);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v___x_367_, 0);
lean_dec(v_unused_401_);
v___x_376_ = v___x_367_;
v_isShared_377_ = v_isSharedCheck_400_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_diag_374_);
lean_inc(v_postponed_373_);
lean_inc(v_zetaDeltaFVarIds_372_);
lean_inc(v_cache_371_);
lean_dec(v___x_367_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_400_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v_mctx_368_);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_mctx_368_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_cache_371_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_zetaDeltaFVarIds_372_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_postponed_373_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v_diag_374_);
v___x_379_ = v_reuseFailAlloc_399_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_env_382_; lean_object* v_auxDeclNGen_383_; lean_object* v_traceState_384_; lean_object* v_cache_385_; lean_object* v_messages_386_; lean_object* v_infoState_387_; lean_object* v_snapshotTasks_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
v___x_380_ = lean_st_ref_put(v___y_327_, v___x_379_);
v___x_381_ = lean_st_ref_take(v___y_329_);
v_env_382_ = lean_ctor_get(v___x_381_, 0);
v_auxDeclNGen_383_ = lean_ctor_get(v___x_381_, 3);
v_traceState_384_ = lean_ctor_get(v___x_381_, 4);
v_cache_385_ = lean_ctor_get(v___x_381_, 5);
v_messages_386_ = lean_ctor_get(v___x_381_, 6);
v_infoState_387_ = lean_ctor_get(v___x_381_, 7);
v_snapshotTasks_388_ = lean_ctor_get(v___x_381_, 8);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; lean_object* v_unused_398_; 
v_unused_397_ = lean_ctor_get(v___x_381_, 2);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v___x_381_, 1);
lean_dec(v_unused_398_);
v___x_390_ = v___x_381_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_snapshotTasks_388_);
lean_inc(v_infoState_387_);
lean_inc(v_messages_386_);
lean_inc(v_cache_385_);
lean_inc(v_traceState_384_);
lean_inc(v_auxDeclNGen_383_);
lean_inc(v_env_382_);
lean_dec(v___x_381_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 2, v_ngen_370_);
lean_ctor_set(v___x_390_, 1, v_nextMacroScope_369_);
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_env_382_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_nextMacroScope_369_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_ngen_370_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_auxDeclNGen_383_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_traceState_384_);
lean_ctor_set(v_reuseFailAlloc_395_, 5, v_cache_385_);
lean_ctor_set(v_reuseFailAlloc_395_, 6, v_messages_386_);
lean_ctor_set(v_reuseFailAlloc_395_, 7, v_infoState_387_);
lean_ctor_set(v_reuseFailAlloc_395_, 8, v_snapshotTasks_388_);
v___x_393_ = v_reuseFailAlloc_395_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; 
v___x_394_ = lean_st_ref_put(v___y_329_, v___x_393_);
v___y_271_ = v_a_346_;
v___y_272_ = v___y_327_;
v___y_273_ = v_fst_340_;
v___y_274_ = v___x_357_;
v___y_275_ = v___x_331_;
v_a_276_ = v_a_365_;
goto v___jp_270_;
}
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_403_; lean_object* v_mctx_404_; lean_object* v_nextMacroScope_405_; lean_object* v_ngen_406_; lean_object* v_cache_407_; lean_object* v_zetaDeltaFVarIds_408_; lean_object* v_postponed_409_; lean_object* v_diag_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_456_; 
lean_dec(v_a_346_);
v_a_402_ = lean_ctor_get(v___x_364_, 1);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_364_, 2);
v___x_403_ = lean_st_ref_take(v___y_327_);
v_mctx_404_ = lean_ctor_get(v_a_402_, 0);
lean_inc_ref(v_mctx_404_);
v_nextMacroScope_405_ = lean_ctor_get(v_a_402_, 1);
lean_inc(v_nextMacroScope_405_);
v_ngen_406_ = lean_ctor_get(v_a_402_, 2);
lean_inc_ref(v_ngen_406_);
lean_dec(v_a_402_);
v_cache_407_ = lean_ctor_get(v___x_403_, 1);
v_zetaDeltaFVarIds_408_ = lean_ctor_get(v___x_403_, 2);
v_postponed_409_ = lean_ctor_get(v___x_403_, 3);
v_diag_410_ = lean_ctor_get(v___x_403_, 4);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v___x_403_, 0);
lean_dec(v_unused_457_);
v___x_412_ = v___x_403_;
v_isShared_413_ = v_isSharedCheck_456_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_diag_410_);
lean_inc(v_postponed_409_);
lean_inc(v_zetaDeltaFVarIds_408_);
lean_inc(v_cache_407_);
lean_dec(v___x_403_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_456_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v_mctx_404_);
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_mctx_404_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_cache_407_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_zetaDeltaFVarIds_408_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_postponed_409_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_diag_410_);
v___x_415_ = v_reuseFailAlloc_455_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_env_418_; lean_object* v_auxDeclNGen_419_; lean_object* v_traceState_420_; lean_object* v_cache_421_; lean_object* v_messages_422_; lean_object* v_infoState_423_; lean_object* v_snapshotTasks_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_452_; 
v___x_416_ = lean_st_ref_put(v___y_327_, v___x_415_);
v___x_417_ = lean_st_ref_take(v___y_329_);
v_env_418_ = lean_ctor_get(v___x_417_, 0);
v_auxDeclNGen_419_ = lean_ctor_get(v___x_417_, 3);
v_traceState_420_ = lean_ctor_get(v___x_417_, 4);
v_cache_421_ = lean_ctor_get(v___x_417_, 5);
v_messages_422_ = lean_ctor_get(v___x_417_, 6);
v_infoState_423_ = lean_ctor_get(v___x_417_, 7);
v_snapshotTasks_424_ = lean_ctor_get(v___x_417_, 8);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; lean_object* v_unused_454_; 
v_unused_453_ = lean_ctor_get(v___x_417_, 2);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v___x_417_, 1);
lean_dec(v_unused_454_);
v___x_426_ = v___x_417_;
v_isShared_427_ = v_isSharedCheck_452_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snapshotTasks_424_);
lean_inc(v_infoState_423_);
lean_inc(v_messages_422_);
lean_inc(v_cache_421_);
lean_inc(v_traceState_420_);
lean_inc(v_auxDeclNGen_419_);
lean_inc(v_env_418_);
lean_dec(v___x_417_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_452_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 2, v_ngen_406_);
lean_ctor_set(v___x_426_, 1, v_nextMacroScope_405_);
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_env_418_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_nextMacroScope_405_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_ngen_406_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_auxDeclNGen_419_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v_traceState_420_);
lean_ctor_set(v_reuseFailAlloc_451_, 5, v_cache_421_);
lean_ctor_set(v_reuseFailAlloc_451_, 6, v_messages_422_);
lean_ctor_set(v_reuseFailAlloc_451_, 7, v_infoState_423_);
lean_ctor_set(v_reuseFailAlloc_451_, 8, v_snapshotTasks_424_);
v___x_429_ = v_reuseFailAlloc_451_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_a_433_; lean_object* v___x_434_; 
v___x_430_ = lean_st_ref_put(v___y_329_, v___x_429_);
v___x_431_ = lean_obj_once(&l_Lean_MVarId_revert___lam__0___closed__3, &l_Lean_MVarId_revert___lam__0___closed__3_once, _init_l_Lean_MVarId_revert___lam__0___closed__3);
v___x_432_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v___x_431_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref(v___x_432_);
v___x_434_ = l_Lean_MVarId_setKind___redArg(v_fst_340_, v___x_357_, v___y_327_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; 
v_unused_442_ = lean_ctor_get(v___x_434_, 0);
lean_dec(v_unused_442_);
v___x_436_ = v___x_434_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_dec(v___x_434_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 1);
lean_ctor_set(v___x_436_, 0, v_a_433_);
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_433_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec(v_a_433_);
v_a_443_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_434_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_434_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_a_346_);
lean_del_object(v___x_343_);
lean_dec(v_snd_341_);
lean_dec(v_fst_340_);
lean_dec(v___x_263_);
v_a_459_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_348_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_348_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_del_object(v___x_343_);
lean_dec(v_snd_341_);
lean_dec(v_fst_340_);
lean_dec(v___x_263_);
v_a_467_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_345_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_345_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v___x_263_);
v_a_476_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_338_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_338_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v___x_263_);
lean_dec(v_mvarId_258_);
v_a_484_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_333_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_333_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0___boxed(lean_object* v_mvarId_513_, lean_object* v___x_514_, lean_object* v_fvarIds_515_, lean_object* v_preserveOrder_516_, lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v_clearAuxDeclsInsteadOfRevert_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
uint8_t v_preserveOrder_boxed_525_; uint8_t v___x_10019__boxed_526_; uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_527_; lean_object* v_res_528_; 
v_preserveOrder_boxed_525_ = lean_unbox(v_preserveOrder_516_);
v___x_10019__boxed_526_ = lean_unbox(v___x_517_);
v_clearAuxDeclsInsteadOfRevert_boxed_527_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_519_);
v_res_528_ = l_Lean_MVarId_revert___lam__0(v_mvarId_513_, v___x_514_, v_fvarIds_515_, v_preserveOrder_boxed_525_, v___x_10019__boxed_526_, v___x_518_, v_clearAuxDeclsInsteadOfRevert_boxed_527_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert(lean_object* v_mvarId_534_, lean_object* v_fvarIds_535_, uint8_t v_preserveOrder_536_, uint8_t v_clearAuxDeclsInsteadOfRevert_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_543_ = lean_array_get_size(v_fvarIds_535_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_nat_dec_eq(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___f_551_; lean_object* v___x_552_; 
v___x_546_ = 1;
v___x_547_ = ((lean_object*)(l_Lean_MVarId_revert___closed__1));
v___x_548_ = lean_box(v_preserveOrder_536_);
v___x_549_ = lean_box(v___x_546_);
v___x_550_ = lean_box(v_clearAuxDeclsInsteadOfRevert_537_);
lean_inc(v_mvarId_534_);
v___f_551_ = lean_alloc_closure((void*)(l_Lean_MVarId_revert___lam__0___boxed), 12, 7);
lean_closure_set(v___f_551_, 0, v_mvarId_534_);
lean_closure_set(v___f_551_, 1, v___x_547_);
lean_closure_set(v___f_551_, 2, v_fvarIds_535_);
lean_closure_set(v___f_551_, 3, v___x_548_);
lean_closure_set(v___f_551_, 4, v___x_549_);
lean_closure_set(v___f_551_, 5, v___x_544_);
lean_closure_set(v___f_551_, 6, v___x_550_);
v___x_552_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_534_, v___f_551_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v_fvarIds_535_);
v___x_553_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_mvarId_534_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object* v_mvarId_556_, lean_object* v_fvarIds_557_, lean_object* v_preserveOrder_558_, lean_object* v_clearAuxDeclsInsteadOfRevert_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
uint8_t v_preserveOrder_boxed_565_; uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_566_; lean_object* v_res_567_; 
v_preserveOrder_boxed_565_ = lean_unbox(v_preserveOrder_558_);
v_clearAuxDeclsInsteadOfRevert_boxed_566_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_559_);
v_res_567_ = l_Lean_MVarId_revert(v_mvarId_556_, v_fvarIds_557_, v_preserveOrder_boxed_565_, v_clearAuxDeclsInsteadOfRevert_boxed_566_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(lean_object* v_00_u03b1_568_, lean_object* v_msg_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v_msg_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___boxed(lean_object* v_00_u03b1_576_, lean_object* v_msg_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(v_00_u03b1_576_, v_msg_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(lean_object* v_as_584_, size_t v_i_585_, size_t v_stop_586_, lean_object* v_b_587_){
_start:
{
lean_object* v___y_589_; uint8_t v___x_593_; 
v___x_593_ = lean_usize_dec_eq(v_i_585_, v_stop_586_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_array_uget_borrowed(v_as_584_, v_i_585_);
if (lean_obj_tag(v___x_594_) == 0)
{
v___y_589_ = v_b_587_;
goto v___jp_588_;
}
else
{
lean_object* v_val_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_val_595_ = lean_ctor_get(v___x_594_, 0);
v___x_596_ = l_Lean_LocalDecl_fvarId(v_val_595_);
v___x_597_ = lean_array_push(v_b_587_, v___x_596_);
v___y_589_ = v___x_597_;
goto v___jp_588_;
}
}
else
{
return v_b_587_;
}
v___jp_588_:
{
size_t v___x_590_; size_t v___x_591_; 
v___x_590_ = ((size_t)1ULL);
v___x_591_ = lean_usize_add(v_i_585_, v___x_590_);
v_i_585_ = v___x_591_;
v_b_587_ = v___y_589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2___boxed(lean_object* v_as_598_, lean_object* v_i_599_, lean_object* v_stop_600_, lean_object* v_b_601_){
_start:
{
size_t v_i_boxed_602_; size_t v_stop_boxed_603_; lean_object* v_res_604_; 
v_i_boxed_602_ = lean_unbox_usize(v_i_599_);
lean_dec(v_i_599_);
v_stop_boxed_603_ = lean_unbox_usize(v_stop_600_);
lean_dec(v_stop_600_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_as_598_, v_i_boxed_602_, v_stop_boxed_603_, v_b_601_);
lean_dec_ref(v_as_598_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
lean_object* v_cs_607_; lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_cs_607_ = lean_ctor_get(v_x_605_, 0);
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_array_get_size(v_cs_607_);
v___x_610_ = lean_nat_dec_lt(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
return v_x_606_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = lean_nat_dec_le(v___x_609_, v___x_609_);
if (v___x_611_ == 0)
{
if (v___x_610_ == 0)
{
return v_x_606_;
}
else
{
size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; 
v___x_612_ = ((size_t)0ULL);
v___x_613_ = lean_usize_of_nat(v___x_609_);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_607_, v___x_612_, v___x_613_, v_x_606_);
return v___x_614_;
}
}
else
{
size_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; 
v___x_615_ = ((size_t)0ULL);
v___x_616_ = lean_usize_of_nat(v___x_609_);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_607_, v___x_615_, v___x_616_, v_x_606_);
return v___x_617_;
}
}
}
else
{
lean_object* v_vs_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_vs_618_ = lean_ctor_get(v_x_605_, 0);
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_array_get_size(v_vs_618_);
v___x_621_ = lean_nat_dec_lt(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
return v_x_606_;
}
else
{
uint8_t v___x_622_; 
v___x_622_ = lean_nat_dec_le(v___x_620_, v___x_620_);
if (v___x_622_ == 0)
{
if (v___x_621_ == 0)
{
return v_x_606_;
}
else
{
size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v___x_623_ = ((size_t)0ULL);
v___x_624_ = lean_usize_of_nat(v___x_620_);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_618_, v___x_623_, v___x_624_, v_x_606_);
return v___x_625_;
}
}
else
{
size_t v___x_626_; size_t v___x_627_; lean_object* v___x_628_; 
v___x_626_ = ((size_t)0ULL);
v___x_627_ = lean_usize_of_nat(v___x_620_);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_618_, v___x_626_, v___x_627_, v_x_606_);
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_629_, size_t v_i_630_, size_t v_stop_631_, lean_object* v_b_632_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = lean_usize_dec_eq(v_i_630_, v_stop_631_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; size_t v___x_636_; size_t v___x_637_; 
v___x_634_ = lean_array_uget_borrowed(v_as_629_, v_i_630_);
v___x_635_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v___x_634_, v_b_632_);
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_add(v_i_630_, v___x_636_);
v_i_630_ = v___x_637_;
v_b_632_ = v___x_635_;
goto _start;
}
else
{
return v_b_632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_639_, lean_object* v_i_640_, lean_object* v_stop_641_, lean_object* v_b_642_){
_start:
{
size_t v_i_boxed_643_; size_t v_stop_boxed_644_; lean_object* v_res_645_; 
v_i_boxed_643_ = lean_unbox_usize(v_i_640_);
lean_dec(v_i_640_);
v_stop_boxed_644_ = lean_unbox_usize(v_stop_641_);
lean_dec(v_stop_641_);
v_res_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_as_639_, v_i_boxed_643_, v_stop_boxed_644_, v_b_642_);
lean_dec_ref(v_as_639_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3___boxed(lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v_x_646_, v_x_647_);
lean_dec_ref(v_x_646_);
return v_res_648_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(lean_object* v_x_650_, size_t v_x_651_, size_t v_x_652_, lean_object* v_x_653_){
_start:
{
if (lean_obj_tag(v_x_650_) == 0)
{
lean_object* v_cs_654_; lean_object* v___x_655_; size_t v___x_656_; lean_object* v_j_657_; lean_object* v___x_658_; size_t v___x_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_cs_654_ = lean_ctor_get(v_x_650_, 0);
v___x_655_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0);
v___x_656_ = lean_usize_shift_right(v_x_651_, v_x_652_);
v_j_657_ = lean_usize_to_nat(v___x_656_);
v___x_658_ = lean_array_get_borrowed(v___x_655_, v_cs_654_, v_j_657_);
v___x_659_ = ((size_t)1ULL);
v___x_660_ = lean_usize_shift_left(v___x_659_, v_x_652_);
v___x_661_ = lean_usize_sub(v___x_660_, v___x_659_);
v___x_662_ = lean_usize_land(v_x_651_, v___x_661_);
v___x_663_ = ((size_t)5ULL);
v___x_664_ = lean_usize_sub(v_x_652_, v___x_663_);
v___x_665_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v___x_658_, v___x_662_, v___x_664_, v_x_653_);
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_add(v_j_657_, v___x_666_);
lean_dec(v_j_657_);
v___x_668_ = lean_array_get_size(v_cs_654_);
v___x_669_ = lean_nat_dec_lt(v___x_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_dec(v___x_667_);
return v___x_665_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_le(v___x_668_, v___x_668_);
if (v___x_670_ == 0)
{
if (v___x_669_ == 0)
{
lean_dec(v___x_667_);
return v___x_665_;
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_usize_of_nat(v___x_667_);
lean_dec(v___x_667_);
v___x_672_ = lean_usize_of_nat(v___x_668_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_654_, v___x_671_, v___x_672_, v___x_665_);
return v___x_673_;
}
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_usize_of_nat(v___x_667_);
lean_dec(v___x_667_);
v___x_675_ = lean_usize_of_nat(v___x_668_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_654_, v___x_674_, v___x_675_, v___x_665_);
return v___x_676_;
}
}
}
else
{
lean_object* v_vs_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_vs_677_ = lean_ctor_get(v_x_650_, 0);
v___x_678_ = lean_usize_to_nat(v_x_651_);
v___x_679_ = lean_array_get_size(v_vs_677_);
v___x_680_ = lean_nat_dec_lt(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
lean_dec(v___x_678_);
return v_x_653_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = lean_nat_dec_le(v___x_679_, v___x_679_);
if (v___x_681_ == 0)
{
if (v___x_680_ == 0)
{
lean_dec(v___x_678_);
return v_x_653_;
}
else
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_usize_of_nat(v___x_678_);
lean_dec(v___x_678_);
v___x_683_ = lean_usize_of_nat(v___x_679_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_677_, v___x_682_, v___x_683_, v_x_653_);
return v___x_684_;
}
}
else
{
size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v___x_685_ = lean_usize_of_nat(v___x_678_);
lean_dec(v___x_678_);
v___x_686_ = lean_usize_of_nat(v___x_679_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_677_, v___x_685_, v___x_686_, v_x_653_);
return v___x_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___boxed(lean_object* v_x_688_, lean_object* v_x_689_, lean_object* v_x_690_, lean_object* v_x_691_){
_start:
{
size_t v_x_1742__boxed_692_; size_t v_x_1743__boxed_693_; lean_object* v_res_694_; 
v_x_1742__boxed_692_ = lean_unbox_usize(v_x_689_);
lean_dec(v_x_689_);
v_x_1743__boxed_693_ = lean_unbox_usize(v_x_690_);
lean_dec(v_x_690_);
v_res_694_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v_x_688_, v_x_1742__boxed_692_, v_x_1743__boxed_693_, v_x_691_);
lean_dec_ref(v_x_688_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(lean_object* v_t_695_, lean_object* v_init_696_, lean_object* v_start_697_){
_start:
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_nat_dec_eq(v_start_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v_root_700_; lean_object* v_tail_701_; size_t v_shift_702_; lean_object* v_tailOff_703_; uint8_t v___x_704_; 
v_root_700_ = lean_ctor_get(v_t_695_, 0);
v_tail_701_ = lean_ctor_get(v_t_695_, 1);
v_shift_702_ = lean_ctor_get_usize(v_t_695_, 4);
v_tailOff_703_ = lean_ctor_get(v_t_695_, 3);
v___x_704_ = lean_nat_dec_le(v_tailOff_703_, v_start_697_);
if (v___x_704_ == 0)
{
size_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_705_ = lean_usize_of_nat(v_start_697_);
v___x_706_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v_root_700_, v___x_705_, v_shift_702_, v_init_696_);
v___x_707_ = lean_array_get_size(v_tail_701_);
v___x_708_ = lean_nat_dec_lt(v___x_698_, v___x_707_);
if (v___x_708_ == 0)
{
return v___x_706_;
}
else
{
uint8_t v___x_709_; 
v___x_709_ = lean_nat_dec_le(v___x_707_, v___x_707_);
if (v___x_709_ == 0)
{
if (v___x_708_ == 0)
{
return v___x_706_;
}
else
{
size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; 
v___x_710_ = ((size_t)0ULL);
v___x_711_ = lean_usize_of_nat(v___x_707_);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_701_, v___x_710_, v___x_711_, v___x_706_);
return v___x_712_;
}
}
else
{
size_t v___x_713_; size_t v___x_714_; lean_object* v___x_715_; 
v___x_713_ = ((size_t)0ULL);
v___x_714_ = lean_usize_of_nat(v___x_707_);
v___x_715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_701_, v___x_713_, v___x_714_, v___x_706_);
return v___x_715_;
}
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_716_ = lean_nat_sub(v_start_697_, v_tailOff_703_);
v___x_717_ = lean_array_get_size(v_tail_701_);
v___x_718_ = lean_nat_dec_lt(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
lean_dec(v___x_716_);
return v_init_696_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = lean_nat_dec_le(v___x_717_, v___x_717_);
if (v___x_719_ == 0)
{
if (v___x_718_ == 0)
{
lean_dec(v___x_716_);
return v_init_696_;
}
else
{
size_t v___x_720_; size_t v___x_721_; lean_object* v___x_722_; 
v___x_720_ = lean_usize_of_nat(v___x_716_);
lean_dec(v___x_716_);
v___x_721_ = lean_usize_of_nat(v___x_717_);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_701_, v___x_720_, v___x_721_, v_init_696_);
return v___x_722_;
}
}
else
{
size_t v___x_723_; size_t v___x_724_; lean_object* v___x_725_; 
v___x_723_ = lean_usize_of_nat(v___x_716_);
lean_dec(v___x_716_);
v___x_724_ = lean_usize_of_nat(v___x_717_);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_701_, v___x_723_, v___x_724_, v_init_696_);
return v___x_725_;
}
}
}
}
else
{
lean_object* v_root_726_; lean_object* v_tail_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_root_726_ = lean_ctor_get(v_t_695_, 0);
v_tail_727_ = lean_ctor_get(v_t_695_, 1);
v___x_728_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v_root_726_, v_init_696_);
v___x_729_ = lean_array_get_size(v_tail_727_);
v___x_730_ = lean_nat_dec_lt(v___x_698_, v___x_729_);
if (v___x_730_ == 0)
{
return v___x_728_;
}
else
{
uint8_t v___x_731_; 
v___x_731_ = lean_nat_dec_le(v___x_729_, v___x_729_);
if (v___x_731_ == 0)
{
if (v___x_730_ == 0)
{
return v___x_728_;
}
else
{
size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; 
v___x_732_ = ((size_t)0ULL);
v___x_733_ = lean_usize_of_nat(v___x_729_);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_727_, v___x_732_, v___x_733_, v___x_728_);
return v___x_734_;
}
}
else
{
size_t v___x_735_; size_t v___x_736_; lean_object* v___x_737_; 
v___x_735_ = ((size_t)0ULL);
v___x_736_ = lean_usize_of_nat(v___x_729_);
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_727_, v___x_735_, v___x_736_, v___x_728_);
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0___boxed(lean_object* v_t_738_, lean_object* v_init_739_, lean_object* v_start_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_t_738_, v_init_739_, v_start_740_);
lean_dec(v_start_740_);
lean_dec_ref(v_t_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(lean_object* v_lctx_742_, lean_object* v_init_743_, lean_object* v_start_744_){
_start:
{
lean_object* v_decls_745_; lean_object* v___x_746_; 
v_decls_745_ = lean_ctor_get(v_lctx_742_, 1);
v___x_746_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_decls_745_, v_init_743_, v_start_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0___boxed(lean_object* v_lctx_747_, lean_object* v_init_748_, lean_object* v_start_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_747_, v_init_748_, v_start_749_);
lean_dec(v_start_749_);
lean_dec_ref(v_lctx_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lam__0(lean_object* v_fvarId_751_, lean_object* v_mvarId_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_751_, v___y_753_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v_lctx_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
v_lctx_760_ = lean_ctor_get(v___y_753_, 2);
v___x_761_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_762_ = l_Lean_LocalDecl_index(v_a_759_);
lean_dec(v_a_759_);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v___x_762_, v___x_763_);
lean_dec(v___x_762_);
v___x_765_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_760_, v___x_761_, v___x_764_);
lean_dec(v___x_764_);
v___x_766_ = 1;
v___x_767_ = l_Lean_MVarId_revert(v_mvarId_752_, v___x_765_, v___x_766_, v___x_766_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
return v___x_767_;
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v_mvarId_752_);
v_a_768_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_758_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_758_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lam__0___boxed(lean_object* v_fvarId_776_, lean_object* v_mvarId_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_MVarId_revertAfter___lam__0(v_fvarId_776_, v_mvarId_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter(lean_object* v_mvarId_784_, lean_object* v_fvarId_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___f_791_; lean_object* v___x_792_; 
lean_inc(v_mvarId_784_);
v___f_791_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertAfter___lam__0___boxed), 7, 2);
lean_closure_set(v___f_791_, 0, v_fvarId_785_);
lean_closure_set(v___f_791_, 1, v_mvarId_784_);
v___x_792_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_784_, v___f_791_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___boxed(lean_object* v_mvarId_793_, lean_object* v_fvarId_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_MVarId_revertAfter(v_mvarId_793_, v_fvarId_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___lam__0(lean_object* v_fvarId_801_, lean_object* v_mvarId_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_801_, v___y_803_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v_lctx_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_815_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v_lctx_810_ = lean_ctor_get(v___y_803_, 2);
v___x_811_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_812_ = l_Lean_LocalDecl_index(v_a_809_);
lean_dec(v_a_809_);
v___x_813_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_810_, v___x_811_, v___x_812_);
lean_dec(v___x_812_);
v___x_814_ = 1;
v___x_815_ = l_Lean_MVarId_revert(v_mvarId_802_, v___x_813_, v___x_814_, v___x_814_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
return v___x_815_;
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_mvarId_802_);
v_a_816_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_808_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_808_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___lam__0___boxed(lean_object* v_fvarId_824_, lean_object* v_mvarId_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_MVarId_revertFrom___lam__0(v_fvarId_824_, v_mvarId_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom(lean_object* v_mvarId_832_, lean_object* v_fvarId_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___f_839_; lean_object* v___x_840_; 
lean_inc(v_mvarId_832_);
v___f_839_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertFrom___lam__0___boxed), 7, 2);
lean_closure_set(v___f_839_, 0, v_fvarId_833_);
lean_closure_set(v___f_839_, 1, v_mvarId_832_);
v___x_840_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_832_, v___f_839_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___boxed(lean_object* v_mvarId_841_, lean_object* v_fvarId_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_MVarId_revertFrom(v_mvarId_841_, v_fvarId_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(lean_object* v_as_849_, size_t v_sz_850_, size_t v_i_851_, lean_object* v_b_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
uint8_t v___x_857_; 
v___x_857_ = lean_usize_dec_lt(v_i_851_, v_sz_850_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v_b_852_);
return v___x_858_;
}
else
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_array_uget_borrowed(v_as_849_, v_i_851_);
lean_inc(v_a_859_);
v___x_860_ = l_Lean_FVarId_getDecl___redArg(v_a_859_, v___y_853_, v___y_854_, v___y_855_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v_a_863_; uint8_t v___x_867_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_867_ = l_Lean_LocalDecl_isAuxDecl(v_a_861_);
lean_dec(v_a_861_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_inc(v_a_859_);
v___x_868_ = lean_array_push(v_b_852_, v_a_859_);
v_a_863_ = v___x_868_;
goto v___jp_862_;
}
else
{
v_a_863_ = v_b_852_;
goto v___jp_862_;
}
v___jp_862_:
{
size_t v___x_864_; size_t v___x_865_; 
v___x_864_ = ((size_t)1ULL);
v___x_865_ = lean_usize_add(v_i_851_, v___x_864_);
v_i_851_ = v___x_865_;
v_b_852_ = v_a_863_;
goto _start;
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref(v_b_852_);
v_a_869_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_860_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_860_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg___boxed(lean_object* v_as_877_, lean_object* v_sz_878_, lean_object* v_i_879_, lean_object* v_b_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
size_t v_sz_boxed_885_; size_t v_i_boxed_886_; lean_object* v_res_887_; 
v_sz_boxed_885_ = lean_unbox_usize(v_sz_878_);
lean_dec(v_sz_878_);
v_i_boxed_886_ = lean_unbox_usize(v_i_879_);
lean_dec(v_i_879_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_877_, v_sz_boxed_885_, v_i_boxed_886_, v_b_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec_ref(v_as_877_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lam__0(lean_object* v_mvarId_888_, lean_object* v___x_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; 
lean_inc(v_mvarId_888_);
v___x_895_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_888_, v___x_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_lctx_896_; lean_object* v___x_897_; lean_object* v___x_898_; size_t v_sz_899_; size_t v___x_900_; lean_object* v___x_901_; 
lean_dec_ref_known(v___x_895_, 1);
v_lctx_896_ = lean_ctor_get(v___y_890_, 2);
v___x_897_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_898_ = l_Lean_LocalContext_getFVarIds(v_lctx_896_);
v_sz_899_ = lean_array_size(v___x_898_);
v___x_900_ = ((size_t)0ULL);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v___x_898_, v_sz_899_, v___x_900_, v___x_897_, v___y_890_, v___y_892_, v___y_893_);
lean_dec_ref(v___x_898_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; uint8_t v___x_903_; lean_object* v___x_904_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v___x_903_ = 1;
v___x_904_ = l_Lean_MVarId_revert(v_mvarId_888_, v_a_902_, v___x_903_, v___x_903_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_913_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_913_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_913_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_913_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v_snd_909_; lean_object* v___x_911_; 
v_snd_909_ = lean_ctor_get(v_a_905_, 1);
lean_inc(v_snd_909_);
lean_dec(v_a_905_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v_snd_909_);
v___x_911_ = v___x_907_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_snd_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
v_a_914_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_904_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_904_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_mvarId_888_);
v_a_922_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_901_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_901_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_mvarId_888_);
v_a_930_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_895_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_895_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lam__0___boxed(lean_object* v_mvarId_938_, lean_object* v___x_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_MVarId_revertAll___lam__0(v_mvarId_938_, v___x_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll(lean_object* v_mvarId_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; lean_object* v___f_956_; lean_object* v___x_957_; 
v___x_955_ = ((lean_object*)(l_Lean_MVarId_revertAll___closed__1));
lean_inc(v_mvarId_949_);
v___f_956_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertAll___lam__0___boxed), 7, 2);
lean_closure_set(v___f_956_, 0, v_mvarId_949_);
lean_closure_set(v___f_956_, 1, v___x_955_);
v___x_957_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_949_, v___f_956_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___boxed(lean_object* v_mvarId_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_MVarId_revertAll(v_mvarId_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(lean_object* v_as_965_, size_t v_sz_966_, size_t v_i_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_965_, v_sz_966_, v_i_967_, v_b_968_, v___y_969_, v___y_971_, v___y_972_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___boxed(lean_object* v_as_975_, lean_object* v_sz_976_, lean_object* v_i_977_, lean_object* v_b_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
size_t v_sz_boxed_984_; size_t v_i_boxed_985_; lean_object* v_res_986_; 
v_sz_boxed_984_ = lean_unbox_usize(v_sz_976_);
lean_dec(v_sz_976_);
v_i_boxed_985_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_res_986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(v_as_975_, v_sz_boxed_984_, v_i_boxed_985_, v_b_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec_ref(v_as_975_);
return v_res_986_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Clear(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Clear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Revert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Revert(builtin);
}
#ifdef __cplusplus
}
#endif
