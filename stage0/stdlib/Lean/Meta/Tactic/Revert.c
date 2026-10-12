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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
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
static const lean_string_object l_Lean_MVarId_revert___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "failed to create binder due to failure when reverting variable dependencies"};
static const lean_object* l_Lean_MVarId_revert___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_revert___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_revert___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_revert___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(lean_object* v_mvarId_1_, lean_object* v_x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v_res_25_;
v_res_25_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_1_, v_x_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg___boxed(lean_object* v_mvarId_26_, lean_object* v_x_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_26_, v_x_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
return v_res_33_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5(lean_object* v_00_u03b1_34_, lean_object* v_mvarId_35_, lean_object* v_x_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_35_, v_x_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
return v___x_42_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_35_ = stack[1].m_obj;
lean_object* v_x_36_ = stack[2].m_obj;
lean_object* v___y_37_ = stack[3].m_obj;
lean_object* v___y_38_ = stack[4].m_obj;
lean_object* v___y_39_ = stack[5].m_obj;
lean_object* v___y_40_ = stack[6].m_obj;
lean_object* v_res_43_;
v_res_43_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5(lean_box(0), v_mvarId_35_, v_x_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___boxed(lean_object* v_00_u03b1_44_, lean_object* v_mvarId_45_, lean_object* v_x_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5(v_00_u03b1_44_, v_mvarId_45_, v_x_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
return v_res_52_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(lean_object* v_msgData_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; lean_object* v_env_60_; uint8_t v___x_61_; lean_object* v_env_62_; lean_object* v___x_63_; lean_object* v_toCold_64_; lean_object* v_mctx_65_; lean_object* v_lctx_66_; lean_object* v_options_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_59_ = lean_st_ref_get(v___y_57_);
v_env_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_env_60_);
lean_dec(v___x_59_);
v___x_61_ = 0;
v_env_62_ = l_Lean_Environment_setRecordingDeps(v_env_60_, v___x_61_);
v___x_63_ = lean_st_ref_get(v___y_55_);
v_toCold_64_ = lean_ctor_get(v___y_56_, 0);
v_mctx_65_ = lean_ctor_get(v___x_63_, 0);
lean_inc_ref(v_mctx_65_);
lean_dec(v___x_63_);
v_lctx_66_ = lean_ctor_get(v___y_54_, 2);
v_options_67_ = lean_ctor_get(v_toCold_64_, 2);
lean_inc_ref(v_options_67_);
lean_inc_ref(v_lctx_66_);
v___x_68_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_68_, 0, v_env_62_);
lean_ctor_set(v___x_68_, 1, v_mctx_65_);
lean_ctor_set(v___x_68_, 2, v_lctx_66_);
lean_ctor_set(v___x_68_, 3, v_options_67_);
v___x_69_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v_msgData_53_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_53_ = stack[0].m_obj;
lean_object* v___y_54_ = stack[1].m_obj;
lean_object* v___y_55_ = stack[2].m_obj;
lean_object* v___y_56_ = stack[3].m_obj;
lean_object* v___y_57_ = stack[4].m_obj;
lean_object* v_res_71_;
v_res_71_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(v_msgData_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3___boxed(lean_object* v_msgData_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(v_msgData_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
return v_res_78_;
}
}
lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(lean_object* v_msg_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_ref_85_; lean_object* v___x_86_; lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_95_; 
v_ref_85_ = lean_ctor_get(v___y_82_, 2);
v___x_86_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(v_msg_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_95_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
lean_inc(v_ref_85_);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_ref_85_);
lean_ctor_set(v___x_91_, 1, v_a_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 1);
lean_ctor_set(v___x_89_, 0, v___x_91_);
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_79_ = stack[0].m_obj;
lean_object* v___y_80_ = stack[1].m_obj;
lean_object* v___y_81_ = stack[2].m_obj;
lean_object* v___y_82_ = stack[3].m_obj;
lean_object* v___y_83_ = stack[4].m_obj;
lean_object* v_res_96_;
v_res_96_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v_msg_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
stack->m_obj
 = v_res_96_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg___boxed(lean_object* v_msg_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v_msg_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_103_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0));
v___x_106_ = l_Lean_stringToMessageData(v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2));
v___x_109_ = l_Lean_stringToMessageData(v___x_108_);
return v___x_109_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(lean_object* v_as_110_, size_t v_sz_111_, size_t v_i_112_, lean_object* v_b_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_a_120_; uint8_t v___x_124_; 
v___x_124_ = lean_usize_dec_lt(v_i_112_, v_sz_111_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v_b_113_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v_a_127_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
v_a_127_ = lean_array_uget_borrowed(v_as_110_, v_i_112_);
lean_inc(v_a_127_);
v___x_128_ = l_Lean_FVarId_getDecl___redArg(v_a_127_, v___y_114_, v___y_116_, v___y_117_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; uint8_t v___x_130_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
lean_dec_ref_known(v___x_128_, 1);
v___x_130_ = l_Lean_LocalDecl_isAuxDecl(v_a_129_);
lean_dec(v_a_129_);
if (v___x_130_ == 0)
{
v_a_120_ = v___x_126_;
goto v___jp_119_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_131_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1);
lean_inc(v_a_127_);
v___x_132_ = l_Lean_mkFVar(v_a_127_);
v___x_133_ = l_Lean_MessageData_ofExpr(v___x_132_);
v___x_134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_131_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3);
v___x_136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v___x_136_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_dec_ref_known(v___x_137_, 1);
v_a_120_ = v___x_126_;
goto v___jp_119_;
}
else
{
return v___x_137_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_128_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_128_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
v___jp_119_:
{
size_t v___x_121_; size_t v___x_122_; 
v___x_121_ = ((size_t)1ULL);
v___x_122_ = lean_usize_add(v_i_112_, v___x_121_);
v_i_112_ = v___x_122_;
v_b_113_ = v_a_120_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_110_ = stack[0].m_obj;
size_t v_sz_111_ = stack[1].m_num;
size_t v_i_112_ = stack[2].m_num;
lean_object* v_b_113_ = stack[3].m_obj;
lean_object* v___y_114_ = stack[4].m_obj;
lean_object* v___y_115_ = stack[5].m_obj;
lean_object* v___y_116_ = stack[6].m_obj;
lean_object* v___y_117_ = stack[7].m_obj;
lean_object* v_res_146_;
v_res_146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_as_110_, v_sz_111_, v_i_112_, v_b_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___boxed(lean_object* v_as_147_, lean_object* v_sz_148_, lean_object* v_i_149_, lean_object* v_b_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
size_t v_sz_boxed_156_; size_t v_i_boxed_157_; lean_object* v_res_158_; 
v_sz_boxed_156_ = lean_unbox_usize(v_sz_148_);
lean_dec(v_sz_148_);
v_i_boxed_157_ = lean_unbox_usize(v_i_149_);
lean_dec(v_i_149_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_as_147_, v_sz_boxed_156_, v_i_boxed_157_, v_b_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec_ref(v_as_147_);
return v_res_158_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(size_t v_sz_159_, size_t v_i_160_, lean_object* v_bs_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = lean_usize_dec_lt(v_i_160_, v_sz_159_);
if (v___x_162_ == 0)
{
return v_bs_161_;
}
else
{
lean_object* v_v_163_; lean_object* v___x_164_; lean_object* v_bs_x27_165_; lean_object* v___x_166_; size_t v___x_167_; size_t v___x_168_; lean_object* v___x_169_; 
v_v_163_ = lean_array_uget(v_bs_161_, v_i_160_);
v___x_164_ = lean_unsigned_to_nat(0u);
v_bs_x27_165_ = lean_array_uset(v_bs_161_, v_i_160_, v___x_164_);
v___x_166_ = l_Lean_mkFVar(v_v_163_);
v___x_167_ = ((size_t)1ULL);
v___x_168_ = lean_usize_add(v_i_160_, v___x_167_);
v___x_169_ = lean_array_uset(v_bs_x27_165_, v_i_160_, v___x_166_);
v_i_160_ = v___x_168_;
v_bs_161_ = v___x_169_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_159_ = stack[0].m_num;
size_t v_i_160_ = stack[1].m_num;
lean_object* v_bs_161_ = stack[2].m_obj;
lean_object* v_res_171_;
v_res_171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(v_sz_159_, v_i_160_, v_bs_161_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0___boxed(lean_object* v_sz_172_, lean_object* v_i_173_, lean_object* v_bs_174_){
_start:
{
size_t v_sz_boxed_175_; size_t v_i_boxed_176_; lean_object* v_res_177_; 
v_sz_boxed_175_ = lean_unbox_usize(v_sz_172_);
lean_dec(v_sz_172_);
v_i_boxed_176_ = lean_unbox_usize(v_i_173_);
lean_dec(v_i_173_);
v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(v_sz_boxed_175_, v_i_boxed_176_, v_bs_174_);
return v_res_177_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(size_t v_sz_178_, size_t v_i_179_, lean_object* v_bs_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_lt(v_i_179_, v_sz_178_);
if (v___x_181_ == 0)
{
return v_bs_180_;
}
else
{
lean_object* v_v_182_; lean_object* v___x_183_; lean_object* v_bs_x27_184_; lean_object* v___x_185_; size_t v___x_186_; size_t v___x_187_; lean_object* v___x_188_; 
v_v_182_ = lean_array_uget(v_bs_180_, v_i_179_);
v___x_183_ = lean_unsigned_to_nat(0u);
v_bs_x27_184_ = lean_array_uset(v_bs_180_, v_i_179_, v___x_183_);
v___x_185_ = l_Lean_Expr_fvarId_x21(v_v_182_);
lean_dec(v_v_182_);
v___x_186_ = ((size_t)1ULL);
v___x_187_ = lean_usize_add(v_i_179_, v___x_186_);
v___x_188_ = lean_array_uset(v_bs_x27_184_, v_i_179_, v___x_185_);
v_i_179_ = v___x_187_;
v_bs_180_ = v___x_188_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_178_ = stack[0].m_num;
size_t v_i_179_ = stack[1].m_num;
lean_object* v_bs_180_ = stack[2].m_obj;
lean_object* v_res_190_;
v_res_190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(v_sz_178_, v_i_179_, v_bs_180_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2___boxed(lean_object* v_sz_191_, lean_object* v_i_192_, lean_object* v_bs_193_){
_start:
{
size_t v_sz_boxed_194_; size_t v_i_boxed_195_; lean_object* v_res_196_; 
v_sz_boxed_194_ = lean_unbox_usize(v_sz_191_);
lean_dec(v_sz_191_);
v_i_boxed_195_ = lean_unbox_usize(v_i_192_);
lean_dec(v_i_192_);
v_res_196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(v_sz_boxed_194_, v_i_boxed_195_, v_bs_193_);
return v_res_196_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(lean_object* v_as_197_, size_t v_sz_198_, size_t v_i_199_, lean_object* v_b_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_a_207_; uint8_t v___x_211_; 
v___x_211_ = lean_usize_dec_lt(v_i_199_, v_sz_198_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v_b_200_);
return v___x_212_;
}
else
{
lean_object* v_fst_213_; lean_object* v_snd_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_248_; 
v_fst_213_ = lean_ctor_get(v_b_200_, 0);
v_snd_214_ = lean_ctor_get(v_b_200_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_b_200_);
if (v_isSharedCheck_248_ == 0)
{
v___x_216_ = v_b_200_;
v_isShared_217_ = v_isSharedCheck_248_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_snd_214_);
lean_inc(v_fst_213_);
lean_dec(v_b_200_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_248_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_a_218_ = lean_array_uget_borrowed(v_as_197_, v_i_199_);
v___x_219_ = l_Lean_Expr_fvarId_x21(v_a_218_);
lean_inc(v___x_219_);
v___x_220_ = l_Lean_FVarId_getDecl___redArg(v___x_219_, v___y_201_, v___y_203_, v___y_204_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; uint8_t v___x_222_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
v___x_222_ = l_Lean_LocalDecl_isAuxDecl(v_a_221_);
lean_dec(v_a_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_225_; 
lean_dec(v___x_219_);
lean_inc(v_a_218_);
v___x_223_ = lean_array_push(v_snd_214_, v_a_218_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_223_);
v___x_225_ = v___x_216_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_fst_213_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
v_a_207_ = v___x_225_;
goto v___jp_206_;
}
}
else
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_MVarId_clear(v_fst_213_, v___x_219_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v_a_228_);
v___x_230_ = v___x_216_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_228_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_snd_214_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
v_a_207_ = v___x_230_;
goto v___jp_206_;
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_del_object(v___x_216_);
lean_dec(v_snd_214_);
v_a_232_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_227_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_227_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec(v___x_219_);
lean_del_object(v___x_216_);
lean_dec(v_snd_214_);
lean_dec(v_fst_213_);
v_a_240_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_220_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_220_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
v___jp_206_:
{
size_t v___x_208_; size_t v___x_209_; 
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_add(v_i_199_, v___x_208_);
v_i_199_ = v___x_209_;
v_b_200_ = v_a_207_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_197_ = stack[0].m_obj;
size_t v_sz_198_ = stack[1].m_num;
size_t v_i_199_ = stack[2].m_num;
lean_object* v_b_200_ = stack[3].m_obj;
lean_object* v___y_201_ = stack[4].m_obj;
lean_object* v___y_202_ = stack[5].m_obj;
lean_object* v___y_203_ = stack[6].m_obj;
lean_object* v___y_204_ = stack[7].m_obj;
lean_object* v_res_249_;
v_res_249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_as_197_, v_sz_198_, v_i_199_, v_b_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1___boxed(lean_object* v_as_250_, lean_object* v_sz_251_, lean_object* v_i_252_, lean_object* v_b_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
size_t v_sz_boxed_259_; size_t v_i_boxed_260_; lean_object* v_res_261_; 
v_sz_boxed_259_ = lean_unbox_usize(v_sz_251_);
lean_dec(v_sz_251_);
v_i_boxed_260_ = lean_unbox_usize(v_i_252_);
lean_dec(v_i_252_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_as_250_, v_sz_boxed_259_, v_i_boxed_260_, v_b_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec_ref(v_as_250_);
return v_res_261_;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lam__0___closed__0(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_box(0);
v___x_263_ = lean_unsigned_to_nat(16u);
v___x_264_ = lean_mk_array(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lam__0___closed__2(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_MVarId_revert___lam__0___closed__1));
v___x_267_ = l_Lean_stringToMessageData(v___x_266_);
return v___x_267_;
}
}
lean_object* l_Lean_MVarId_revert___lam__0(lean_object* v_fvarIds_268_, uint8_t v_preserveOrder_269_, uint8_t v___x_270_, lean_object* v___x_271_, lean_object* v_mvarId_272_, lean_object* v___x_273_, uint8_t v_clearAuxDeclsInsteadOfRevert_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___y_281_; uint8_t v___y_282_; lean_object* v___y_283_; size_t v___y_284_; lean_object* v___y_285_; lean_object* v_a_286_; lean_object* v___x_500_; 
lean_inc(v_mvarId_272_);
v___x_500_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_272_, v___x_273_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_dec_ref_known(v___x_500_, 1);
if (v_clearAuxDeclsInsteadOfRevert_274_ == 0)
{
lean_object* v___x_501_; size_t v_sz_502_; size_t v___x_503_; lean_object* v___x_504_; 
v___x_501_ = lean_box(0);
v_sz_502_ = lean_array_size(v_fvarIds_268_);
v___x_503_ = ((size_t)0ULL);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_fvarIds_268_, v_sz_502_, v___x_503_, v___x_501_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_dec_ref_known(v___x_504_, 1);
goto v___jp_335_;
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_mvarId_272_);
lean_dec(v___x_271_);
lean_dec_ref(v_fvarIds_268_);
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
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
}
else
{
goto v___jp_335_;
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_mvarId_272_);
lean_dec(v___x_271_);
lean_dec_ref(v_fvarIds_268_);
v_a_513_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_500_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_500_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
v___jp_280_:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_MVarId_setKind___redArg(v___y_283_, v___y_282_, v___y_281_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_fst_288_; lean_object* v_snd_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref_known(v___x_287_, 1);
v_fst_288_ = lean_ctor_get(v_a_286_, 0);
v_snd_289_ = lean_ctor_get(v_a_286_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_a_286_);
if (v_isSharedCheck_326_ == 0)
{
v___x_291_ = v_a_286_;
v_isShared_292_ = v_isSharedCheck_326_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_snd_289_);
lean_inc(v_fst_288_);
lean_dec(v_a_286_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_326_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = l_Lean_Expr_getAppFn(v_fst_288_);
lean_dec(v_fst_288_);
v___x_294_ = l_Lean_Expr_mvarId_x21(v___x_293_);
lean_dec_ref(v___x_293_);
lean_inc(v___x_294_);
v___x_295_ = l_Lean_MVarId_setKind___redArg(v___x_294_, v___y_282_, v___y_281_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v___x_296_; 
lean_dec_ref_known(v___x_295_, 1);
lean_inc(v___x_294_);
v___x_296_ = l_Lean_MVarId_setTag___redArg(v___x_294_, v___y_285_, v___y_281_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_308_; 
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v___x_296_, 0);
lean_dec(v_unused_309_);
v___x_298_ = v___x_296_;
v_isShared_299_ = v_isSharedCheck_308_;
goto v_resetjp_297_;
}
else
{
lean_dec(v___x_296_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_308_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
size_t v_sz_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v_sz_300_ = lean_array_size(v_snd_289_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(v_sz_300_, v___y_284_, v_snd_289_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v___x_294_);
lean_ctor_set(v___x_291_, 0, v___x_301_);
v___x_303_ = v___x_291_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_294_);
v___x_303_ = v_reuseFailAlloc_307_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_305_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_303_);
v___x_305_ = v___x_298_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
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
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec(v___x_294_);
lean_del_object(v___x_291_);
lean_dec(v_snd_289_);
v_a_310_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_296_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_296_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec(v___x_294_);
lean_del_object(v___x_291_);
lean_dec(v_snd_289_);
lean_dec(v___y_285_);
v_a_318_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_295_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_295_);
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
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_a_286_);
lean_dec(v___y_285_);
v_a_327_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_287_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_287_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
v___jp_335_:
{
size_t v_sz_336_; size_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_sz_336_ = lean_array_size(v_fvarIds_268_);
v___x_337_ = ((size_t)0ULL);
v___x_338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(v_sz_336_, v___x_337_, v_fvarIds_268_);
v___x_339_ = l_Lean_Meta_collectForwardDeps(v___x_338_, v_preserveOrder_269_, v___x_270_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v___x_342_; size_t v_sz_343_; lean_object* v___x_344_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 1);
v___x_341_ = lean_mk_empty_array_with_capacity(v___x_271_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_mvarId_272_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v_sz_343_ = lean_array_size(v_a_340_);
v___x_344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_a_340_, v_sz_343_, v___x_337_, v___x_342_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v_a_340_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v_fst_346_; lean_object* v_snd_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_483_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v_fst_346_ = lean_ctor_get(v_a_345_, 0);
v_snd_347_ = lean_ctor_get(v_a_345_, 1);
v_isSharedCheck_483_ = !lean_is_exclusive(v_a_345_);
if (v_isSharedCheck_483_ == 0)
{
v___x_349_ = v_a_345_;
v_isShared_350_ = v_isSharedCheck_483_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_snd_347_);
lean_inc(v_fst_346_);
lean_dec(v_a_345_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_483_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; 
lean_inc(v_fst_346_);
v___x_351_ = l_Lean_MVarId_getTag(v_fst_346_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; uint8_t v___x_353_; lean_object* v___x_354_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = 0;
lean_inc(v_fst_346_);
v___x_354_ = l_Lean_MVarId_setKind___redArg(v_fst_346_, v___x_353_, v___y_276_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_lctx_355_; uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v_mctx_358_; lean_object* v___x_359_; lean_object* v_ngen_360_; lean_object* v___x_361_; lean_object* v_toCold_362_; lean_object* v_quotContext_363_; lean_object* v_nextMacroScope_364_; lean_object* v___x_366_; 
lean_dec_ref_known(v___x_354_, 1);
v_lctx_355_ = lean_ctor_get(v___y_275_, 2);
v___x_356_ = 2;
v___x_357_ = lean_st_ref_get(v___y_276_);
v_mctx_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc_ref(v_mctx_358_);
lean_dec(v___x_357_);
v___x_359_ = lean_st_ref_get(v___y_278_);
v_ngen_360_ = lean_ctor_get(v___x_359_, 2);
lean_inc_ref(v_ngen_360_);
lean_dec(v___x_359_);
v___x_361_ = lean_st_ref_get(v___y_278_);
v_toCold_362_ = lean_ctor_get(v___y_277_, 0);
v_quotContext_363_ = lean_ctor_get(v_toCold_362_, 8);
v_nextMacroScope_364_ = lean_ctor_get(v___x_361_, 1);
lean_inc(v_nextMacroScope_364_);
lean_dec(v___x_361_);
lean_inc_ref(v_lctx_355_);
lean_inc(v_quotContext_363_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v_lctx_355_);
lean_ctor_set(v___x_349_, 0, v_quotContext_363_);
v___x_366_ = v___x_349_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_quotContext_363_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_lctx_355_);
v___x_366_ = v_reuseFailAlloc_466_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = lean_obj_once(&l_Lean_MVarId_revert___lam__0___closed__0, &l_Lean_MVarId_revert___lam__0___closed__0_once, _init_l_Lean_MVarId_revert___lam__0___closed__0);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_271_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_369_, 0, v_mctx_358_);
lean_ctor_set(v___x_369_, 1, v_nextMacroScope_364_);
lean_ctor_set(v___x_369_, 2, v_ngen_360_);
lean_ctor_set(v___x_369_, 3, v___x_368_);
lean_inc(v_fst_346_);
v___x_370_ = l_Lean_MetavarContext_revert(v_snd_347_, v_fst_346_, v_preserveOrder_269_, v___x_366_, v___x_369_);
lean_dec_ref(v___x_366_);
lean_dec(v_snd_347_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v_a_372_; lean_object* v_mctx_373_; lean_object* v_nextMacroScope_374_; lean_object* v_ngen_375_; lean_object* v___x_376_; lean_object* v_cache_377_; lean_object* v_zetaDeltaFVarIds_378_; lean_object* v_postponed_379_; lean_object* v_diag_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_407_; 
v_a_371_ = lean_ctor_get(v___x_370_, 1);
lean_inc(v_a_371_);
v_a_372_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_370_, 2);
v_mctx_373_ = lean_ctor_get(v_a_371_, 0);
lean_inc_ref(v_mctx_373_);
v_nextMacroScope_374_ = lean_ctor_get(v_a_371_, 1);
lean_inc(v_nextMacroScope_374_);
v_ngen_375_ = lean_ctor_get(v_a_371_, 2);
lean_inc_ref(v_ngen_375_);
lean_dec(v_a_371_);
v___x_376_ = lean_st_ref_take(v___y_276_);
v_cache_377_ = lean_ctor_get(v___x_376_, 1);
v_zetaDeltaFVarIds_378_ = lean_ctor_get(v___x_376_, 2);
v_postponed_379_ = lean_ctor_get(v___x_376_, 3);
v_diag_380_ = lean_ctor_get(v___x_376_, 4);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v___x_376_, 0);
lean_dec(v_unused_408_);
v___x_382_ = v___x_376_;
v_isShared_383_ = v_isSharedCheck_407_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_diag_380_);
lean_inc(v_postponed_379_);
lean_inc(v_zetaDeltaFVarIds_378_);
lean_inc(v_cache_377_);
lean_dec(v___x_376_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_407_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_mctx_373_);
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_mctx_373_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_cache_377_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_zetaDeltaFVarIds_378_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_postponed_379_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_diag_380_);
v___x_385_ = v_reuseFailAlloc_406_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_env_388_; lean_object* v_auxDeclNGen_389_; lean_object* v_traceState_390_; lean_object* v_cache_391_; lean_object* v_recordedDeps_392_; lean_object* v_messages_393_; lean_object* v_infoState_394_; lean_object* v_snapshotTasks_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
v___x_386_ = lean_st_ref_put(v___y_276_, v___x_385_);
v___x_387_ = lean_st_ref_take(v___y_278_);
v_env_388_ = lean_ctor_get(v___x_387_, 0);
v_auxDeclNGen_389_ = lean_ctor_get(v___x_387_, 3);
v_traceState_390_ = lean_ctor_get(v___x_387_, 4);
v_cache_391_ = lean_ctor_get(v___x_387_, 5);
v_recordedDeps_392_ = lean_ctor_get(v___x_387_, 6);
v_messages_393_ = lean_ctor_get(v___x_387_, 7);
v_infoState_394_ = lean_ctor_get(v___x_387_, 8);
v_snapshotTasks_395_ = lean_ctor_get(v___x_387_, 9);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; lean_object* v_unused_405_; 
v_unused_404_ = lean_ctor_get(v___x_387_, 2);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v___x_387_, 1);
lean_dec(v_unused_405_);
v___x_397_ = v___x_387_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_snapshotTasks_395_);
lean_inc(v_infoState_394_);
lean_inc(v_messages_393_);
lean_inc(v_recordedDeps_392_);
lean_inc(v_cache_391_);
lean_inc(v_traceState_390_);
lean_inc(v_auxDeclNGen_389_);
lean_inc(v_env_388_);
lean_dec(v___x_387_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 2, v_ngen_375_);
lean_ctor_set(v___x_397_, 1, v_nextMacroScope_374_);
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_env_388_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_nextMacroScope_374_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_ngen_375_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_auxDeclNGen_389_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_traceState_390_);
lean_ctor_set(v_reuseFailAlloc_402_, 5, v_cache_391_);
lean_ctor_set(v_reuseFailAlloc_402_, 6, v_recordedDeps_392_);
lean_ctor_set(v_reuseFailAlloc_402_, 7, v_messages_393_);
lean_ctor_set(v_reuseFailAlloc_402_, 8, v_infoState_394_);
lean_ctor_set(v_reuseFailAlloc_402_, 9, v_snapshotTasks_395_);
v___x_400_ = v_reuseFailAlloc_402_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; 
v___x_401_ = lean_st_ref_put(v___y_278_, v___x_400_);
v___y_281_ = v___y_276_;
v___y_282_ = v___x_356_;
v___y_283_ = v_fst_346_;
v___y_284_ = v___x_337_;
v___y_285_ = v_a_352_;
v_a_286_ = v_a_372_;
goto v___jp_280_;
}
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v_mctx_410_; lean_object* v_nextMacroScope_411_; lean_object* v_ngen_412_; lean_object* v___x_413_; lean_object* v_cache_414_; lean_object* v_zetaDeltaFVarIds_415_; lean_object* v_postponed_416_; lean_object* v_diag_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_a_352_);
v_a_409_ = lean_ctor_get(v___x_370_, 1);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_370_, 2);
v_mctx_410_ = lean_ctor_get(v_a_409_, 0);
lean_inc_ref(v_mctx_410_);
v_nextMacroScope_411_ = lean_ctor_get(v_a_409_, 1);
lean_inc(v_nextMacroScope_411_);
v_ngen_412_ = lean_ctor_get(v_a_409_, 2);
lean_inc_ref(v_ngen_412_);
lean_dec(v_a_409_);
v___x_413_ = lean_st_ref_take(v___y_276_);
v_cache_414_ = lean_ctor_get(v___x_413_, 1);
v_zetaDeltaFVarIds_415_ = lean_ctor_get(v___x_413_, 2);
v_postponed_416_ = lean_ctor_get(v___x_413_, 3);
v_diag_417_ = lean_ctor_get(v___x_413_, 4);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_413_, 0);
lean_dec(v_unused_465_);
v___x_419_ = v___x_413_;
v_isShared_420_ = v_isSharedCheck_464_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_diag_417_);
lean_inc(v_postponed_416_);
lean_inc(v_zetaDeltaFVarIds_415_);
lean_inc(v_cache_414_);
lean_dec(v___x_413_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_464_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v_mctx_410_);
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_mctx_410_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_cache_414_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_zetaDeltaFVarIds_415_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_postponed_416_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_diag_417_);
v___x_422_ = v_reuseFailAlloc_463_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_env_425_; lean_object* v_auxDeclNGen_426_; lean_object* v_traceState_427_; lean_object* v_cache_428_; lean_object* v_recordedDeps_429_; lean_object* v_messages_430_; lean_object* v_infoState_431_; lean_object* v_snapshotTasks_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_460_; 
v___x_423_ = lean_st_ref_put(v___y_276_, v___x_422_);
v___x_424_ = lean_st_ref_take(v___y_278_);
v_env_425_ = lean_ctor_get(v___x_424_, 0);
v_auxDeclNGen_426_ = lean_ctor_get(v___x_424_, 3);
v_traceState_427_ = lean_ctor_get(v___x_424_, 4);
v_cache_428_ = lean_ctor_get(v___x_424_, 5);
v_recordedDeps_429_ = lean_ctor_get(v___x_424_, 6);
v_messages_430_ = lean_ctor_get(v___x_424_, 7);
v_infoState_431_ = lean_ctor_get(v___x_424_, 8);
v_snapshotTasks_432_ = lean_ctor_get(v___x_424_, 9);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; lean_object* v_unused_462_; 
v_unused_461_ = lean_ctor_get(v___x_424_, 2);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v___x_424_, 1);
lean_dec(v_unused_462_);
v___x_434_ = v___x_424_;
v_isShared_435_ = v_isSharedCheck_460_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_snapshotTasks_432_);
lean_inc(v_infoState_431_);
lean_inc(v_messages_430_);
lean_inc(v_recordedDeps_429_);
lean_inc(v_cache_428_);
lean_inc(v_traceState_427_);
lean_inc(v_auxDeclNGen_426_);
lean_inc(v_env_425_);
lean_dec(v___x_424_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_460_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 2, v_ngen_412_);
lean_ctor_set(v___x_434_, 1, v_nextMacroScope_411_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_env_425_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_nextMacroScope_411_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_ngen_412_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_auxDeclNGen_426_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_traceState_427_);
lean_ctor_set(v_reuseFailAlloc_459_, 5, v_cache_428_);
lean_ctor_set(v_reuseFailAlloc_459_, 6, v_recordedDeps_429_);
lean_ctor_set(v_reuseFailAlloc_459_, 7, v_messages_430_);
lean_ctor_set(v_reuseFailAlloc_459_, 8, v_infoState_431_);
lean_ctor_set(v_reuseFailAlloc_459_, 9, v_snapshotTasks_432_);
v___x_437_ = v_reuseFailAlloc_459_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_a_441_; lean_object* v___x_442_; 
v___x_438_ = lean_st_ref_put(v___y_278_, v___x_437_);
v___x_439_ = lean_obj_once(&l_Lean_MVarId_revert___lam__0___closed__2, &l_Lean_MVarId_revert___lam__0___closed__2_once, _init_l_Lean_MVarId_revert___lam__0___closed__2);
v___x_440_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v___x_439_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref(v___x_440_);
v___x_442_ = l_Lean_MVarId_setKind___redArg(v_fst_346_, v___x_356_, v___y_276_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v___x_442_, 0);
lean_dec(v_unused_450_);
v___x_444_ = v___x_442_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_dec(v___x_442_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 1);
lean_ctor_set(v___x_444_, 0, v_a_441_);
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_441_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_a_441_);
v_a_451_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_442_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_442_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
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
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec(v_a_352_);
lean_del_object(v___x_349_);
lean_dec(v_snd_347_);
lean_dec(v_fst_346_);
lean_dec(v___x_271_);
v_a_467_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_354_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_354_);
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
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_del_object(v___x_349_);
lean_dec(v_snd_347_);
lean_dec(v_fst_346_);
lean_dec(v___x_271_);
v_a_475_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_351_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_351_);
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
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec(v___x_271_);
v_a_484_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_344_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_344_);
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
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_mvarId_272_);
lean_dec(v___x_271_);
v_a_492_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_339_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_339_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_revert___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarIds_268_ = stack[0].m_obj;
uint8_t v_preserveOrder_269_ = stack[1].m_num;
uint8_t v___x_270_ = stack[2].m_num;
lean_object* v___x_271_ = stack[3].m_obj;
lean_object* v_mvarId_272_ = stack[4].m_obj;
lean_object* v___x_273_ = stack[5].m_obj;
uint8_t v_clearAuxDeclsInsteadOfRevert_274_ = stack[6].m_num;
lean_object* v___y_275_ = stack[7].m_obj;
lean_object* v___y_276_ = stack[8].m_obj;
lean_object* v___y_277_ = stack[9].m_obj;
lean_object* v___y_278_ = stack[10].m_obj;
lean_object* v_res_521_;
v_res_521_ = l_Lean_MVarId_revert___lam__0(v_fvarIds_268_, v_preserveOrder_269_, v___x_270_, v___x_271_, v_mvarId_272_, v___x_273_, v_clearAuxDeclsInsteadOfRevert_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
stack->m_obj
 = v_res_521_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0___boxed(lean_object* v_fvarIds_522_, lean_object* v_preserveOrder_523_, lean_object* v___x_524_, lean_object* v___x_525_, lean_object* v_mvarId_526_, lean_object* v___x_527_, lean_object* v_clearAuxDeclsInsteadOfRevert_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
uint8_t v_preserveOrder_boxed_534_; uint8_t v___x_9162__boxed_535_; uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_536_; lean_object* v_res_537_; 
v_preserveOrder_boxed_534_ = lean_unbox(v_preserveOrder_523_);
v___x_9162__boxed_535_ = lean_unbox(v___x_524_);
v_clearAuxDeclsInsteadOfRevert_boxed_536_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_528_);
v_res_537_ = l_Lean_MVarId_revert___lam__0(v_fvarIds_522_, v_preserveOrder_boxed_534_, v___x_9162__boxed_535_, v___x_525_, v_mvarId_526_, v___x_527_, v_clearAuxDeclsInsteadOfRevert_boxed_536_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
return v_res_537_;
}
}
lean_object* l_Lean_MVarId_revert(lean_object* v_mvarId_543_, lean_object* v_fvarIds_544_, uint8_t v_preserveOrder_545_, uint8_t v_clearAuxDeclsInsteadOfRevert_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_552_ = lean_array_get_size(v_fvarIds_544_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_nat_dec_eq(v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___f_560_; lean_object* v___x_561_; 
v___x_555_ = 1;
v___x_556_ = ((lean_object*)(l_Lean_MVarId_revert___closed__1));
v___x_557_ = lean_box(v_preserveOrder_545_);
v___x_558_ = lean_box(v___x_555_);
v___x_559_ = lean_box(v_clearAuxDeclsInsteadOfRevert_546_);
lean_inc(v_mvarId_543_);
v___f_560_ = lean_alloc_closure((void*)(l_Lean_MVarId_revert___lam__0___boxed), 12, 7);
lean_closure_set(v___f_560_, 0, v_fvarIds_544_);
lean_closure_set(v___f_560_, 1, v___x_557_);
lean_closure_set(v___f_560_, 2, v___x_558_);
lean_closure_set(v___f_560_, 3, v___x_553_);
lean_closure_set(v___f_560_, 4, v_mvarId_543_);
lean_closure_set(v___f_560_, 5, v___x_556_);
lean_closure_set(v___f_560_, 6, v___x_559_);
v___x_561_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_543_, v___f_560_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v_fvarIds_544_);
v___x_562_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v_mvarId_543_);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
}
LEAN_EXPORT void l_Lean_MVarId_revert_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_543_ = stack[0].m_obj;
lean_object* v_fvarIds_544_ = stack[1].m_obj;
uint8_t v_preserveOrder_545_ = stack[2].m_num;
uint8_t v_clearAuxDeclsInsteadOfRevert_546_ = stack[3].m_num;
lean_object* v_a_547_ = stack[4].m_obj;
lean_object* v_a_548_ = stack[5].m_obj;
lean_object* v_a_549_ = stack[6].m_obj;
lean_object* v_a_550_ = stack[7].m_obj;
lean_object* v_res_565_;
v_res_565_ = l_Lean_MVarId_revert(v_mvarId_543_, v_fvarIds_544_, v_preserveOrder_545_, v_clearAuxDeclsInsteadOfRevert_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
stack->m_obj
 = v_res_565_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object* v_mvarId_566_, lean_object* v_fvarIds_567_, lean_object* v_preserveOrder_568_, lean_object* v_clearAuxDeclsInsteadOfRevert_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
uint8_t v_preserveOrder_boxed_575_; uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_576_; lean_object* v_res_577_; 
v_preserveOrder_boxed_575_ = lean_unbox(v_preserveOrder_568_);
v_clearAuxDeclsInsteadOfRevert_boxed_576_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_569_);
v_res_577_ = l_Lean_MVarId_revert(v_mvarId_566_, v_fvarIds_567_, v_preserveOrder_boxed_575_, v_clearAuxDeclsInsteadOfRevert_boxed_576_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
return v_res_577_;
}
}
lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(lean_object* v_00_u03b1_578_, lean_object* v_msg_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v_msg_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
return v___x_585_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_MVarId_revert_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_579_ = stack[1].m_obj;
lean_object* v___y_580_ = stack[2].m_obj;
lean_object* v___y_581_ = stack[3].m_obj;
lean_object* v___y_582_ = stack[4].m_obj;
lean_object* v___y_583_ = stack[5].m_obj;
lean_object* v_res_586_;
v_res_586_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(lean_box(0), v_msg_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
stack->m_obj
 = v_res_586_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___boxed(lean_object* v_00_u03b1_587_, lean_object* v_msg_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(v_00_u03b1_587_, v_msg_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_594_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(lean_object* v_as_595_, size_t v_i_596_, size_t v_stop_597_, lean_object* v_b_598_){
_start:
{
lean_object* v___y_600_; uint8_t v___x_604_; 
v___x_604_ = lean_usize_dec_eq(v_i_596_, v_stop_597_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_array_uget_borrowed(v_as_595_, v_i_596_);
if (lean_obj_tag(v___x_605_) == 0)
{
v___y_600_ = v_b_598_;
goto v___jp_599_;
}
else
{
lean_object* v_val_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_val_606_ = lean_ctor_get(v___x_605_, 0);
v___x_607_ = l_Lean_LocalDecl_fvarId(v_val_606_);
v___x_608_ = lean_array_push(v_b_598_, v___x_607_);
v___y_600_ = v___x_608_;
goto v___jp_599_;
}
}
else
{
return v_b_598_;
}
v___jp_599_:
{
size_t v___x_601_; size_t v___x_602_; 
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_add(v_i_596_, v___x_601_);
v_i_596_ = v___x_602_;
v_b_598_ = v___y_600_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_595_ = stack[0].m_obj;
size_t v_i_596_ = stack[1].m_num;
size_t v_stop_597_ = stack[2].m_num;
lean_object* v_b_598_ = stack[3].m_obj;
lean_object* v_res_609_;
v_res_609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_as_595_, v_i_596_, v_stop_597_, v_b_598_);
stack->m_obj
 = v_res_609_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2___boxed(lean_object* v_as_610_, lean_object* v_i_611_, lean_object* v_stop_612_, lean_object* v_b_613_){
_start:
{
size_t v_i_boxed_614_; size_t v_stop_boxed_615_; lean_object* v_res_616_; 
v_i_boxed_614_ = lean_unbox_usize(v_i_611_);
lean_dec(v_i_611_);
v_stop_boxed_615_ = lean_unbox_usize(v_stop_612_);
lean_dec(v_stop_612_);
v_res_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_as_610_, v_i_boxed_614_, v_stop_boxed_615_, v_b_613_);
lean_dec_ref(v_as_610_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_617_) == 0)
{
lean_object* v_cs_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_cs_619_ = lean_ctor_get(v_x_617_, 0);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_array_get_size(v_cs_619_);
v___x_622_ = lean_nat_dec_lt(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
return v_x_618_;
}
else
{
size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v___x_623_ = ((size_t)0ULL);
v___x_624_ = lean_usize_of_nat(v___x_621_);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_619_, v___x_623_, v___x_624_, v_x_618_);
return v___x_625_;
}
}
else
{
lean_object* v_vs_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_vs_626_ = lean_ctor_get(v_x_617_, 0);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_array_get_size(v_vs_626_);
v___x_629_ = lean_nat_dec_lt(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
return v_x_618_;
}
else
{
size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
v___x_630_ = ((size_t)0ULL);
v___x_631_ = lean_usize_of_nat(v___x_628_);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_626_, v___x_630_, v___x_631_, v_x_618_);
return v___x_632_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_633_, size_t v_i_634_, size_t v_stop_635_, lean_object* v_b_636_){
_start:
{
uint8_t v___x_637_; 
v___x_637_ = lean_usize_dec_eq(v_i_634_, v_stop_635_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; size_t v___x_640_; size_t v___x_641_; 
v___x_638_ = lean_array_uget_borrowed(v_as_633_, v_i_634_);
v___x_639_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v___x_638_, v_b_636_);
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_add(v_i_634_, v___x_640_);
v_i_634_ = v___x_641_;
v_b_636_ = v___x_639_;
goto _start;
}
else
{
return v_b_636_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_633_ = stack[0].m_obj;
size_t v_i_634_ = stack[1].m_num;
size_t v_stop_635_ = stack[2].m_num;
lean_object* v_b_636_ = stack[3].m_obj;
lean_object* v_res_643_;
v_res_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_as_633_, v_i_634_, v_stop_635_, v_b_636_);
stack->m_obj
 = v_res_643_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_644_, lean_object* v_i_645_, lean_object* v_stop_646_, lean_object* v_b_647_){
_start:
{
size_t v_i_boxed_648_; size_t v_stop_boxed_649_; lean_object* v_res_650_; 
v_i_boxed_648_ = lean_unbox_usize(v_i_645_);
lean_dec(v_i_645_);
v_stop_boxed_649_ = lean_unbox_usize(v_stop_646_);
lean_dec(v_stop_646_);
v_res_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_as_644_, v_i_boxed_648_, v_stop_boxed_649_, v_b_647_);
lean_dec_ref(v_as_644_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3___boxed(lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v_x_651_, v_x_652_);
lean_dec_ref(v_x_651_);
return v_res_653_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_654_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(lean_object* v_x_655_, size_t v_x_656_, size_t v_x_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_655_) == 0)
{
lean_object* v_cs_659_; lean_object* v___x_660_; size_t v___x_661_; lean_object* v_j_662_; lean_object* v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_cs_659_ = lean_ctor_get(v_x_655_, 0);
v___x_660_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0);
v___x_661_ = lean_usize_shift_right(v_x_656_, v_x_657_);
v_j_662_ = lean_usize_to_nat(v___x_661_);
v___x_663_ = lean_array_get_borrowed(v___x_660_, v_cs_659_, v_j_662_);
v___x_664_ = ((size_t)1ULL);
v___x_665_ = lean_usize_shift_left(v___x_664_, v_x_657_);
v___x_666_ = lean_usize_sub(v___x_665_, v___x_664_);
v___x_667_ = lean_usize_land(v_x_656_, v___x_666_);
v___x_668_ = ((size_t)5ULL);
v___x_669_ = lean_usize_sub(v_x_657_, v___x_668_);
v___x_670_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v___x_663_, v___x_667_, v___x_669_, v_x_658_);
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_add(v_j_662_, v___x_671_);
lean_dec(v_j_662_);
v___x_673_ = lean_array_get_size(v_cs_659_);
v___x_674_ = lean_nat_dec_lt(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_dec(v___x_672_);
return v___x_670_;
}
else
{
size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_usize_of_nat(v___x_672_);
lean_dec(v___x_672_);
v___x_676_ = lean_usize_of_nat(v___x_673_);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_659_, v___x_675_, v___x_676_, v___x_670_);
return v___x_677_;
}
}
else
{
lean_object* v_vs_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_vs_678_ = lean_ctor_get(v_x_655_, 0);
v___x_679_ = lean_usize_to_nat(v_x_656_);
v___x_680_ = lean_array_get_size(v_vs_678_);
v___x_681_ = lean_nat_dec_lt(v___x_679_, v___x_680_);
if (v___x_681_ == 0)
{
lean_dec(v___x_679_);
return v_x_658_;
}
else
{
size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_usize_of_nat(v___x_679_);
lean_dec(v___x_679_);
v___x_683_ = lean_usize_of_nat(v___x_680_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_678_, v___x_682_, v___x_683_, v_x_658_);
return v___x_684_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_655_ = stack[0].m_obj;
size_t v_x_656_ = stack[1].m_num;
size_t v_x_657_ = stack[2].m_num;
lean_object* v_x_658_ = stack[3].m_obj;
lean_object* v_res_685_;
v_res_685_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v_x_655_, v_x_656_, v_x_657_, v_x_658_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___boxed(lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
size_t v_x_1406__boxed_690_; size_t v_x_1407__boxed_691_; lean_object* v_res_692_; 
v_x_1406__boxed_690_ = lean_unbox_usize(v_x_687_);
lean_dec(v_x_687_);
v_x_1407__boxed_691_ = lean_unbox_usize(v_x_688_);
lean_dec(v_x_688_);
v_res_692_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v_x_686_, v_x_1406__boxed_690_, v_x_1407__boxed_691_, v_x_689_);
lean_dec_ref(v_x_686_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(lean_object* v_t_693_, lean_object* v_init_694_, lean_object* v_start_695_){
_start:
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_nat_dec_eq(v_start_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v_root_698_; lean_object* v_tail_699_; size_t v_shift_700_; lean_object* v_tailOff_701_; uint8_t v___x_702_; 
v_root_698_ = lean_ctor_get(v_t_693_, 0);
v_tail_699_ = lean_ctor_get(v_t_693_, 1);
v_shift_700_ = lean_ctor_get_usize(v_t_693_, 4);
v_tailOff_701_ = lean_ctor_get(v_t_693_, 3);
v___x_702_ = lean_nat_dec_le(v_tailOff_701_, v_start_695_);
if (v___x_702_ == 0)
{
size_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_703_ = lean_usize_of_nat(v_start_695_);
v___x_704_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v_root_698_, v___x_703_, v_shift_700_, v_init_694_);
v___x_705_ = lean_array_get_size(v_tail_699_);
v___x_706_ = lean_nat_dec_lt(v___x_696_, v___x_705_);
if (v___x_706_ == 0)
{
return v___x_704_;
}
else
{
size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v___x_707_ = ((size_t)0ULL);
v___x_708_ = lean_usize_of_nat(v___x_705_);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_699_, v___x_707_, v___x_708_, v___x_704_);
return v___x_709_;
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_710_ = lean_nat_sub(v_start_695_, v_tailOff_701_);
v___x_711_ = lean_array_get_size(v_tail_699_);
v___x_712_ = lean_nat_dec_lt(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec(v___x_710_);
return v_init_694_;
}
else
{
size_t v___x_713_; size_t v___x_714_; lean_object* v___x_715_; 
v___x_713_ = lean_usize_of_nat(v___x_710_);
lean_dec(v___x_710_);
v___x_714_ = lean_usize_of_nat(v___x_711_);
v___x_715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_699_, v___x_713_, v___x_714_, v_init_694_);
return v___x_715_;
}
}
}
else
{
lean_object* v_root_716_; lean_object* v_tail_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_root_716_ = lean_ctor_get(v_t_693_, 0);
v_tail_717_ = lean_ctor_get(v_t_693_, 1);
v___x_718_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v_root_716_, v_init_694_);
v___x_719_ = lean_array_get_size(v_tail_717_);
v___x_720_ = lean_nat_dec_lt(v___x_696_, v___x_719_);
if (v___x_720_ == 0)
{
return v___x_718_;
}
else
{
size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
v___x_721_ = ((size_t)0ULL);
v___x_722_ = lean_usize_of_nat(v___x_719_);
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_717_, v___x_721_, v___x_722_, v___x_718_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0___boxed(lean_object* v_t_724_, lean_object* v_init_725_, lean_object* v_start_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_t_724_, v_init_725_, v_start_726_);
lean_dec(v_start_726_);
lean_dec_ref(v_t_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(lean_object* v_lctx_728_, lean_object* v_init_729_, lean_object* v_start_730_){
_start:
{
lean_object* v_decls_731_; lean_object* v___x_732_; 
v_decls_731_ = lean_ctor_get(v_lctx_728_, 1);
v___x_732_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_decls_731_, v_init_729_, v_start_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0___boxed(lean_object* v_lctx_733_, lean_object* v_init_734_, lean_object* v_start_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_733_, v_init_734_, v_start_735_);
lean_dec(v_start_735_);
lean_dec_ref(v_lctx_733_);
return v_res_736_;
}
}
lean_object* l_Lean_MVarId_revertAfter___lam__0(lean_object* v_fvarId_737_, lean_object* v_mvarId_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_737_, v___y_739_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v_lctx_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; lean_object* v___x_753_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v_lctx_746_ = lean_ctor_get(v___y_739_, 2);
v___x_747_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_748_ = l_Lean_LocalDecl_index(v_a_745_);
lean_dec(v_a_745_);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v___x_748_, v___x_749_);
lean_dec(v___x_748_);
v___x_751_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_746_, v___x_747_, v___x_750_);
lean_dec(v___x_750_);
v___x_752_ = 1;
v___x_753_ = l_Lean_MVarId_revert(v_mvarId_738_, v___x_751_, v___x_752_, v___x_752_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
return v___x_753_;
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_mvarId_738_);
v_a_754_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_744_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_744_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_revertAfter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_737_ = stack[0].m_obj;
lean_object* v_mvarId_738_ = stack[1].m_obj;
lean_object* v___y_739_ = stack[2].m_obj;
lean_object* v___y_740_ = stack[3].m_obj;
lean_object* v___y_741_ = stack[4].m_obj;
lean_object* v___y_742_ = stack[5].m_obj;
lean_object* v_res_762_;
v_res_762_ = l_Lean_MVarId_revertAfter___lam__0(v_fvarId_737_, v_mvarId_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lam__0___boxed(lean_object* v_fvarId_763_, lean_object* v_mvarId_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_MVarId_revertAfter___lam__0(v_fvarId_763_, v_mvarId_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_770_;
}
}
lean_object* l_Lean_MVarId_revertAfter(lean_object* v_mvarId_771_, lean_object* v_fvarId_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___f_778_; lean_object* v___x_779_; 
lean_inc(v_mvarId_771_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertAfter___lam__0___boxed), 7, 2);
lean_closure_set(v___f_778_, 0, v_fvarId_772_);
lean_closure_set(v___f_778_, 1, v_mvarId_771_);
v___x_779_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_771_, v___f_778_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_779_;
}
}
LEAN_EXPORT void l_Lean_MVarId_revertAfter_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_771_ = stack[0].m_obj;
lean_object* v_fvarId_772_ = stack[1].m_obj;
lean_object* v_a_773_ = stack[2].m_obj;
lean_object* v_a_774_ = stack[3].m_obj;
lean_object* v_a_775_ = stack[4].m_obj;
lean_object* v_a_776_ = stack[5].m_obj;
lean_object* v_res_780_;
v_res_780_ = l_Lean_MVarId_revertAfter(v_mvarId_771_, v_fvarId_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
stack->m_obj
 = v_res_780_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___boxed(lean_object* v_mvarId_781_, lean_object* v_fvarId_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_MVarId_revertAfter(v_mvarId_781_, v_fvarId_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
return v_res_788_;
}
}
lean_object* l_Lean_MVarId_revertFrom___lam__0(lean_object* v_fvarId_789_, lean_object* v_mvarId_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_789_, v___y_791_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v_lctx_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
v_lctx_798_ = lean_ctor_get(v___y_791_, 2);
v___x_799_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_800_ = l_Lean_LocalDecl_index(v_a_797_);
lean_dec(v_a_797_);
v___x_801_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_798_, v___x_799_, v___x_800_);
lean_dec(v___x_800_);
v___x_802_ = 1;
v___x_803_ = l_Lean_MVarId_revert(v_mvarId_790_, v___x_801_, v___x_802_, v___x_802_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
return v___x_803_;
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_mvarId_790_);
v_a_804_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_796_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_796_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_revertFrom___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_789_ = stack[0].m_obj;
lean_object* v_mvarId_790_ = stack[1].m_obj;
lean_object* v___y_791_ = stack[2].m_obj;
lean_object* v___y_792_ = stack[3].m_obj;
lean_object* v___y_793_ = stack[4].m_obj;
lean_object* v___y_794_ = stack[5].m_obj;
lean_object* v_res_812_;
v_res_812_ = l_Lean_MVarId_revertFrom___lam__0(v_fvarId_789_, v_mvarId_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
stack->m_obj
 = v_res_812_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___lam__0___boxed(lean_object* v_fvarId_813_, lean_object* v_mvarId_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_MVarId_revertFrom___lam__0(v_fvarId_813_, v_mvarId_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_820_;
}
}
lean_object* l_Lean_MVarId_revertFrom(lean_object* v_mvarId_821_, lean_object* v_fvarId_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___f_828_; lean_object* v___x_829_; 
lean_inc(v_mvarId_821_);
v___f_828_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertFrom___lam__0___boxed), 7, 2);
lean_closure_set(v___f_828_, 0, v_fvarId_822_);
lean_closure_set(v___f_828_, 1, v_mvarId_821_);
v___x_829_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_821_, v___f_828_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
return v___x_829_;
}
}
LEAN_EXPORT void l_Lean_MVarId_revertFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_821_ = stack[0].m_obj;
lean_object* v_fvarId_822_ = stack[1].m_obj;
lean_object* v_a_823_ = stack[2].m_obj;
lean_object* v_a_824_ = stack[3].m_obj;
lean_object* v_a_825_ = stack[4].m_obj;
lean_object* v_a_826_ = stack[5].m_obj;
lean_object* v_res_830_;
v_res_830_ = l_Lean_MVarId_revertFrom(v_mvarId_821_, v_fvarId_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
stack->m_obj
 = v_res_830_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___boxed(lean_object* v_mvarId_831_, lean_object* v_fvarId_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_MVarId_revertFrom(v_mvarId_831_, v_fvarId_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
return v_res_838_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(lean_object* v_as_839_, size_t v_sz_840_, size_t v_i_841_, lean_object* v_b_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_a_848_; uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_lt(v_i_841_, v_sz_840_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v_b_842_);
return v___x_853_;
}
else
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_array_uget_borrowed(v_as_839_, v_i_841_);
lean_inc(v_a_854_);
v___x_855_ = l_Lean_FVarId_getDecl___redArg(v_a_854_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; uint8_t v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = l_Lean_LocalDecl_isAuxDecl(v_a_856_);
lean_dec(v_a_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
lean_inc(v_a_854_);
v___x_858_ = lean_array_push(v_b_842_, v_a_854_);
v_a_848_ = v___x_858_;
goto v___jp_847_;
}
else
{
v_a_848_ = v_b_842_;
goto v___jp_847_;
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec_ref(v_b_842_);
v_a_859_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_855_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_855_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
v___jp_847_:
{
size_t v___x_849_; size_t v___x_850_; 
v___x_849_ = ((size_t)1ULL);
v___x_850_ = lean_usize_add(v_i_841_, v___x_849_);
v_i_841_ = v___x_850_;
v_b_842_ = v_a_848_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_839_ = stack[0].m_obj;
size_t v_sz_840_ = stack[1].m_num;
size_t v_i_841_ = stack[2].m_num;
lean_object* v_b_842_ = stack[3].m_obj;
lean_object* v___y_843_ = stack[4].m_obj;
lean_object* v___y_844_ = stack[5].m_obj;
lean_object* v___y_845_ = stack[6].m_obj;
lean_object* v_res_867_;
v_res_867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_839_, v_sz_840_, v_i_841_, v_b_842_, v___y_843_, v___y_844_, v___y_845_);
stack->m_obj
 = v_res_867_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg___boxed(lean_object* v_as_868_, lean_object* v_sz_869_, lean_object* v_i_870_, lean_object* v_b_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
size_t v_sz_boxed_876_; size_t v_i_boxed_877_; lean_object* v_res_878_; 
v_sz_boxed_876_ = lean_unbox_usize(v_sz_869_);
lean_dec(v_sz_869_);
v_i_boxed_877_ = lean_unbox_usize(v_i_870_);
lean_dec(v_i_870_);
v_res_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_868_, v_sz_boxed_876_, v_i_boxed_877_, v_b_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec_ref(v_as_868_);
return v_res_878_;
}
}
lean_object* l_Lean_MVarId_revertAll___lam__0(lean_object* v_mvarId_879_, lean_object* v___x_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; 
lean_inc(v_mvarId_879_);
v___x_886_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_879_, v___x_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_lctx_887_; lean_object* v___x_888_; lean_object* v___x_889_; size_t v_sz_890_; size_t v___x_891_; lean_object* v___x_892_; 
lean_dec_ref_known(v___x_886_, 1);
v_lctx_887_ = lean_ctor_get(v___y_881_, 2);
v___x_888_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_889_ = l_Lean_LocalContext_getFVarIds(v_lctx_887_);
v_sz_890_ = lean_array_size(v___x_889_);
v___x_891_ = ((size_t)0ULL);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v___x_889_, v_sz_890_, v___x_891_, v___x_888_, v___y_881_, v___y_883_, v___y_884_);
lean_dec_ref(v___x_889_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; uint8_t v___x_894_; lean_object* v___x_895_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = 1;
v___x_895_ = l_Lean_MVarId_revert(v_mvarId_879_, v_a_893_, v___x_894_, v___x_894_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_904_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_904_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_snd_900_; lean_object* v___x_902_; 
v_snd_900_ = lean_ctor_get(v_a_896_, 1);
lean_inc(v_snd_900_);
lean_dec(v_a_896_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v_snd_900_);
v___x_902_ = v___x_898_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_snd_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_a_905_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_895_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_895_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_mvarId_879_);
v_a_913_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_892_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_892_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v_mvarId_879_);
v_a_921_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_886_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_886_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_revertAll___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_879_ = stack[0].m_obj;
lean_object* v___x_880_ = stack[1].m_obj;
lean_object* v___y_881_ = stack[2].m_obj;
lean_object* v___y_882_ = stack[3].m_obj;
lean_object* v___y_883_ = stack[4].m_obj;
lean_object* v___y_884_ = stack[5].m_obj;
lean_object* v_res_929_;
v_res_929_ = l_Lean_MVarId_revertAll___lam__0(v_mvarId_879_, v___x_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
stack->m_obj
 = v_res_929_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lam__0___boxed(lean_object* v_mvarId_930_, lean_object* v___x_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_MVarId_revertAll___lam__0(v_mvarId_930_, v___x_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_937_;
}
}
lean_object* l_Lean_MVarId_revertAll(lean_object* v_mvarId_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_947_; lean_object* v___f_948_; lean_object* v___x_949_; 
v___x_947_ = ((lean_object*)(l_Lean_MVarId_revertAll___closed__1));
lean_inc(v_mvarId_941_);
v___f_948_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertAll___lam__0___boxed), 7, 2);
lean_closure_set(v___f_948_, 0, v_mvarId_941_);
lean_closure_set(v___f_948_, 1, v___x_947_);
v___x_949_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_941_, v___f_948_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
return v___x_949_;
}
}
LEAN_EXPORT void l_Lean_MVarId_revertAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_941_ = stack[0].m_obj;
lean_object* v_a_942_ = stack[1].m_obj;
lean_object* v_a_943_ = stack[2].m_obj;
lean_object* v_a_944_ = stack[3].m_obj;
lean_object* v_a_945_ = stack[4].m_obj;
lean_object* v_res_950_;
v_res_950_ = l_Lean_MVarId_revertAll(v_mvarId_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
stack->m_obj
 = v_res_950_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___boxed(lean_object* v_mvarId_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_MVarId_revertAll(v_mvarId_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_957_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(lean_object* v_as_958_, size_t v_sz_959_, size_t v_i_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_958_, v_sz_959_, v_i_960_, v_b_961_, v___y_962_, v___y_964_, v___y_965_);
return v___x_967_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_958_ = stack[0].m_obj;
size_t v_sz_959_ = stack[1].m_num;
size_t v_i_960_ = stack[2].m_num;
lean_object* v_b_961_ = stack[3].m_obj;
lean_object* v___y_962_ = stack[4].m_obj;
lean_object* v___y_963_ = stack[5].m_obj;
lean_object* v___y_964_ = stack[6].m_obj;
lean_object* v___y_965_ = stack[7].m_obj;
lean_object* v_res_968_;
v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(v_as_958_, v_sz_959_, v_i_960_, v_b_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
stack->m_obj
 = v_res_968_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___boxed(lean_object* v_as_969_, lean_object* v_sz_970_, lean_object* v_i_971_, lean_object* v_b_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
size_t v_sz_boxed_978_; size_t v_i_boxed_979_; lean_object* v_res_980_; 
v_sz_boxed_978_ = lean_unbox_usize(v_sz_970_);
lean_dec(v_sz_970_);
v_i_boxed_979_ = lean_unbox_usize(v_i_971_);
lean_dec(v_i_971_);
v_res_980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(v_as_969_, v_sz_boxed_978_, v_i_boxed_979_, v_b_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec_ref(v_as_969_);
return v_res_980_;
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
