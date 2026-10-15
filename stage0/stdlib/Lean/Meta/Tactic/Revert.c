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
lean_object* v___x_57_; lean_object* v_env_58_; uint8_t v___x_59_; lean_object* v_env_60_; lean_object* v___x_61_; lean_object* v_toCold_62_; lean_object* v_mctx_63_; lean_object* v_lctx_64_; lean_object* v_options_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_57_ = lean_st_ref_get(v___y_55_);
v_env_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc_ref(v_env_58_);
lean_dec(v___x_57_);
v___x_59_ = 0;
v_env_60_ = l_Lean_Environment_setRecordingDeps(v_env_58_, v___x_59_);
v___x_61_ = lean_st_ref_get(v___y_53_);
v_toCold_62_ = lean_ctor_get(v___y_54_, 0);
v_mctx_63_ = lean_ctor_get(v___x_61_, 0);
lean_inc_ref(v_mctx_63_);
lean_dec(v___x_61_);
v_lctx_64_ = lean_ctor_get(v___y_52_, 2);
v_options_65_ = lean_ctor_get(v_toCold_62_, 2);
lean_inc_ref(v_options_65_);
lean_inc_ref(v_lctx_64_);
v___x_66_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_66_, 0, v_env_60_);
lean_ctor_set(v___x_66_, 1, v_mctx_63_);
lean_ctor_set(v___x_66_, 2, v_lctx_64_);
lean_ctor_set(v___x_66_, 3, v_options_65_);
v___x_67_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v_msgData_51_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3___boxed(lean_object* v_msgData_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(v_msgData_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(lean_object* v_msg_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_ref_82_; lean_object* v___x_83_; lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_92_; 
v_ref_82_ = lean_ctor_get(v___y_79_, 2);
v___x_83_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_revert_spec__3_spec__3(v_msg_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_92_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_90_; 
lean_inc(v_ref_82_);
v___x_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_88_, 0, v_ref_82_);
lean_ctor_set(v___x_88_, 1, v_a_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 1);
lean_ctor_set(v___x_86_, 0, v___x_88_);
v___x_90_ = v___x_86_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg___boxed(lean_object* v_msg_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v_msg_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_99_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__0));
v___x_102_ = l_Lean_stringToMessageData(v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__2));
v___x_105_ = l_Lean_stringToMessageData(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(lean_object* v_as_106_, size_t v_sz_107_, size_t v_i_108_, lean_object* v_b_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_a_116_; uint8_t v___x_120_; 
v___x_120_ = lean_usize_dec_lt(v_i_108_, v_sz_107_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; 
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v_b_109_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v_a_123_; lean_object* v___x_124_; 
v___x_122_ = lean_box(0);
v_a_123_ = lean_array_uget_borrowed(v_as_106_, v_i_108_);
lean_inc(v_a_123_);
v___x_124_ = l_Lean_FVarId_getDecl___redArg(v_a_123_, v___y_110_, v___y_112_, v___y_113_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; uint8_t v___x_126_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_124_, 1);
v___x_126_ = l_Lean_LocalDecl_isAuxDecl(v_a_125_);
lean_dec(v_a_125_);
if (v___x_126_ == 0)
{
v_a_116_ = v___x_122_;
goto v___jp_115_;
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_127_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__1);
lean_inc(v_a_123_);
v___x_128_ = l_Lean_mkFVar(v_a_123_);
v___x_129_ = l_Lean_MessageData_ofExpr(v___x_128_);
v___x_130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_127_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___closed__3);
v___x_132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v___x_132_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_dec_ref_known(v___x_133_, 1);
v_a_116_ = v___x_122_;
goto v___jp_115_;
}
else
{
return v___x_133_;
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
v_a_134_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_124_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_124_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
v___jp_115_:
{
size_t v___x_117_; size_t v___x_118_; 
v___x_117_ = ((size_t)1ULL);
v___x_118_ = lean_usize_add(v_i_108_, v___x_117_);
v_i_108_ = v___x_118_;
v_b_109_ = v_a_116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4___boxed(lean_object* v_as_142_, lean_object* v_sz_143_, lean_object* v_i_144_, lean_object* v_b_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
size_t v_sz_boxed_151_; size_t v_i_boxed_152_; lean_object* v_res_153_; 
v_sz_boxed_151_ = lean_unbox_usize(v_sz_143_);
lean_dec(v_sz_143_);
v_i_boxed_152_ = lean_unbox_usize(v_i_144_);
lean_dec(v_i_144_);
v_res_153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_as_142_, v_sz_boxed_151_, v_i_boxed_152_, v_b_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec_ref(v_as_142_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(size_t v_sz_154_, size_t v_i_155_, lean_object* v_bs_156_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = lean_usize_dec_lt(v_i_155_, v_sz_154_);
if (v___x_157_ == 0)
{
return v_bs_156_;
}
else
{
lean_object* v_v_158_; lean_object* v___x_159_; lean_object* v_bs_x27_160_; lean_object* v___x_161_; size_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; 
v_v_158_ = lean_array_uget(v_bs_156_, v_i_155_);
v___x_159_ = lean_unsigned_to_nat(0u);
v_bs_x27_160_ = lean_array_uset(v_bs_156_, v_i_155_, v___x_159_);
v___x_161_ = l_Lean_mkFVar(v_v_158_);
v___x_162_ = ((size_t)1ULL);
v___x_163_ = lean_usize_add(v_i_155_, v___x_162_);
v___x_164_ = lean_array_uset(v_bs_x27_160_, v_i_155_, v___x_161_);
v_i_155_ = v___x_163_;
v_bs_156_ = v___x_164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0___boxed(lean_object* v_sz_166_, lean_object* v_i_167_, lean_object* v_bs_168_){
_start:
{
size_t v_sz_boxed_169_; size_t v_i_boxed_170_; lean_object* v_res_171_; 
v_sz_boxed_169_ = lean_unbox_usize(v_sz_166_);
lean_dec(v_sz_166_);
v_i_boxed_170_ = lean_unbox_usize(v_i_167_);
lean_dec(v_i_167_);
v_res_171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(v_sz_boxed_169_, v_i_boxed_170_, v_bs_168_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(size_t v_sz_172_, size_t v_i_173_, lean_object* v_bs_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = lean_usize_dec_lt(v_i_173_, v_sz_172_);
if (v___x_175_ == 0)
{
return v_bs_174_;
}
else
{
lean_object* v_v_176_; lean_object* v___x_177_; lean_object* v_bs_x27_178_; lean_object* v___x_179_; size_t v___x_180_; size_t v___x_181_; lean_object* v___x_182_; 
v_v_176_ = lean_array_uget(v_bs_174_, v_i_173_);
v___x_177_ = lean_unsigned_to_nat(0u);
v_bs_x27_178_ = lean_array_uset(v_bs_174_, v_i_173_, v___x_177_);
v___x_179_ = l_Lean_Expr_fvarId_x21(v_v_176_);
lean_dec(v_v_176_);
v___x_180_ = ((size_t)1ULL);
v___x_181_ = lean_usize_add(v_i_173_, v___x_180_);
v___x_182_ = lean_array_uset(v_bs_x27_178_, v_i_173_, v___x_179_);
v_i_173_ = v___x_181_;
v_bs_174_ = v___x_182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2___boxed(lean_object* v_sz_184_, lean_object* v_i_185_, lean_object* v_bs_186_){
_start:
{
size_t v_sz_boxed_187_; size_t v_i_boxed_188_; lean_object* v_res_189_; 
v_sz_boxed_187_ = lean_unbox_usize(v_sz_184_);
lean_dec(v_sz_184_);
v_i_boxed_188_ = lean_unbox_usize(v_i_185_);
lean_dec(v_i_185_);
v_res_189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(v_sz_boxed_187_, v_i_boxed_188_, v_bs_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(lean_object* v_as_190_, size_t v_sz_191_, size_t v_i_192_, lean_object* v_b_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_a_200_; uint8_t v___x_204_; 
v___x_204_ = lean_usize_dec_lt(v_i_192_, v_sz_191_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v_b_193_);
return v___x_205_;
}
else
{
lean_object* v_fst_206_; lean_object* v_snd_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_241_; 
v_fst_206_ = lean_ctor_get(v_b_193_, 0);
v_snd_207_ = lean_ctor_get(v_b_193_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_b_193_);
if (v_isSharedCheck_241_ == 0)
{
v___x_209_ = v_b_193_;
v_isShared_210_ = v_isSharedCheck_241_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_snd_207_);
lean_inc(v_fst_206_);
lean_dec(v_b_193_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_241_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_a_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_a_211_ = lean_array_uget_borrowed(v_as_190_, v_i_192_);
v___x_212_ = l_Lean_Expr_fvarId_x21(v_a_211_);
lean_inc(v___x_212_);
v___x_213_ = l_Lean_FVarId_getDecl___redArg(v___x_212_, v___y_194_, v___y_196_, v___y_197_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; uint8_t v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v___x_215_ = l_Lean_LocalDecl_isAuxDecl(v_a_214_);
lean_dec(v_a_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_218_; 
lean_dec(v___x_212_);
lean_inc(v_a_211_);
v___x_216_ = lean_array_push(v_snd_207_, v_a_211_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___x_216_);
v___x_218_ = v___x_209_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_fst_206_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
v_a_200_ = v___x_218_;
goto v___jp_199_;
}
}
else
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_MVarId_clear(v_fst_206_, v___x_212_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v_a_221_);
v___x_223_ = v___x_209_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_221_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_snd_207_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
v_a_200_ = v___x_223_;
goto v___jp_199_;
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_del_object(v___x_209_);
lean_dec(v_snd_207_);
v_a_225_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_220_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_220_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec(v___x_212_);
lean_del_object(v___x_209_);
lean_dec(v_snd_207_);
lean_dec(v_fst_206_);
v_a_233_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_213_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_213_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
v___jp_199_:
{
size_t v___x_201_; size_t v___x_202_; 
v___x_201_ = ((size_t)1ULL);
v___x_202_ = lean_usize_add(v_i_192_, v___x_201_);
v_i_192_ = v___x_202_;
v_b_193_ = v_a_200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1___boxed(lean_object* v_as_242_, lean_object* v_sz_243_, lean_object* v_i_244_, lean_object* v_b_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
size_t v_sz_boxed_251_; size_t v_i_boxed_252_; lean_object* v_res_253_; 
v_sz_boxed_251_ = lean_unbox_usize(v_sz_243_);
lean_dec(v_sz_243_);
v_i_boxed_252_ = lean_unbox_usize(v_i_244_);
lean_dec(v_i_244_);
v_res_253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_as_242_, v_sz_boxed_251_, v_i_boxed_252_, v_b_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec_ref(v_as_242_);
return v_res_253_;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lam__0___closed__0(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_box(0);
v___x_255_ = lean_unsigned_to_nat(16u);
v___x_256_ = lean_mk_array(v___x_255_, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lam__0___closed__2(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_MVarId_revert___lam__0___closed__1));
v___x_259_ = l_Lean_stringToMessageData(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0(lean_object* v_fvarIds_260_, uint8_t v_preserveOrder_261_, uint8_t v___x_262_, lean_object* v___x_263_, lean_object* v_mvarId_264_, lean_object* v___x_265_, uint8_t v_clearAuxDeclsInsteadOfRevert_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___y_273_; uint8_t v___y_274_; lean_object* v___y_275_; size_t v___y_276_; lean_object* v___y_277_; lean_object* v_a_278_; lean_object* v___x_492_; 
lean_inc(v_mvarId_264_);
v___x_492_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_264_, v___x_265_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_dec_ref_known(v___x_492_, 1);
if (v_clearAuxDeclsInsteadOfRevert_266_ == 0)
{
lean_object* v___x_493_; size_t v_sz_494_; size_t v___x_495_; lean_object* v___x_496_; 
v___x_493_ = lean_box(0);
v_sz_494_ = lean_array_size(v_fvarIds_260_);
v___x_495_ = ((size_t)0ULL);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_fvarIds_260_, v_sz_494_, v___x_495_, v___x_493_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_dec_ref_known(v___x_496_, 1);
goto v___jp_327_;
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v_mvarId_264_);
lean_dec(v___x_263_);
lean_dec_ref(v_fvarIds_260_);
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
goto v___jp_327_;
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_mvarId_264_);
lean_dec(v___x_263_);
lean_dec_ref(v_fvarIds_260_);
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
v___jp_272_:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_MVarId_setKind___redArg(v___y_275_, v___y_274_, v___y_273_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_fst_280_; lean_object* v_snd_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_318_; 
lean_dec_ref_known(v___x_279_, 1);
v_fst_280_ = lean_ctor_get(v_a_278_, 0);
v_snd_281_ = lean_ctor_get(v_a_278_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_a_278_);
if (v_isSharedCheck_318_ == 0)
{
v___x_283_ = v_a_278_;
v_isShared_284_ = v_isSharedCheck_318_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_snd_281_);
lean_inc(v_fst_280_);
lean_dec(v_a_278_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_318_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = l_Lean_Expr_getAppFn(v_fst_280_);
lean_dec(v_fst_280_);
v___x_286_ = l_Lean_Expr_mvarId_x21(v___x_285_);
lean_dec_ref(v___x_285_);
lean_inc(v___x_286_);
v___x_287_ = l_Lean_MVarId_setKind___redArg(v___x_286_, v___y_274_, v___y_273_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_288_; 
lean_dec_ref_known(v___x_287_, 1);
lean_inc(v___x_286_);
v___x_288_ = l_Lean_MVarId_setTag___redArg(v___x_286_, v___y_277_, v___y_273_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_300_; 
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v___x_288_, 0);
lean_dec(v_unused_301_);
v___x_290_ = v___x_288_;
v_isShared_291_ = v_isSharedCheck_300_;
goto v_resetjp_289_;
}
else
{
lean_dec(v___x_288_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_300_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
size_t v_sz_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v_sz_292_ = lean_array_size(v_snd_281_);
v___x_293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(v_sz_292_, v___y_276_, v_snd_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___x_286_);
lean_ctor_set(v___x_283_, 0, v___x_293_);
v___x_295_ = v___x_283_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v___x_286_);
v___x_295_ = v_reuseFailAlloc_299_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_295_);
v___x_297_ = v___x_290_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec(v___x_286_);
lean_del_object(v___x_283_);
lean_dec(v_snd_281_);
v_a_302_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_288_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_288_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
lean_dec(v___x_286_);
lean_del_object(v___x_283_);
lean_dec(v_snd_281_);
lean_dec(v___y_277_);
v_a_310_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_287_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_287_);
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
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec_ref(v_a_278_);
lean_dec(v___y_277_);
v_a_319_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_279_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_279_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
v___jp_327_:
{
size_t v_sz_328_; size_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_sz_328_ = lean_array_size(v_fvarIds_260_);
v___x_329_ = ((size_t)0ULL);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(v_sz_328_, v___x_329_, v_fvarIds_260_);
v___x_331_ = l_Lean_Meta_collectForwardDeps(v___x_330_, v_preserveOrder_261_, v___x_262_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; lean_object* v___x_334_; size_t v_sz_335_; lean_object* v___x_336_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = lean_mk_empty_array_with_capacity(v___x_263_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v_mvarId_264_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v_sz_335_ = lean_array_size(v_a_332_);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_a_332_, v_sz_335_, v___x_329_, v___x_334_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v_a_332_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_475_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v_fst_338_ = lean_ctor_get(v_a_337_, 0);
v_snd_339_ = lean_ctor_get(v_a_337_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_a_337_);
if (v_isSharedCheck_475_ == 0)
{
v___x_341_ = v_a_337_;
v_isShared_342_ = v_isSharedCheck_475_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_snd_339_);
lean_inc(v_fst_338_);
lean_dec(v_a_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_475_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; 
lean_inc(v_fst_338_);
v___x_343_ = l_Lean_MVarId_getTag(v_fst_338_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; uint8_t v___x_345_; lean_object* v___x_346_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = 0;
lean_inc(v_fst_338_);
v___x_346_ = l_Lean_MVarId_setKind___redArg(v_fst_338_, v___x_345_, v___y_268_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_lctx_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v_mctx_350_; lean_object* v___x_351_; lean_object* v_ngen_352_; lean_object* v___x_353_; lean_object* v_toCold_354_; lean_object* v_quotContext_355_; lean_object* v_nextMacroScope_356_; lean_object* v___x_358_; 
lean_dec_ref_known(v___x_346_, 1);
v_lctx_347_ = lean_ctor_get(v___y_267_, 2);
v___x_348_ = 2;
v___x_349_ = lean_st_ref_get(v___y_268_);
v_mctx_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc_ref(v_mctx_350_);
lean_dec(v___x_349_);
v___x_351_ = lean_st_ref_get(v___y_270_);
v_ngen_352_ = lean_ctor_get(v___x_351_, 2);
lean_inc_ref(v_ngen_352_);
lean_dec(v___x_351_);
v___x_353_ = lean_st_ref_get(v___y_270_);
v_toCold_354_ = lean_ctor_get(v___y_269_, 0);
v_quotContext_355_ = lean_ctor_get(v_toCold_354_, 8);
v_nextMacroScope_356_ = lean_ctor_get(v___x_353_, 1);
lean_inc(v_nextMacroScope_356_);
lean_dec(v___x_353_);
lean_inc_ref(v_lctx_347_);
lean_inc(v_quotContext_355_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v_lctx_347_);
lean_ctor_set(v___x_341_, 0, v_quotContext_355_);
v___x_358_ = v___x_341_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_quotContext_355_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_lctx_347_);
v___x_358_ = v_reuseFailAlloc_458_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = lean_obj_once(&l_Lean_MVarId_revert___lam__0___closed__0, &l_Lean_MVarId_revert___lam__0___closed__0_once, _init_l_Lean_MVarId_revert___lam__0___closed__0);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_263_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_361_, 0, v_mctx_350_);
lean_ctor_set(v___x_361_, 1, v_nextMacroScope_356_);
lean_ctor_set(v___x_361_, 2, v_ngen_352_);
lean_ctor_set(v___x_361_, 3, v___x_360_);
lean_inc(v_fst_338_);
v___x_362_ = l_Lean_MetavarContext_revert(v_snd_339_, v_fst_338_, v_preserveOrder_261_, v___x_358_, v___x_361_);
lean_dec_ref(v___x_358_);
lean_dec(v_snd_339_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v_a_364_; lean_object* v_mctx_365_; lean_object* v_nextMacroScope_366_; lean_object* v_ngen_367_; lean_object* v___x_368_; lean_object* v_cache_369_; lean_object* v_zetaDeltaFVarIds_370_; lean_object* v_postponed_371_; lean_object* v_diag_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_399_; 
v_a_363_ = lean_ctor_get(v___x_362_, 1);
lean_inc(v_a_363_);
v_a_364_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_362_, 2);
v_mctx_365_ = lean_ctor_get(v_a_363_, 0);
lean_inc_ref(v_mctx_365_);
v_nextMacroScope_366_ = lean_ctor_get(v_a_363_, 1);
lean_inc(v_nextMacroScope_366_);
v_ngen_367_ = lean_ctor_get(v_a_363_, 2);
lean_inc_ref(v_ngen_367_);
lean_dec(v_a_363_);
v___x_368_ = lean_st_ref_take(v___y_268_);
v_cache_369_ = lean_ctor_get(v___x_368_, 1);
v_zetaDeltaFVarIds_370_ = lean_ctor_get(v___x_368_, 2);
v_postponed_371_ = lean_ctor_get(v___x_368_, 3);
v_diag_372_ = lean_ctor_get(v___x_368_, 4);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v___x_368_, 0);
lean_dec(v_unused_400_);
v___x_374_ = v___x_368_;
v_isShared_375_ = v_isSharedCheck_399_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_diag_372_);
lean_inc(v_postponed_371_);
lean_inc(v_zetaDeltaFVarIds_370_);
lean_inc(v_cache_369_);
lean_dec(v___x_368_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_399_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v_mctx_365_);
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_mctx_365_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_cache_369_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_zetaDeltaFVarIds_370_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_postponed_371_);
lean_ctor_set(v_reuseFailAlloc_398_, 4, v_diag_372_);
v___x_377_ = v_reuseFailAlloc_398_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_env_380_; lean_object* v_auxDeclNGen_381_; lean_object* v_traceState_382_; lean_object* v_cache_383_; lean_object* v_recordedDeps_384_; lean_object* v_messages_385_; lean_object* v_infoState_386_; lean_object* v_snapshotTasks_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_395_; 
v___x_378_ = lean_st_ref_put(v___y_268_, v___x_377_);
v___x_379_ = lean_st_ref_take(v___y_270_);
v_env_380_ = lean_ctor_get(v___x_379_, 0);
v_auxDeclNGen_381_ = lean_ctor_get(v___x_379_, 3);
v_traceState_382_ = lean_ctor_get(v___x_379_, 4);
v_cache_383_ = lean_ctor_get(v___x_379_, 5);
v_recordedDeps_384_ = lean_ctor_get(v___x_379_, 6);
v_messages_385_ = lean_ctor_get(v___x_379_, 7);
v_infoState_386_ = lean_ctor_get(v___x_379_, 8);
v_snapshotTasks_387_ = lean_ctor_get(v___x_379_, 9);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; lean_object* v_unused_397_; 
v_unused_396_ = lean_ctor_get(v___x_379_, 2);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v___x_379_, 1);
lean_dec(v_unused_397_);
v___x_389_ = v___x_379_;
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_snapshotTasks_387_);
lean_inc(v_infoState_386_);
lean_inc(v_messages_385_);
lean_inc(v_recordedDeps_384_);
lean_inc(v_cache_383_);
lean_inc(v_traceState_382_);
lean_inc(v_auxDeclNGen_381_);
lean_inc(v_env_380_);
lean_dec(v___x_379_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 2, v_ngen_367_);
lean_ctor_set(v___x_389_, 1, v_nextMacroScope_366_);
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_env_380_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_nextMacroScope_366_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_ngen_367_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_auxDeclNGen_381_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v_traceState_382_);
lean_ctor_set(v_reuseFailAlloc_394_, 5, v_cache_383_);
lean_ctor_set(v_reuseFailAlloc_394_, 6, v_recordedDeps_384_);
lean_ctor_set(v_reuseFailAlloc_394_, 7, v_messages_385_);
lean_ctor_set(v_reuseFailAlloc_394_, 8, v_infoState_386_);
lean_ctor_set(v_reuseFailAlloc_394_, 9, v_snapshotTasks_387_);
v___x_392_ = v_reuseFailAlloc_394_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; 
v___x_393_ = lean_st_ref_put(v___y_270_, v___x_392_);
v___y_273_ = v___y_268_;
v___y_274_ = v___x_348_;
v___y_275_ = v_fst_338_;
v___y_276_ = v___x_329_;
v___y_277_ = v_a_344_;
v_a_278_ = v_a_364_;
goto v___jp_272_;
}
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v_mctx_402_; lean_object* v_nextMacroScope_403_; lean_object* v_ngen_404_; lean_object* v___x_405_; lean_object* v_cache_406_; lean_object* v_zetaDeltaFVarIds_407_; lean_object* v_postponed_408_; lean_object* v_diag_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_456_; 
lean_dec(v_a_344_);
v_a_401_ = lean_ctor_get(v___x_362_, 1);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_362_, 2);
v_mctx_402_ = lean_ctor_get(v_a_401_, 0);
lean_inc_ref(v_mctx_402_);
v_nextMacroScope_403_ = lean_ctor_get(v_a_401_, 1);
lean_inc(v_nextMacroScope_403_);
v_ngen_404_ = lean_ctor_get(v_a_401_, 2);
lean_inc_ref(v_ngen_404_);
lean_dec(v_a_401_);
v___x_405_ = lean_st_ref_take(v___y_268_);
v_cache_406_ = lean_ctor_get(v___x_405_, 1);
v_zetaDeltaFVarIds_407_ = lean_ctor_get(v___x_405_, 2);
v_postponed_408_ = lean_ctor_get(v___x_405_, 3);
v_diag_409_ = lean_ctor_get(v___x_405_, 4);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v___x_405_, 0);
lean_dec(v_unused_457_);
v___x_411_ = v___x_405_;
v_isShared_412_ = v_isSharedCheck_456_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_diag_409_);
lean_inc(v_postponed_408_);
lean_inc(v_zetaDeltaFVarIds_407_);
lean_inc(v_cache_406_);
lean_dec(v___x_405_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_456_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v_mctx_402_);
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_mctx_402_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_cache_406_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_zetaDeltaFVarIds_407_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_postponed_408_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_diag_409_);
v___x_414_ = v_reuseFailAlloc_455_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_env_417_; lean_object* v_auxDeclNGen_418_; lean_object* v_traceState_419_; lean_object* v_cache_420_; lean_object* v_recordedDeps_421_; lean_object* v_messages_422_; lean_object* v_infoState_423_; lean_object* v_snapshotTasks_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_452_; 
v___x_415_ = lean_st_ref_put(v___y_268_, v___x_414_);
v___x_416_ = lean_st_ref_take(v___y_270_);
v_env_417_ = lean_ctor_get(v___x_416_, 0);
v_auxDeclNGen_418_ = lean_ctor_get(v___x_416_, 3);
v_traceState_419_ = lean_ctor_get(v___x_416_, 4);
v_cache_420_ = lean_ctor_get(v___x_416_, 5);
v_recordedDeps_421_ = lean_ctor_get(v___x_416_, 6);
v_messages_422_ = lean_ctor_get(v___x_416_, 7);
v_infoState_423_ = lean_ctor_get(v___x_416_, 8);
v_snapshotTasks_424_ = lean_ctor_get(v___x_416_, 9);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; lean_object* v_unused_454_; 
v_unused_453_ = lean_ctor_get(v___x_416_, 2);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v___x_416_, 1);
lean_dec(v_unused_454_);
v___x_426_ = v___x_416_;
v_isShared_427_ = v_isSharedCheck_452_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snapshotTasks_424_);
lean_inc(v_infoState_423_);
lean_inc(v_messages_422_);
lean_inc(v_recordedDeps_421_);
lean_inc(v_cache_420_);
lean_inc(v_traceState_419_);
lean_inc(v_auxDeclNGen_418_);
lean_inc(v_env_417_);
lean_dec(v___x_416_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_452_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 2, v_ngen_404_);
lean_ctor_set(v___x_426_, 1, v_nextMacroScope_403_);
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_env_417_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_nextMacroScope_403_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_ngen_404_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_auxDeclNGen_418_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v_traceState_419_);
lean_ctor_set(v_reuseFailAlloc_451_, 5, v_cache_420_);
lean_ctor_set(v_reuseFailAlloc_451_, 6, v_recordedDeps_421_);
lean_ctor_set(v_reuseFailAlloc_451_, 7, v_messages_422_);
lean_ctor_set(v_reuseFailAlloc_451_, 8, v_infoState_423_);
lean_ctor_set(v_reuseFailAlloc_451_, 9, v_snapshotTasks_424_);
v___x_429_ = v_reuseFailAlloc_451_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_a_433_; lean_object* v___x_434_; 
v___x_430_ = lean_st_ref_put(v___y_270_, v___x_429_);
v___x_431_ = lean_obj_once(&l_Lean_MVarId_revert___lam__0___closed__2, &l_Lean_MVarId_revert___lam__0___closed__2_once, _init_l_Lean_MVarId_revert___lam__0___closed__2);
v___x_432_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v___x_431_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref(v___x_432_);
v___x_434_ = l_Lean_MVarId_setKind___redArg(v_fst_338_, v___x_348_, v___y_268_);
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
lean_dec(v_a_344_);
lean_del_object(v___x_341_);
lean_dec(v_snd_339_);
lean_dec(v_fst_338_);
lean_dec(v___x_263_);
v_a_459_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_346_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_346_);
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
lean_del_object(v___x_341_);
lean_dec(v_snd_339_);
lean_dec(v_fst_338_);
lean_dec(v___x_263_);
v_a_467_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_343_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_343_);
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
v_a_476_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_336_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_336_);
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
lean_dec(v_mvarId_264_);
lean_dec(v___x_263_);
v_a_484_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_331_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_331_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0___boxed(lean_object* v_fvarIds_513_, lean_object* v_preserveOrder_514_, lean_object* v___x_515_, lean_object* v___x_516_, lean_object* v_mvarId_517_, lean_object* v___x_518_, lean_object* v_clearAuxDeclsInsteadOfRevert_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
uint8_t v_preserveOrder_boxed_525_; uint8_t v___x_8982__boxed_526_; uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_527_; lean_object* v_res_528_; 
v_preserveOrder_boxed_525_ = lean_unbox(v_preserveOrder_514_);
v___x_8982__boxed_526_ = lean_unbox(v___x_515_);
v_clearAuxDeclsInsteadOfRevert_boxed_527_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_519_);
v_res_528_ = l_Lean_MVarId_revert___lam__0(v_fvarIds_513_, v_preserveOrder_boxed_525_, v___x_8982__boxed_526_, v___x_516_, v_mvarId_517_, v___x_518_, v_clearAuxDeclsInsteadOfRevert_boxed_527_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
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
lean_closure_set(v___f_551_, 0, v_fvarIds_535_);
lean_closure_set(v___f_551_, 1, v___x_548_);
lean_closure_set(v___f_551_, 2, v___x_549_);
lean_closure_set(v___f_551_, 3, v___x_544_);
lean_closure_set(v___f_551_, 4, v_mvarId_534_);
lean_closure_set(v___f_551_, 5, v___x_547_);
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
size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_609_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_607_, v___x_611_, v___x_612_, v_x_606_);
return v___x_613_;
}
}
else
{
lean_object* v_vs_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_vs_614_ = lean_ctor_get(v_x_605_, 0);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_array_get_size(v_vs_614_);
v___x_617_ = lean_nat_dec_lt(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
return v_x_606_;
}
else
{
size_t v___x_618_; size_t v___x_619_; lean_object* v___x_620_; 
v___x_618_ = ((size_t)0ULL);
v___x_619_ = lean_usize_of_nat(v___x_616_);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_614_, v___x_618_, v___x_619_, v_x_606_);
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_621_, size_t v_i_622_, size_t v_stop_623_, lean_object* v_b_624_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = lean_usize_dec_eq(v_i_622_, v_stop_623_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; size_t v___x_628_; size_t v___x_629_; 
v___x_626_ = lean_array_uget_borrowed(v_as_621_, v_i_622_);
v___x_627_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v___x_626_, v_b_624_);
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_add(v_i_622_, v___x_628_);
v_i_622_ = v___x_629_;
v_b_624_ = v___x_627_;
goto _start;
}
else
{
return v_b_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_631_, lean_object* v_i_632_, lean_object* v_stop_633_, lean_object* v_b_634_){
_start:
{
size_t v_i_boxed_635_; size_t v_stop_boxed_636_; lean_object* v_res_637_; 
v_i_boxed_635_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_stop_boxed_636_ = lean_unbox_usize(v_stop_633_);
lean_dec(v_stop_633_);
v_res_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_as_631_, v_i_boxed_635_, v_stop_boxed_636_, v_b_634_);
lean_dec_ref(v_as_631_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3___boxed(lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v_x_638_, v_x_639_);
lean_dec_ref(v_x_638_);
return v_res_640_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(lean_object* v_x_642_, size_t v_x_643_, size_t v_x_644_, lean_object* v_x_645_){
_start:
{
if (lean_obj_tag(v_x_642_) == 0)
{
lean_object* v_cs_646_; lean_object* v___x_647_; size_t v___x_648_; lean_object* v_j_649_; lean_object* v___x_650_; size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_cs_646_ = lean_ctor_get(v_x_642_, 0);
v___x_647_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0);
v___x_648_ = lean_usize_shift_right(v_x_643_, v_x_644_);
v_j_649_ = lean_usize_to_nat(v___x_648_);
v___x_650_ = lean_array_get_borrowed(v___x_647_, v_cs_646_, v_j_649_);
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_shift_left(v___x_651_, v_x_644_);
v___x_653_ = lean_usize_sub(v___x_652_, v___x_651_);
v___x_654_ = lean_usize_land(v_x_643_, v___x_653_);
v___x_655_ = ((size_t)5ULL);
v___x_656_ = lean_usize_sub(v_x_644_, v___x_655_);
v___x_657_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v___x_650_, v___x_654_, v___x_656_, v_x_645_);
v___x_658_ = lean_unsigned_to_nat(1u);
v___x_659_ = lean_nat_add(v_j_649_, v___x_658_);
lean_dec(v_j_649_);
v___x_660_ = lean_array_get_size(v_cs_646_);
v___x_661_ = lean_nat_dec_lt(v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_dec(v___x_659_);
return v___x_657_;
}
else
{
size_t v___x_662_; size_t v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_usize_of_nat(v___x_659_);
lean_dec(v___x_659_);
v___x_663_ = lean_usize_of_nat(v___x_660_);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_646_, v___x_662_, v___x_663_, v___x_657_);
return v___x_664_;
}
}
else
{
lean_object* v_vs_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_vs_665_ = lean_ctor_get(v_x_642_, 0);
v___x_666_ = lean_usize_to_nat(v_x_643_);
v___x_667_ = lean_array_get_size(v_vs_665_);
v___x_668_ = lean_nat_dec_lt(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_dec(v___x_666_);
return v_x_645_;
}
else
{
size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_usize_of_nat(v___x_666_);
lean_dec(v___x_666_);
v___x_670_ = lean_usize_of_nat(v___x_667_);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_665_, v___x_669_, v___x_670_, v_x_645_);
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___boxed(lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
size_t v_x_1372__boxed_676_; size_t v_x_1373__boxed_677_; lean_object* v_res_678_; 
v_x_1372__boxed_676_ = lean_unbox_usize(v_x_673_);
lean_dec(v_x_673_);
v_x_1373__boxed_677_ = lean_unbox_usize(v_x_674_);
lean_dec(v_x_674_);
v_res_678_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v_x_672_, v_x_1372__boxed_676_, v_x_1373__boxed_677_, v_x_675_);
lean_dec_ref(v_x_672_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(lean_object* v_t_679_, lean_object* v_init_680_, lean_object* v_start_681_){
_start:
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_nat_dec_eq(v_start_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v_root_684_; lean_object* v_tail_685_; size_t v_shift_686_; lean_object* v_tailOff_687_; uint8_t v___x_688_; 
v_root_684_ = lean_ctor_get(v_t_679_, 0);
v_tail_685_ = lean_ctor_get(v_t_679_, 1);
v_shift_686_ = lean_ctor_get_usize(v_t_679_, 4);
v_tailOff_687_ = lean_ctor_get(v_t_679_, 3);
v___x_688_ = lean_nat_dec_le(v_tailOff_687_, v_start_681_);
if (v___x_688_ == 0)
{
size_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_689_ = lean_usize_of_nat(v_start_681_);
v___x_690_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v_root_684_, v___x_689_, v_shift_686_, v_init_680_);
v___x_691_ = lean_array_get_size(v_tail_685_);
v___x_692_ = lean_nat_dec_lt(v___x_682_, v___x_691_);
if (v___x_692_ == 0)
{
return v___x_690_;
}
else
{
size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; 
v___x_693_ = ((size_t)0ULL);
v___x_694_ = lean_usize_of_nat(v___x_691_);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_685_, v___x_693_, v___x_694_, v___x_690_);
return v___x_695_;
}
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_696_ = lean_nat_sub(v_start_681_, v_tailOff_687_);
v___x_697_ = lean_array_get_size(v_tail_685_);
v___x_698_ = lean_nat_dec_lt(v___x_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_dec(v___x_696_);
return v_init_680_;
}
else
{
size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; 
v___x_699_ = lean_usize_of_nat(v___x_696_);
lean_dec(v___x_696_);
v___x_700_ = lean_usize_of_nat(v___x_697_);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_685_, v___x_699_, v___x_700_, v_init_680_);
return v___x_701_;
}
}
}
else
{
lean_object* v_root_702_; lean_object* v_tail_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_root_702_ = lean_ctor_get(v_t_679_, 0);
v_tail_703_ = lean_ctor_get(v_t_679_, 1);
v___x_704_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v_root_702_, v_init_680_);
v___x_705_ = lean_array_get_size(v_tail_703_);
v___x_706_ = lean_nat_dec_lt(v___x_682_, v___x_705_);
if (v___x_706_ == 0)
{
return v___x_704_;
}
else
{
size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v___x_707_ = ((size_t)0ULL);
v___x_708_ = lean_usize_of_nat(v___x_705_);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_703_, v___x_707_, v___x_708_, v___x_704_);
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0___boxed(lean_object* v_t_710_, lean_object* v_init_711_, lean_object* v_start_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_t_710_, v_init_711_, v_start_712_);
lean_dec(v_start_712_);
lean_dec_ref(v_t_710_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(lean_object* v_lctx_714_, lean_object* v_init_715_, lean_object* v_start_716_){
_start:
{
lean_object* v_decls_717_; lean_object* v___x_718_; 
v_decls_717_ = lean_ctor_get(v_lctx_714_, 1);
v___x_718_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_decls_717_, v_init_715_, v_start_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0___boxed(lean_object* v_lctx_719_, lean_object* v_init_720_, lean_object* v_start_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_719_, v_init_720_, v_start_721_);
lean_dec(v_start_721_);
lean_dec_ref(v_lctx_719_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lam__0(lean_object* v_fvarId_723_, lean_object* v_mvarId_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_723_, v___y_725_, v___y_727_, v___y_728_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v_lctx_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v_lctx_732_ = lean_ctor_get(v___y_725_, 2);
v___x_733_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_734_ = l_Lean_LocalDecl_index(v_a_731_);
lean_dec(v_a_731_);
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_nat_add(v___x_734_, v___x_735_);
lean_dec(v___x_734_);
v___x_737_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_732_, v___x_733_, v___x_736_);
lean_dec(v___x_736_);
v___x_738_ = 1;
v___x_739_ = l_Lean_MVarId_revert(v_mvarId_724_, v___x_737_, v___x_738_, v___x_738_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
return v___x_739_;
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_mvarId_724_);
v_a_740_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_730_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_730_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lam__0___boxed(lean_object* v_fvarId_748_, lean_object* v_mvarId_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_MVarId_revertAfter___lam__0(v_fvarId_748_, v_mvarId_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter(lean_object* v_mvarId_756_, lean_object* v_fvarId_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___f_763_; lean_object* v___x_764_; 
lean_inc(v_mvarId_756_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertAfter___lam__0___boxed), 7, 2);
lean_closure_set(v___f_763_, 0, v_fvarId_757_);
lean_closure_set(v___f_763_, 1, v_mvarId_756_);
v___x_764_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_756_, v___f_763_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___boxed(lean_object* v_mvarId_765_, lean_object* v_fvarId_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_MVarId_revertAfter(v_mvarId_765_, v_fvarId_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___lam__0(lean_object* v_fvarId_773_, lean_object* v_mvarId_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_773_, v___y_775_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v_lctx_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
v_lctx_782_ = lean_ctor_get(v___y_775_, 2);
v___x_783_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_784_ = l_Lean_LocalDecl_index(v_a_781_);
lean_dec(v_a_781_);
v___x_785_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_782_, v___x_783_, v___x_784_);
lean_dec(v___x_784_);
v___x_786_ = 1;
v___x_787_ = l_Lean_MVarId_revert(v_mvarId_774_, v___x_785_, v___x_786_, v___x_786_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
return v___x_787_;
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_mvarId_774_);
v_a_788_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_780_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_780_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___lam__0___boxed(lean_object* v_fvarId_796_, lean_object* v_mvarId_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_MVarId_revertFrom___lam__0(v_fvarId_796_, v_mvarId_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom(lean_object* v_mvarId_804_, lean_object* v_fvarId_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___f_811_; lean_object* v___x_812_; 
lean_inc(v_mvarId_804_);
v___f_811_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertFrom___lam__0___boxed), 7, 2);
lean_closure_set(v___f_811_, 0, v_fvarId_805_);
lean_closure_set(v___f_811_, 1, v_mvarId_804_);
v___x_812_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_804_, v___f_811_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___boxed(lean_object* v_mvarId_813_, lean_object* v_fvarId_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_MVarId_revertFrom(v_mvarId_813_, v_fvarId_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(lean_object* v_as_821_, size_t v_sz_822_, size_t v_i_823_, lean_object* v_b_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_a_830_; uint8_t v___x_834_; 
v___x_834_ = lean_usize_dec_lt(v_i_823_, v_sz_822_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v_b_824_);
return v___x_835_;
}
else
{
lean_object* v_a_836_; lean_object* v___x_837_; 
v_a_836_ = lean_array_uget_borrowed(v_as_821_, v_i_823_);
lean_inc(v_a_836_);
v___x_837_ = l_Lean_FVarId_getDecl___redArg(v_a_836_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; uint8_t v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = l_Lean_LocalDecl_isAuxDecl(v_a_838_);
lean_dec(v_a_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
lean_inc(v_a_836_);
v___x_840_ = lean_array_push(v_b_824_, v_a_836_);
v_a_830_ = v___x_840_;
goto v___jp_829_;
}
else
{
v_a_830_ = v_b_824_;
goto v___jp_829_;
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec_ref(v_b_824_);
v_a_841_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_837_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_837_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
v___jp_829_:
{
size_t v___x_831_; size_t v___x_832_; 
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_add(v_i_823_, v___x_831_);
v_i_823_ = v___x_832_;
v_b_824_ = v_a_830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg___boxed(lean_object* v_as_849_, lean_object* v_sz_850_, lean_object* v_i_851_, lean_object* v_b_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
size_t v_sz_boxed_857_; size_t v_i_boxed_858_; lean_object* v_res_859_; 
v_sz_boxed_857_ = lean_unbox_usize(v_sz_850_);
lean_dec(v_sz_850_);
v_i_boxed_858_ = lean_unbox_usize(v_i_851_);
lean_dec(v_i_851_);
v_res_859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_849_, v_sz_boxed_857_, v_i_boxed_858_, v_b_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec_ref(v_as_849_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lam__0(lean_object* v_mvarId_860_, lean_object* v___x_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; 
lean_inc(v_mvarId_860_);
v___x_867_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_860_, v___x_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_lctx_868_; lean_object* v___x_869_; lean_object* v___x_870_; size_t v_sz_871_; size_t v___x_872_; lean_object* v___x_873_; 
lean_dec_ref_known(v___x_867_, 1);
v_lctx_868_ = lean_ctor_get(v___y_862_, 2);
v___x_869_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_870_ = l_Lean_LocalContext_getFVarIds(v_lctx_868_);
v_sz_871_ = lean_array_size(v___x_870_);
v___x_872_ = ((size_t)0ULL);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v___x_870_, v_sz_871_, v___x_872_, v___x_869_, v___y_862_, v___y_864_, v___y_865_);
lean_dec_ref(v___x_870_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; uint8_t v___x_875_; lean_object* v___x_876_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
v___x_875_ = 1;
v___x_876_ = l_Lean_MVarId_revert(v_mvarId_860_, v_a_874_, v___x_875_, v___x_875_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_885_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_885_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_885_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_885_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_snd_881_; lean_object* v___x_883_; 
v_snd_881_ = lean_ctor_get(v_a_877_, 1);
lean_inc(v_snd_881_);
lean_dec(v_a_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v_snd_881_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_snd_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
v_a_886_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_876_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_876_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_mvarId_860_);
v_a_894_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_873_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_873_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_mvarId_860_);
v_a_902_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_867_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_867_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___lam__0___boxed(lean_object* v_mvarId_910_, lean_object* v___x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_MVarId_revertAll___lam__0(v_mvarId_910_, v___x_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll(lean_object* v_mvarId_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; lean_object* v___f_928_; lean_object* v___x_929_; 
v___x_927_ = ((lean_object*)(l_Lean_MVarId_revertAll___closed__1));
lean_inc(v_mvarId_921_);
v___f_928_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertAll___lam__0___boxed), 7, 2);
lean_closure_set(v___f_928_, 0, v_mvarId_921_);
lean_closure_set(v___f_928_, 1, v___x_927_);
v___x_929_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_921_, v___f_928_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAll___boxed(lean_object* v_mvarId_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_MVarId_revertAll(v_mvarId_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(lean_object* v_as_937_, size_t v_sz_938_, size_t v_i_939_, lean_object* v_b_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_937_, v_sz_938_, v_i_939_, v_b_940_, v___y_941_, v___y_943_, v___y_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___boxed(lean_object* v_as_947_, lean_object* v_sz_948_, lean_object* v_i_949_, lean_object* v_b_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
size_t v_sz_boxed_956_; size_t v_i_boxed_957_; lean_object* v_res_958_; 
v_sz_boxed_956_ = lean_unbox_usize(v_sz_948_);
lean_dec(v_sz_948_);
v_i_boxed_957_ = lean_unbox_usize(v_i_949_);
lean_dec(v_i_949_);
v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(v_as_947_, v_sz_boxed_956_, v_i_boxed_957_, v_b_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec_ref(v_as_947_);
return v_res_958_;
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
