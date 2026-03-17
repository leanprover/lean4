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
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_collectForwardDeps(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___y_107_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v_b_106_);
return v___x_118_;
}
else
{
lean_object* v_a_119_; lean_object* v___x_120_; 
v_a_119_ = lean_array_uget_borrowed(v_as_103_, v_i_105_);
lean_inc_ref(v___y_107_);
lean_inc(v_a_119_);
v___x_120_ = l_Lean_FVarId_getDecl___redArg(v_a_119_, v___y_107_, v___y_109_, v___y_110_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref(v___x_120_);
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
lean_dec_ref(v___x_130_);
v_a_113_ = v___x_122_;
goto v___jp_112_;
}
else
{
lean_dec_ref(v___y_107_);
return v___x_130_;
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec_ref(v___y_107_);
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
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v_b_190_);
return v___x_202_;
}
else
{
lean_object* v_a_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_a_203_ = lean_array_uget_borrowed(v_as_187_, v_i_189_);
v___x_204_ = l_Lean_Expr_fvarId_x21(v_a_203_);
lean_inc_ref(v___y_191_);
lean_inc(v___x_204_);
v___x_205_ = l_Lean_FVarId_getDecl___redArg(v___x_204_, v___y_191_, v___y_193_, v___y_194_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v_fst_207_; lean_object* v_snd_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_230_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref(v___x_205_);
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
lean_inc(v___y_194_);
lean_inc_ref(v___y_193_);
lean_inc(v___y_192_);
lean_inc_ref(v___y_191_);
v___x_217_ = l_Lean_MVarId_clear(v_fst_207_, v___x_204_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref(v___x_217_);
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
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
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
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
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
lean_dec_ref(v_as_239_);
return v_res_250_;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lam__0___closed__0(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_box(0);
v___x_252_ = lean_unsigned_to_nat(16u);
v___x_253_ = lean_mk_array(v___x_252_, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_MVarId_revert___lam__0___closed__2(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l_Lean_MVarId_revert___lam__0___closed__1));
v___x_256_ = l_Lean_stringToMessageData(v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0(lean_object* v_mvarId_257_, lean_object* v___x_258_, lean_object* v_fvarIds_259_, uint8_t v_preserveOrder_260_, uint8_t v___x_261_, lean_object* v___x_262_, uint8_t v_clearAuxDeclsInsteadOfRevert_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___y_270_; lean_object* v___y_271_; uint8_t v___y_272_; lean_object* v___y_273_; size_t v___y_274_; lean_object* v_a_275_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___x_490_; 
lean_inc(v_mvarId_257_);
v___x_490_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_257_, v___x_258_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_dec_ref(v___x_490_);
if (v_clearAuxDeclsInsteadOfRevert_263_ == 0)
{
lean_object* v___x_491_; size_t v_sz_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_491_ = lean_box(0);
v_sz_492_ = lean_array_size(v_fvarIds_259_);
v___x_493_ = ((size_t)0ULL);
lean_inc_ref(v___y_264_);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__4(v_fvarIds_259_, v_sz_492_, v___x_493_, v___x_491_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_dec_ref(v___x_494_);
v___y_325_ = v___y_264_;
v___y_326_ = v___y_265_;
v___y_327_ = v___y_266_;
v___y_328_ = v___y_267_;
goto v___jp_324_;
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___x_262_);
lean_dec_ref(v_fvarIds_259_);
lean_dec(v_mvarId_257_);
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
v___y_325_ = v___y_264_;
v___y_326_ = v___y_265_;
v___y_327_ = v___y_266_;
v___y_328_ = v___y_267_;
goto v___jp_324_;
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___x_262_);
lean_dec_ref(v_fvarIds_259_);
lean_dec(v_mvarId_257_);
v_a_503_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_490_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_490_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
v___jp_269_:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_MVarId_setKind___redArg(v___y_273_, v___y_272_, v___y_271_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_fst_277_; lean_object* v_snd_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v___x_276_);
v_fst_277_ = lean_ctor_get(v_a_275_, 0);
v_snd_278_ = lean_ctor_get(v_a_275_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v_a_275_);
if (v_isSharedCheck_315_ == 0)
{
v___x_280_ = v_a_275_;
v_isShared_281_ = v_isSharedCheck_315_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_snd_278_);
lean_inc(v_fst_277_);
lean_dec(v_a_275_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_315_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = l_Lean_Expr_getAppFn(v_fst_277_);
lean_dec(v_fst_277_);
v___x_283_ = l_Lean_Expr_mvarId_x21(v___x_282_);
lean_dec_ref(v___x_282_);
lean_inc(v___x_283_);
v___x_284_ = l_Lean_MVarId_setKind___redArg(v___x_283_, v___y_272_, v___y_271_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v___x_285_; 
lean_dec_ref(v___x_284_);
lean_inc(v___x_283_);
v___x_285_ = l_Lean_MVarId_setTag___redArg(v___x_283_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_297_; 
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v___x_285_, 0);
lean_dec(v_unused_298_);
v___x_287_ = v___x_285_;
v_isShared_288_ = v_isSharedCheck_297_;
goto v_resetjp_286_;
}
else
{
lean_dec(v___x_285_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_297_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
size_t v_sz_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v_sz_289_ = lean_array_size(v_snd_278_);
v___x_290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__2(v_sz_289_, v___y_274_, v_snd_278_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v___x_283_);
lean_ctor_set(v___x_280_, 0, v___x_290_);
v___x_292_ = v___x_280_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_283_);
v___x_292_ = v_reuseFailAlloc_296_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_294_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_292_);
v___x_294_ = v___x_287_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec(v___x_283_);
lean_del_object(v___x_280_);
lean_dec(v_snd_278_);
v_a_299_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_285_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_285_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec(v___x_283_);
lean_del_object(v___x_280_);
lean_dec(v_snd_278_);
lean_dec(v___y_271_);
lean_dec(v___y_270_);
v_a_307_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_284_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_284_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v_a_275_);
lean_dec(v___y_271_);
lean_dec(v___y_270_);
v_a_316_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_276_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_276_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
v___jp_324_:
{
size_t v_sz_329_; size_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_sz_329_ = lean_array_size(v_fvarIds_259_);
v___x_330_ = ((size_t)0ULL);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_revert_spec__0(v_sz_329_, v___x_330_, v_fvarIds_259_);
lean_inc_ref(v___y_325_);
v___x_332_ = l_Lean_Meta_collectForwardDeps(v___x_331_, v_preserveOrder_260_, v___x_261_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_334_; lean_object* v___x_335_; size_t v_sz_336_; lean_object* v___x_337_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_332_);
v___x_334_ = lean_mk_empty_array_with_capacity(v___x_262_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v_mvarId_257_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v_sz_336_ = lean_array_size(v_a_333_);
lean_inc(v___y_328_);
lean_inc_ref(v___y_327_);
lean_inc(v___y_326_);
lean_inc_ref(v___y_325_);
v___x_337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revert_spec__1(v_a_333_, v_sz_336_, v___x_330_, v___x_335_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v_a_333_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v_fst_339_; lean_object* v_snd_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_473_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref(v___x_337_);
v_fst_339_ = lean_ctor_get(v_a_338_, 0);
v_snd_340_ = lean_ctor_get(v_a_338_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_a_338_);
if (v_isSharedCheck_473_ == 0)
{
v___x_342_ = v_a_338_;
v_isShared_343_ = v_isSharedCheck_473_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_snd_340_);
lean_inc(v_fst_339_);
lean_dec(v_a_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_473_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; 
lean_inc(v_fst_339_);
v___x_344_ = l_Lean_MVarId_getTag(v_fst_339_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; uint8_t v___x_346_; lean_object* v___x_347_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref(v___x_344_);
v___x_346_ = 0;
lean_inc(v_fst_339_);
v___x_347_ = l_Lean_MVarId_setKind___redArg(v_fst_339_, v___x_346_, v___y_326_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_lctx_351_; lean_object* v_mctx_352_; lean_object* v_ngen_353_; lean_object* v_quotContext_354_; lean_object* v_nextMacroScope_355_; uint8_t v___x_356_; lean_object* v___x_358_; 
lean_dec_ref(v___x_347_);
v___x_348_ = lean_st_ref_get(v___y_326_);
v___x_349_ = lean_st_ref_get(v___y_328_);
v___x_350_ = lean_st_ref_get(v___y_328_);
v_lctx_351_ = lean_ctor_get(v___y_325_, 2);
v_mctx_352_ = lean_ctor_get(v___x_348_, 0);
lean_inc_ref(v_mctx_352_);
lean_dec(v___x_348_);
v_ngen_353_ = lean_ctor_get(v___x_349_, 2);
lean_inc_ref(v_ngen_353_);
lean_dec(v___x_349_);
v_quotContext_354_ = lean_ctor_get(v___y_327_, 10);
v_nextMacroScope_355_ = lean_ctor_get(v___x_350_, 1);
lean_inc(v_nextMacroScope_355_);
lean_dec(v___x_350_);
v___x_356_ = 2;
lean_inc_ref(v_lctx_351_);
lean_inc(v_quotContext_354_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v_lctx_351_);
lean_ctor_set(v___x_342_, 0, v_quotContext_354_);
v___x_358_ = v___x_342_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_quotContext_354_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_lctx_351_);
v___x_358_ = v_reuseFailAlloc_456_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = lean_obj_once(&l_Lean_MVarId_revert___lam__0___closed__0, &l_Lean_MVarId_revert___lam__0___closed__0_once, _init_l_Lean_MVarId_revert___lam__0___closed__0);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_262_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_361_, 0, v_mctx_352_);
lean_ctor_set(v___x_361_, 1, v_nextMacroScope_355_);
lean_ctor_set(v___x_361_, 2, v_ngen_353_);
lean_ctor_set(v___x_361_, 3, v___x_360_);
lean_inc(v_fst_339_);
v___x_362_ = l_Lean_MetavarContext_revert(v_snd_340_, v_fst_339_, v_preserveOrder_260_, v___x_358_, v___x_361_);
lean_dec_ref(v___x_358_);
lean_dec(v_snd_340_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v_a_364_; lean_object* v___x_365_; lean_object* v_mctx_366_; lean_object* v_nextMacroScope_367_; lean_object* v_ngen_368_; lean_object* v_cache_369_; lean_object* v_zetaDeltaFVarIds_370_; lean_object* v_postponed_371_; lean_object* v_diag_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v___y_327_);
lean_dec_ref(v___y_325_);
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
v_a_364_ = lean_ctor_get(v___x_362_, 1);
lean_inc(v_a_364_);
lean_dec_ref(v___x_362_);
v___x_365_ = lean_st_ref_take(v___y_326_);
v_mctx_366_ = lean_ctor_get(v_a_364_, 0);
lean_inc_ref(v_mctx_366_);
v_nextMacroScope_367_ = lean_ctor_get(v_a_364_, 1);
lean_inc(v_nextMacroScope_367_);
v_ngen_368_ = lean_ctor_get(v_a_364_, 2);
lean_inc_ref(v_ngen_368_);
lean_dec(v_a_364_);
v_cache_369_ = lean_ctor_get(v___x_365_, 1);
v_zetaDeltaFVarIds_370_ = lean_ctor_get(v___x_365_, 2);
v_postponed_371_ = lean_ctor_get(v___x_365_, 3);
v_diag_372_ = lean_ctor_get(v___x_365_, 4);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; 
v_unused_399_ = lean_ctor_get(v___x_365_, 0);
lean_dec(v_unused_399_);
v___x_374_ = v___x_365_;
v_isShared_375_ = v_isSharedCheck_398_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_diag_372_);
lean_inc(v_postponed_371_);
lean_inc(v_zetaDeltaFVarIds_370_);
lean_inc(v_cache_369_);
lean_dec(v___x_365_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_398_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v_mctx_366_);
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_mctx_366_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_cache_369_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_zetaDeltaFVarIds_370_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_postponed_371_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v_diag_372_);
v___x_377_ = v_reuseFailAlloc_397_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_env_380_; lean_object* v_auxDeclNGen_381_; lean_object* v_traceState_382_; lean_object* v_cache_383_; lean_object* v_messages_384_; lean_object* v_infoState_385_; lean_object* v_snapshotTasks_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_394_; 
v___x_378_ = lean_st_ref_set(v___y_326_, v___x_377_);
v___x_379_ = lean_st_ref_take(v___y_328_);
v_env_380_ = lean_ctor_get(v___x_379_, 0);
v_auxDeclNGen_381_ = lean_ctor_get(v___x_379_, 3);
v_traceState_382_ = lean_ctor_get(v___x_379_, 4);
v_cache_383_ = lean_ctor_get(v___x_379_, 5);
v_messages_384_ = lean_ctor_get(v___x_379_, 6);
v_infoState_385_ = lean_ctor_get(v___x_379_, 7);
v_snapshotTasks_386_ = lean_ctor_get(v___x_379_, 8);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; lean_object* v_unused_396_; 
v_unused_395_ = lean_ctor_get(v___x_379_, 2);
lean_dec(v_unused_395_);
v_unused_396_ = lean_ctor_get(v___x_379_, 1);
lean_dec(v_unused_396_);
v___x_388_ = v___x_379_;
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_snapshotTasks_386_);
lean_inc(v_infoState_385_);
lean_inc(v_messages_384_);
lean_inc(v_cache_383_);
lean_inc(v_traceState_382_);
lean_inc(v_auxDeclNGen_381_);
lean_inc(v_env_380_);
lean_dec(v___x_379_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_394_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 2, v_ngen_368_);
lean_ctor_set(v___x_388_, 1, v_nextMacroScope_367_);
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_env_380_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_nextMacroScope_367_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_ngen_368_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v_auxDeclNGen_381_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v_traceState_382_);
lean_ctor_set(v_reuseFailAlloc_393_, 5, v_cache_383_);
lean_ctor_set(v_reuseFailAlloc_393_, 6, v_messages_384_);
lean_ctor_set(v_reuseFailAlloc_393_, 7, v_infoState_385_);
lean_ctor_set(v_reuseFailAlloc_393_, 8, v_snapshotTasks_386_);
v___x_391_ = v_reuseFailAlloc_393_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; 
v___x_392_ = lean_st_ref_set(v___y_328_, v___x_391_);
lean_dec(v___y_328_);
v___y_270_ = v_a_345_;
v___y_271_ = v___y_326_;
v___y_272_ = v___x_356_;
v___y_273_ = v_fst_339_;
v___y_274_ = v___x_330_;
v_a_275_ = v_a_363_;
goto v___jp_269_;
}
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_401_; lean_object* v_mctx_402_; lean_object* v_nextMacroScope_403_; lean_object* v_ngen_404_; lean_object* v_cache_405_; lean_object* v_zetaDeltaFVarIds_406_; lean_object* v_postponed_407_; lean_object* v_diag_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_454_; 
lean_dec(v_a_345_);
v_a_400_ = lean_ctor_get(v___x_362_, 1);
lean_inc(v_a_400_);
lean_dec_ref(v___x_362_);
v___x_401_ = lean_st_ref_take(v___y_326_);
v_mctx_402_ = lean_ctor_get(v_a_400_, 0);
lean_inc_ref(v_mctx_402_);
v_nextMacroScope_403_ = lean_ctor_get(v_a_400_, 1);
lean_inc(v_nextMacroScope_403_);
v_ngen_404_ = lean_ctor_get(v_a_400_, 2);
lean_inc_ref(v_ngen_404_);
lean_dec(v_a_400_);
v_cache_405_ = lean_ctor_get(v___x_401_, 1);
v_zetaDeltaFVarIds_406_ = lean_ctor_get(v___x_401_, 2);
v_postponed_407_ = lean_ctor_get(v___x_401_, 3);
v_diag_408_ = lean_ctor_get(v___x_401_, 4);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; 
v_unused_455_ = lean_ctor_get(v___x_401_, 0);
lean_dec(v_unused_455_);
v___x_410_ = v___x_401_;
v_isShared_411_ = v_isSharedCheck_454_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_diag_408_);
lean_inc(v_postponed_407_);
lean_inc(v_zetaDeltaFVarIds_406_);
lean_inc(v_cache_405_);
lean_dec(v___x_401_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_454_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v_mctx_402_);
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_mctx_402_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_cache_405_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_zetaDeltaFVarIds_406_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_postponed_407_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_diag_408_);
v___x_413_ = v_reuseFailAlloc_453_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_env_416_; lean_object* v_auxDeclNGen_417_; lean_object* v_traceState_418_; lean_object* v_cache_419_; lean_object* v_messages_420_; lean_object* v_infoState_421_; lean_object* v_snapshotTasks_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_450_; 
v___x_414_ = lean_st_ref_set(v___y_326_, v___x_413_);
v___x_415_ = lean_st_ref_take(v___y_328_);
v_env_416_ = lean_ctor_get(v___x_415_, 0);
v_auxDeclNGen_417_ = lean_ctor_get(v___x_415_, 3);
v_traceState_418_ = lean_ctor_get(v___x_415_, 4);
v_cache_419_ = lean_ctor_get(v___x_415_, 5);
v_messages_420_ = lean_ctor_get(v___x_415_, 6);
v_infoState_421_ = lean_ctor_get(v___x_415_, 7);
v_snapshotTasks_422_ = lean_ctor_get(v___x_415_, 8);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; lean_object* v_unused_452_; 
v_unused_451_ = lean_ctor_get(v___x_415_, 2);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v___x_415_, 1);
lean_dec(v_unused_452_);
v___x_424_ = v___x_415_;
v_isShared_425_ = v_isSharedCheck_450_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_snapshotTasks_422_);
lean_inc(v_infoState_421_);
lean_inc(v_messages_420_);
lean_inc(v_cache_419_);
lean_inc(v_traceState_418_);
lean_inc(v_auxDeclNGen_417_);
lean_inc(v_env_416_);
lean_dec(v___x_415_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_450_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 2, v_ngen_404_);
lean_ctor_set(v___x_424_, 1, v_nextMacroScope_403_);
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_env_416_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_nextMacroScope_403_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v_ngen_404_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_auxDeclNGen_417_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v_traceState_418_);
lean_ctor_set(v_reuseFailAlloc_449_, 5, v_cache_419_);
lean_ctor_set(v_reuseFailAlloc_449_, 6, v_messages_420_);
lean_ctor_set(v_reuseFailAlloc_449_, 7, v_infoState_421_);
lean_ctor_set(v_reuseFailAlloc_449_, 8, v_snapshotTasks_422_);
v___x_427_ = v_reuseFailAlloc_449_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v_a_431_; lean_object* v___x_432_; 
v___x_428_ = lean_st_ref_set(v___y_328_, v___x_427_);
v___x_429_ = lean_obj_once(&l_Lean_MVarId_revert___lam__0___closed__2, &l_Lean_MVarId_revert___lam__0___closed__2_once, _init_l_Lean_MVarId_revert___lam__0___closed__2);
v___x_430_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v___x_429_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec_ref(v___y_325_);
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref(v___x_430_);
v___x_432_ = l_Lean_MVarId_setKind___redArg(v_fst_339_, v___x_356_, v___y_326_);
lean_dec(v___y_326_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v___x_432_, 0);
lean_dec(v_unused_440_);
v___x_434_ = v___x_432_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_dec(v___x_432_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 1);
lean_ctor_set(v___x_434_, 0, v_a_431_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_431_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec(v_a_431_);
v_a_441_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_432_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_432_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
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
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_a_345_);
lean_del_object(v___x_342_);
lean_dec(v_snd_340_);
lean_dec(v_fst_339_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___x_262_);
v_a_457_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_347_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_347_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_del_object(v___x_342_);
lean_dec(v_snd_340_);
lean_dec(v_fst_339_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___x_262_);
v_a_465_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_344_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_344_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___x_262_);
v_a_474_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_337_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_337_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___x_262_);
lean_dec(v_mvarId_257_);
v_a_482_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_332_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_332_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___lam__0___boxed(lean_object* v_mvarId_511_, lean_object* v___x_512_, lean_object* v_fvarIds_513_, lean_object* v_preserveOrder_514_, lean_object* v___x_515_, lean_object* v___x_516_, lean_object* v_clearAuxDeclsInsteadOfRevert_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v_preserveOrder_boxed_523_; uint8_t v___x_11237__boxed_524_; uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_525_; lean_object* v_res_526_; 
v_preserveOrder_boxed_523_ = lean_unbox(v_preserveOrder_514_);
v___x_11237__boxed_524_ = lean_unbox(v___x_515_);
v_clearAuxDeclsInsteadOfRevert_boxed_525_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_517_);
v_res_526_ = l_Lean_MVarId_revert___lam__0(v_mvarId_511_, v___x_512_, v_fvarIds_513_, v_preserveOrder_boxed_523_, v___x_11237__boxed_524_, v___x_516_, v_clearAuxDeclsInsteadOfRevert_boxed_525_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert(lean_object* v_mvarId_532_, lean_object* v_fvarIds_533_, uint8_t v_preserveOrder_534_, uint8_t v_clearAuxDeclsInsteadOfRevert_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_541_ = lean_array_get_size(v_fvarIds_533_);
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = lean_nat_dec_eq(v___x_541_, v___x_542_);
if (v___x_543_ == 0)
{
uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___f_549_; lean_object* v___x_550_; 
v___x_544_ = 1;
v___x_545_ = ((lean_object*)(l_Lean_MVarId_revert___closed__1));
v___x_546_ = lean_box(v_preserveOrder_534_);
v___x_547_ = lean_box(v___x_544_);
v___x_548_ = lean_box(v_clearAuxDeclsInsteadOfRevert_535_);
lean_inc(v_mvarId_532_);
v___f_549_ = lean_alloc_closure((void*)(l_Lean_MVarId_revert___lam__0___boxed), 12, 7);
lean_closure_set(v___f_549_, 0, v_mvarId_532_);
lean_closure_set(v___f_549_, 1, v___x_545_);
lean_closure_set(v___f_549_, 2, v_fvarIds_533_);
lean_closure_set(v___f_549_, 3, v___x_546_);
lean_closure_set(v___f_549_, 4, v___x_547_);
lean_closure_set(v___f_549_, 5, v___x_542_);
lean_closure_set(v___f_549_, 6, v___x_548_);
v___x_550_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_532_, v___f_549_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec_ref(v_fvarIds_533_);
v___x_551_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v_mvarId_532_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revert___boxed(lean_object* v_mvarId_554_, lean_object* v_fvarIds_555_, lean_object* v_preserveOrder_556_, lean_object* v_clearAuxDeclsInsteadOfRevert_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
uint8_t v_preserveOrder_boxed_563_; uint8_t v_clearAuxDeclsInsteadOfRevert_boxed_564_; lean_object* v_res_565_; 
v_preserveOrder_boxed_563_ = lean_unbox(v_preserveOrder_556_);
v_clearAuxDeclsInsteadOfRevert_boxed_564_ = lean_unbox(v_clearAuxDeclsInsteadOfRevert_557_);
v_res_565_ = l_Lean_MVarId_revert(v_mvarId_554_, v_fvarIds_555_, v_preserveOrder_boxed_563_, v_clearAuxDeclsInsteadOfRevert_boxed_564_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(lean_object* v_00_u03b1_566_, lean_object* v_msg_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___redArg(v_msg_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_MVarId_revert_spec__3___boxed(lean_object* v_00_u03b1_574_, lean_object* v_msg_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_throwError___at___00Lean_MVarId_revert_spec__3(v_00_u03b1_574_, v_msg_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(lean_object* v_as_582_, size_t v_i_583_, size_t v_stop_584_, lean_object* v_b_585_){
_start:
{
lean_object* v___y_587_; uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_eq(v_i_583_, v_stop_584_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_array_uget_borrowed(v_as_582_, v_i_583_);
if (lean_obj_tag(v___x_592_) == 0)
{
v___y_587_ = v_b_585_;
goto v___jp_586_;
}
else
{
lean_object* v_val_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_val_593_ = lean_ctor_get(v___x_592_, 0);
v___x_594_ = l_Lean_LocalDecl_fvarId(v_val_593_);
v___x_595_ = lean_array_push(v_b_585_, v___x_594_);
v___y_587_ = v___x_595_;
goto v___jp_586_;
}
}
else
{
return v_b_585_;
}
v___jp_586_:
{
size_t v___x_588_; size_t v___x_589_; 
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_add(v_i_583_, v___x_588_);
v_i_583_ = v___x_589_;
v_b_585_ = v___y_587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2___boxed(lean_object* v_as_596_, lean_object* v_i_597_, lean_object* v_stop_598_, lean_object* v_b_599_){
_start:
{
size_t v_i_boxed_600_; size_t v_stop_boxed_601_; lean_object* v_res_602_; 
v_i_boxed_600_ = lean_unbox_usize(v_i_597_);
lean_dec(v_i_597_);
v_stop_boxed_601_ = lean_unbox_usize(v_stop_598_);
lean_dec(v_stop_598_);
v_res_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_as_596_, v_i_boxed_600_, v_stop_boxed_601_, v_b_599_);
lean_dec_ref(v_as_596_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
if (lean_obj_tag(v_x_603_) == 0)
{
lean_object* v_cs_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_cs_605_ = lean_ctor_get(v_x_603_, 0);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_array_get_size(v_cs_605_);
v___x_608_ = lean_nat_dec_lt(v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
return v_x_604_;
}
else
{
uint8_t v___x_609_; 
v___x_609_ = lean_nat_dec_le(v___x_607_, v___x_607_);
if (v___x_609_ == 0)
{
if (v___x_608_ == 0)
{
return v_x_604_;
}
else
{
size_t v___x_610_; size_t v___x_611_; lean_object* v___x_612_; 
v___x_610_ = ((size_t)0ULL);
v___x_611_ = lean_usize_of_nat(v___x_607_);
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_605_, v___x_610_, v___x_611_, v_x_604_);
return v___x_612_;
}
}
else
{
size_t v___x_613_; size_t v___x_614_; lean_object* v___x_615_; 
v___x_613_ = ((size_t)0ULL);
v___x_614_ = lean_usize_of_nat(v___x_607_);
v___x_615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_605_, v___x_613_, v___x_614_, v_x_604_);
return v___x_615_;
}
}
}
else
{
lean_object* v_vs_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_vs_616_ = lean_ctor_get(v_x_603_, 0);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = lean_array_get_size(v_vs_616_);
v___x_619_ = lean_nat_dec_lt(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
return v_x_604_;
}
else
{
uint8_t v___x_620_; 
v___x_620_ = lean_nat_dec_le(v___x_618_, v___x_618_);
if (v___x_620_ == 0)
{
if (v___x_619_ == 0)
{
return v_x_604_;
}
else
{
size_t v___x_621_; size_t v___x_622_; lean_object* v___x_623_; 
v___x_621_ = ((size_t)0ULL);
v___x_622_ = lean_usize_of_nat(v___x_618_);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_616_, v___x_621_, v___x_622_, v_x_604_);
return v___x_623_;
}
}
else
{
size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; 
v___x_624_ = ((size_t)0ULL);
v___x_625_ = lean_usize_of_nat(v___x_618_);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_616_, v___x_624_, v___x_625_, v_x_604_);
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(lean_object* v_as_627_, size_t v_i_628_, size_t v_stop_629_, lean_object* v_b_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = lean_usize_dec_eq(v_i_628_, v_stop_629_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; size_t v___x_634_; size_t v___x_635_; 
v___x_632_ = lean_array_uget_borrowed(v_as_627_, v_i_628_);
v___x_633_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v___x_632_, v_b_630_);
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_add(v_i_628_, v___x_634_);
v_i_628_ = v___x_635_;
v_b_630_ = v___x_633_;
goto _start;
}
else
{
return v_b_630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_as_637_, lean_object* v_i_638_, lean_object* v_stop_639_, lean_object* v_b_640_){
_start:
{
size_t v_i_boxed_641_; size_t v_stop_boxed_642_; lean_object* v_res_643_; 
v_i_boxed_641_ = lean_unbox_usize(v_i_638_);
lean_dec(v_i_638_);
v_stop_boxed_642_ = lean_unbox_usize(v_stop_639_);
lean_dec(v_stop_639_);
v_res_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_as_637_, v_i_boxed_641_, v_stop_boxed_642_, v_b_640_);
lean_dec_ref(v_as_637_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3___boxed(lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v_x_644_, v_x_645_);
lean_dec_ref(v_x_644_);
return v_res_646_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(lean_object* v_x_648_, size_t v_x_649_, size_t v_x_650_, lean_object* v_x_651_){
_start:
{
if (lean_obj_tag(v_x_648_) == 0)
{
lean_object* v_cs_652_; lean_object* v___x_653_; size_t v___x_654_; lean_object* v_j_655_; lean_object* v___x_656_; size_t v___x_657_; size_t v___x_658_; size_t v___x_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_cs_652_ = lean_ctor_get(v_x_648_, 0);
v___x_653_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___closed__0);
v___x_654_ = lean_usize_shift_right(v_x_649_, v_x_650_);
v_j_655_ = lean_usize_to_nat(v___x_654_);
v___x_656_ = lean_array_get_borrowed(v___x_653_, v_cs_652_, v_j_655_);
v___x_657_ = ((size_t)1ULL);
v___x_658_ = lean_usize_shift_left(v___x_657_, v_x_650_);
v___x_659_ = lean_usize_sub(v___x_658_, v___x_657_);
v___x_660_ = lean_usize_land(v_x_649_, v___x_659_);
v___x_661_ = ((size_t)5ULL);
v___x_662_ = lean_usize_sub(v_x_650_, v___x_661_);
v___x_663_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v___x_656_, v___x_660_, v___x_662_, v_x_651_);
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_nat_add(v_j_655_, v___x_664_);
lean_dec(v_j_655_);
v___x_666_ = lean_array_get_size(v_cs_652_);
v___x_667_ = lean_nat_dec_lt(v___x_665_, v___x_666_);
if (v___x_667_ == 0)
{
lean_dec(v___x_665_);
return v___x_663_;
}
else
{
uint8_t v___x_668_; 
v___x_668_ = lean_nat_dec_le(v___x_666_, v___x_666_);
if (v___x_668_ == 0)
{
if (v___x_667_ == 0)
{
lean_dec(v___x_665_);
return v___x_663_;
}
else
{
size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_usize_of_nat(v___x_665_);
lean_dec(v___x_665_);
v___x_670_ = lean_usize_of_nat(v___x_666_);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_652_, v___x_669_, v___x_670_, v___x_663_);
return v___x_671_;
}
}
else
{
size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_usize_of_nat(v___x_665_);
lean_dec(v___x_665_);
v___x_673_ = lean_usize_of_nat(v___x_666_);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1_spec__2(v_cs_652_, v___x_672_, v___x_673_, v___x_663_);
return v___x_674_;
}
}
}
else
{
lean_object* v_vs_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_vs_675_ = lean_ctor_get(v_x_648_, 0);
v___x_676_ = lean_usize_to_nat(v_x_649_);
v___x_677_ = lean_array_get_size(v_vs_675_);
v___x_678_ = lean_nat_dec_lt(v___x_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_dec(v___x_676_);
return v_x_651_;
}
else
{
uint8_t v___x_679_; 
v___x_679_ = lean_nat_dec_le(v___x_677_, v___x_677_);
if (v___x_679_ == 0)
{
if (v___x_678_ == 0)
{
lean_dec(v___x_676_);
return v_x_651_;
}
else
{
size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_usize_of_nat(v___x_676_);
lean_dec(v___x_676_);
v___x_681_ = lean_usize_of_nat(v___x_677_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_675_, v___x_680_, v___x_681_, v_x_651_);
return v___x_682_;
}
}
else
{
size_t v___x_683_; size_t v___x_684_; lean_object* v___x_685_; 
v___x_683_ = lean_usize_of_nat(v___x_676_);
lean_dec(v___x_676_);
v___x_684_ = lean_usize_of_nat(v___x_677_);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_vs_675_, v___x_683_, v___x_684_, v_x_651_);
return v___x_685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1___boxed(lean_object* v_x_686_, lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
size_t v_x_1746__boxed_690_; size_t v_x_1747__boxed_691_; lean_object* v_res_692_; 
v_x_1746__boxed_690_ = lean_unbox_usize(v_x_687_);
lean_dec(v_x_687_);
v_x_1747__boxed_691_ = lean_unbox_usize(v_x_688_);
lean_dec(v_x_688_);
v_res_692_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__1(v_x_686_, v_x_1746__boxed_690_, v_x_1747__boxed_691_, v_x_689_);
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
uint8_t v___x_707_; 
v___x_707_ = lean_nat_dec_le(v___x_705_, v___x_705_);
if (v___x_707_ == 0)
{
if (v___x_706_ == 0)
{
return v___x_704_;
}
else
{
size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; 
v___x_708_ = ((size_t)0ULL);
v___x_709_ = lean_usize_of_nat(v___x_705_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_699_, v___x_708_, v___x_709_, v___x_704_);
return v___x_710_;
}
}
else
{
size_t v___x_711_; size_t v___x_712_; lean_object* v___x_713_; 
v___x_711_ = ((size_t)0ULL);
v___x_712_ = lean_usize_of_nat(v___x_705_);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_699_, v___x_711_, v___x_712_, v___x_704_);
return v___x_713_;
}
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_714_ = lean_nat_sub(v_start_695_, v_tailOff_701_);
v___x_715_ = lean_array_get_size(v_tail_699_);
v___x_716_ = lean_nat_dec_lt(v___x_714_, v___x_715_);
if (v___x_716_ == 0)
{
lean_dec(v___x_714_);
return v_init_694_;
}
else
{
uint8_t v___x_717_; 
v___x_717_ = lean_nat_dec_le(v___x_715_, v___x_715_);
if (v___x_717_ == 0)
{
if (v___x_716_ == 0)
{
lean_dec(v___x_714_);
return v_init_694_;
}
else
{
size_t v___x_718_; size_t v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_usize_of_nat(v___x_714_);
lean_dec(v___x_714_);
v___x_719_ = lean_usize_of_nat(v___x_715_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_699_, v___x_718_, v___x_719_, v_init_694_);
return v___x_720_;
}
}
else
{
size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_usize_of_nat(v___x_714_);
lean_dec(v___x_714_);
v___x_722_ = lean_usize_of_nat(v___x_715_);
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_699_, v___x_721_, v___x_722_, v_init_694_);
return v___x_723_;
}
}
}
}
else
{
lean_object* v_root_724_; lean_object* v_tail_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_root_724_ = lean_ctor_get(v_t_693_, 0);
v_tail_725_ = lean_ctor_get(v_t_693_, 1);
v___x_726_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__3(v_root_724_, v_init_694_);
v___x_727_ = lean_array_get_size(v_tail_725_);
v___x_728_ = lean_nat_dec_lt(v___x_696_, v___x_727_);
if (v___x_728_ == 0)
{
return v___x_726_;
}
else
{
uint8_t v___x_729_; 
v___x_729_ = lean_nat_dec_le(v___x_727_, v___x_727_);
if (v___x_729_ == 0)
{
if (v___x_728_ == 0)
{
return v___x_726_;
}
else
{
size_t v___x_730_; size_t v___x_731_; lean_object* v___x_732_; 
v___x_730_ = ((size_t)0ULL);
v___x_731_ = lean_usize_of_nat(v___x_727_);
v___x_732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_725_, v___x_730_, v___x_731_, v___x_726_);
return v___x_732_;
}
}
else
{
size_t v___x_733_; size_t v___x_734_; lean_object* v___x_735_; 
v___x_733_ = ((size_t)0ULL);
v___x_734_ = lean_usize_of_nat(v___x_727_);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0_spec__2(v_tail_725_, v___x_733_, v___x_734_, v___x_726_);
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0___boxed(lean_object* v_t_736_, lean_object* v_init_737_, lean_object* v_start_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_t_736_, v_init_737_, v_start_738_);
lean_dec(v_start_738_);
lean_dec_ref(v_t_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(lean_object* v_lctx_740_, lean_object* v_init_741_, lean_object* v_start_742_){
_start:
{
lean_object* v_decls_743_; lean_object* v___x_744_; 
v_decls_743_ = lean_ctor_get(v_lctx_740_, 1);
v___x_744_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0_spec__0(v_decls_743_, v_init_741_, v_start_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0___boxed(lean_object* v_lctx_745_, lean_object* v_init_746_, lean_object* v_start_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_745_, v_init_746_, v_start_747_);
lean_dec(v_start_747_);
lean_dec_ref(v_lctx_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lam__0(lean_object* v_fvarId_749_, lean_object* v_mvarId_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
lean_inc_ref(v___y_751_);
v___x_756_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_749_, v___y_751_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v_lctx_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; lean_object* v___x_765_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref(v___x_756_);
v_lctx_758_ = lean_ctor_get(v___y_751_, 2);
v___x_759_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_760_ = l_Lean_LocalDecl_index(v_a_757_);
lean_dec(v_a_757_);
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_add(v___x_760_, v___x_761_);
lean_dec(v___x_760_);
v___x_763_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_758_, v___x_759_, v___x_762_);
lean_dec(v___x_762_);
v___x_764_ = 1;
v___x_765_ = l_Lean_MVarId_revert(v_mvarId_750_, v___x_763_, v___x_764_, v___x_764_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
return v___x_765_;
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v_mvarId_750_);
v_a_766_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_756_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_756_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___lam__0___boxed(lean_object* v_fvarId_774_, lean_object* v_mvarId_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_MVarId_revertAfter___lam__0(v_fvarId_774_, v_mvarId_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter(lean_object* v_mvarId_782_, lean_object* v_fvarId_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___f_789_; lean_object* v___x_790_; 
lean_inc(v_mvarId_782_);
v___f_789_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertAfter___lam__0___boxed), 7, 2);
lean_closure_set(v___f_789_, 0, v_fvarId_783_);
lean_closure_set(v___f_789_, 1, v_mvarId_782_);
v___x_790_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_782_, v___f_789_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertAfter___boxed(lean_object* v_mvarId_791_, lean_object* v_fvarId_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_MVarId_revertAfter(v_mvarId_791_, v_fvarId_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___lam__0(lean_object* v_fvarId_799_, lean_object* v_mvarId_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; 
lean_inc_ref(v___y_801_);
v___x_806_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_799_, v___y_801_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v_lctx_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; lean_object* v___x_813_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v___x_806_);
v_lctx_808_ = lean_ctor_get(v___y_801_, 2);
v___x_809_ = ((lean_object*)(l_Lean_MVarId_revert___closed__2));
v___x_810_ = l_Lean_LocalDecl_index(v_a_807_);
lean_dec(v_a_807_);
v___x_811_ = l_Lean_LocalContext_foldlM___at___00Lean_MVarId_revertAfter_spec__0(v_lctx_808_, v___x_809_, v___x_810_);
lean_dec(v___x_810_);
v___x_812_ = 1;
v___x_813_ = l_Lean_MVarId_revert(v_mvarId_800_, v___x_811_, v___x_812_, v___x_812_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
return v___x_813_;
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v_mvarId_800_);
v_a_814_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_806_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_806_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___lam__0___boxed(lean_object* v_fvarId_822_, lean_object* v_mvarId_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_MVarId_revertFrom___lam__0(v_fvarId_822_, v_mvarId_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom(lean_object* v_mvarId_830_, lean_object* v_fvarId_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___f_837_; lean_object* v___x_838_; 
lean_inc(v_mvarId_830_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_MVarId_revertFrom___lam__0___boxed), 7, 2);
lean_closure_set(v___f_837_, 0, v_fvarId_831_);
lean_closure_set(v___f_837_, 1, v_mvarId_830_);
v___x_838_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_revert_spec__5___redArg(v_mvarId_830_, v___f_837_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_revertFrom___boxed(lean_object* v_mvarId_839_, lean_object* v_fvarId_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_MVarId_revertFrom(v_mvarId_839_, v_fvarId_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
return v_res_846_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Clear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Revert(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
