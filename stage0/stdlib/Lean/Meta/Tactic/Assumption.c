// Lean compiler output
// Module: Lean.Meta.Tactic.Assumption
// Imports: public import Lean.Meta.Tactic.Util
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_findLocalDeclWithType_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_assumptionCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l_Lean_MVarId_assumptionCore___closed__0 = (const lean_object*)&l_Lean_MVarId_assumptionCore___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_assumptionCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_assumptionCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 18, 34, 73, 19, 20, 120, 164)}};
static const lean_object* l_Lean_MVarId_assumptionCore___closed__1 = (const lean_object*)&l_Lean_MVarId_assumptionCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assumption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_type_1_, lean_object* v_as_2_, lean_object* v_i_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v_zero_9_; uint8_t v_isZero_10_; 
v_zero_9_ = lean_unsigned_to_nat(0u);
v_isZero_10_ = lean_nat_dec_eq(v_i_3_, v_zero_9_);
if (v_isZero_10_ == 1)
{
lean_object* v___x_11_; lean_object* v___x_12_; 
lean_dec(v_i_3_);
lean_dec_ref(v_type_1_);
v___x_11_ = lean_box(0);
v___x_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
else
{
lean_object* v_one_13_; lean_object* v_n_14_; lean_object* v___x_15_; 
v_one_13_ = lean_unsigned_to_nat(1u);
v_n_14_ = lean_nat_sub(v_i_3_, v_one_13_);
lean_dec(v_i_3_);
v___x_15_ = lean_array_fget(v_as_2_, v_n_14_);
if (lean_obj_tag(v___x_15_) == 0)
{
v_i_3_ = v_n_14_;
goto _start;
}
else
{
lean_object* v_val_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_47_; 
v_val_17_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_47_ == 0)
{
v___x_19_ = v___x_15_;
v_isShared_20_ = v_isSharedCheck_47_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_val_17_);
lean_dec(v___x_15_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_47_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
uint8_t v___x_21_; 
v___x_21_ = l_Lean_LocalDecl_isImplementationDetail(v_val_17_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = l_Lean_LocalDecl_type(v_val_17_);
lean_inc_ref(v_type_1_);
v___x_23_ = l_Lean_Meta_isExprDefEq(v_type_1_, v___x_22_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_37_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_37_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_37_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_37_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
uint8_t v___x_28_; 
v___x_28_ = lean_unbox(v_a_24_);
lean_dec(v_a_24_);
if (v___x_28_ == 0)
{
lean_del_object(v___x_26_);
lean_del_object(v___x_19_);
lean_dec(v_val_17_);
v_i_3_ = v_n_14_;
goto _start;
}
else
{
lean_object* v___x_30_; lean_object* v___x_32_; 
lean_dec(v_n_14_);
lean_dec_ref(v_type_1_);
v___x_30_ = l_Lean_LocalDecl_fvarId(v_val_17_);
lean_dec(v_val_17_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v___x_30_);
v___x_32_ = v___x_19_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_36_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_34_; 
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_32_);
v___x_34_ = v___x_26_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_32_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
lean_del_object(v___x_19_);
lean_dec(v_val_17_);
lean_dec(v_n_14_);
lean_dec_ref(v_type_1_);
v_a_38_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_23_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_23_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
else
{
lean_del_object(v___x_19_);
lean_dec(v_val_17_);
v_i_3_ = v_n_14_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_type_48_, lean_object* v_as_49_, lean_object* v_i_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_48_, v_as_49_, v_i_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec_ref(v_as_49_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_type_57_, lean_object* v_as_58_, lean_object* v_i_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_zero_65_; uint8_t v_isZero_66_; 
v_zero_65_ = lean_unsigned_to_nat(0u);
v_isZero_66_ = lean_nat_dec_eq(v_i_59_, v_zero_65_);
if (v_isZero_66_ == 1)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_i_59_);
lean_dec_ref(v_type_57_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
else
{
lean_object* v_one_69_; lean_object* v_n_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_one_69_ = lean_unsigned_to_nat(1u);
v_n_70_ = lean_nat_sub(v_i_59_, v_one_69_);
lean_dec(v_i_59_);
v___x_71_ = lean_array_fget_borrowed(v_as_58_, v_n_70_);
lean_inc_ref(v_type_57_);
v___x_72_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(v_type_57_, v___x_71_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
if (lean_obj_tag(v_a_73_) == 0)
{
lean_dec_ref_known(v___x_72_, 1);
v_i_59_ = v_n_70_;
goto _start;
}
else
{
lean_dec_ref_known(v_a_73_, 1);
lean_dec(v_n_70_);
lean_dec_ref(v_type_57_);
return v___x_72_;
}
}
else
{
lean_dec(v_n_70_);
lean_dec_ref(v_type_57_);
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(lean_object* v_type_75_, lean_object* v_x_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
if (lean_obj_tag(v_x_76_) == 0)
{
lean_object* v_cs_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_cs_82_ = lean_ctor_get(v_x_76_, 0);
v___x_83_ = lean_array_get_size(v_cs_82_);
v___x_84_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_type_75_, v_cs_82_, v___x_83_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
return v___x_84_;
}
else
{
lean_object* v_vs_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_vs_85_ = lean_ctor_get(v_x_76_, 0);
v___x_86_ = lean_array_get_size(v_vs_85_);
v___x_87_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_75_, v_vs_85_, v___x_86_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_type_88_, lean_object* v_x_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(v_type_88_, v_x_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec_ref(v_x_89_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_type_96_, lean_object* v_as_97_, lean_object* v_i_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_type_96_, v_as_97_, v_i_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec_ref(v_as_97_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0(lean_object* v_type_105_, lean_object* v_t_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_root_112_; lean_object* v_tail_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_root_112_ = lean_ctor_get(v_t_106_, 0);
v_tail_113_ = lean_ctor_get(v_t_106_, 1);
v___x_114_ = lean_array_get_size(v_tail_113_);
lean_inc_ref(v_type_105_);
v___x_115_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_105_, v_tail_113_, v___x_114_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
if (lean_obj_tag(v_a_116_) == 0)
{
lean_object* v___x_117_; 
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(v_type_105_, v_root_112_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
return v___x_117_;
}
else
{
lean_dec_ref_known(v_a_116_, 1);
lean_dec_ref(v_type_105_);
return v___x_115_;
}
}
else
{
lean_dec_ref(v_type_105_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0___boxed(lean_object* v_type_118_, lean_object* v_t_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0(v_type_118_, v_t_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec_ref(v_t_119_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0(lean_object* v_type_126_, lean_object* v_lctx_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_decls_133_; lean_object* v___x_134_; 
v_decls_133_ = lean_ctor_get(v_lctx_127_, 1);
v___x_134_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0(v_type_126_, v_decls_133_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0___boxed(lean_object* v_type_135_, lean_object* v_lctx_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0(v_type_135_, v_lctx_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec_ref(v_lctx_136_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object* v_type_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_lctx_149_; lean_object* v___x_150_; 
v_lctx_149_ = lean_ctor_get(v_a_144_, 2);
v___x_150_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0(v_type_143_, v_lctx_149_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_findLocalDeclWithType_x3f___boxed(lean_object* v_type_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_type_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1(lean_object* v_type_158_, lean_object* v_as_159_, lean_object* v_i_160_, lean_object* v_a_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_158_, v_as_159_, v_i_160_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_type_168_, lean_object* v_as_169_, lean_object* v_i_170_, lean_object* v_a_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1(v_type_168_, v_as_169_, v_i_170_, v_a_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec_ref(v_as_169_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_type_178_, lean_object* v_as_179_, lean_object* v_i_180_, lean_object* v_a_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_type_178_, v_as_179_, v_i_180_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_type_188_, lean_object* v_as_189_, lean_object* v_i_190_, lean_object* v_a_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3(v_type_188_, v_as_189_, v_i_190_, v_a_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec_ref(v_as_189_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(lean_object* v_mvarId_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
v_a_214_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_205_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_205_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg___boxed(lean_object* v_mvarId_222_, lean_object* v_x_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(v_mvarId_222_, v_x_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1(lean_object* v_00_u03b1_230_, lean_object* v_mvarId_231_, lean_object* v_x_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(v_mvarId_231_, v_x_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___boxed(lean_object* v_00_u03b1_239_, lean_object* v_mvarId_240_, lean_object* v_x_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1(v_00_u03b1_239_, v_mvarId_240_, v_x_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_ks_252_; lean_object* v_vs_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_277_; 
v_ks_252_ = lean_ctor_get(v_x_248_, 0);
v_vs_253_ = lean_ctor_get(v_x_248_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_248_);
if (v_isSharedCheck_277_ == 0)
{
v___x_255_ = v_x_248_;
v_isShared_256_ = v_isSharedCheck_277_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_vs_253_);
lean_inc(v_ks_252_);
lean_dec(v_x_248_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_277_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_get_size(v_ks_252_);
v___x_258_ = lean_nat_dec_lt(v_x_249_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec(v_x_249_);
v___x_259_ = lean_array_push(v_ks_252_, v_x_250_);
v___x_260_ = lean_array_push(v_vs_253_, v_x_251_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_260_);
lean_ctor_set(v___x_255_, 0, v___x_259_);
v___x_262_ = v___x_255_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
lean_object* v_k_x27_264_; uint8_t v___x_265_; 
v_k_x27_264_ = lean_array_fget_borrowed(v_ks_252_, v_x_249_);
v___x_265_ = l_Lean_instBEqMVarId_beq(v_x_250_, v_k_x27_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_267_; 
if (v_isShared_256_ == 0)
{
v___x_267_ = v___x_255_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_ks_252_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_vs_253_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_x_249_, v___x_268_);
lean_dec(v_x_249_);
v_x_248_ = v___x_267_;
v_x_249_ = v___x_269_;
goto _start;
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_array_fset(v_ks_252_, v_x_249_, v_x_250_);
v___x_273_ = lean_array_fset(v_vs_253_, v_x_249_, v_x_251_);
lean_dec(v_x_249_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_273_);
lean_ctor_set(v___x_255_, 0, v___x_272_);
v___x_275_ = v___x_255_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_278_, lean_object* v_k_279_, lean_object* v_v_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_278_, v___x_281_, v_k_279_, v_v_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_284_, size_t v_x_285_, size_t v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v_es_289_; size_t v___x_290_; size_t v___x_291_; lean_object* v_j_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_es_289_ = lean_ctor_get(v_x_284_, 0);
v___x_290_ = ((size_t)31ULL);
v___x_291_ = lean_usize_land(v_x_285_, v___x_290_);
v_j_292_ = lean_usize_to_nat(v___x_291_);
v___x_293_ = lean_array_get_size(v_es_289_);
v___x_294_ = lean_nat_dec_lt(v_j_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_dec(v_j_292_);
lean_dec(v_x_288_);
lean_dec(v_x_287_);
return v_x_284_;
}
else
{
lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_333_; 
lean_inc_ref(v_es_289_);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v_x_284_, 0);
lean_dec(v_unused_334_);
v___x_296_ = v_x_284_;
v_isShared_297_ = v_isSharedCheck_333_;
goto v_resetjp_295_;
}
else
{
lean_dec(v_x_284_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_333_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_v_298_; lean_object* v___x_299_; lean_object* v_xs_x27_300_; lean_object* v___y_302_; 
v_v_298_ = lean_array_fget(v_es_289_, v_j_292_);
v___x_299_ = lean_box(0);
v_xs_x27_300_ = lean_array_fset(v_es_289_, v_j_292_, v___x_299_);
switch(lean_obj_tag(v_v_298_))
{
case 0:
{
lean_object* v_key_307_; lean_object* v_val_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_318_; 
v_key_307_ = lean_ctor_get(v_v_298_, 0);
v_val_308_ = lean_ctor_get(v_v_298_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_v_298_);
if (v_isSharedCheck_318_ == 0)
{
v___x_310_ = v_v_298_;
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_val_308_);
lean_inc(v_key_307_);
lean_dec(v_v_298_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
uint8_t v___x_312_; 
v___x_312_ = l_Lean_instBEqMVarId_beq(v_x_287_, v_key_307_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_del_object(v___x_310_);
v___x_313_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_307_, v_val_308_, v_x_287_, v_x_288_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
v___y_302_ = v___x_314_;
goto v___jp_301_;
}
else
{
lean_object* v___x_316_; 
lean_dec(v_val_308_);
lean_dec(v_key_307_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v_x_288_);
lean_ctor_set(v___x_310_, 0, v_x_287_);
v___x_316_ = v___x_310_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_x_287_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_x_288_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
v___y_302_ = v___x_316_;
goto v___jp_301_;
}
}
}
}
case 1:
{
lean_object* v_node_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_331_; 
v_node_319_ = lean_ctor_get(v_v_298_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_v_298_);
if (v_isSharedCheck_331_ == 0)
{
v___x_321_ = v_v_298_;
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_node_319_);
lean_dec(v_v_298_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_323_ = ((size_t)5ULL);
v___x_324_ = lean_usize_shift_right(v_x_285_, v___x_323_);
v___x_325_ = ((size_t)1ULL);
v___x_326_ = lean_usize_add(v_x_286_, v___x_325_);
v___x_327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_node_319_, v___x_324_, v___x_326_, v_x_287_, v_x_288_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_327_);
v___x_329_ = v___x_321_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
v___y_302_ = v___x_329_;
goto v___jp_301_;
}
}
}
default: 
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v_x_287_);
lean_ctor_set(v___x_332_, 1, v_x_288_);
v___y_302_ = v___x_332_;
goto v___jp_301_;
}
}
v___jp_301_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = lean_array_fset(v_xs_x27_300_, v_j_292_, v___y_302_);
lean_dec(v_j_292_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_303_);
v___x_305_ = v___x_296_;
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
}
else
{
lean_object* v_ks_335_; lean_object* v_vs_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_354_; 
v_ks_335_ = lean_ctor_get(v_x_284_, 0);
v_vs_336_ = lean_ctor_get(v_x_284_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_354_ == 0)
{
v___x_338_ = v_x_284_;
v_isShared_339_ = v_isSharedCheck_354_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_vs_336_);
lean_inc(v_ks_335_);
lean_dec(v_x_284_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_354_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_ks_335_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_vs_336_);
v___x_341_ = v_reuseFailAlloc_353_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v_newNode_342_; size_t v___x_343_; uint8_t v___x_344_; 
v_newNode_342_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(v___x_341_, v_x_287_, v_x_288_);
v___x_343_ = ((size_t)7ULL);
v___x_344_ = lean_usize_dec_le(v___x_343_, v_x_286_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_345_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_342_);
v___x_346_ = lean_unsigned_to_nat(4u);
v___x_347_ = lean_nat_dec_lt(v___x_345_, v___x_346_);
lean_dec(v___x_345_);
if (v___x_347_ == 0)
{
lean_object* v_ks_348_; lean_object* v_vs_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_ks_348_ = lean_ctor_get(v_newNode_342_, 0);
lean_inc_ref(v_ks_348_);
v_vs_349_ = lean_ctor_get(v_newNode_342_, 1);
lean_inc_ref(v_vs_349_);
lean_dec_ref(v_newNode_342_);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_352_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_x_286_, v_ks_348_, v_vs_349_, v___x_350_, v___x_351_);
lean_dec_ref(v_vs_349_);
lean_dec_ref(v_ks_348_);
return v___x_352_;
}
else
{
return v_newNode_342_;
}
}
else
{
return v_newNode_342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_355_, lean_object* v_keys_356_, lean_object* v_vals_357_, lean_object* v_i_358_, lean_object* v_entries_359_){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = lean_array_get_size(v_keys_356_);
v___x_361_ = lean_nat_dec_lt(v_i_358_, v___x_360_);
if (v___x_361_ == 0)
{
lean_dec(v_i_358_);
return v_entries_359_;
}
else
{
lean_object* v_k_362_; lean_object* v_v_363_; uint64_t v___x_364_; size_t v_h_365_; size_t v___x_366_; lean_object* v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v_h_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_k_362_ = lean_array_fget_borrowed(v_keys_356_, v_i_358_);
v_v_363_ = lean_array_fget_borrowed(v_vals_357_, v_i_358_);
v___x_364_ = l_Lean_instHashableMVarId_hash(v_k_362_);
v_h_365_ = lean_uint64_to_usize(v___x_364_);
v___x_366_ = ((size_t)5ULL);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_sub(v_depth_355_, v___x_368_);
v___x_370_ = lean_usize_mul(v___x_366_, v___x_369_);
v_h_371_ = lean_usize_shift_right(v_h_365_, v___x_370_);
v___x_372_ = lean_nat_add(v_i_358_, v___x_367_);
lean_dec(v_i_358_);
lean_inc(v_v_363_);
lean_inc(v_k_362_);
v___x_373_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_entries_359_, v_h_371_, v_depth_355_, v_k_362_, v_v_363_);
v_i_358_ = v___x_372_;
v_entries_359_ = v___x_373_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_375_, lean_object* v_keys_376_, lean_object* v_vals_377_, lean_object* v_i_378_, lean_object* v_entries_379_){
_start:
{
size_t v_depth_boxed_380_; lean_object* v_res_381_; 
v_depth_boxed_380_ = lean_unbox_usize(v_depth_375_);
lean_dec(v_depth_375_);
v_res_381_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_380_, v_keys_376_, v_vals_377_, v_i_378_, v_entries_379_);
lean_dec_ref(v_vals_377_);
lean_dec_ref(v_keys_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
size_t v_x_1409__boxed_387_; size_t v_x_1410__boxed_388_; lean_object* v_res_389_; 
v_x_1409__boxed_387_ = lean_unbox_usize(v_x_383_);
lean_dec(v_x_383_);
v_x_1410__boxed_388_ = lean_unbox_usize(v_x_384_);
lean_dec(v_x_384_);
v_res_389_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_382_, v_x_1409__boxed_387_, v_x_1410__boxed_388_, v_x_385_, v_x_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
uint64_t v___x_393_; size_t v___x_394_; size_t v___x_395_; lean_object* v___x_396_; 
v___x_393_ = l_Lean_instHashableMVarId_hash(v_x_391_);
v___x_394_ = lean_uint64_to_usize(v___x_393_);
v___x_395_ = ((size_t)1ULL);
v___x_396_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_390_, v___x_394_, v___x_395_, v_x_391_, v_x_392_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(lean_object* v_mvarId_397_, lean_object* v_val_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; lean_object* v_mctx_402_; lean_object* v_cache_403_; lean_object* v_zetaDeltaFVarIds_404_; lean_object* v_postponed_405_; lean_object* v_diag_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_435_; 
v___x_401_ = lean_st_ref_take(v___y_399_);
v_mctx_402_ = lean_ctor_get(v___x_401_, 0);
v_cache_403_ = lean_ctor_get(v___x_401_, 1);
v_zetaDeltaFVarIds_404_ = lean_ctor_get(v___x_401_, 2);
v_postponed_405_ = lean_ctor_get(v___x_401_, 3);
v_diag_406_ = lean_ctor_get(v___x_401_, 4);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_435_ == 0)
{
v___x_408_ = v___x_401_;
v_isShared_409_ = v_isSharedCheck_435_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_diag_406_);
lean_inc(v_postponed_405_);
lean_inc(v_zetaDeltaFVarIds_404_);
lean_inc(v_cache_403_);
lean_inc(v_mctx_402_);
lean_dec(v___x_401_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_435_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_depth_410_; lean_object* v_levelAssignDepth_411_; lean_object* v_lmvarCounter_412_; lean_object* v_mvarCounter_413_; lean_object* v_lDecls_414_; lean_object* v_decls_415_; lean_object* v_userNames_416_; lean_object* v_lAssignment_417_; lean_object* v_eAssignment_418_; lean_object* v_dAssignment_419_; lean_object* v_instanceTypedMVars_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_434_; 
v_depth_410_ = lean_ctor_get(v_mctx_402_, 0);
v_levelAssignDepth_411_ = lean_ctor_get(v_mctx_402_, 1);
v_lmvarCounter_412_ = lean_ctor_get(v_mctx_402_, 2);
v_mvarCounter_413_ = lean_ctor_get(v_mctx_402_, 3);
v_lDecls_414_ = lean_ctor_get(v_mctx_402_, 4);
v_decls_415_ = lean_ctor_get(v_mctx_402_, 5);
v_userNames_416_ = lean_ctor_get(v_mctx_402_, 6);
v_lAssignment_417_ = lean_ctor_get(v_mctx_402_, 7);
v_eAssignment_418_ = lean_ctor_get(v_mctx_402_, 8);
v_dAssignment_419_ = lean_ctor_get(v_mctx_402_, 9);
v_instanceTypedMVars_420_ = lean_ctor_get(v_mctx_402_, 10);
v_isSharedCheck_434_ = !lean_is_exclusive(v_mctx_402_);
if (v_isSharedCheck_434_ == 0)
{
v___x_422_ = v_mctx_402_;
v_isShared_423_ = v_isSharedCheck_434_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_instanceTypedMVars_420_);
lean_inc(v_dAssignment_419_);
lean_inc(v_eAssignment_418_);
lean_inc(v_lAssignment_417_);
lean_inc(v_userNames_416_);
lean_inc(v_decls_415_);
lean_inc(v_lDecls_414_);
lean_inc(v_mvarCounter_413_);
lean_inc(v_lmvarCounter_412_);
lean_inc(v_levelAssignDepth_411_);
lean_inc(v_depth_410_);
lean_dec(v_mctx_402_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_434_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(v_eAssignment_418_, v_mvarId_397_, v_val_398_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 8, v___x_424_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_depth_410_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_levelAssignDepth_411_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_lmvarCounter_412_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_mvarCounter_413_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v_lDecls_414_);
lean_ctor_set(v_reuseFailAlloc_433_, 5, v_decls_415_);
lean_ctor_set(v_reuseFailAlloc_433_, 6, v_userNames_416_);
lean_ctor_set(v_reuseFailAlloc_433_, 7, v_lAssignment_417_);
lean_ctor_set(v_reuseFailAlloc_433_, 8, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_433_, 9, v_dAssignment_419_);
lean_ctor_set(v_reuseFailAlloc_433_, 10, v_instanceTypedMVars_420_);
v___x_426_ = v_reuseFailAlloc_433_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_426_);
v___x_428_ = v___x_408_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_cache_403_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_zetaDeltaFVarIds_404_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v_postponed_405_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_diag_406_);
v___x_428_ = v_reuseFailAlloc_432_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_st_ref_put(v___y_399_, v___x_428_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg___boxed(lean_object* v_mvarId_436_, lean_object* v_val_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(v_mvarId_436_, v_val_437_, v___y_438_);
lean_dec(v___y_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore___lam__0(lean_object* v_mvarId_441_, lean_object* v___x_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; 
lean_inc(v_mvarId_441_);
v___x_448_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_441_, v___x_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_449_; 
lean_dec_ref_known(v___x_448_, 1);
lean_inc(v_mvarId_441_);
v___x_449_ = l_Lean_MVarId_getType(v_mvarId_441_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_a_450_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_474_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_474_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_474_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_474_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
if (lean_obj_tag(v_a_452_) == 0)
{
uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec(v_mvarId_441_);
v___x_456_ = 0;
v___x_457_ = lean_box(v___x_456_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_457_);
v___x_459_ = v___x_454_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
else
{
lean_object* v_val_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_472_; 
lean_del_object(v___x_454_);
v_val_461_ = lean_ctor_get(v_a_452_, 0);
lean_inc(v_val_461_);
lean_dec_ref_known(v_a_452_, 1);
v___x_462_ = l_Lean_mkFVar(v_val_461_);
v___x_463_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(v_mvarId_441_, v___x_462_, v___y_444_);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v___x_463_, 0);
lean_dec(v_unused_473_);
v___x_465_ = v___x_463_;
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
else
{
lean_dec(v___x_463_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
uint8_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_467_ = 1;
v___x_468_ = lean_box(v___x_467_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_468_);
v___x_470_ = v___x_465_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
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
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v_mvarId_441_);
v_a_475_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_451_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_451_);
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
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v_mvarId_441_);
v_a_483_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_449_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_449_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_mvarId_441_);
v_a_491_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_448_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_448_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore___lam__0___boxed(lean_object* v_mvarId_499_, lean_object* v___x_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_MVarId_assumptionCore___lam__0(v_mvarId_499_, v___x_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore(lean_object* v_mvarId_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v___x_516_; lean_object* v___f_517_; lean_object* v___x_518_; 
v___x_516_ = ((lean_object*)(l_Lean_MVarId_assumptionCore___closed__1));
lean_inc(v_mvarId_510_);
v___f_517_ = lean_alloc_closure((void*)(l_Lean_MVarId_assumptionCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_517_, 0, v_mvarId_510_);
lean_closure_set(v___f_517_, 1, v___x_516_);
v___x_518_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(v_mvarId_510_, v___f_517_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore___boxed(lean_object* v_mvarId_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_MVarId_assumptionCore(v_mvarId_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0(lean_object* v_mvarId_526_, lean_object* v_val_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(v_mvarId_526_, v_val_527_, v___y_529_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___boxed(lean_object* v_mvarId_534_, lean_object* v_val_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0(v_mvarId_534_, v_val_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0(lean_object* v_00_u03b2_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(v_x_543_, v_x_544_, v_x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_547_, lean_object* v_x_548_, size_t v_x_549_, size_t v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_548_, v_x_549_, v_x_550_, v_x_551_, v_x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_554_, lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
size_t v_x_1785__boxed_560_; size_t v_x_1786__boxed_561_; lean_object* v_res_562_; 
v_x_1785__boxed_560_ = lean_unbox_usize(v_x_556_);
lean_dec(v_x_556_);
v_x_1786__boxed_561_ = lean_unbox_usize(v_x_557_);
lean_dec(v_x_557_);
v_res_562_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2(v_00_u03b2_554_, v_x_555_, v_x_1785__boxed_560_, v_x_1786__boxed_561_, v_x_558_, v_x_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_563_, lean_object* v_n_564_, lean_object* v_k_565_, lean_object* v_v_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(v_n_564_, v_k_565_, v_v_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_568_, size_t v_depth_569_, lean_object* v_keys_570_, lean_object* v_vals_571_, lean_object* v_heq_572_, lean_object* v_i_573_, lean_object* v_entries_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_569_, v_keys_570_, v_vals_571_, v_i_573_, v_entries_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_576_, lean_object* v_depth_577_, lean_object* v_keys_578_, lean_object* v_vals_579_, lean_object* v_heq_580_, lean_object* v_i_581_, lean_object* v_entries_582_){
_start:
{
size_t v_depth_boxed_583_; lean_object* v_res_584_; 
v_depth_boxed_583_ = lean_unbox_usize(v_depth_577_);
lean_dec(v_depth_577_);
v_res_584_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_576_, v_depth_boxed_583_, v_keys_578_, v_vals_579_, v_heq_580_, v_i_581_, v_entries_582_);
lean_dec_ref(v_vals_579_);
lean_dec_ref(v_keys_578_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_586_, v_x_587_, v_x_588_, v_x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumption(lean_object* v_mvarId_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_597_; 
lean_inc(v_mvarId_591_);
v___x_597_ = l_Lean_MVarId_assumptionCore(v_mvarId_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_610_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_610_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_610_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_610_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
uint8_t v___x_602_; 
v___x_602_ = lean_unbox(v_a_598_);
lean_dec(v_a_598_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
lean_del_object(v___x_600_);
v___x_603_ = ((lean_object*)(l_Lean_MVarId_assumptionCore___closed__1));
v___x_604_ = lean_box(0);
v___x_605_ = l_Lean_Meta_throwTacticEx___redArg(v___x_603_, v_mvarId_591_, v___x_604_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
return v___x_605_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_608_; 
lean_dec(v_mvarId_591_);
v___x_606_ = lean_box(0);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_606_);
v___x_608_ = v___x_600_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_mvarId_591_);
v_a_611_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_597_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_597_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumption___boxed(lean_object* v_mvarId_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_MVarId_assumption(v_mvarId_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
return v_res_625_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Assumption(builtin);
}
#ifdef __cplusplus
}
#endif
