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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_type_1_, lean_object* v_as_2_, lean_object* v_i_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1_ = stack[0].m_obj;
lean_object* v_as_2_ = stack[1].m_obj;
lean_object* v_i_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v_res_48_;
v_res_48_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_1_, v_as_2_, v_i_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_type_49_, lean_object* v_as_50_, lean_object* v_i_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_49_, v_as_50_, v_i_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec_ref(v_as_50_);
return v_res_57_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_type_58_, lean_object* v_as_59_, lean_object* v_i_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_zero_66_; uint8_t v_isZero_67_; 
v_zero_66_ = lean_unsigned_to_nat(0u);
v_isZero_67_ = lean_nat_dec_eq(v_i_60_, v_zero_66_);
if (v_isZero_67_ == 1)
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_i_60_);
lean_dec_ref(v_type_58_);
v___x_68_ = lean_box(0);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
else
{
lean_object* v_one_70_; lean_object* v_n_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_one_70_ = lean_unsigned_to_nat(1u);
v_n_71_ = lean_nat_sub(v_i_60_, v_one_70_);
lean_dec(v_i_60_);
v___x_72_ = lean_array_fget_borrowed(v_as_59_, v_n_71_);
lean_inc_ref(v_type_58_);
v___x_73_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(v_type_58_, v___x_72_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
if (lean_obj_tag(v_a_74_) == 0)
{
lean_dec_ref_known(v___x_73_, 1);
v_i_60_ = v_n_71_;
goto _start;
}
else
{
lean_dec(v_n_71_);
lean_dec_ref(v_type_58_);
return v___x_73_;
}
}
else
{
lean_dec(v_n_71_);
lean_dec_ref(v_type_58_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_58_ = stack[0].m_obj;
lean_object* v_as_59_ = stack[1].m_obj;
lean_object* v_i_60_ = stack[2].m_obj;
lean_object* v___y_61_ = stack[3].m_obj;
lean_object* v___y_62_ = stack[4].m_obj;
lean_object* v___y_63_ = stack[5].m_obj;
lean_object* v___y_64_ = stack[6].m_obj;
lean_object* v_res_76_;
v_res_76_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_type_58_, v_as_59_, v_i_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
stack->m_obj
 = v_res_76_;
}
lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(lean_object* v_type_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v_cs_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_cs_84_ = lean_ctor_get(v_x_78_, 0);
v___x_85_ = lean_array_get_size(v_cs_84_);
v___x_86_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_type_77_, v_cs_84_, v___x_85_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
return v___x_86_;
}
else
{
lean_object* v_vs_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_vs_87_ = lean_ctor_get(v_x_78_, 0);
v___x_88_ = lean_array_get_size(v_vs_87_);
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_77_, v_vs_87_, v___x_88_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
return v___x_89_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_77_ = stack[0].m_obj;
lean_object* v_x_78_ = stack[1].m_obj;
lean_object* v___y_79_ = stack[2].m_obj;
lean_object* v___y_80_ = stack[3].m_obj;
lean_object* v___y_81_ = stack[4].m_obj;
lean_object* v___y_82_ = stack[5].m_obj;
lean_object* v_res_90_;
v_res_90_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(v_type_77_, v_x_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_type_91_, lean_object* v_x_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(v_type_91_, v_x_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec_ref(v_x_92_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_type_99_, lean_object* v_as_100_, lean_object* v_i_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_type_99_, v_as_100_, v_i_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec_ref(v_as_100_);
return v_res_107_;
}
}
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0(lean_object* v_type_108_, lean_object* v_t_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_root_115_; lean_object* v_tail_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_root_115_ = lean_ctor_get(v_t_109_, 0);
v_tail_116_ = lean_ctor_get(v_t_109_, 1);
v___x_117_ = lean_array_get_size(v_tail_116_);
lean_inc_ref(v_type_108_);
v___x_118_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_108_, v_tail_116_, v___x_117_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
if (lean_obj_tag(v_a_119_) == 0)
{
lean_object* v___x_120_; 
lean_dec_ref_known(v___x_118_, 1);
v___x_120_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(v_type_108_, v_root_115_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
return v___x_120_;
}
else
{
lean_dec_ref(v_type_108_);
return v___x_118_;
}
}
else
{
lean_dec_ref(v_type_108_);
return v___x_118_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_108_ = stack[0].m_obj;
lean_object* v_t_109_ = stack[1].m_obj;
lean_object* v___y_110_ = stack[2].m_obj;
lean_object* v___y_111_ = stack[3].m_obj;
lean_object* v___y_112_ = stack[4].m_obj;
lean_object* v___y_113_ = stack[5].m_obj;
lean_object* v_res_121_;
v_res_121_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0(v_type_108_, v_t_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
stack->m_obj
 = v_res_121_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0___boxed(lean_object* v_type_122_, lean_object* v_t_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0(v_type_122_, v_t_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec_ref(v_t_123_);
return v_res_129_;
}
}
lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0(lean_object* v_type_130_, lean_object* v_lctx_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_decls_137_; lean_object* v___x_138_; 
v_decls_137_ = lean_ctor_get(v_lctx_131_, 1);
v___x_138_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0(v_type_130_, v_decls_137_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
return v___x_138_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_130_ = stack[0].m_obj;
lean_object* v_lctx_131_ = stack[1].m_obj;
lean_object* v___y_132_ = stack[2].m_obj;
lean_object* v___y_133_ = stack[3].m_obj;
lean_object* v___y_134_ = stack[4].m_obj;
lean_object* v___y_135_ = stack[5].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0(v_type_130_, v_lctx_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0___boxed(lean_object* v_type_140_, lean_object* v_lctx_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0(v_type_140_, v_lctx_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec_ref(v_lctx_141_);
return v_res_147_;
}
}
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object* v_type_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_lctx_154_; lean_object* v___x_155_; 
v_lctx_154_ = lean_ctor_get(v_a_149_, 2);
v___x_155_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0(v_type_148_, v_lctx_154_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
return v___x_155_;
}
}
LEAN_EXPORT void l_Lean_Meta_findLocalDeclWithType_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_148_ = stack[0].m_obj;
lean_object* v_a_149_ = stack[1].m_obj;
lean_object* v_a_150_ = stack[2].m_obj;
lean_object* v_a_151_ = stack[3].m_obj;
lean_object* v_a_152_ = stack[4].m_obj;
lean_object* v_res_156_;
v_res_156_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_type_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_findLocalDeclWithType_x3f___boxed(lean_object* v_type_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_type_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
return v_res_163_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1(lean_object* v_type_164_, lean_object* v_as_165_, lean_object* v_i_166_, lean_object* v_a_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_164_, v_as_165_, v_i_166_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
return v___x_173_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_164_ = stack[0].m_obj;
lean_object* v_as_165_ = stack[1].m_obj;
lean_object* v_i_166_ = stack[2].m_obj;
lean_object* v___y_168_ = stack[4].m_obj;
lean_object* v___y_169_ = stack[5].m_obj;
lean_object* v___y_170_ = stack[6].m_obj;
lean_object* v___y_171_ = stack[7].m_obj;
lean_object* v_res_174_;
v_res_174_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1(v_type_164_, v_as_165_, v_i_166_, lean_box(0), v___y_168_, v___y_169_, v___y_170_, v___y_171_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_type_175_, lean_object* v_as_176_, lean_object* v_i_177_, lean_object* v_a_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1(v_type_175_, v_as_176_, v_i_177_, v_a_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec_ref(v_as_176_);
return v_res_184_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_type_185_, lean_object* v_as_186_, lean_object* v_i_187_, lean_object* v_a_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_type_185_, v_as_186_, v_i_187_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
return v___x_194_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_185_ = stack[0].m_obj;
lean_object* v_as_186_ = stack[1].m_obj;
lean_object* v_i_187_ = stack[2].m_obj;
lean_object* v___y_189_ = stack[4].m_obj;
lean_object* v___y_190_ = stack[5].m_obj;
lean_object* v___y_191_ = stack[6].m_obj;
lean_object* v___y_192_ = stack[7].m_obj;
lean_object* v_res_195_;
v_res_195_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3(v_type_185_, v_as_186_, v_i_187_, lean_box(0), v___y_189_, v___y_190_, v___y_191_, v___y_192_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_type_196_, lean_object* v_as_197_, lean_object* v_i_198_, lean_object* v_a_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3(v_type_196_, v_as_197_, v_i_198_, v_a_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec_ref(v_as_197_);
return v_res_205_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(lean_object* v_mvarId_206_, lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_206_, v_x_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
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
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
v_a_222_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_213_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_213_);
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_206_ = stack[0].m_obj;
lean_object* v_x_207_ = stack[1].m_obj;
lean_object* v___y_208_ = stack[2].m_obj;
lean_object* v___y_209_ = stack[3].m_obj;
lean_object* v___y_210_ = stack[4].m_obj;
lean_object* v___y_211_ = stack[5].m_obj;
lean_object* v_res_230_;
v_res_230_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(v_mvarId_206_, v_x_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg___boxed(lean_object* v_mvarId_231_, lean_object* v_x_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(v_mvarId_231_, v_x_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
return v_res_238_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1(lean_object* v_00_u03b1_239_, lean_object* v_mvarId_240_, lean_object* v_x_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(v_mvarId_240_, v_x_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
return v___x_247_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_240_ = stack[1].m_obj;
lean_object* v_x_241_ = stack[2].m_obj;
lean_object* v___y_242_ = stack[3].m_obj;
lean_object* v___y_243_ = stack[4].m_obj;
lean_object* v___y_244_ = stack[5].m_obj;
lean_object* v___y_245_ = stack[6].m_obj;
lean_object* v_res_248_;
v_res_248_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1(lean_box(0), v_mvarId_240_, v_x_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___boxed(lean_object* v_00_u03b1_249_, lean_object* v_mvarId_250_, lean_object* v_x_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1(v_00_u03b1_249_, v_mvarId_250_, v_x_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
lean_object* v_ks_262_; lean_object* v_vs_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_287_; 
v_ks_262_ = lean_ctor_get(v_x_258_, 0);
v_vs_263_ = lean_ctor_get(v_x_258_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_287_ == 0)
{
v___x_265_ = v_x_258_;
v_isShared_266_ = v_isSharedCheck_287_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_vs_263_);
lean_inc(v_ks_262_);
lean_dec(v_x_258_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_287_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_array_get_size(v_ks_262_);
v___x_268_ = lean_nat_dec_lt(v_x_259_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
lean_dec(v_x_259_);
v___x_269_ = lean_array_push(v_ks_262_, v_x_260_);
v___x_270_ = lean_array_push(v_vs_263_, v_x_261_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_270_);
lean_ctor_set(v___x_265_, 0, v___x_269_);
v___x_272_ = v___x_265_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
else
{
lean_object* v_k_x27_274_; uint8_t v___x_275_; 
v_k_x27_274_ = lean_array_fget_borrowed(v_ks_262_, v_x_259_);
v___x_275_ = l_Lean_instBEqMVarId_beq(v_x_260_, v_k_x27_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_277_; 
if (v_isShared_266_ == 0)
{
v___x_277_ = v___x_265_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_ks_262_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_vs_263_);
v___x_277_ = v_reuseFailAlloc_281_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_x_259_, v___x_278_);
lean_dec(v_x_259_);
v_x_258_ = v___x_277_;
v_x_259_ = v___x_279_;
goto _start;
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_282_ = lean_array_fset(v_ks_262_, v_x_259_, v_x_260_);
v___x_283_ = lean_array_fset(v_vs_263_, v_x_259_, v_x_261_);
lean_dec(v_x_259_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_283_);
lean_ctor_set(v___x_265_, 0, v___x_282_);
v___x_285_ = v___x_265_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_282_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_288_, lean_object* v_k_289_, lean_object* v_v_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_288_, v___x_291_, v_k_289_, v_v_290_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_293_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_294_, size_t v_x_295_, size_t v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
lean_object* v_es_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v_j_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_es_299_ = lean_ctor_get(v_x_294_, 0);
v___x_300_ = ((size_t)31ULL);
v___x_301_ = lean_usize_land(v_x_295_, v___x_300_);
v_j_302_ = lean_usize_to_nat(v___x_301_);
v___x_303_ = lean_array_get_size(v_es_299_);
v___x_304_ = lean_nat_dec_lt(v_j_302_, v___x_303_);
if (v___x_304_ == 0)
{
lean_dec(v_j_302_);
lean_dec(v_x_298_);
lean_dec(v_x_297_);
return v_x_294_;
}
else
{
lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_343_; 
lean_inc_ref(v_es_299_);
v_isSharedCheck_343_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v_x_294_, 0);
lean_dec(v_unused_344_);
v___x_306_ = v_x_294_;
v_isShared_307_ = v_isSharedCheck_343_;
goto v_resetjp_305_;
}
else
{
lean_dec(v_x_294_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_343_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_v_308_; lean_object* v___x_309_; lean_object* v_xs_x27_310_; lean_object* v___y_312_; 
v_v_308_ = lean_array_fget(v_es_299_, v_j_302_);
v___x_309_ = lean_box(0);
v_xs_x27_310_ = lean_array_fset(v_es_299_, v_j_302_, v___x_309_);
switch(lean_obj_tag(v_v_308_))
{
case 0:
{
lean_object* v_key_317_; lean_object* v_val_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v_key_317_ = lean_ctor_get(v_v_308_, 0);
v_val_318_ = lean_ctor_get(v_v_308_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_v_308_);
if (v_isSharedCheck_328_ == 0)
{
v___x_320_ = v_v_308_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_val_318_);
lean_inc(v_key_317_);
lean_dec(v_v_308_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
uint8_t v___x_322_; 
v___x_322_ = l_Lean_instBEqMVarId_beq(v_x_297_, v_key_317_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_del_object(v___x_320_);
v___x_323_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_317_, v_val_318_, v_x_297_, v_x_298_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
v___y_312_ = v___x_324_;
goto v___jp_311_;
}
else
{
lean_object* v___x_326_; 
lean_dec(v_val_318_);
lean_dec(v_key_317_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v_x_298_);
lean_ctor_set(v___x_320_, 0, v_x_297_);
v___x_326_ = v___x_320_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_x_297_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_x_298_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
v___y_312_ = v___x_326_;
goto v___jp_311_;
}
}
}
}
case 1:
{
lean_object* v_node_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_341_; 
v_node_329_ = lean_ctor_get(v_v_308_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_v_308_);
if (v_isSharedCheck_341_ == 0)
{
v___x_331_ = v_v_308_;
v_isShared_332_ = v_isSharedCheck_341_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_node_329_);
lean_dec(v_v_308_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_341_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
size_t v___x_333_; size_t v___x_334_; size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_333_ = ((size_t)5ULL);
v___x_334_ = lean_usize_shift_right(v_x_295_, v___x_333_);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_x_296_, v___x_335_);
v___x_337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_node_329_, v___x_334_, v___x_336_, v_x_297_, v_x_298_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_337_);
v___x_339_ = v___x_331_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
v___y_312_ = v___x_339_;
goto v___jp_311_;
}
}
}
default: 
{
lean_object* v___x_342_; 
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v_x_297_);
lean_ctor_set(v___x_342_, 1, v_x_298_);
v___y_312_ = v___x_342_;
goto v___jp_311_;
}
}
v___jp_311_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = lean_array_fset(v_xs_x27_310_, v_j_302_, v___y_312_);
lean_dec(v_j_302_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_313_);
v___x_315_ = v___x_306_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
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
lean_object* v_ks_345_; lean_object* v_vs_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_364_; 
v_ks_345_ = lean_ctor_get(v_x_294_, 0);
v_vs_346_ = lean_ctor_get(v_x_294_, 1);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_364_ == 0)
{
v___x_348_ = v_x_294_;
v_isShared_349_ = v_isSharedCheck_364_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_vs_346_);
lean_inc(v_ks_345_);
lean_dec(v_x_294_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_364_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_ks_345_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_vs_346_);
v___x_351_ = v_reuseFailAlloc_363_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v_newNode_352_; size_t v___x_353_; uint8_t v___x_354_; 
v_newNode_352_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(v___x_351_, v_x_297_, v_x_298_);
v___x_353_ = ((size_t)7ULL);
v___x_354_ = lean_usize_dec_le(v___x_353_, v_x_296_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_355_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_352_);
v___x_356_ = lean_unsigned_to_nat(4u);
v___x_357_ = lean_nat_dec_lt(v___x_355_, v___x_356_);
lean_dec(v___x_355_);
if (v___x_357_ == 0)
{
lean_object* v_ks_358_; lean_object* v_vs_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_ks_358_ = lean_ctor_get(v_newNode_352_, 0);
lean_inc_ref(v_ks_358_);
v_vs_359_ = lean_ctor_get(v_newNode_352_, 1);
lean_inc_ref(v_vs_359_);
lean_dec_ref(v_newNode_352_);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_362_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_x_296_, v_ks_358_, v_vs_359_, v___x_360_, v___x_361_);
lean_dec_ref(v_vs_359_);
lean_dec_ref(v_ks_358_);
return v___x_362_;
}
else
{
return v_newNode_352_;
}
}
else
{
return v_newNode_352_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_294_ = stack[0].m_obj;
size_t v_x_295_ = stack[1].m_num;
size_t v_x_296_ = stack[2].m_num;
lean_object* v_x_297_ = stack[3].m_obj;
lean_object* v_x_298_ = stack[4].m_obj;
lean_object* v_res_365_;
v_res_365_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_294_, v_x_295_, v_x_296_, v_x_297_, v_x_298_);
stack->m_obj
 = v_res_365_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_366_, lean_object* v_keys_367_, lean_object* v_vals_368_, lean_object* v_i_369_, lean_object* v_entries_370_){
_start:
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_array_get_size(v_keys_367_);
v___x_372_ = lean_nat_dec_lt(v_i_369_, v___x_371_);
if (v___x_372_ == 0)
{
lean_dec(v_i_369_);
return v_entries_370_;
}
else
{
lean_object* v_k_373_; lean_object* v_v_374_; uint64_t v___x_375_; size_t v_h_376_; size_t v___x_377_; lean_object* v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v_h_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_k_373_ = lean_array_fget_borrowed(v_keys_367_, v_i_369_);
v_v_374_ = lean_array_fget_borrowed(v_vals_368_, v_i_369_);
v___x_375_ = l_Lean_instHashableMVarId_hash(v_k_373_);
v_h_376_ = lean_uint64_to_usize(v___x_375_);
v___x_377_ = ((size_t)5ULL);
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_sub(v_depth_366_, v___x_379_);
v___x_381_ = lean_usize_mul(v___x_377_, v___x_380_);
v_h_382_ = lean_usize_shift_right(v_h_376_, v___x_381_);
v___x_383_ = lean_nat_add(v_i_369_, v___x_378_);
lean_dec(v_i_369_);
lean_inc(v_v_374_);
lean_inc(v_k_373_);
v___x_384_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_entries_370_, v_h_382_, v_depth_366_, v_k_373_, v_v_374_);
v_i_369_ = v___x_383_;
v_entries_370_ = v___x_384_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_366_ = stack[0].m_num;
lean_object* v_keys_367_ = stack[1].m_obj;
lean_object* v_vals_368_ = stack[2].m_obj;
lean_object* v_i_369_ = stack[3].m_obj;
lean_object* v_entries_370_ = stack[4].m_obj;
lean_object* v_res_386_;
v_res_386_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_366_, v_keys_367_, v_vals_368_, v_i_369_, v_entries_370_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_387_, lean_object* v_keys_388_, lean_object* v_vals_389_, lean_object* v_i_390_, lean_object* v_entries_391_){
_start:
{
size_t v_depth_boxed_392_; lean_object* v_res_393_; 
v_depth_boxed_392_ = lean_unbox_usize(v_depth_387_);
lean_dec(v_depth_387_);
v_res_393_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_392_, v_keys_388_, v_vals_389_, v_i_390_, v_entries_391_);
lean_dec_ref(v_vals_389_);
lean_dec_ref(v_keys_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
size_t v_x_1485__boxed_399_; size_t v_x_1486__boxed_400_; lean_object* v_res_401_; 
v_x_1485__boxed_399_ = lean_unbox_usize(v_x_395_);
lean_dec(v_x_395_);
v_x_1486__boxed_400_ = lean_unbox_usize(v_x_396_);
lean_dec(v_x_396_);
v_res_401_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_394_, v_x_1485__boxed_399_, v_x_1486__boxed_400_, v_x_397_, v_x_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
uint64_t v___x_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_405_ = l_Lean_instHashableMVarId_hash(v_x_403_);
v___x_406_ = lean_uint64_to_usize(v___x_405_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_402_, v___x_406_, v___x_407_, v_x_403_, v_x_404_);
return v___x_408_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(lean_object* v_mvarId_409_, lean_object* v_val_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; lean_object* v_mctx_414_; lean_object* v_cache_415_; lean_object* v_zetaDeltaFVarIds_416_; lean_object* v_postponed_417_; lean_object* v_diag_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_448_; 
v___x_413_ = lean_st_ref_take(v___y_411_);
v_mctx_414_ = lean_ctor_get(v___x_413_, 0);
v_cache_415_ = lean_ctor_get(v___x_413_, 1);
v_zetaDeltaFVarIds_416_ = lean_ctor_get(v___x_413_, 2);
v_postponed_417_ = lean_ctor_get(v___x_413_, 3);
v_diag_418_ = lean_ctor_get(v___x_413_, 4);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_448_ == 0)
{
v___x_420_ = v___x_413_;
v_isShared_421_ = v_isSharedCheck_448_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_diag_418_);
lean_inc(v_postponed_417_);
lean_inc(v_zetaDeltaFVarIds_416_);
lean_inc(v_cache_415_);
lean_inc(v_mctx_414_);
lean_dec(v___x_413_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_448_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_depth_422_; lean_object* v_levelAssignDepth_423_; lean_object* v_lmvarCounter_424_; lean_object* v_mvarCounter_425_; lean_object* v_lDecls_426_; lean_object* v_decls_427_; lean_object* v_userNames_428_; lean_object* v_lAssignment_429_; lean_object* v_eAssignment_430_; lean_object* v_dAssignment_431_; lean_object* v_instanceTypedMVars_432_; lean_object* v_synthNormMemo_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_447_; 
v_depth_422_ = lean_ctor_get(v_mctx_414_, 0);
v_levelAssignDepth_423_ = lean_ctor_get(v_mctx_414_, 1);
v_lmvarCounter_424_ = lean_ctor_get(v_mctx_414_, 2);
v_mvarCounter_425_ = lean_ctor_get(v_mctx_414_, 3);
v_lDecls_426_ = lean_ctor_get(v_mctx_414_, 4);
v_decls_427_ = lean_ctor_get(v_mctx_414_, 5);
v_userNames_428_ = lean_ctor_get(v_mctx_414_, 6);
v_lAssignment_429_ = lean_ctor_get(v_mctx_414_, 7);
v_eAssignment_430_ = lean_ctor_get(v_mctx_414_, 8);
v_dAssignment_431_ = lean_ctor_get(v_mctx_414_, 9);
v_instanceTypedMVars_432_ = lean_ctor_get(v_mctx_414_, 10);
v_synthNormMemo_433_ = lean_ctor_get(v_mctx_414_, 11);
v_isSharedCheck_447_ = !lean_is_exclusive(v_mctx_414_);
if (v_isSharedCheck_447_ == 0)
{
v___x_435_ = v_mctx_414_;
v_isShared_436_ = v_isSharedCheck_447_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_synthNormMemo_433_);
lean_inc(v_instanceTypedMVars_432_);
lean_inc(v_dAssignment_431_);
lean_inc(v_eAssignment_430_);
lean_inc(v_lAssignment_429_);
lean_inc(v_userNames_428_);
lean_inc(v_decls_427_);
lean_inc(v_lDecls_426_);
lean_inc(v_mvarCounter_425_);
lean_inc(v_lmvarCounter_424_);
lean_inc(v_levelAssignDepth_423_);
lean_inc(v_depth_422_);
lean_dec(v_mctx_414_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_447_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_437_ = lean_box(0);
v___x_438_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(v_eAssignment_430_, v_mvarId_409_, v_val_410_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 8, v___x_438_);
v___x_440_ = v___x_435_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_depth_422_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_levelAssignDepth_423_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_lmvarCounter_424_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_mvarCounter_425_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v_lDecls_426_);
lean_ctor_set(v_reuseFailAlloc_446_, 5, v_decls_427_);
lean_ctor_set(v_reuseFailAlloc_446_, 6, v_userNames_428_);
lean_ctor_set(v_reuseFailAlloc_446_, 7, v_lAssignment_429_);
lean_ctor_set(v_reuseFailAlloc_446_, 8, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_446_, 9, v_dAssignment_431_);
lean_ctor_set(v_reuseFailAlloc_446_, 10, v_instanceTypedMVars_432_);
lean_ctor_set(v_reuseFailAlloc_446_, 11, v_synthNormMemo_433_);
v___x_440_ = v_reuseFailAlloc_446_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_442_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_440_);
v___x_442_ = v___x_420_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_cache_415_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_zetaDeltaFVarIds_416_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_postponed_417_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_diag_418_);
v___x_442_ = v_reuseFailAlloc_445_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_st_ref_put(v___y_411_, v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_437_);
return v___x_444_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_409_ = stack[0].m_obj;
lean_object* v_val_410_ = stack[1].m_obj;
lean_object* v___y_411_ = stack[2].m_obj;
lean_object* v_res_449_;
v_res_449_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(v_mvarId_409_, v_val_410_, v___y_411_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg___boxed(lean_object* v_mvarId_450_, lean_object* v_val_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(v_mvarId_450_, v_val_451_, v___y_452_);
lean_dec(v___y_452_);
return v_res_454_;
}
}
lean_object* l_Lean_MVarId_assumptionCore___lam__0(lean_object* v_mvarId_455_, lean_object* v___x_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; 
lean_inc(v_mvarId_455_);
v___x_462_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_455_, v___x_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v___x_463_; 
lean_dec_ref_known(v___x_462_, 1);
lean_inc(v_mvarId_455_);
v___x_463_ = l_Lean_MVarId_getType(v_mvarId_455_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_a_464_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_488_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_488_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_488_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_488_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
if (lean_obj_tag(v_a_466_) == 0)
{
uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
lean_dec(v_mvarId_455_);
v___x_470_ = 0;
v___x_471_ = lean_box(v___x_470_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
else
{
lean_object* v_val_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_486_; 
lean_del_object(v___x_468_);
v_val_475_ = lean_ctor_get(v_a_466_, 0);
lean_inc(v_val_475_);
lean_dec_ref_known(v_a_466_, 1);
v___x_476_ = l_Lean_mkFVar(v_val_475_);
v___x_477_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(v_mvarId_455_, v___x_476_, v___y_458_);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v___x_477_, 0);
lean_dec(v_unused_487_);
v___x_479_ = v___x_477_;
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
else
{
lean_dec(v___x_477_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_481_ = 1;
v___x_482_ = lean_box(v___x_481_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_482_);
v___x_484_ = v___x_479_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v_mvarId_455_);
v_a_489_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_465_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_465_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v_mvarId_455_);
v_a_497_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_463_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_463_);
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
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_mvarId_455_);
v_a_505_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_462_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_462_);
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
}
LEAN_EXPORT void l_Lean_MVarId_assumptionCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_455_ = stack[0].m_obj;
lean_object* v___x_456_ = stack[1].m_obj;
lean_object* v___y_457_ = stack[2].m_obj;
lean_object* v___y_458_ = stack[3].m_obj;
lean_object* v___y_459_ = stack[4].m_obj;
lean_object* v___y_460_ = stack[5].m_obj;
lean_object* v_res_513_;
v_res_513_ = l_Lean_MVarId_assumptionCore___lam__0(v_mvarId_455_, v___x_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore___lam__0___boxed(lean_object* v_mvarId_514_, lean_object* v___x_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_MVarId_assumptionCore___lam__0(v_mvarId_514_, v___x_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
return v_res_521_;
}
}
lean_object* l_Lean_MVarId_assumptionCore(lean_object* v_mvarId_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_531_; lean_object* v___f_532_; lean_object* v___x_533_; 
v___x_531_ = ((lean_object*)(l_Lean_MVarId_assumptionCore___closed__1));
lean_inc(v_mvarId_525_);
v___f_532_ = lean_alloc_closure((void*)(l_Lean_MVarId_assumptionCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_532_, 0, v_mvarId_525_);
lean_closure_set(v___f_532_, 1, v___x_531_);
v___x_533_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(v_mvarId_525_, v___f_532_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
return v___x_533_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assumptionCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_525_ = stack[0].m_obj;
lean_object* v_a_526_ = stack[1].m_obj;
lean_object* v_a_527_ = stack[2].m_obj;
lean_object* v_a_528_ = stack[3].m_obj;
lean_object* v_a_529_ = stack[4].m_obj;
lean_object* v_res_534_;
v_res_534_ = l_Lean_MVarId_assumptionCore(v_mvarId_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
stack->m_obj
 = v_res_534_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore___boxed(lean_object* v_mvarId_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_MVarId_assumptionCore(v_mvarId_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
return v_res_541_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0(lean_object* v_mvarId_542_, lean_object* v_val_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(v_mvarId_542_, v_val_543_, v___y_545_);
return v___x_549_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_542_ = stack[0].m_obj;
lean_object* v_val_543_ = stack[1].m_obj;
lean_object* v___y_544_ = stack[2].m_obj;
lean_object* v___y_545_ = stack[3].m_obj;
lean_object* v___y_546_ = stack[4].m_obj;
lean_object* v___y_547_ = stack[5].m_obj;
lean_object* v_res_550_;
v_res_550_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0(v_mvarId_542_, v_val_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
stack->m_obj
 = v_res_550_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___boxed(lean_object* v_mvarId_551_, lean_object* v_val_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0(v_mvarId_551_, v_val_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0(lean_object* v_00_u03b2_559_, lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(v_x_560_, v_x_561_, v_x_562_);
return v___x_563_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_564_, lean_object* v_x_565_, size_t v_x_566_, size_t v_x_567_, lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_565_, v_x_566_, v_x_567_, v_x_568_, v_x_569_);
return v___x_570_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_565_ = stack[1].m_obj;
size_t v_x_566_ = stack[2].m_num;
size_t v_x_567_ = stack[3].m_num;
lean_object* v_x_568_ = stack[4].m_obj;
lean_object* v_x_569_ = stack[5].m_obj;
lean_object* v_res_571_;
v_res_571_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2(lean_box(0), v_x_565_, v_x_566_, v_x_567_, v_x_568_, v_x_569_);
stack->m_obj
 = v_res_571_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_572_, lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
size_t v_x_2061__boxed_578_; size_t v_x_2062__boxed_579_; lean_object* v_res_580_; 
v_x_2061__boxed_578_ = lean_unbox_usize(v_x_574_);
lean_dec(v_x_574_);
v_x_2062__boxed_579_ = lean_unbox_usize(v_x_575_);
lean_dec(v_x_575_);
v_res_580_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2(v_00_u03b2_572_, v_x_573_, v_x_2061__boxed_578_, v_x_2062__boxed_579_, v_x_576_, v_x_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_581_, lean_object* v_n_582_, lean_object* v_k_583_, lean_object* v_v_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(v_n_582_, v_k_583_, v_v_584_);
return v___x_585_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_586_, size_t v_depth_587_, lean_object* v_keys_588_, lean_object* v_vals_589_, lean_object* v_heq_590_, lean_object* v_i_591_, lean_object* v_entries_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_587_, v_keys_588_, v_vals_589_, v_i_591_, v_entries_592_);
return v___x_593_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_depth_587_ = stack[1].m_num;
lean_object* v_keys_588_ = stack[2].m_obj;
lean_object* v_vals_589_ = stack[3].m_obj;
lean_object* v_i_591_ = stack[5].m_obj;
lean_object* v_entries_592_ = stack[6].m_obj;
lean_object* v_res_594_;
v_res_594_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4(lean_box(0), v_depth_587_, v_keys_588_, v_vals_589_, lean_box(0), v_i_591_, v_entries_592_);
stack->m_obj
 = v_res_594_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_595_, lean_object* v_depth_596_, lean_object* v_keys_597_, lean_object* v_vals_598_, lean_object* v_heq_599_, lean_object* v_i_600_, lean_object* v_entries_601_){
_start:
{
size_t v_depth_boxed_602_; lean_object* v_res_603_; 
v_depth_boxed_602_ = lean_unbox_usize(v_depth_596_);
lean_dec(v_depth_596_);
v_res_603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_595_, v_depth_boxed_602_, v_keys_597_, v_vals_598_, v_heq_599_, v_i_600_, v_entries_601_);
lean_dec_ref(v_vals_598_);
lean_dec_ref(v_keys_597_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_604_, lean_object* v_x_605_, lean_object* v_x_606_, lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_605_, v_x_606_, v_x_607_, v_x_608_);
return v___x_609_;
}
}
lean_object* l_Lean_MVarId_assumption(lean_object* v_mvarId_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___x_616_; 
lean_inc(v_mvarId_610_);
v___x_616_ = l_Lean_MVarId_assumptionCore(v_mvarId_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_629_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_629_ == 0)
{
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_629_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_629_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
uint8_t v___x_621_; 
v___x_621_ = lean_unbox(v_a_617_);
lean_dec(v_a_617_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
lean_del_object(v___x_619_);
v___x_622_ = ((lean_object*)(l_Lean_MVarId_assumptionCore___closed__1));
v___x_623_ = lean_box(0);
v___x_624_ = l_Lean_Meta_throwTacticEx___redArg(v___x_622_, v_mvarId_610_, v___x_623_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_627_; 
lean_dec(v_mvarId_610_);
v___x_625_ = lean_box(0);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_625_);
v___x_627_ = v___x_619_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v_mvarId_610_);
v_a_630_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_616_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_616_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assumption_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_610_ = stack[0].m_obj;
lean_object* v_a_611_ = stack[1].m_obj;
lean_object* v_a_612_ = stack[2].m_obj;
lean_object* v_a_613_ = stack[3].m_obj;
lean_object* v_a_614_ = stack[4].m_obj;
lean_object* v_res_638_;
v_res_638_ = l_Lean_MVarId_assumption(v_mvarId_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_);
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumption___boxed(lean_object* v_mvarId_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_MVarId_assumption(v_mvarId_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
return v_res_645_;
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
