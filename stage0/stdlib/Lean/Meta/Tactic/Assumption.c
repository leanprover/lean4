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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2;
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
lean_dec_ref(v___x_72_);
v_i_59_ = v_n_70_;
goto _start;
}
else
{
lean_dec_ref(v_a_73_);
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
lean_dec_ref(v___x_115_);
v___x_117_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(v_type_105_, v_root_112_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
return v___x_117_;
}
else
{
lean_dec_ref(v_a_116_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; 
v___x_283_ = ((size_t)5ULL);
v___x_284_ = ((size_t)1ULL);
v___x_285_ = lean_usize_shift_left(v___x_284_, v___x_283_);
return v___x_285_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; 
v___x_286_ = ((size_t)1ULL);
v___x_287_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_288_ = lean_usize_sub(v___x_287_, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(lean_object* v_x_290_, size_t v_x_291_, size_t v_x_292_, lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_object* v_es_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; lean_object* v_j_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_es_295_ = lean_ctor_get(v_x_290_, 0);
v___x_296_ = ((size_t)5ULL);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_299_ = lean_usize_land(v_x_291_, v___x_298_);
v_j_300_ = lean_usize_to_nat(v___x_299_);
v___x_301_ = lean_array_get_size(v_es_295_);
v___x_302_ = lean_nat_dec_lt(v_j_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_dec(v_j_300_);
lean_dec(v_x_294_);
lean_dec(v_x_293_);
return v_x_290_;
}
else
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_339_; 
lean_inc_ref(v_es_295_);
v_isSharedCheck_339_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v_x_290_, 0);
lean_dec(v_unused_340_);
v___x_304_ = v_x_290_;
v_isShared_305_ = v_isSharedCheck_339_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_x_290_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_339_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v_v_306_; lean_object* v___x_307_; lean_object* v_xs_x27_308_; lean_object* v___y_310_; 
v_v_306_ = lean_array_fget(v_es_295_, v_j_300_);
v___x_307_ = lean_box(0);
v_xs_x27_308_ = lean_array_fset(v_es_295_, v_j_300_, v___x_307_);
switch(lean_obj_tag(v_v_306_))
{
case 0:
{
lean_object* v_key_315_; lean_object* v_val_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_326_; 
v_key_315_ = lean_ctor_get(v_v_306_, 0);
v_val_316_ = lean_ctor_get(v_v_306_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_v_306_);
if (v_isSharedCheck_326_ == 0)
{
v___x_318_ = v_v_306_;
v_isShared_319_ = v_isSharedCheck_326_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_val_316_);
lean_inc(v_key_315_);
lean_dec(v_v_306_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_326_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; 
v___x_320_ = l_Lean_instBEqMVarId_beq(v_x_293_, v_key_315_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_318_);
v___x_321_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_315_, v_val_316_, v_x_293_, v_x_294_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___y_310_ = v___x_322_;
goto v___jp_309_;
}
else
{
lean_object* v___x_324_; 
lean_dec(v_val_316_);
lean_dec(v_key_315_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v_x_294_);
lean_ctor_set(v___x_318_, 0, v_x_293_);
v___x_324_ = v___x_318_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_x_293_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_x_294_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
v___y_310_ = v___x_324_;
goto v___jp_309_;
}
}
}
}
case 1:
{
lean_object* v_node_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_337_; 
v_node_327_ = lean_ctor_get(v_v_306_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_v_306_);
if (v_isSharedCheck_337_ == 0)
{
v___x_329_ = v_v_306_;
v_isShared_330_ = v_isSharedCheck_337_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_node_327_);
lean_dec(v_v_306_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_337_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_331_ = lean_usize_shift_right(v_x_291_, v___x_296_);
v___x_332_ = lean_usize_add(v_x_292_, v___x_297_);
v___x_333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_node_327_, v___x_331_, v___x_332_, v_x_293_, v_x_294_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_333_);
v___x_335_ = v___x_329_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
v___y_310_ = v___x_335_;
goto v___jp_309_;
}
}
}
default: 
{
lean_object* v___x_338_; 
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v_x_293_);
lean_ctor_set(v___x_338_, 1, v_x_294_);
v___y_310_ = v___x_338_;
goto v___jp_309_;
}
}
v___jp_309_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_array_fset(v_xs_x27_308_, v_j_300_, v___y_310_);
lean_dec(v_j_300_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_311_);
v___x_313_ = v___x_304_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
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
lean_object* v_ks_341_; lean_object* v_vs_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_362_; 
v_ks_341_ = lean_ctor_get(v_x_290_, 0);
v_vs_342_ = lean_ctor_get(v_x_290_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_362_ == 0)
{
v___x_344_ = v_x_290_;
v_isShared_345_ = v_isSharedCheck_362_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_vs_342_);
lean_inc(v_ks_341_);
lean_dec(v_x_290_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_362_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_ks_341_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_vs_342_);
v___x_347_ = v_reuseFailAlloc_361_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v_newNode_348_; uint8_t v___y_350_; size_t v___x_356_; uint8_t v___x_357_; 
v_newNode_348_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(v___x_347_, v_x_293_, v_x_294_);
v___x_356_ = ((size_t)7ULL);
v___x_357_ = lean_usize_dec_le(v___x_356_, v_x_292_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_358_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_348_);
v___x_359_ = lean_unsigned_to_nat(4u);
v___x_360_ = lean_nat_dec_lt(v___x_358_, v___x_359_);
lean_dec(v___x_358_);
v___y_350_ = v___x_360_;
goto v___jp_349_;
}
else
{
v___y_350_ = v___x_357_;
goto v___jp_349_;
}
v___jp_349_:
{
if (v___y_350_ == 0)
{
lean_object* v_ks_351_; lean_object* v_vs_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_ks_351_ = lean_ctor_get(v_newNode_348_, 0);
lean_inc_ref(v_ks_351_);
v_vs_352_ = lean_ctor_get(v_newNode_348_, 1);
lean_inc_ref(v_vs_352_);
lean_dec_ref(v_newNode_348_);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_355_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_x_292_, v_ks_351_, v_vs_352_, v___x_353_, v___x_354_);
lean_dec_ref(v_vs_352_);
lean_dec_ref(v_ks_351_);
return v___x_355_;
}
else
{
return v_newNode_348_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_363_, lean_object* v_keys_364_, lean_object* v_vals_365_, lean_object* v_i_366_, lean_object* v_entries_367_){
_start:
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_array_get_size(v_keys_364_);
v___x_369_ = lean_nat_dec_lt(v_i_366_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec(v_i_366_);
return v_entries_367_;
}
else
{
lean_object* v_k_370_; lean_object* v_v_371_; uint64_t v___x_372_; size_t v_h_373_; size_t v___x_374_; lean_object* v___x_375_; size_t v___x_376_; size_t v___x_377_; size_t v___x_378_; size_t v_h_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_k_370_ = lean_array_fget_borrowed(v_keys_364_, v_i_366_);
v_v_371_ = lean_array_fget_borrowed(v_vals_365_, v_i_366_);
v___x_372_ = l_Lean_instHashableMVarId_hash(v_k_370_);
v_h_373_ = lean_uint64_to_usize(v___x_372_);
v___x_374_ = ((size_t)5ULL);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_sub(v_depth_363_, v___x_376_);
v___x_378_ = lean_usize_mul(v___x_374_, v___x_377_);
v_h_379_ = lean_usize_shift_right(v_h_373_, v___x_378_);
v___x_380_ = lean_nat_add(v_i_366_, v___x_375_);
lean_dec(v_i_366_);
lean_inc(v_v_371_);
lean_inc(v_k_370_);
v___x_381_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_entries_367_, v_h_379_, v_depth_363_, v_k_370_, v_v_371_);
v_i_366_ = v___x_380_;
v_entries_367_ = v___x_381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_383_, lean_object* v_keys_384_, lean_object* v_vals_385_, lean_object* v_i_386_, lean_object* v_entries_387_){
_start:
{
size_t v_depth_boxed_388_; lean_object* v_res_389_; 
v_depth_boxed_388_ = lean_unbox_usize(v_depth_383_);
lean_dec(v_depth_383_);
v_res_389_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_388_, v_keys_384_, v_vals_385_, v_i_386_, v_entries_387_);
lean_dec_ref(v_vals_385_);
lean_dec_ref(v_keys_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
size_t v_x_1415__boxed_395_; size_t v_x_1416__boxed_396_; lean_object* v_res_397_; 
v_x_1415__boxed_395_ = lean_unbox_usize(v_x_391_);
lean_dec(v_x_391_);
v_x_1416__boxed_396_ = lean_unbox_usize(v_x_392_);
lean_dec(v_x_392_);
v_res_397_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_390_, v_x_1415__boxed_395_, v_x_1416__boxed_396_, v_x_393_, v_x_394_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
uint64_t v___x_401_; size_t v___x_402_; size_t v___x_403_; lean_object* v___x_404_; 
v___x_401_ = l_Lean_instHashableMVarId_hash(v_x_399_);
v___x_402_ = lean_uint64_to_usize(v___x_401_);
v___x_403_ = ((size_t)1ULL);
v___x_404_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_398_, v___x_402_, v___x_403_, v_x_399_, v_x_400_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(lean_object* v_mvarId_405_, lean_object* v_val_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v_mctx_410_; lean_object* v_cache_411_; lean_object* v_zetaDeltaFVarIds_412_; lean_object* v_postponed_413_; lean_object* v_diag_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_442_; 
v___x_409_ = lean_st_ref_take(v___y_407_);
v_mctx_410_ = lean_ctor_get(v___x_409_, 0);
v_cache_411_ = lean_ctor_get(v___x_409_, 1);
v_zetaDeltaFVarIds_412_ = lean_ctor_get(v___x_409_, 2);
v_postponed_413_ = lean_ctor_get(v___x_409_, 3);
v_diag_414_ = lean_ctor_get(v___x_409_, 4);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_442_ == 0)
{
v___x_416_ = v___x_409_;
v_isShared_417_ = v_isSharedCheck_442_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_diag_414_);
lean_inc(v_postponed_413_);
lean_inc(v_zetaDeltaFVarIds_412_);
lean_inc(v_cache_411_);
lean_inc(v_mctx_410_);
lean_dec(v___x_409_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_442_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v_depth_418_; lean_object* v_levelAssignDepth_419_; lean_object* v_lmvarCounter_420_; lean_object* v_mvarCounter_421_; lean_object* v_lDecls_422_; lean_object* v_decls_423_; lean_object* v_userNames_424_; lean_object* v_lAssignment_425_; lean_object* v_eAssignment_426_; lean_object* v_dAssignment_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_441_; 
v_depth_418_ = lean_ctor_get(v_mctx_410_, 0);
v_levelAssignDepth_419_ = lean_ctor_get(v_mctx_410_, 1);
v_lmvarCounter_420_ = lean_ctor_get(v_mctx_410_, 2);
v_mvarCounter_421_ = lean_ctor_get(v_mctx_410_, 3);
v_lDecls_422_ = lean_ctor_get(v_mctx_410_, 4);
v_decls_423_ = lean_ctor_get(v_mctx_410_, 5);
v_userNames_424_ = lean_ctor_get(v_mctx_410_, 6);
v_lAssignment_425_ = lean_ctor_get(v_mctx_410_, 7);
v_eAssignment_426_ = lean_ctor_get(v_mctx_410_, 8);
v_dAssignment_427_ = lean_ctor_get(v_mctx_410_, 9);
v_isSharedCheck_441_ = !lean_is_exclusive(v_mctx_410_);
if (v_isSharedCheck_441_ == 0)
{
v___x_429_ = v_mctx_410_;
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_dAssignment_427_);
lean_inc(v_eAssignment_426_);
lean_inc(v_lAssignment_425_);
lean_inc(v_userNames_424_);
lean_inc(v_decls_423_);
lean_inc(v_lDecls_422_);
lean_inc(v_mvarCounter_421_);
lean_inc(v_lmvarCounter_420_);
lean_inc(v_levelAssignDepth_419_);
lean_inc(v_depth_418_);
lean_dec(v_mctx_410_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(v_eAssignment_426_, v_mvarId_405_, v_val_406_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 8, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_depth_418_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_levelAssignDepth_419_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_lmvarCounter_420_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_mvarCounter_421_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_lDecls_422_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_decls_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_userNames_424_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v_lAssignment_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 8, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_440_, 9, v_dAssignment_427_);
v___x_433_ = v_reuseFailAlloc_440_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_433_);
v___x_435_ = v___x_416_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_cache_411_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_zetaDeltaFVarIds_412_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v_postponed_413_);
lean_ctor_set(v_reuseFailAlloc_439_, 4, v_diag_414_);
v___x_435_ = v_reuseFailAlloc_439_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_st_ref_set(v___y_407_, v___x_435_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg___boxed(lean_object* v_mvarId_443_, lean_object* v_val_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(v_mvarId_443_, v_val_444_, v___y_445_);
lean_dec(v___y_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore___lam__0(lean_object* v_mvarId_448_, lean_object* v___x_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; 
lean_inc(v_mvarId_448_);
v___x_455_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_448_, v___x_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_456_; 
lean_dec_ref(v___x_455_);
lean_inc(v_mvarId_448_);
v___x_456_ = l_Lean_MVarId_getType(v_mvarId_448_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_458_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref(v___x_456_);
v___x_458_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_a_457_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_481_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_481_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_481_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_481_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
if (lean_obj_tag(v_a_459_) == 0)
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
lean_dec(v_mvarId_448_);
v___x_463_ = 0;
v___x_464_ = lean_box(v___x_463_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_464_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
lean_object* v_val_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_479_; 
lean_del_object(v___x_461_);
v_val_468_ = lean_ctor_get(v_a_459_, 0);
lean_inc(v_val_468_);
lean_dec_ref(v_a_459_);
v___x_469_ = l_Lean_mkFVar(v_val_468_);
v___x_470_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(v_mvarId_448_, v___x_469_, v___y_451_);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v___x_470_, 0);
lean_dec(v_unused_480_);
v___x_472_ = v___x_470_;
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
else
{
lean_dec(v___x_470_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = 1;
v___x_475_ = lean_box(v___x_474_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_dec(v_mvarId_448_);
v_a_482_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_458_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_458_);
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
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_mvarId_448_);
v_a_490_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_456_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_456_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_mvarId_448_);
v_a_498_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_455_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_455_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore___lam__0___boxed(lean_object* v_mvarId_506_, lean_object* v___x_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_MVarId_assumptionCore___lam__0(v_mvarId_506_, v___x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore(lean_object* v_mvarId_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v___x_523_; lean_object* v___f_524_; lean_object* v___x_525_; 
v___x_523_ = ((lean_object*)(l_Lean_MVarId_assumptionCore___closed__1));
lean_inc(v_mvarId_517_);
v___f_524_ = lean_alloc_closure((void*)(l_Lean_MVarId_assumptionCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_524_, 0, v_mvarId_517_);
lean_closure_set(v___f_524_, 1, v___x_523_);
v___x_525_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(v_mvarId_517_, v___f_524_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumptionCore___boxed(lean_object* v_mvarId_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_MVarId_assumptionCore(v_mvarId_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0(lean_object* v_mvarId_533_, lean_object* v_val_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(v_mvarId_533_, v_val_534_, v___y_536_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___boxed(lean_object* v_mvarId_541_, lean_object* v_val_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0(v_mvarId_541_, v_val_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0(lean_object* v_00_u03b2_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(v_x_550_, v_x_551_, v_x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_554_, lean_object* v_x_555_, size_t v_x_556_, size_t v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_555_, v_x_556_, v_x_557_, v_x_558_, v_x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_561_, lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
size_t v_x_1801__boxed_567_; size_t v_x_1802__boxed_568_; lean_object* v_res_569_; 
v_x_1801__boxed_567_ = lean_unbox_usize(v_x_563_);
lean_dec(v_x_563_);
v_x_1802__boxed_568_ = lean_unbox_usize(v_x_564_);
lean_dec(v_x_564_);
v_res_569_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2(v_00_u03b2_561_, v_x_562_, v_x_1801__boxed_567_, v_x_1802__boxed_568_, v_x_565_, v_x_566_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_570_, lean_object* v_n_571_, lean_object* v_k_572_, lean_object* v_v_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(v_n_571_, v_k_572_, v_v_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_575_, size_t v_depth_576_, lean_object* v_keys_577_, lean_object* v_vals_578_, lean_object* v_heq_579_, lean_object* v_i_580_, lean_object* v_entries_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_576_, v_keys_577_, v_vals_578_, v_i_580_, v_entries_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_583_, lean_object* v_depth_584_, lean_object* v_keys_585_, lean_object* v_vals_586_, lean_object* v_heq_587_, lean_object* v_i_588_, lean_object* v_entries_589_){
_start:
{
size_t v_depth_boxed_590_; lean_object* v_res_591_; 
v_depth_boxed_590_ = lean_unbox_usize(v_depth_584_);
lean_dec(v_depth_584_);
v_res_591_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_583_, v_depth_boxed_590_, v_keys_585_, v_vals_586_, v_heq_587_, v_i_588_, v_entries_589_);
lean_dec_ref(v_vals_586_);
lean_dec_ref(v_keys_585_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_592_, lean_object* v_x_593_, lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_593_, v_x_594_, v_x_595_, v_x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumption(lean_object* v_mvarId_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; 
lean_inc(v_mvarId_598_);
v___x_604_ = l_Lean_MVarId_assumptionCore(v_mvarId_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_617_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_617_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_609_; 
v___x_609_ = lean_unbox(v_a_605_);
lean_dec(v_a_605_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
lean_del_object(v___x_607_);
v___x_610_ = ((lean_object*)(l_Lean_MVarId_assumptionCore___closed__1));
v___x_611_ = lean_box(0);
v___x_612_ = l_Lean_Meta_throwTacticEx___redArg(v___x_610_, v_mvarId_598_, v___x_611_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_615_; 
lean_dec(v_mvarId_598_);
v___x_613_ = lean_box(0);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_613_);
v___x_615_ = v___x_607_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_mvarId_598_);
v_a_618_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_604_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_604_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assumption___boxed(lean_object* v_mvarId_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_MVarId_assumption(v_mvarId_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_632_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
