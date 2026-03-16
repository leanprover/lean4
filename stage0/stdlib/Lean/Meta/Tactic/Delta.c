// Lean compiler output
// Module: Lean.Meta.Tactic.Delta
// Imports: public import Lean.Meta.Tactic.Replace import Lean.Meta.Transform
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
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_changeLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_change(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_deltaExpand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_deltaExpand___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_deltaExpand___closed__0 = (const lean_object*)&l_Lean_Meta_deltaExpand___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_deltaTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "delta"};
static const lean_object* l_Lean_MVarId_deltaTarget___closed__0 = (const lean_object*)&l_Lean_MVarId_deltaTarget___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_deltaTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_deltaTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 170, 171, 73, 211, 254, 35, 39)}};
static const lean_object* l_Lean_MVarId_deltaTarget___closed__1 = (const lean_object*)&l_Lean_MVarId_deltaTarget___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f(lean_object* v_e_1_, lean_object* v_p_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Expr_getAppFn(v_e_1_);
if (lean_obj_tag(v___x_9_) == 4)
{
lean_object* v_declName_10_; lean_object* v_us_11_; lean_object* v___x_12_; lean_object* v_env_16_; uint8_t v___x_17_; lean_object* v___x_18_; 
v_declName_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_declName_10_);
v_us_11_ = lean_ctor_get(v___x_9_, 1);
lean_inc(v_us_11_);
lean_dec_ref(v___x_9_);
v___x_12_ = lean_st_ref_get(v_a_4_);
v_env_16_ = lean_ctor_get(v___x_12_, 0);
lean_inc_ref(v_env_16_);
lean_dec(v___x_12_);
v___x_17_ = 0;
v___x_18_ = l_Lean_Environment_find_x3f(v_env_16_, v_declName_10_, v___x_17_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_dec(v_us_11_);
lean_dec_ref(v_p_2_);
lean_dec_ref(v_e_1_);
goto v___jp_6_;
}
else
{
lean_object* v_val_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_55_; 
v_val_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_55_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_55_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_val_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_55_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_23_ = l_Lean_ConstantInfo_name(v_val_19_);
v___x_24_ = lean_apply_1(v_p_2_, v___x_23_);
v___x_25_ = lean_unbox(v___x_24_);
if (v___x_25_ == 0)
{
lean_del_object(v___x_21_);
lean_dec(v_val_19_);
lean_dec(v_us_11_);
lean_dec_ref(v_e_1_);
goto v___jp_13_;
}
else
{
uint8_t v___x_26_; 
v___x_26_ = l_Lean_ConstantInfo_hasValue(v_val_19_, v___x_17_);
if (v___x_26_ == 0)
{
lean_del_object(v___x_21_);
lean_dec(v_val_19_);
lean_dec(v_us_11_);
lean_dec_ref(v_e_1_);
goto v___jp_13_;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_27_ = l_Lean_ConstantInfo_levelParams(v_val_19_);
v___x_28_ = l_List_lengthTR___redArg(v___x_27_);
lean_dec(v___x_27_);
v___x_29_ = l_List_lengthTR___redArg(v_us_11_);
v___x_30_ = lean_nat_dec_eq(v___x_28_, v___x_29_);
lean_dec(v___x_29_);
lean_dec(v___x_28_);
if (v___x_30_ == 0)
{
lean_del_object(v___x_21_);
lean_dec(v_val_19_);
lean_dec(v_us_11_);
lean_dec_ref(v_e_1_);
goto v___jp_13_;
}
else
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Core_instantiateValueLevelParams(v_val_19_, v_us_11_, v_a_3_, v_a_4_);
lean_dec(v_val_19_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_46_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_46_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_46_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_46_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_36_ = l_Lean_Expr_getAppNumArgs(v_e_1_);
v___x_37_ = lean_mk_empty_array_with_capacity(v___x_36_);
lean_dec(v___x_36_);
v___x_38_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_1_, v___x_37_);
v___x_39_ = l_Lean_Expr_betaRev(v_a_32_, v___x_38_, v___x_26_, v___x_17_);
lean_dec_ref(v___x_38_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_39_);
v___x_41_ = v___x_21_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_45_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_43_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 0, v___x_41_);
v___x_43_ = v___x_34_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
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
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_54_; 
lean_del_object(v___x_21_);
lean_dec_ref(v_e_1_);
v_a_47_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_54_ == 0)
{
v___x_49_ = v___x_31_;
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_31_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_54_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_52_; 
if (v_isShared_50_ == 0)
{
v___x_52_ = v___x_49_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_a_47_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
}
}
}
}
v___jp_13_:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_box(0);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
else
{
lean_dec_ref(v___x_9_);
lean_dec_ref(v_p_2_);
lean_dec_ref(v_e_1_);
goto v___jp_6_;
}
v___jp_6_:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_box(0);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f___boxed(lean_object* v_e_56_, lean_object* v_p_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Meta_delta_x3f(v_e_56_, v_p_57_, v_a_58_, v_a_59_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__0(lean_object* v_p_62_, lean_object* v_e_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Meta_delta_x3f(v_e_63_, v_p_62_, v___y_64_, v___y_65_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_87_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_87_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_87_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_87_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
if (lean_obj_tag(v_a_68_) == 0)
{
lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_72_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_72_, 0, v_a_68_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_72_);
v___x_74_ = v___x_70_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
else
{
lean_object* v_val_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_86_; 
v_val_76_ = lean_ctor_get(v_a_68_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v_a_68_);
if (v_isSharedCheck_86_ == 0)
{
v___x_78_ = v_a_68_;
v_isShared_79_ = v_isSharedCheck_86_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_val_76_);
lean_dec(v_a_68_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_86_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_val_76_);
v___x_81_ = v_reuseFailAlloc_85_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_83_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_81_);
v___x_83_ = v___x_70_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
}
else
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_88_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_67_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_67_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_88_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__0___boxed(lean_object* v_p_96_, lean_object* v_e_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Meta_deltaExpand___lam__0(v_p_96_, v_e_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__1(lean_object* v_e_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v_e_102_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__1___boxed(lean_object* v_e_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Meta_deltaExpand___lam__1(v_e_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_113_, lean_object* v_x_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_apply_1(v_x_114_, lean_box(0));
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_120_, lean_object* v_x_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(v_00_u03b1_120_, v_x_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_126_, lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_box(0);
return v___x_128_;
}
else
{
lean_object* v_key_129_; lean_object* v_value_130_; lean_object* v_tail_131_; uint8_t v___x_132_; 
v_key_129_ = lean_ctor_get(v_x_127_, 0);
v_value_130_ = lean_ctor_get(v_x_127_, 1);
v_tail_131_ = lean_ctor_get(v_x_127_, 2);
v___x_132_ = l_Lean_ExprStructEq_beq(v_key_129_, v_a_126_);
if (v___x_132_ == 0)
{
v_x_127_ = v_tail_131_;
goto _start;
}
else
{
lean_object* v___x_134_; 
lean_inc(v_value_130_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v_value_130_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_135_, lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_135_, v_x_136_);
lean_dec(v_x_136_);
lean_dec_ref(v_a_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(lean_object* v_m_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_buckets_140_; lean_object* v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v_fold_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v___x_148_; size_t v___x_149_; size_t v___x_150_; size_t v___x_151_; size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_buckets_140_ = lean_ctor_get(v_m_138_, 1);
v___x_141_ = lean_array_get_size(v_buckets_140_);
v___x_142_ = l_Lean_ExprStructEq_hash(v_a_139_);
v___x_143_ = 32ULL;
v___x_144_ = lean_uint64_shift_right(v___x_142_, v___x_143_);
v_fold_145_ = lean_uint64_xor(v___x_142_, v___x_144_);
v___x_146_ = 16ULL;
v___x_147_ = lean_uint64_shift_right(v_fold_145_, v___x_146_);
v___x_148_ = lean_uint64_xor(v_fold_145_, v___x_147_);
v___x_149_ = lean_uint64_to_usize(v___x_148_);
v___x_150_ = lean_usize_of_nat(v___x_141_);
v___x_151_ = ((size_t)1ULL);
v___x_152_ = lean_usize_sub(v___x_150_, v___x_151_);
v___x_153_ = lean_usize_land(v___x_149_, v___x_152_);
v___x_154_ = lean_array_uget_borrowed(v_buckets_140_, v___x_153_);
v___x_155_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_139_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_m_156_, v_a_157_);
lean_dec_ref(v_a_157_);
lean_dec_ref(v_m_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_159_, lean_object* v_b_160_, lean_object* v_x_161_){
_start:
{
if (lean_obj_tag(v_x_161_) == 0)
{
lean_dec(v_b_160_);
lean_dec_ref(v_a_159_);
return v_x_161_;
}
else
{
lean_object* v_key_162_; lean_object* v_value_163_; lean_object* v_tail_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_176_; 
v_key_162_ = lean_ctor_get(v_x_161_, 0);
v_value_163_ = lean_ctor_get(v_x_161_, 1);
v_tail_164_ = lean_ctor_get(v_x_161_, 2);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_161_);
if (v_isSharedCheck_176_ == 0)
{
v___x_166_ = v_x_161_;
v_isShared_167_ = v_isSharedCheck_176_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_tail_164_);
lean_inc(v_value_163_);
lean_inc(v_key_162_);
lean_dec(v_x_161_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_176_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
uint8_t v___x_168_; 
v___x_168_ = l_Lean_ExprStructEq_beq(v_key_162_, v_a_159_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_a_159_, v_b_160_, v_tail_164_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 2, v___x_169_);
v___x_171_ = v___x_166_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_key_162_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_value_163_);
lean_ctor_set(v_reuseFailAlloc_172_, 2, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
else
{
lean_object* v___x_174_; 
lean_dec(v_value_163_);
lean_dec(v_key_162_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v_b_160_);
lean_ctor_set(v___x_166_, 0, v_a_159_);
v___x_174_ = v___x_166_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_159_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_b_160_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_tail_164_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
return v_x_177_;
}
else
{
lean_object* v_key_179_; lean_object* v_value_180_; lean_object* v_tail_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_204_; 
v_key_179_ = lean_ctor_get(v_x_178_, 0);
v_value_180_ = lean_ctor_get(v_x_178_, 1);
v_tail_181_ = lean_ctor_get(v_x_178_, 2);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_204_ == 0)
{
v___x_183_ = v_x_178_;
v_isShared_184_ = v_isSharedCheck_204_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_tail_181_);
lean_inc(v_value_180_);
lean_inc(v_key_179_);
lean_dec(v_x_178_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_204_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v_fold_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_185_ = lean_array_get_size(v_x_177_);
v___x_186_ = l_Lean_ExprStructEq_hash(v_key_179_);
v___x_187_ = 32ULL;
v___x_188_ = lean_uint64_shift_right(v___x_186_, v___x_187_);
v_fold_189_ = lean_uint64_xor(v___x_186_, v___x_188_);
v___x_190_ = 16ULL;
v___x_191_ = lean_uint64_shift_right(v_fold_189_, v___x_190_);
v___x_192_ = lean_uint64_xor(v_fold_189_, v___x_191_);
v___x_193_ = lean_uint64_to_usize(v___x_192_);
v___x_194_ = lean_usize_of_nat(v___x_185_);
v___x_195_ = ((size_t)1ULL);
v___x_196_ = lean_usize_sub(v___x_194_, v___x_195_);
v___x_197_ = lean_usize_land(v___x_193_, v___x_196_);
v___x_198_ = lean_array_uget_borrowed(v_x_177_, v___x_197_);
lean_inc(v___x_198_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 2, v___x_198_);
v___x_200_ = v___x_183_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_key_179_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_value_180_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v___x_198_);
v___x_200_ = v_reuseFailAlloc_203_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; 
v___x_201_ = lean_array_uset(v_x_177_, v___x_197_, v___x_200_);
v_x_177_ = v___x_201_;
v_x_178_ = v_tail_181_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_205_, lean_object* v_source_206_, lean_object* v_target_207_){
_start:
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_array_get_size(v_source_206_);
v___x_209_ = lean_nat_dec_lt(v_i_205_, v___x_208_);
if (v___x_209_ == 0)
{
lean_dec_ref(v_source_206_);
lean_dec(v_i_205_);
return v_target_207_;
}
else
{
lean_object* v_es_210_; lean_object* v___x_211_; lean_object* v_source_212_; lean_object* v_target_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_es_210_ = lean_array_fget(v_source_206_, v_i_205_);
v___x_211_ = lean_box(0);
v_source_212_ = lean_array_fset(v_source_206_, v_i_205_, v___x_211_);
v_target_213_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_207_, v_es_210_);
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_add(v_i_205_, v___x_214_);
lean_dec(v_i_205_);
v_i_205_ = v___x_215_;
v_source_206_ = v_source_212_;
v_target_207_ = v_target_213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_nbuckets_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_218_ = lean_array_get_size(v_data_217_);
v___x_219_ = lean_unsigned_to_nat(2u);
v_nbuckets_220_ = lean_nat_mul(v___x_218_, v___x_219_);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_box(0);
v___x_223_ = lean_mk_array(v_nbuckets_220_, v___x_222_);
v___x_224_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_221_, v_data_217_, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
uint8_t v___x_227_; 
v___x_227_ = 0;
return v___x_227_;
}
else
{
lean_object* v_key_228_; lean_object* v_tail_229_; uint8_t v___x_230_; 
v_key_228_ = lean_ctor_get(v_x_226_, 0);
v_tail_229_ = lean_ctor_get(v_x_226_, 2);
v___x_230_ = l_Lean_ExprStructEq_beq(v_key_228_, v_a_225_);
if (v___x_230_ == 0)
{
v_x_226_ = v_tail_229_;
goto _start;
}
else
{
return v___x_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_232_, lean_object* v_x_233_){
_start:
{
uint8_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg(v_a_232_, v_x_233_);
lean_dec(v_x_233_);
lean_dec_ref(v_a_232_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(lean_object* v_m_236_, lean_object* v_a_237_, lean_object* v_b_238_){
_start:
{
lean_object* v_size_239_; lean_object* v_buckets_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_283_; 
v_size_239_ = lean_ctor_get(v_m_236_, 0);
v_buckets_240_ = lean_ctor_get(v_m_236_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_m_236_);
if (v_isSharedCheck_283_ == 0)
{
v___x_242_ = v_m_236_;
v_isShared_243_ = v_isSharedCheck_283_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_buckets_240_);
lean_inc(v_size_239_);
lean_dec(v_m_236_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_283_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v_fold_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v_bkt_257_; uint8_t v___x_258_; 
v___x_244_ = lean_array_get_size(v_buckets_240_);
v___x_245_ = l_Lean_ExprStructEq_hash(v_a_237_);
v___x_246_ = 32ULL;
v___x_247_ = lean_uint64_shift_right(v___x_245_, v___x_246_);
v_fold_248_ = lean_uint64_xor(v___x_245_, v___x_247_);
v___x_249_ = 16ULL;
v___x_250_ = lean_uint64_shift_right(v_fold_248_, v___x_249_);
v___x_251_ = lean_uint64_xor(v_fold_248_, v___x_250_);
v___x_252_ = lean_uint64_to_usize(v___x_251_);
v___x_253_ = lean_usize_of_nat(v___x_244_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_sub(v___x_253_, v___x_254_);
v___x_256_ = lean_usize_land(v___x_252_, v___x_255_);
v_bkt_257_ = lean_array_uget_borrowed(v_buckets_240_, v___x_256_);
v___x_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg(v_a_237_, v_bkt_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v_size_x27_260_; lean_object* v___x_261_; lean_object* v_buckets_x27_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_259_ = lean_unsigned_to_nat(1u);
v_size_x27_260_ = lean_nat_add(v_size_239_, v___x_259_);
lean_dec(v_size_239_);
lean_inc(v_bkt_257_);
v___x_261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_261_, 0, v_a_237_);
lean_ctor_set(v___x_261_, 1, v_b_238_);
lean_ctor_set(v___x_261_, 2, v_bkt_257_);
v_buckets_x27_262_ = lean_array_uset(v_buckets_240_, v___x_256_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(4u);
v___x_264_ = lean_nat_mul(v_size_x27_260_, v___x_263_);
v___x_265_ = lean_unsigned_to_nat(3u);
v___x_266_ = lean_nat_div(v___x_264_, v___x_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_array_get_size(v_buckets_x27_262_);
v___x_268_ = lean_nat_dec_le(v___x_266_, v___x_267_);
lean_dec(v___x_266_);
if (v___x_268_ == 0)
{
lean_object* v_val_269_; lean_object* v___x_271_; 
v_val_269_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_262_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_val_269_);
lean_ctor_set(v___x_242_, 0, v_size_x27_260_);
v___x_271_ = v___x_242_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_size_x27_260_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_val_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
else
{
lean_object* v___x_274_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_buckets_x27_262_);
lean_ctor_set(v___x_242_, 0, v_size_x27_260_);
v___x_274_ = v___x_242_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_size_x27_260_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_buckets_x27_262_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
lean_object* v___x_276_; lean_object* v_buckets_x27_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
lean_inc(v_bkt_257_);
v___x_276_ = lean_box(0);
v_buckets_x27_277_ = lean_array_uset(v_buckets_240_, v___x_256_, v___x_276_);
v___x_278_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_a_237_, v_b_238_, v_bkt_257_);
v___x_279_ = lean_array_uset(v_buckets_x27_277_, v___x_256_, v___x_278_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_279_);
v___x_281_ = v___x_242_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_size_239_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(lean_object* v_a_284_, lean_object* v_e_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_288_ = lean_st_ref_take(v_a_284_);
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v___x_288_, v_e_285_, v_a_286_);
v___x_290_ = lean_st_ref_set(v_a_284_, v___x_289_);
v___x_291_ = lean_box(0);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed(lean_object* v_a_292_, lean_object* v_e_293_, lean_object* v_a_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(v_a_292_, v_e_293_, v_a_294_);
lean_dec(v_a_292_);
return v_res_296_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = l_Lean_maxRecDepthErrorMessage;
v___x_303_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_305_ = l_Lean_MessageData_ofFormat(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_307_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_308_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_309_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_ref_309_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(lean_object* v_x_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___y_323_; lean_object* v_fileName_332_; lean_object* v_fileMap_333_; lean_object* v_options_334_; lean_object* v_currRecDepth_335_; lean_object* v_maxRecDepth_336_; lean_object* v_ref_337_; lean_object* v_currNamespace_338_; lean_object* v_openDecls_339_; lean_object* v_initHeartbeats_340_; lean_object* v_maxHeartbeats_341_; lean_object* v_quotContext_342_; lean_object* v_currMacroScope_343_; uint8_t v_diag_344_; lean_object* v_cancelTk_x3f_345_; uint8_t v_suppressElabErrors_346_; lean_object* v_inheritedTraceOptions_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_359_; 
v_fileName_332_ = lean_ctor_get(v___y_319_, 0);
v_fileMap_333_ = lean_ctor_get(v___y_319_, 1);
v_options_334_ = lean_ctor_get(v___y_319_, 2);
v_currRecDepth_335_ = lean_ctor_get(v___y_319_, 3);
v_maxRecDepth_336_ = lean_ctor_get(v___y_319_, 4);
v_ref_337_ = lean_ctor_get(v___y_319_, 5);
v_currNamespace_338_ = lean_ctor_get(v___y_319_, 6);
v_openDecls_339_ = lean_ctor_get(v___y_319_, 7);
v_initHeartbeats_340_ = lean_ctor_get(v___y_319_, 8);
v_maxHeartbeats_341_ = lean_ctor_get(v___y_319_, 9);
v_quotContext_342_ = lean_ctor_get(v___y_319_, 10);
v_currMacroScope_343_ = lean_ctor_get(v___y_319_, 11);
v_diag_344_ = lean_ctor_get_uint8(v___y_319_, sizeof(void*)*14);
v_cancelTk_x3f_345_ = lean_ctor_get(v___y_319_, 12);
v_suppressElabErrors_346_ = lean_ctor_get_uint8(v___y_319_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_347_ = lean_ctor_get(v___y_319_, 13);
v_isSharedCheck_359_ = !lean_is_exclusive(v___y_319_);
if (v_isSharedCheck_359_ == 0)
{
v___x_349_ = v___y_319_;
v_isShared_350_ = v_isSharedCheck_359_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_inheritedTraceOptions_347_);
lean_inc(v_cancelTk_x3f_345_);
lean_inc(v_currMacroScope_343_);
lean_inc(v_quotContext_342_);
lean_inc(v_maxHeartbeats_341_);
lean_inc(v_initHeartbeats_340_);
lean_inc(v_openDecls_339_);
lean_inc(v_currNamespace_338_);
lean_inc(v_ref_337_);
lean_inc(v_maxRecDepth_336_);
lean_inc(v_currRecDepth_335_);
lean_inc(v_options_334_);
lean_inc(v_fileMap_333_);
lean_inc(v_fileName_332_);
lean_dec(v___y_319_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_359_;
goto v_resetjp_348_;
}
v___jp_322_:
{
if (lean_obj_tag(v___y_323_) == 0)
{
return v___y_323_;
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
v_a_324_ = lean_ctor_get(v___y_323_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___y_323_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___y_323_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___y_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
v_resetjp_348_:
{
uint8_t v___x_351_; 
v___x_351_ = lean_nat_dec_eq(v_currRecDepth_335_, v_maxRecDepth_336_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_currRecDepth_335_, v___x_352_);
lean_dec(v_currRecDepth_335_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 3, v___x_353_);
v___x_355_ = v___x_349_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_fileName_332_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_fileMap_333_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_options_334_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_maxRecDepth_336_);
lean_ctor_set(v_reuseFailAlloc_357_, 5, v_ref_337_);
lean_ctor_set(v_reuseFailAlloc_357_, 6, v_currNamespace_338_);
lean_ctor_set(v_reuseFailAlloc_357_, 7, v_openDecls_339_);
lean_ctor_set(v_reuseFailAlloc_357_, 8, v_initHeartbeats_340_);
lean_ctor_set(v_reuseFailAlloc_357_, 9, v_maxHeartbeats_341_);
lean_ctor_set(v_reuseFailAlloc_357_, 10, v_quotContext_342_);
lean_ctor_set(v_reuseFailAlloc_357_, 11, v_currMacroScope_343_);
lean_ctor_set(v_reuseFailAlloc_357_, 12, v_cancelTk_x3f_345_);
lean_ctor_set(v_reuseFailAlloc_357_, 13, v_inheritedTraceOptions_347_);
lean_ctor_set_uint8(v_reuseFailAlloc_357_, sizeof(void*)*14, v_diag_344_);
lean_ctor_set_uint8(v_reuseFailAlloc_357_, sizeof(void*)*14 + 1, v_suppressElabErrors_346_);
v___x_355_ = v_reuseFailAlloc_357_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_356_; 
v___x_356_ = lean_apply_4(v_x_317_, v___y_318_, v___x_355_, v___y_320_, lean_box(0));
v___y_323_ = v___x_356_;
goto v___jp_322_;
}
}
else
{
lean_object* v___x_358_; 
lean_del_object(v___x_349_);
lean_dec_ref(v_inheritedTraceOptions_347_);
lean_dec(v_cancelTk_x3f_345_);
lean_dec(v_currMacroScope_343_);
lean_dec(v_quotContext_342_);
lean_dec(v_maxHeartbeats_341_);
lean_dec(v_initHeartbeats_340_);
lean_dec(v_openDecls_339_);
lean_dec(v_currNamespace_338_);
lean_dec(v_maxRecDepth_336_);
lean_dec(v_currRecDepth_335_);
lean_dec_ref(v_options_334_);
lean_dec_ref(v_fileMap_333_);
lean_dec_ref(v_fileName_332_);
lean_dec(v___y_320_);
lean_dec(v___y_318_);
lean_dec_ref(v_x_317_);
v___x_358_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_337_);
v___y_323_ = v___x_358_;
goto v___jp_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_360_, v___y_361_, v___y_362_, v___y_363_);
return v_res_365_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_366_; lean_object* v_dummy_367_; 
v___x_366_ = lean_box(0);
v_dummy_367_ = l_Lean_Expr_sort___override(v___x_366_);
return v_dummy_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(lean_object* v_pre_368_, lean_object* v_post_369_, size_t v_sz_370_, size_t v_i_371_, lean_object* v_bs_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = lean_usize_dec_lt(v_i_371_, v_sz_370_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v_post_369_);
lean_dec_ref(v_pre_368_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v_bs_372_);
return v___x_378_;
}
else
{
lean_object* v_v_379_; lean_object* v___x_380_; 
v_v_379_ = lean_array_uget_borrowed(v_bs_372_, v_i_371_);
lean_inc(v___y_375_);
lean_inc_ref(v___y_374_);
lean_inc(v___y_373_);
lean_inc(v_v_379_);
lean_inc_ref(v_post_369_);
lean_inc_ref(v_pre_368_);
v___x_380_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_368_, v_post_369_, v_v_379_, v___y_373_, v___y_374_, v___y_375_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; lean_object* v_bs_x27_383_; size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref(v___x_380_);
v___x_382_ = lean_unsigned_to_nat(0u);
v_bs_x27_383_ = lean_array_uset(v_bs_372_, v_i_371_, v___x_382_);
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_add(v_i_371_, v___x_384_);
v___x_386_ = lean_array_uset(v_bs_x27_383_, v_i_371_, v_a_381_);
v_i_371_ = v___x_385_;
v_bs_372_ = v___x_386_;
goto _start;
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v_bs_372_);
lean_dec_ref(v_post_369_);
lean_dec_ref(v_pre_368_);
v_a_388_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_380_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_380_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(lean_object* v_pre_396_, lean_object* v_post_397_, lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
if (lean_obj_tag(v_x_398_) == 5)
{
lean_object* v_fn_405_; lean_object* v_arg_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_fn_405_ = lean_ctor_get(v_x_398_, 0);
lean_inc_ref(v_fn_405_);
v_arg_406_ = lean_ctor_get(v_x_398_, 1);
lean_inc_ref(v_arg_406_);
lean_dec_ref(v_x_398_);
v___x_407_ = lean_array_set(v_x_399_, v_x_400_, v_arg_406_);
v___x_408_ = lean_unsigned_to_nat(1u);
v___x_409_ = lean_nat_sub(v_x_400_, v___x_408_);
lean_dec(v_x_400_);
v_x_398_ = v_fn_405_;
v_x_399_ = v___x_407_;
v_x_400_ = v___x_409_;
goto _start;
}
else
{
lean_object* v___x_411_; 
lean_dec(v_x_400_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
lean_inc(v___y_401_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_396_);
v___x_411_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_396_, v_post_397_, v_x_398_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; size_t v_sz_413_; size_t v___x_414_; lean_object* v___x_415_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v___x_411_);
v_sz_413_ = lean_array_size(v_x_399_);
v___x_414_ = ((size_t)0ULL);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
lean_inc(v___y_401_);
lean_inc_ref(v_post_397_);
lean_inc_ref(v_pre_396_);
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_396_, v_post_397_, v_sz_413_, v___x_414_, v_x_399_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref(v___x_415_);
v___x_417_ = l_Lean_mkAppN(v_a_412_, v_a_416_);
lean_dec(v_a_416_);
v___x_418_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_396_, v_post_397_, v___x_417_, v___y_401_, v___y_402_, v___y_403_);
return v___x_418_;
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_a_412_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_396_);
v_a_419_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_415_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_415_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v_x_399_);
lean_dec_ref(v_post_397_);
lean_dec_ref(v_pre_396_);
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(lean_object* v_pre_427_, lean_object* v_e_428_, lean_object* v_post_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; uint8_t v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; uint8_t v___y_442_; lean_object* v___y_452_; uint8_t v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; uint8_t v___y_457_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; uint8_t v___y_469_; uint8_t v___y_470_; lean_object* v___x_477_; 
lean_inc_ref(v_pre_427_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc_ref(v_e_428_);
v___x_477_ = lean_apply_4(v_pre_427_, v_e_428_, v___y_431_, v___y_432_, lean_box(0));
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_567_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_567_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_567_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_567_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___y_483_; 
switch(lean_obj_tag(v_a_478_))
{
case 0:
{
lean_object* v_e_557_; lean_object* v___x_559_; 
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_e_428_);
lean_dec_ref(v_pre_427_);
v_e_557_ = lean_ctor_get(v_a_478_, 0);
lean_inc_ref(v_e_557_);
lean_dec_ref(v_a_478_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v_e_557_);
v___x_559_ = v___x_480_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_e_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
case 1:
{
lean_object* v_e_561_; lean_object* v___x_562_; 
lean_del_object(v___x_480_);
lean_dec_ref(v_e_428_);
v_e_561_ = lean_ctor_get(v_a_478_, 0);
lean_inc_ref(v_e_561_);
lean_dec_ref(v_a_478_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v_post_429_);
lean_inc_ref(v_pre_427_);
v___x_562_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_427_, v_post_429_, v_e_561_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_564_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref(v___x_562_);
v___x_564_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v_a_563_, v___y_430_, v___y_431_, v___y_432_);
return v___x_564_;
}
else
{
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_pre_427_);
return v___x_562_;
}
}
default: 
{
lean_object* v_e_x3f_565_; 
lean_del_object(v___x_480_);
v_e_x3f_565_ = lean_ctor_get(v_a_478_, 0);
lean_inc(v_e_x3f_565_);
lean_dec_ref(v_a_478_);
if (lean_obj_tag(v_e_x3f_565_) == 0)
{
v___y_483_ = v_e_428_;
goto v___jp_482_;
}
else
{
lean_object* v_val_566_; 
lean_dec_ref(v_e_428_);
v_val_566_ = lean_ctor_get(v_e_x3f_565_, 0);
lean_inc(v_val_566_);
lean_dec_ref(v_e_x3f_565_);
v___y_483_ = v_val_566_;
goto v___jp_482_;
}
}
}
v___jp_482_:
{
switch(lean_obj_tag(v___y_483_))
{
case 7:
{
lean_object* v_binderName_484_; lean_object* v_binderType_485_; lean_object* v_body_486_; uint8_t v_binderInfo_487_; lean_object* v___x_488_; 
v_binderName_484_ = lean_ctor_get(v___y_483_, 0);
lean_inc(v_binderName_484_);
v_binderType_485_ = lean_ctor_get(v___y_483_, 1);
v_body_486_ = lean_ctor_get(v___y_483_, 2);
v_binderInfo_487_ = lean_ctor_get_uint8(v___y_483_, sizeof(void*)*3 + 8);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v_binderType_485_);
lean_inc_ref(v_post_429_);
lean_inc_ref(v_pre_427_);
v___x_488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_427_, v_post_429_, v_binderType_485_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v_body_486_);
lean_inc_ref(v_post_429_);
lean_inc_ref(v_pre_427_);
v___x_490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_427_, v_post_429_, v_body_486_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; size_t v___x_492_; size_t v___x_493_; uint8_t v___x_494_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref(v___x_490_);
v___x_492_ = lean_ptr_addr(v_binderType_485_);
v___x_493_ = lean_ptr_addr(v_a_489_);
v___x_494_ = lean_usize_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
v___y_465_ = v___y_483_;
v___y_466_ = v_a_489_;
v___y_467_ = v_a_491_;
v___y_468_ = v_binderName_484_;
v___y_469_ = v_binderInfo_487_;
v___y_470_ = v___x_494_;
goto v___jp_464_;
}
else
{
size_t v___x_495_; size_t v___x_496_; uint8_t v___x_497_; 
v___x_495_ = lean_ptr_addr(v_body_486_);
v___x_496_ = lean_ptr_addr(v_a_491_);
v___x_497_ = lean_usize_dec_eq(v___x_495_, v___x_496_);
v___y_465_ = v___y_483_;
v___y_466_ = v_a_489_;
v___y_467_ = v_a_491_;
v___y_468_ = v_binderName_484_;
v___y_469_ = v_binderInfo_487_;
v___y_470_ = v___x_497_;
goto v___jp_464_;
}
}
else
{
lean_dec(v_a_489_);
lean_dec(v_binderName_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_pre_427_);
return v___x_490_;
}
}
else
{
lean_dec(v_binderName_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_pre_427_);
return v___x_488_;
}
}
case 6:
{
lean_object* v_binderName_498_; lean_object* v_binderType_499_; lean_object* v_body_500_; uint8_t v_binderInfo_501_; lean_object* v___x_502_; 
v_binderName_498_ = lean_ctor_get(v___y_483_, 0);
lean_inc(v_binderName_498_);
v_binderType_499_ = lean_ctor_get(v___y_483_, 1);
v_body_500_ = lean_ctor_get(v___y_483_, 2);
v_binderInfo_501_ = lean_ctor_get_uint8(v___y_483_, sizeof(void*)*3 + 8);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v_binderType_499_);
lean_inc_ref(v_post_429_);
lean_inc_ref(v_pre_427_);
v___x_502_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_427_, v_post_429_, v_binderType_499_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___x_502_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v_body_500_);
lean_inc_ref(v_post_429_);
lean_inc_ref(v_pre_427_);
v___x_504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_427_, v_post_429_, v_body_500_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; size_t v___x_506_; size_t v___x_507_; uint8_t v___x_508_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref(v___x_504_);
v___x_506_ = lean_ptr_addr(v_binderType_499_);
v___x_507_ = lean_ptr_addr(v_a_503_);
v___x_508_ = lean_usize_dec_eq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
v___y_452_ = v___y_483_;
v___y_453_ = v_binderInfo_501_;
v___y_454_ = v_binderName_498_;
v___y_455_ = v_a_505_;
v___y_456_ = v_a_503_;
v___y_457_ = v___x_508_;
goto v___jp_451_;
}
else
{
size_t v___x_509_; size_t v___x_510_; uint8_t v___x_511_; 
v___x_509_ = lean_ptr_addr(v_body_500_);
v___x_510_ = lean_ptr_addr(v_a_505_);
v___x_511_ = lean_usize_dec_eq(v___x_509_, v___x_510_);
v___y_452_ = v___y_483_;
v___y_453_ = v_binderInfo_501_;
v___y_454_ = v_binderName_498_;
v___y_455_ = v_a_505_;
v___y_456_ = v_a_503_;
v___y_457_ = v___x_511_;
goto v___jp_451_;
}
}
else
{
lean_dec(v_a_503_);
lean_dec(v_binderName_498_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_pre_427_);
return v___x_504_;
}
}
else
{
lean_dec(v_binderName_498_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_pre_427_);
return v___x_502_;
}
}
case 8:
{
lean_object* v_declName_512_; lean_object* v_type_513_; lean_object* v_value_514_; lean_object* v_body_515_; uint8_t v_nondep_516_; lean_object* v___x_517_; 
v_declName_512_ = lean_ctor_get(v___y_483_, 0);
lean_inc(v_declName_512_);
v_type_513_ = lean_ctor_get(v___y_483_, 1);
v_value_514_ = lean_ctor_get(v___y_483_, 2);
v_body_515_ = lean_ctor_get(v___y_483_, 3);
lean_inc_ref(v_body_515_);
v_nondep_516_ = lean_ctor_get_uint8(v___y_483_, sizeof(void*)*4 + 8);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v_type_513_);
lean_inc_ref(v_post_429_);
lean_inc_ref(v_pre_427_);
v___x_517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_427_, v_post_429_, v_type_513_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_519_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref(v___x_517_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v_value_514_);
lean_inc_ref(v_post_429_);
lean_inc_ref(v_pre_427_);
v___x_519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_427_, v_post_429_, v_value_514_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref(v___x_519_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v_body_515_);
lean_inc_ref(v_post_429_);
lean_inc_ref(v_pre_427_);
v___x_521_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_427_, v_post_429_, v_body_515_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; size_t v___x_523_; size_t v___x_524_; uint8_t v___x_525_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v___x_521_);
v___x_523_ = lean_ptr_addr(v_type_513_);
v___x_524_ = lean_ptr_addr(v_a_518_);
v___x_525_ = lean_usize_dec_eq(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
v___y_435_ = v___y_483_;
v___y_436_ = v_a_520_;
v___y_437_ = v_a_518_;
v___y_438_ = v_nondep_516_;
v___y_439_ = v_body_515_;
v___y_440_ = v_declName_512_;
v___y_441_ = v_a_522_;
v___y_442_ = v___x_525_;
goto v___jp_434_;
}
else
{
size_t v___x_526_; size_t v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_ptr_addr(v_value_514_);
v___x_527_ = lean_ptr_addr(v_a_520_);
v___x_528_ = lean_usize_dec_eq(v___x_526_, v___x_527_);
v___y_435_ = v___y_483_;
v___y_436_ = v_a_520_;
v___y_437_ = v_a_518_;
v___y_438_ = v_nondep_516_;
v___y_439_ = v_body_515_;
v___y_440_ = v_declName_512_;
v___y_441_ = v_a_522_;
v___y_442_ = v___x_528_;
goto v___jp_434_;
}
}
else
{
lean_dec(v_a_520_);
lean_dec(v_a_518_);
lean_dec_ref(v_body_515_);
lean_dec(v_declName_512_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_pre_427_);
return v___x_521_;
}
}
else
{
lean_dec(v_a_518_);
lean_dec_ref(v_body_515_);
lean_dec(v_declName_512_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_pre_427_);
return v___x_519_;
}
}
else
{
lean_dec_ref(v_body_515_);
lean_dec(v_declName_512_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_pre_427_);
return v___x_517_;
}
}
case 5:
{
lean_object* v_dummy_529_; lean_object* v_nargs_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_dummy_529_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0);
v_nargs_530_ = l_Lean_Expr_getAppNumArgs(v___y_483_);
lean_inc(v_nargs_530_);
v___x_531_ = lean_mk_array(v_nargs_530_, v_dummy_529_);
v___x_532_ = lean_unsigned_to_nat(1u);
v___x_533_ = lean_nat_sub(v_nargs_530_, v___x_532_);
lean_dec(v_nargs_530_);
v___x_534_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_427_, v_post_429_, v___y_483_, v___x_531_, v___x_533_, v___y_430_, v___y_431_, v___y_432_);
return v___x_534_;
}
case 10:
{
lean_object* v_data_535_; lean_object* v_expr_536_; lean_object* v___x_537_; 
v_data_535_ = lean_ctor_get(v___y_483_, 0);
v_expr_536_ = lean_ctor_get(v___y_483_, 1);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v_expr_536_);
lean_inc_ref(v_post_429_);
lean_inc_ref(v_pre_427_);
v___x_537_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_427_, v_post_429_, v_expr_536_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; size_t v___x_539_; size_t v___x_540_; uint8_t v___x_541_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref(v___x_537_);
v___x_539_ = lean_ptr_addr(v_expr_536_);
v___x_540_ = lean_ptr_addr(v_a_538_);
v___x_541_ = lean_usize_dec_eq(v___x_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_inc(v_data_535_);
lean_dec_ref(v___y_483_);
v___x_542_ = l_Lean_Expr_mdata___override(v_data_535_, v_a_538_);
v___x_543_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___x_542_, v___y_430_, v___y_431_, v___y_432_);
return v___x_543_;
}
else
{
lean_object* v___x_544_; 
lean_dec(v_a_538_);
v___x_544_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___y_483_, v___y_430_, v___y_431_, v___y_432_);
return v___x_544_;
}
}
else
{
lean_dec_ref(v___y_483_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_pre_427_);
return v___x_537_;
}
}
case 11:
{
lean_object* v_typeName_545_; lean_object* v_idx_546_; lean_object* v_struct_547_; lean_object* v___x_548_; 
v_typeName_545_ = lean_ctor_get(v___y_483_, 0);
v_idx_546_ = lean_ctor_get(v___y_483_, 1);
v_struct_547_ = lean_ctor_get(v___y_483_, 2);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v_struct_547_);
lean_inc_ref(v_post_429_);
lean_inc_ref(v_pre_427_);
v___x_548_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_427_, v_post_429_, v_struct_547_, v___y_430_, v___y_431_, v___y_432_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; size_t v___x_550_; size_t v___x_551_; uint8_t v___x_552_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v___x_548_);
v___x_550_ = lean_ptr_addr(v_struct_547_);
v___x_551_ = lean_ptr_addr(v_a_549_);
v___x_552_ = lean_usize_dec_eq(v___x_550_, v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc(v_idx_546_);
lean_inc(v_typeName_545_);
lean_dec_ref(v___y_483_);
v___x_553_ = l_Lean_Expr_proj___override(v_typeName_545_, v_idx_546_, v_a_549_);
v___x_554_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___x_553_, v___y_430_, v___y_431_, v___y_432_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; 
lean_dec(v_a_549_);
v___x_555_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___y_483_, v___y_430_, v___y_431_, v___y_432_);
return v___x_555_;
}
}
else
{
lean_dec_ref(v___y_483_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_pre_427_);
return v___x_548_;
}
}
default: 
{
lean_object* v___x_556_; 
v___x_556_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___y_483_, v___y_430_, v___y_431_, v___y_432_);
return v___x_556_;
}
}
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v_post_429_);
lean_dec_ref(v_e_428_);
lean_dec_ref(v_pre_427_);
v_a_568_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_477_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_477_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
v___jp_434_:
{
if (v___y_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec_ref(v___y_439_);
lean_dec_ref(v___y_435_);
v___x_443_ = l_Lean_Expr_letE___override(v___y_440_, v___y_437_, v___y_436_, v___y_441_, v___y_438_);
v___x_444_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___x_443_, v___y_430_, v___y_431_, v___y_432_);
return v___x_444_;
}
else
{
size_t v___x_445_; size_t v___x_446_; uint8_t v___x_447_; 
v___x_445_ = lean_ptr_addr(v___y_439_);
lean_dec_ref(v___y_439_);
v___x_446_ = lean_ptr_addr(v___y_441_);
v___x_447_ = lean_usize_dec_eq(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref(v___y_435_);
v___x_448_ = l_Lean_Expr_letE___override(v___y_440_, v___y_437_, v___y_436_, v___y_441_, v___y_438_);
v___x_449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___x_448_, v___y_430_, v___y_431_, v___y_432_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; 
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_437_);
lean_dec_ref(v___y_436_);
v___x_450_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___y_435_, v___y_430_, v___y_431_, v___y_432_);
return v___x_450_;
}
}
}
v___jp_451_:
{
if (v___y_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec_ref(v___y_452_);
v___x_458_ = l_Lean_Expr_lam___override(v___y_454_, v___y_456_, v___y_455_, v___y_453_);
v___x_459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___x_458_, v___y_430_, v___y_431_, v___y_432_);
return v___x_459_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = l_Lean_instBEqBinderInfo_beq(v___y_453_, v___y_453_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec_ref(v___y_452_);
v___x_461_ = l_Lean_Expr_lam___override(v___y_454_, v___y_456_, v___y_455_, v___y_453_);
v___x_462_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___x_461_, v___y_430_, v___y_431_, v___y_432_);
return v___x_462_;
}
else
{
lean_object* v___x_463_; 
lean_dec_ref(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
v___x_463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___y_452_, v___y_430_, v___y_431_, v___y_432_);
return v___x_463_;
}
}
}
v___jp_464_:
{
if (v___y_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
lean_dec_ref(v___y_465_);
v___x_471_ = l_Lean_Expr_forallE___override(v___y_468_, v___y_466_, v___y_467_, v___y_469_);
v___x_472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___x_471_, v___y_430_, v___y_431_, v___y_432_);
return v___x_472_;
}
else
{
uint8_t v___x_473_; 
v___x_473_ = l_Lean_instBEqBinderInfo_beq(v___y_469_, v___y_469_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec_ref(v___y_465_);
v___x_474_ = l_Lean_Expr_forallE___override(v___y_468_, v___y_466_, v___y_467_, v___y_469_);
v___x_475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___x_474_, v___y_430_, v___y_431_, v___y_432_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; 
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec_ref(v___y_466_);
v___x_476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_427_, v_post_429_, v___y_465_, v___y_430_, v___y_431_, v___y_432_);
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_576_, lean_object* v_e_577_, lean_object* v_post_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(v_pre_576_, v_e_577_, v_post_578_, v___y_579_, v___y_580_, v___y_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(lean_object* v_pre_584_, lean_object* v_post_585_, lean_object* v_e_586_, lean_object* v_a_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_inc(v_a_587_);
v___x_591_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_591_, 0, lean_box(0));
lean_closure_set(v___x_591_, 1, lean_box(0));
lean_closure_set(v___x_591_, 2, v_a_587_);
v___x_592_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_box(0), v___x_591_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_623_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_623_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_623_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_623_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; 
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_a_593_, v_e_586_);
lean_dec(v_a_593_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___f_598_; lean_object* v___x_599_; 
lean_del_object(v___x_595_);
lean_inc_ref(v_e_586_);
v___f_598_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed), 7, 3);
lean_closure_set(v___f_598_, 0, v_pre_584_);
lean_closure_set(v___f_598_, 1, v_e_586_);
lean_closure_set(v___f_598_, 2, v_post_585_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
lean_inc(v_a_587_);
v___x_599_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v___f_598_, v_a_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___f_601_; lean_object* v___x_602_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref(v___x_599_);
lean_inc(v_a_600_);
v___f_601_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_601_, 0, v_a_587_);
lean_closure_set(v___f_601_, 1, v_e_586_);
lean_closure_set(v___f_601_, 2, v_a_600_);
v___x_602_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_box(0), v___f_601_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_602_, 0);
lean_dec(v_unused_610_);
v___x_604_ = v___x_602_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_dec(v___x_602_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_a_600_);
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_600_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_a_600_);
v_a_611_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_602_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_602_);
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
else
{
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_e_586_);
return v___x_599_;
}
}
else
{
lean_object* v_val_619_; lean_object* v___x_621_; 
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_e_586_);
lean_dec_ref(v_post_585_);
lean_dec_ref(v_pre_584_);
v_val_619_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_val_619_);
lean_dec_ref(v___x_597_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_val_619_);
v___x_621_ = v___x_595_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_val_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_e_586_);
lean_dec_ref(v_post_585_);
lean_dec_ref(v_pre_584_);
v_a_624_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_592_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_592_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(lean_object* v_pre_632_, lean_object* v_post_633_, lean_object* v_e_634_, lean_object* v_a_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; 
lean_inc_ref(v_post_633_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc_ref(v_e_634_);
v___x_639_ = lean_apply_4(v_post_633_, v_e_634_, v___y_636_, v___y_637_, lean_box(0));
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_658_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_658_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_658_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_658_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
switch(lean_obj_tag(v_a_640_))
{
case 0:
{
lean_object* v_e_644_; lean_object* v___x_646_; 
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_e_634_);
lean_dec_ref(v_post_633_);
lean_dec_ref(v_pre_632_);
v_e_644_ = lean_ctor_get(v_a_640_, 0);
lean_inc_ref(v_e_644_);
lean_dec_ref(v_a_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_e_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_e_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
case 1:
{
lean_object* v_e_648_; lean_object* v___x_649_; 
lean_del_object(v___x_642_);
lean_dec_ref(v_e_634_);
v_e_648_ = lean_ctor_get(v_a_640_, 0);
lean_inc_ref(v_e_648_);
lean_dec_ref(v_a_640_);
v___x_649_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_632_, v_post_633_, v_e_648_, v_a_635_, v___y_636_, v___y_637_);
return v___x_649_;
}
default: 
{
lean_object* v_e_x3f_650_; 
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_post_633_);
lean_dec_ref(v_pre_632_);
v_e_x3f_650_ = lean_ctor_get(v_a_640_, 0);
lean_inc(v_e_x3f_650_);
lean_dec_ref(v_a_640_);
if (lean_obj_tag(v_e_x3f_650_) == 0)
{
lean_object* v___x_652_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_e_634_);
v___x_652_ = v___x_642_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_e_634_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
else
{
lean_object* v_val_654_; lean_object* v___x_656_; 
lean_dec_ref(v_e_634_);
v_val_654_ = lean_ctor_get(v_e_x3f_650_, 0);
lean_inc(v_val_654_);
lean_dec_ref(v_e_x3f_650_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v_val_654_);
v___x_656_ = v___x_642_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_val_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_e_634_);
lean_dec_ref(v_post_633_);
lean_dec_ref(v_pre_632_);
v_a_659_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_639_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_639_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_667_, lean_object* v_post_668_, lean_object* v_e_669_, lean_object* v_a_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_667_, v_post_668_, v_e_669_, v_a_670_, v___y_671_, v___y_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_675_, lean_object* v_post_676_, lean_object* v_sz_677_, lean_object* v_i_678_, lean_object* v_bs_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
size_t v_sz_boxed_684_; size_t v_i_boxed_685_; lean_object* v_res_686_; 
v_sz_boxed_684_ = lean_unbox_usize(v_sz_677_);
lean_dec(v_sz_677_);
v_i_boxed_685_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_675_, v_post_676_, v_sz_boxed_684_, v_i_boxed_685_, v_bs_679_, v___y_680_, v___y_681_, v___y_682_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_687_, lean_object* v_post_688_, lean_object* v_x_689_, lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_687_, v_post_688_, v_x_689_, v_x_690_, v_x_691_, v___y_692_, v___y_693_, v___y_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___boxed(lean_object* v_pre_697_, lean_object* v_post_698_, lean_object* v_e_699_, lean_object* v_a_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_697_, v_post_698_, v_e_699_, v_a_700_, v___y_701_, v___y_702_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_object* v_00_u03b1_705_, lean_object* v_x_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_apply_1(v_x_706_, lean_box(0));
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0___boxed(lean_object* v_00_u03b1_712_, lean_object* v_x_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(v_00_u03b1_712_, v_x_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_717_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_box(0);
v___x_719_ = lean_unsigned_to_nat(16u);
v___x_720_ = lean_mk_array(v___x_719_, v___x_718_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0);
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___x_721_);
return v___x_723_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1);
v___x_725_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_725_, 0, lean_box(0));
lean_closure_set(v___x_725_, 1, lean_box(0));
lean_closure_set(v___x_725_, 2, v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(lean_object* v_input_726_, lean_object* v_pre_727_, lean_object* v_post_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_a_734_; lean_object* v___x_735_; 
v___x_732_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2);
v___x_733_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_box(0), v___x_732_, v___y_729_, v___y_730_);
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref(v___x_733_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v_a_734_);
v___x_735_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_727_, v_post_728_, v_input_726_, v_a_734_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref(v___x_735_);
v___x_737_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_737_, 0, lean_box(0));
lean_closure_set(v___x_737_, 1, lean_box(0));
lean_closure_set(v___x_737_, 2, v_a_734_);
v___x_738_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_box(0), v___x_737_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; 
v_unused_746_ = lean_ctor_get(v___x_738_, 0);
lean_dec(v_unused_746_);
v___x_740_ = v___x_738_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_dec(v___x_738_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v_a_736_);
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_736_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_dec(v_a_734_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___boxed(lean_object* v_input_747_, lean_object* v_pre_748_, lean_object* v_post_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(v_input_747_, v_pre_748_, v_post_749_, v___y_750_, v___y_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand(lean_object* v_e_755_, lean_object* v_p_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___f_760_; lean_object* v___f_761_; lean_object* v___x_762_; 
v___f_760_ = lean_alloc_closure((void*)(l_Lean_Meta_deltaExpand___lam__0___boxed), 5, 1);
lean_closure_set(v___f_760_, 0, v_p_756_);
v___f_761_ = ((lean_object*)(l_Lean_Meta_deltaExpand___closed__0));
v___x_762_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(v_e_755_, v___f_760_, v___f_761_, v_a_757_, v_a_758_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___boxed(lean_object* v_e_763_, lean_object* v_p_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Meta_deltaExpand(v_e_763_, v_p_764_, v_a_765_, v_a_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_769_, lean_object* v_m_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_m_770_, v_a_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_773_, lean_object* v_m_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(v_00_u03b2_773_, v_m_774_, v_a_775_);
lean_dec_ref(v_a_775_);
lean_dec_ref(v_m_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_777_, lean_object* v_ref_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_778_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_783_, lean_object* v_ref_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_783_, v_ref_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_789_, lean_object* v_x_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_790_, v___y_791_, v___y_792_, v___y_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_796_, lean_object* v_x_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(v_00_u03b1_796_, v_x_797_, v___y_798_, v___y_799_, v___y_800_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_803_, lean_object* v_m_804_, lean_object* v_a_805_, lean_object* v_b_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v_m_804_, v_a_805_, v_b_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_808_, lean_object* v_a_809_, lean_object* v_x_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_809_, v_x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_812_, lean_object* v_a_813_, lean_object* v_x_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_812_, v_a_813_, v_x_814_);
lean_dec(v_x_814_);
lean_dec_ref(v_a_813_);
return v_res_815_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_816_, lean_object* v_a_817_, lean_object* v_x_818_){
_start:
{
uint8_t v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg(v_a_817_, v_x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_820_, lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_820_, v_a_821_, v_x_822_);
lean_dec(v_x_822_);
lean_dec_ref(v_a_821_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_825_, lean_object* v_data_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_data_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_828_, lean_object* v_a_829_, lean_object* v_b_830_, lean_object* v_x_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_a_829_, v_b_830_, v_x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_833_, lean_object* v_i_834_, lean_object* v_source_835_, lean_object* v_target_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_834_, v_source_835_, v_target_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_839_, v_x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(lean_object* v_mvarId_842_, lean_object* v_x_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_842_, v_x_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
v_a_858_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_849_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_849_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg___boxed(lean_object* v_mvarId_866_, lean_object* v_x_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_866_, v_x_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(lean_object* v_00_u03b1_874_, lean_object* v_mvarId_875_, lean_object* v_x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_875_, v_x_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___boxed(lean_object* v_00_u03b1_883_, lean_object* v_mvarId_884_, lean_object* v_x_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(v_00_u03b1_883_, v_mvarId_884_, v_x_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lam__0(lean_object* v_mvarId_892_, lean_object* v___x_893_, lean_object* v_p_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; 
lean_inc(v_mvarId_892_);
v___x_900_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_892_, v___x_893_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___x_901_; 
lean_dec_ref(v___x_900_);
lean_inc(v_mvarId_892_);
v___x_901_ = l_Lean_MVarId_getType(v_mvarId_892_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_903_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref(v___x_901_);
lean_inc(v___y_898_);
lean_inc_ref(v___y_897_);
v___x_903_ = l_Lean_Meta_deltaExpand(v_a_902_, v_p_894_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; uint8_t v___x_905_; lean_object* v___x_906_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref(v___x_903_);
v___x_905_ = 0;
v___x_906_ = l_Lean_MVarId_change(v_mvarId_892_, v_a_904_, v___x_905_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_906_;
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v_mvarId_892_);
v_a_907_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_903_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_903_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_p_894_);
lean_dec(v_mvarId_892_);
v_a_915_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_901_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_901_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_p_894_);
lean_dec(v_mvarId_892_);
v_a_923_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_900_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_900_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lam__0___boxed(lean_object* v_mvarId_931_, lean_object* v___x_932_, lean_object* v_p_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_MVarId_deltaTarget___lam__0(v_mvarId_931_, v___x_932_, v_p_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget(lean_object* v_mvarId_943_, lean_object* v_p_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; lean_object* v___f_951_; lean_object* v___x_952_; 
v___x_950_ = ((lean_object*)(l_Lean_MVarId_deltaTarget___closed__1));
lean_inc(v_mvarId_943_);
v___f_951_ = lean_alloc_closure((void*)(l_Lean_MVarId_deltaTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_951_, 0, v_mvarId_943_);
lean_closure_set(v___f_951_, 1, v___x_950_);
lean_closure_set(v___f_951_, 2, v_p_944_);
v___x_952_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_943_, v___f_951_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___boxed(lean_object* v_mvarId_953_, lean_object* v_p_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_MVarId_deltaTarget(v_mvarId_953_, v_p_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lam__0(lean_object* v_mvarId_961_, lean_object* v___x_962_, lean_object* v_fvarId_963_, lean_object* v_p_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; 
lean_inc(v_mvarId_961_);
v___x_970_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_961_, v___x_962_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v___x_971_; 
lean_dec_ref(v___x_970_);
lean_inc_ref(v___y_965_);
lean_inc(v_fvarId_963_);
v___x_971_ = l_Lean_FVarId_getType___redArg(v_fvarId_963_, v___y_965_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref(v___x_971_);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
v___x_973_ = l_Lean_Meta_deltaExpand(v_a_972_, v_p_964_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; uint8_t v___x_975_; lean_object* v___x_976_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref(v___x_973_);
v___x_975_ = 0;
v___x_976_ = l_Lean_MVarId_changeLocalDecl(v_mvarId_961_, v_fvarId_963_, v_a_974_, v___x_975_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_976_;
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v_fvarId_963_);
lean_dec(v_mvarId_961_);
v_a_977_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_973_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_973_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec_ref(v_p_964_);
lean_dec(v_fvarId_963_);
lean_dec(v_mvarId_961_);
v_a_985_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_971_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_971_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec_ref(v_p_964_);
lean_dec(v_fvarId_963_);
lean_dec(v_mvarId_961_);
v_a_993_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_970_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_970_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lam__0___boxed(lean_object* v_mvarId_1001_, lean_object* v___x_1002_, lean_object* v_fvarId_1003_, lean_object* v_p_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_MVarId_deltaLocalDecl___lam__0(v_mvarId_1001_, v___x_1002_, v_fvarId_1003_, v_p_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl(lean_object* v_mvarId_1011_, lean_object* v_fvarId_1012_, lean_object* v_p_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___x_1021_; 
v___x_1019_ = ((lean_object*)(l_Lean_MVarId_deltaTarget___closed__1));
lean_inc(v_mvarId_1011_);
v___f_1020_ = lean_alloc_closure((void*)(l_Lean_MVarId_deltaLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1020_, 0, v_mvarId_1011_);
lean_closure_set(v___f_1020_, 1, v___x_1019_);
lean_closure_set(v___f_1020_, 2, v_fvarId_1012_);
lean_closure_set(v___f_1020_, 3, v_p_1013_);
v___x_1021_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_1011_, v___f_1020_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___boxed(lean_object* v_mvarId_1022_, lean_object* v_fvarId_1023_, lean_object* v_p_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_MVarId_deltaLocalDecl(v_mvarId_1022_, v_fvarId_1023_, v_p_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
return v_res_1030_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Delta(builtin);
}
#ifdef __cplusplus
}
#endif
