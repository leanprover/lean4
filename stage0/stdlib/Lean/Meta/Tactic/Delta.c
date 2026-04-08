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
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f(lean_object* v_e_1_, lean_object* v_p_2_, uint8_t v_allowOpaque_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Expr_getAppFn(v_e_1_);
if (lean_obj_tag(v___x_10_) == 4)
{
lean_object* v_declName_11_; lean_object* v_us_12_; lean_object* v___x_13_; lean_object* v_env_17_; uint8_t v___x_18_; lean_object* v___x_19_; 
v_declName_11_ = lean_ctor_get(v___x_10_, 0);
lean_inc(v_declName_11_);
v_us_12_ = lean_ctor_get(v___x_10_, 1);
lean_inc(v_us_12_);
lean_dec_ref(v___x_10_);
v___x_13_ = lean_st_ref_get(v_a_5_);
v_env_17_ = lean_ctor_get(v___x_13_, 0);
lean_inc_ref(v_env_17_);
lean_dec(v___x_13_);
v___x_18_ = 0;
v___x_19_ = l_Lean_Environment_find_x3f(v_env_17_, v_declName_11_, v___x_18_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_dec(v_us_12_);
lean_dec_ref(v_p_2_);
lean_dec_ref(v_e_1_);
goto v___jp_7_;
}
else
{
lean_object* v_val_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_56_; 
v_val_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_56_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_56_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_val_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_56_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_24_ = l_Lean_ConstantInfo_name(v_val_20_);
v___x_25_ = lean_apply_1(v_p_2_, v___x_24_);
v___x_26_ = lean_unbox(v___x_25_);
if (v___x_26_ == 0)
{
lean_del_object(v___x_22_);
lean_dec(v_val_20_);
lean_dec(v_us_12_);
lean_dec_ref(v_e_1_);
goto v___jp_14_;
}
else
{
uint8_t v___x_27_; 
v___x_27_ = l_Lean_ConstantInfo_hasValue(v_val_20_, v_allowOpaque_3_);
if (v___x_27_ == 0)
{
lean_del_object(v___x_22_);
lean_dec(v_val_20_);
lean_dec(v_us_12_);
lean_dec_ref(v_e_1_);
goto v___jp_14_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_28_ = l_Lean_ConstantInfo_levelParams(v_val_20_);
v___x_29_ = l_List_lengthTR___redArg(v___x_28_);
lean_dec(v___x_28_);
v___x_30_ = l_List_lengthTR___redArg(v_us_12_);
v___x_31_ = lean_nat_dec_eq(v___x_29_, v___x_30_);
lean_dec(v___x_30_);
lean_dec(v___x_29_);
if (v___x_31_ == 0)
{
lean_del_object(v___x_22_);
lean_dec(v_val_20_);
lean_dec(v_us_12_);
lean_dec_ref(v_e_1_);
goto v___jp_14_;
}
else
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Core_instantiateValueLevelParams(v_val_20_, v_us_12_, v_allowOpaque_3_, v_a_4_, v_a_5_);
lean_dec(v_val_20_);
if (lean_obj_tag(v___x_32_) == 0)
{
lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_47_; 
v_a_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_47_ == 0)
{
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_47_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_47_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_37_ = l_Lean_Expr_getAppNumArgs(v_e_1_);
v___x_38_ = lean_mk_empty_array_with_capacity(v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_1_, v___x_38_);
v___x_40_ = l_Lean_Expr_betaRev(v_a_33_, v___x_39_, v___x_27_, v___x_18_);
lean_dec_ref(v___x_39_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_40_);
v___x_42_ = v___x_22_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_40_);
v___x_42_ = v_reuseFailAlloc_46_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_44_; 
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_42_);
v___x_44_ = v___x_35_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_42_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
else
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
lean_del_object(v___x_22_);
lean_dec_ref(v_e_1_);
v_a_48_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_32_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_32_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
}
}
}
}
v___jp_14_:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_box(0);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
else
{
lean_dec_ref(v___x_10_);
lean_dec_ref(v_p_2_);
lean_dec_ref(v_e_1_);
goto v___jp_7_;
}
v___jp_7_:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_box(0);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f___boxed(lean_object* v_e_57_, lean_object* v_p_58_, lean_object* v_allowOpaque_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
uint8_t v_allowOpaque_boxed_63_; lean_object* v_res_64_; 
v_allowOpaque_boxed_63_ = lean_unbox(v_allowOpaque_59_);
v_res_64_ = l_Lean_Meta_delta_x3f(v_e_57_, v_p_58_, v_allowOpaque_boxed_63_, v_a_60_, v_a_61_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__0(lean_object* v_p_65_, uint8_t v_allowOpaque_66_, lean_object* v_e_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_delta_x3f(v_e_67_, v_p_65_, v_allowOpaque_66_, v___y_68_, v___y_69_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_91_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_91_ == 0)
{
v___x_74_ = v___x_71_;
v_isShared_75_ = v_isSharedCheck_91_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_91_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
if (lean_obj_tag(v_a_72_) == 0)
{
lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_76_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_76_, 0, v_a_72_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_76_);
v___x_78_ = v___x_74_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
else
{
lean_object* v_val_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_90_; 
v_val_80_ = lean_ctor_get(v_a_72_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_a_72_);
if (v_isSharedCheck_90_ == 0)
{
v___x_82_ = v_a_72_;
v_isShared_83_ = v_isSharedCheck_90_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_val_80_);
lean_dec(v_a_72_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_90_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_val_80_);
v___x_85_ = v_reuseFailAlloc_89_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_87_; 
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_85_);
v___x_87_ = v___x_74_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 1, 0);
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
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
v_a_92_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_71_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_71_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__0___boxed(lean_object* v_p_100_, lean_object* v_allowOpaque_101_, lean_object* v_e_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
uint8_t v_allowOpaque_boxed_106_; lean_object* v_res_107_; 
v_allowOpaque_boxed_106_ = lean_unbox(v_allowOpaque_101_);
v_res_107_ = l_Lean_Meta_deltaExpand___lam__0(v_p_100_, v_allowOpaque_boxed_106_, v_e_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__1(lean_object* v_e_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v_e_108_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lam__1___boxed(lean_object* v_e_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Meta_deltaExpand___lam__1(v_e_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_119_, lean_object* v_x_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_apply_1(v_x_120_, lean_box(0));
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_126_, lean_object* v_x_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(v_00_u03b1_126_, v_x_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_132_, lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_box(0);
return v___x_134_;
}
else
{
lean_object* v_key_135_; lean_object* v_value_136_; lean_object* v_tail_137_; uint8_t v___x_138_; 
v_key_135_ = lean_ctor_get(v_x_133_, 0);
v_value_136_ = lean_ctor_get(v_x_133_, 1);
v_tail_137_ = lean_ctor_get(v_x_133_, 2);
v___x_138_ = l_Lean_ExprStructEq_beq(v_key_135_, v_a_132_);
if (v___x_138_ == 0)
{
v_x_133_ = v_tail_137_;
goto _start;
}
else
{
lean_object* v___x_140_; 
lean_inc(v_value_136_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_value_136_);
return v___x_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_141_, lean_object* v_x_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_141_, v_x_142_);
lean_dec(v_x_142_);
lean_dec_ref(v_a_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(lean_object* v_m_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_buckets_146_; lean_object* v___x_147_; uint64_t v___x_148_; uint64_t v___x_149_; uint64_t v___x_150_; uint64_t v_fold_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; size_t v___x_158_; size_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_buckets_146_ = lean_ctor_get(v_m_144_, 1);
v___x_147_ = lean_array_get_size(v_buckets_146_);
v___x_148_ = l_Lean_ExprStructEq_hash(v_a_145_);
v___x_149_ = 32ULL;
v___x_150_ = lean_uint64_shift_right(v___x_148_, v___x_149_);
v_fold_151_ = lean_uint64_xor(v___x_148_, v___x_150_);
v___x_152_ = 16ULL;
v___x_153_ = lean_uint64_shift_right(v_fold_151_, v___x_152_);
v___x_154_ = lean_uint64_xor(v_fold_151_, v___x_153_);
v___x_155_ = lean_uint64_to_usize(v___x_154_);
v___x_156_ = lean_usize_of_nat(v___x_147_);
v___x_157_ = ((size_t)1ULL);
v___x_158_ = lean_usize_sub(v___x_156_, v___x_157_);
v___x_159_ = lean_usize_land(v___x_155_, v___x_158_);
v___x_160_ = lean_array_uget_borrowed(v_buckets_146_, v___x_159_);
v___x_161_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_145_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_m_162_, v_a_163_);
lean_dec_ref(v_a_163_);
lean_dec_ref(v_m_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_165_, lean_object* v_b_166_, lean_object* v_x_167_){
_start:
{
if (lean_obj_tag(v_x_167_) == 0)
{
lean_dec(v_b_166_);
lean_dec_ref(v_a_165_);
return v_x_167_;
}
else
{
lean_object* v_key_168_; lean_object* v_value_169_; lean_object* v_tail_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_182_; 
v_key_168_ = lean_ctor_get(v_x_167_, 0);
v_value_169_ = lean_ctor_get(v_x_167_, 1);
v_tail_170_ = lean_ctor_get(v_x_167_, 2);
v_isSharedCheck_182_ = !lean_is_exclusive(v_x_167_);
if (v_isSharedCheck_182_ == 0)
{
v___x_172_ = v_x_167_;
v_isShared_173_ = v_isSharedCheck_182_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_tail_170_);
lean_inc(v_value_169_);
lean_inc(v_key_168_);
lean_dec(v_x_167_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_182_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
uint8_t v___x_174_; 
v___x_174_ = l_Lean_ExprStructEq_beq(v_key_168_, v_a_165_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_a_165_, v_b_166_, v_tail_170_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 2, v___x_175_);
v___x_177_ = v___x_172_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_key_168_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_value_169_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
else
{
lean_object* v___x_180_; 
lean_dec(v_value_169_);
lean_dec(v_key_168_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v_b_166_);
lean_ctor_set(v___x_172_, 0, v_a_165_);
v___x_180_ = v___x_172_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_165_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_b_166_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v_tail_170_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
return v_x_183_;
}
else
{
lean_object* v_key_185_; lean_object* v_value_186_; lean_object* v_tail_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_210_; 
v_key_185_ = lean_ctor_get(v_x_184_, 0);
v_value_186_ = lean_ctor_get(v_x_184_, 1);
v_tail_187_ = lean_ctor_get(v_x_184_, 2);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_210_ == 0)
{
v___x_189_ = v_x_184_;
v_isShared_190_ = v_isSharedCheck_210_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_tail_187_);
lean_inc(v_value_186_);
lean_inc(v_key_185_);
lean_dec(v_x_184_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_210_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; uint64_t v___x_192_; uint64_t v___x_193_; uint64_t v___x_194_; uint64_t v_fold_195_; uint64_t v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_191_ = lean_array_get_size(v_x_183_);
v___x_192_ = l_Lean_ExprStructEq_hash(v_key_185_);
v___x_193_ = 32ULL;
v___x_194_ = lean_uint64_shift_right(v___x_192_, v___x_193_);
v_fold_195_ = lean_uint64_xor(v___x_192_, v___x_194_);
v___x_196_ = 16ULL;
v___x_197_ = lean_uint64_shift_right(v_fold_195_, v___x_196_);
v___x_198_ = lean_uint64_xor(v_fold_195_, v___x_197_);
v___x_199_ = lean_uint64_to_usize(v___x_198_);
v___x_200_ = lean_usize_of_nat(v___x_191_);
v___x_201_ = ((size_t)1ULL);
v___x_202_ = lean_usize_sub(v___x_200_, v___x_201_);
v___x_203_ = lean_usize_land(v___x_199_, v___x_202_);
v___x_204_ = lean_array_uget_borrowed(v_x_183_, v___x_203_);
lean_inc(v___x_204_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 2, v___x_204_);
v___x_206_ = v___x_189_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_key_185_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_value_186_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v___x_204_);
v___x_206_ = v_reuseFailAlloc_209_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; 
v___x_207_ = lean_array_uset(v_x_183_, v___x_203_, v___x_206_);
v_x_183_ = v___x_207_;
v_x_184_ = v_tail_187_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_211_, lean_object* v_source_212_, lean_object* v_target_213_){
_start:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_array_get_size(v_source_212_);
v___x_215_ = lean_nat_dec_lt(v_i_211_, v___x_214_);
if (v___x_215_ == 0)
{
lean_dec_ref(v_source_212_);
lean_dec(v_i_211_);
return v_target_213_;
}
else
{
lean_object* v_es_216_; lean_object* v___x_217_; lean_object* v_source_218_; lean_object* v_target_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_es_216_ = lean_array_fget(v_source_212_, v_i_211_);
v___x_217_ = lean_box(0);
v_source_218_ = lean_array_fset(v_source_212_, v_i_211_, v___x_217_);
v_target_219_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_213_, v_es_216_);
v___x_220_ = lean_unsigned_to_nat(1u);
v___x_221_ = lean_nat_add(v_i_211_, v___x_220_);
lean_dec(v_i_211_);
v_i_211_ = v___x_221_;
v_source_212_ = v_source_218_;
v_target_213_ = v_target_219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_nbuckets_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_224_ = lean_array_get_size(v_data_223_);
v___x_225_ = lean_unsigned_to_nat(2u);
v_nbuckets_226_ = lean_nat_mul(v___x_224_, v___x_225_);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_box(0);
v___x_229_ = lean_mk_array(v_nbuckets_226_, v___x_228_);
v___x_230_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_227_, v_data_223_, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_231_, lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
uint8_t v___x_233_; 
v___x_233_ = 0;
return v___x_233_;
}
else
{
lean_object* v_key_234_; lean_object* v_tail_235_; uint8_t v___x_236_; 
v_key_234_ = lean_ctor_get(v_x_232_, 0);
v_tail_235_ = lean_ctor_get(v_x_232_, 2);
v___x_236_ = l_Lean_ExprStructEq_beq(v_key_234_, v_a_231_);
if (v___x_236_ == 0)
{
v_x_232_ = v_tail_235_;
goto _start;
}
else
{
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_238_, lean_object* v_x_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg(v_a_238_, v_x_239_);
lean_dec(v_x_239_);
lean_dec_ref(v_a_238_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(lean_object* v_m_242_, lean_object* v_a_243_, lean_object* v_b_244_){
_start:
{
lean_object* v_size_245_; lean_object* v_buckets_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_289_; 
v_size_245_ = lean_ctor_get(v_m_242_, 0);
v_buckets_246_ = lean_ctor_get(v_m_242_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v_m_242_);
if (v_isSharedCheck_289_ == 0)
{
v___x_248_ = v_m_242_;
v_isShared_249_ = v_isSharedCheck_289_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_buckets_246_);
lean_inc(v_size_245_);
lean_dec(v_m_242_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_289_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v_fold_254_; uint64_t v___x_255_; uint64_t v___x_256_; uint64_t v___x_257_; size_t v___x_258_; size_t v___x_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; lean_object* v_bkt_263_; uint8_t v___x_264_; 
v___x_250_ = lean_array_get_size(v_buckets_246_);
v___x_251_ = l_Lean_ExprStructEq_hash(v_a_243_);
v___x_252_ = 32ULL;
v___x_253_ = lean_uint64_shift_right(v___x_251_, v___x_252_);
v_fold_254_ = lean_uint64_xor(v___x_251_, v___x_253_);
v___x_255_ = 16ULL;
v___x_256_ = lean_uint64_shift_right(v_fold_254_, v___x_255_);
v___x_257_ = lean_uint64_xor(v_fold_254_, v___x_256_);
v___x_258_ = lean_uint64_to_usize(v___x_257_);
v___x_259_ = lean_usize_of_nat(v___x_250_);
v___x_260_ = ((size_t)1ULL);
v___x_261_ = lean_usize_sub(v___x_259_, v___x_260_);
v___x_262_ = lean_usize_land(v___x_258_, v___x_261_);
v_bkt_263_ = lean_array_uget_borrowed(v_buckets_246_, v___x_262_);
v___x_264_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg(v_a_243_, v_bkt_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v_size_x27_266_; lean_object* v___x_267_; lean_object* v_buckets_x27_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v_size_x27_266_ = lean_nat_add(v_size_245_, v___x_265_);
lean_dec(v_size_245_);
lean_inc(v_bkt_263_);
v___x_267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_267_, 0, v_a_243_);
lean_ctor_set(v___x_267_, 1, v_b_244_);
lean_ctor_set(v___x_267_, 2, v_bkt_263_);
v_buckets_x27_268_ = lean_array_uset(v_buckets_246_, v___x_262_, v___x_267_);
v___x_269_ = lean_unsigned_to_nat(4u);
v___x_270_ = lean_nat_mul(v_size_x27_266_, v___x_269_);
v___x_271_ = lean_unsigned_to_nat(3u);
v___x_272_ = lean_nat_div(v___x_270_, v___x_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_array_get_size(v_buckets_x27_268_);
v___x_274_ = lean_nat_dec_le(v___x_272_, v___x_273_);
lean_dec(v___x_272_);
if (v___x_274_ == 0)
{
lean_object* v_val_275_; lean_object* v___x_277_; 
v_val_275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_268_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v_val_275_);
lean_ctor_set(v___x_248_, 0, v_size_x27_266_);
v___x_277_ = v___x_248_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_size_x27_266_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_val_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
else
{
lean_object* v___x_280_; 
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v_buckets_x27_268_);
lean_ctor_set(v___x_248_, 0, v_size_x27_266_);
v___x_280_ = v___x_248_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_size_x27_266_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_buckets_x27_268_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v___x_282_; lean_object* v_buckets_x27_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
lean_inc(v_bkt_263_);
v___x_282_ = lean_box(0);
v_buckets_x27_283_ = lean_array_uset(v_buckets_246_, v___x_262_, v___x_282_);
v___x_284_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_a_243_, v_b_244_, v_bkt_263_);
v___x_285_ = lean_array_uset(v_buckets_x27_283_, v___x_262_, v___x_284_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v___x_285_);
v___x_287_ = v___x_248_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_size_245_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(lean_object* v_a_290_, lean_object* v_e_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_294_ = lean_st_ref_take(v_a_290_);
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v___x_294_, v_e_291_, v_a_292_);
v___x_296_ = lean_st_ref_set(v_a_290_, v___x_295_);
v___x_297_ = lean_box(0);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed(lean_object* v_a_298_, lean_object* v_e_299_, lean_object* v_a_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(v_a_298_, v_e_299_, v_a_300_);
lean_dec(v_a_298_);
return v_res_302_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = l_Lean_maxRecDepthErrorMessage;
v___x_309_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_311_ = l_Lean_MessageData_ofFormat(v___x_310_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_313_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_314_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_315_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v_ref_315_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(lean_object* v_x_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___y_329_; lean_object* v_fileName_338_; lean_object* v_fileMap_339_; lean_object* v_options_340_; lean_object* v_currRecDepth_341_; lean_object* v_maxRecDepth_342_; lean_object* v_ref_343_; lean_object* v_currNamespace_344_; lean_object* v_openDecls_345_; lean_object* v_initHeartbeats_346_; lean_object* v_maxHeartbeats_347_; lean_object* v_quotContext_348_; lean_object* v_currMacroScope_349_; uint8_t v_diag_350_; lean_object* v_cancelTk_x3f_351_; uint8_t v_suppressElabErrors_352_; lean_object* v_inheritedTraceOptions_353_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_fileName_338_ = lean_ctor_get(v___y_325_, 0);
v_fileMap_339_ = lean_ctor_get(v___y_325_, 1);
v_options_340_ = lean_ctor_get(v___y_325_, 2);
v_currRecDepth_341_ = lean_ctor_get(v___y_325_, 3);
v_maxRecDepth_342_ = lean_ctor_get(v___y_325_, 4);
v_ref_343_ = lean_ctor_get(v___y_325_, 5);
v_currNamespace_344_ = lean_ctor_get(v___y_325_, 6);
v_openDecls_345_ = lean_ctor_get(v___y_325_, 7);
v_initHeartbeats_346_ = lean_ctor_get(v___y_325_, 8);
v_maxHeartbeats_347_ = lean_ctor_get(v___y_325_, 9);
v_quotContext_348_ = lean_ctor_get(v___y_325_, 10);
v_currMacroScope_349_ = lean_ctor_get(v___y_325_, 11);
v_diag_350_ = lean_ctor_get_uint8(v___y_325_, sizeof(void*)*14);
v_cancelTk_x3f_351_ = lean_ctor_get(v___y_325_, 12);
v_suppressElabErrors_352_ = lean_ctor_get_uint8(v___y_325_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_353_ = lean_ctor_get(v___y_325_, 13);
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_nat_dec_eq(v_maxRecDepth_342_, v___x_359_);
if (v___x_360_ == 0)
{
uint8_t v___x_361_; 
v___x_361_ = lean_nat_dec_eq(v_currRecDepth_341_, v_maxRecDepth_342_);
if (v___x_361_ == 0)
{
goto v___jp_354_;
}
else
{
lean_object* v___x_362_; 
lean_dec_ref(v_x_323_);
lean_inc(v_ref_343_);
v___x_362_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_343_);
v___y_329_ = v___x_362_;
goto v___jp_328_;
}
}
else
{
goto v___jp_354_;
}
v___jp_328_:
{
if (lean_obj_tag(v___y_329_) == 0)
{
return v___y_329_;
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_a_330_ = lean_ctor_get(v___y_329_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___y_329_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___y_329_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___y_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
v___jp_354_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_currRecDepth_341_, v___x_355_);
lean_inc_ref(v_inheritedTraceOptions_353_);
lean_inc(v_cancelTk_x3f_351_);
lean_inc(v_currMacroScope_349_);
lean_inc(v_quotContext_348_);
lean_inc(v_maxHeartbeats_347_);
lean_inc(v_initHeartbeats_346_);
lean_inc(v_openDecls_345_);
lean_inc(v_currNamespace_344_);
lean_inc(v_ref_343_);
lean_inc(v_maxRecDepth_342_);
lean_inc_ref(v_options_340_);
lean_inc_ref(v_fileMap_339_);
lean_inc_ref(v_fileName_338_);
v___x_357_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_357_, 0, v_fileName_338_);
lean_ctor_set(v___x_357_, 1, v_fileMap_339_);
lean_ctor_set(v___x_357_, 2, v_options_340_);
lean_ctor_set(v___x_357_, 3, v___x_356_);
lean_ctor_set(v___x_357_, 4, v_maxRecDepth_342_);
lean_ctor_set(v___x_357_, 5, v_ref_343_);
lean_ctor_set(v___x_357_, 6, v_currNamespace_344_);
lean_ctor_set(v___x_357_, 7, v_openDecls_345_);
lean_ctor_set(v___x_357_, 8, v_initHeartbeats_346_);
lean_ctor_set(v___x_357_, 9, v_maxHeartbeats_347_);
lean_ctor_set(v___x_357_, 10, v_quotContext_348_);
lean_ctor_set(v___x_357_, 11, v_currMacroScope_349_);
lean_ctor_set(v___x_357_, 12, v_cancelTk_x3f_351_);
lean_ctor_set(v___x_357_, 13, v_inheritedTraceOptions_353_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*14, v_diag_350_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*14 + 1, v_suppressElabErrors_352_);
lean_inc(v___y_326_);
lean_inc(v___y_324_);
v___x_358_ = lean_apply_4(v_x_323_, v___y_324_, v___x_357_, v___y_326_, lean_box(0));
v___y_329_ = v___x_358_;
goto v___jp_328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
return v_res_368_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_370_; lean_object* v_dummy_371_; 
v___x_370_ = lean_box(0);
v_dummy_371_ = l_Lean_Expr_sort___override(v___x_370_);
return v_dummy_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(lean_object* v_pre_372_, lean_object* v_post_373_, size_t v_sz_374_, size_t v_i_375_, lean_object* v_bs_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
uint8_t v___x_381_; 
v___x_381_ = lean_usize_dec_lt(v_i_375_, v_sz_374_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
lean_dec_ref(v_post_373_);
lean_dec_ref(v_pre_372_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_bs_376_);
return v___x_382_;
}
else
{
lean_object* v_v_383_; lean_object* v___x_384_; 
v_v_383_ = lean_array_uget_borrowed(v_bs_376_, v_i_375_);
lean_inc(v_v_383_);
lean_inc_ref(v_post_373_);
lean_inc_ref(v_pre_372_);
v___x_384_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_372_, v_post_373_, v_v_383_, v___y_377_, v___y_378_, v___y_379_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v_bs_x27_387_; size_t v___x_388_; size_t v___x_389_; lean_object* v___x_390_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref(v___x_384_);
v___x_386_ = lean_unsigned_to_nat(0u);
v_bs_x27_387_ = lean_array_uset(v_bs_376_, v_i_375_, v___x_386_);
v___x_388_ = ((size_t)1ULL);
v___x_389_ = lean_usize_add(v_i_375_, v___x_388_);
v___x_390_ = lean_array_uset(v_bs_x27_387_, v_i_375_, v_a_385_);
v_i_375_ = v___x_389_;
v_bs_376_ = v___x_390_;
goto _start;
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v_bs_376_);
lean_dec_ref(v_post_373_);
lean_dec_ref(v_pre_372_);
v_a_392_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_384_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_384_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(lean_object* v_pre_400_, lean_object* v_post_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
if (lean_obj_tag(v_x_402_) == 5)
{
lean_object* v_fn_409_; lean_object* v_arg_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_fn_409_ = lean_ctor_get(v_x_402_, 0);
lean_inc_ref(v_fn_409_);
v_arg_410_ = lean_ctor_get(v_x_402_, 1);
lean_inc_ref(v_arg_410_);
lean_dec_ref(v_x_402_);
v___x_411_ = lean_array_set(v_x_403_, v_x_404_, v_arg_410_);
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_nat_sub(v_x_404_, v___x_412_);
lean_dec(v_x_404_);
v_x_402_ = v_fn_409_;
v_x_403_ = v___x_411_;
v_x_404_ = v___x_413_;
goto _start;
}
else
{
lean_object* v___x_415_; 
lean_dec(v_x_404_);
lean_inc_ref(v_post_401_);
lean_inc_ref(v_pre_400_);
v___x_415_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_400_, v_post_401_, v_x_402_, v___y_405_, v___y_406_, v___y_407_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; size_t v_sz_417_; size_t v___x_418_; lean_object* v___x_419_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref(v___x_415_);
v_sz_417_ = lean_array_size(v_x_403_);
v___x_418_ = ((size_t)0ULL);
lean_inc_ref(v_post_401_);
lean_inc_ref(v_pre_400_);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_400_, v_post_401_, v_sz_417_, v___x_418_, v_x_403_, v___y_405_, v___y_406_, v___y_407_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref(v___x_419_);
v___x_421_ = l_Lean_mkAppN(v_a_416_, v_a_420_);
lean_dec(v_a_420_);
v___x_422_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_400_, v_post_401_, v___x_421_, v___y_405_, v___y_406_, v___y_407_);
return v___x_422_;
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec(v_a_416_);
lean_dec_ref(v_post_401_);
lean_dec_ref(v_pre_400_);
v_a_423_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_419_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_419_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_dec_ref(v_x_403_);
lean_dec_ref(v_post_401_);
lean_dec_ref(v_pre_400_);
return v___x_415_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(lean_object* v___x_431_, lean_object* v_pre_432_, lean_object* v_e_433_, lean_object* v_post_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
uint8_t v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; uint8_t v___y_447_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; uint8_t v___y_461_; uint8_t v___y_462_; uint8_t v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; uint8_t v___y_475_; lean_object* v___x_482_; 
v___x_482_ = l_Lean_Core_checkSystem(v___x_431_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v___x_482_);
lean_inc_ref(v_pre_432_);
lean_inc(v___y_437_);
lean_inc_ref(v___y_436_);
lean_inc_ref(v_e_433_);
v___x_483_ = lean_apply_4(v_pre_432_, v_e_433_, v___y_436_, v___y_437_, lean_box(0));
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_573_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_573_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_573_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_573_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___y_489_; 
switch(lean_obj_tag(v_a_484_))
{
case 0:
{
lean_object* v_e_563_; lean_object* v___x_565_; 
lean_dec_ref(v_post_434_);
lean_dec_ref(v_e_433_);
lean_dec_ref(v_pre_432_);
v_e_563_ = lean_ctor_get(v_a_484_, 0);
lean_inc_ref(v_e_563_);
lean_dec_ref(v_a_484_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v_e_563_);
v___x_565_ = v___x_486_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_e_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
case 1:
{
lean_object* v_e_567_; lean_object* v___x_568_; 
lean_del_object(v___x_486_);
lean_dec_ref(v_e_433_);
v_e_567_ = lean_ctor_get(v_a_484_, 0);
lean_inc_ref(v_e_567_);
lean_dec_ref(v_a_484_);
lean_inc_ref(v_post_434_);
lean_inc_ref(v_pre_432_);
v___x_568_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_432_, v_post_434_, v_e_567_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref(v___x_568_);
v___x_570_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v_a_569_, v___y_435_, v___y_436_, v___y_437_);
return v___x_570_;
}
else
{
lean_dec_ref(v_post_434_);
lean_dec_ref(v_pre_432_);
return v___x_568_;
}
}
default: 
{
lean_object* v_e_x3f_571_; 
lean_del_object(v___x_486_);
v_e_x3f_571_ = lean_ctor_get(v_a_484_, 0);
lean_inc(v_e_x3f_571_);
lean_dec_ref(v_a_484_);
if (lean_obj_tag(v_e_x3f_571_) == 0)
{
v___y_489_ = v_e_433_;
goto v___jp_488_;
}
else
{
lean_object* v_val_572_; 
lean_dec_ref(v_e_433_);
v_val_572_ = lean_ctor_get(v_e_x3f_571_, 0);
lean_inc(v_val_572_);
lean_dec_ref(v_e_x3f_571_);
v___y_489_ = v_val_572_;
goto v___jp_488_;
}
}
}
v___jp_488_:
{
switch(lean_obj_tag(v___y_489_))
{
case 7:
{
lean_object* v_binderName_490_; lean_object* v_binderType_491_; lean_object* v_body_492_; uint8_t v_binderInfo_493_; lean_object* v___x_494_; 
v_binderName_490_ = lean_ctor_get(v___y_489_, 0);
lean_inc(v_binderName_490_);
v_binderType_491_ = lean_ctor_get(v___y_489_, 1);
v_body_492_ = lean_ctor_get(v___y_489_, 2);
v_binderInfo_493_ = lean_ctor_get_uint8(v___y_489_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_491_);
lean_inc_ref(v_post_434_);
lean_inc_ref(v_pre_432_);
v___x_494_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_432_, v_post_434_, v_binderType_491_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_496_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref(v___x_494_);
lean_inc_ref(v_body_492_);
lean_inc_ref(v_post_434_);
lean_inc_ref(v_pre_432_);
v___x_496_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_432_, v_post_434_, v_body_492_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; size_t v___x_498_; size_t v___x_499_; uint8_t v___x_500_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref(v___x_496_);
v___x_498_ = lean_ptr_addr(v_binderType_491_);
v___x_499_ = lean_ptr_addr(v_a_495_);
v___x_500_ = lean_usize_dec_eq(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
v___y_470_ = v_binderInfo_493_;
v___y_471_ = v_a_497_;
v___y_472_ = v_a_495_;
v___y_473_ = v___y_489_;
v___y_474_ = v_binderName_490_;
v___y_475_ = v___x_500_;
goto v___jp_469_;
}
else
{
size_t v___x_501_; size_t v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_ptr_addr(v_body_492_);
v___x_502_ = lean_ptr_addr(v_a_497_);
v___x_503_ = lean_usize_dec_eq(v___x_501_, v___x_502_);
v___y_470_ = v_binderInfo_493_;
v___y_471_ = v_a_497_;
v___y_472_ = v_a_495_;
v___y_473_ = v___y_489_;
v___y_474_ = v_binderName_490_;
v___y_475_ = v___x_503_;
goto v___jp_469_;
}
}
else
{
lean_dec(v_a_495_);
lean_dec(v_binderName_490_);
lean_dec_ref(v___y_489_);
lean_dec_ref(v_post_434_);
lean_dec_ref(v_pre_432_);
return v___x_496_;
}
}
else
{
lean_dec_ref(v___y_489_);
lean_dec(v_binderName_490_);
lean_dec_ref(v_post_434_);
lean_dec_ref(v_pre_432_);
return v___x_494_;
}
}
case 6:
{
lean_object* v_binderName_504_; lean_object* v_binderType_505_; lean_object* v_body_506_; uint8_t v_binderInfo_507_; lean_object* v___x_508_; 
v_binderName_504_ = lean_ctor_get(v___y_489_, 0);
lean_inc(v_binderName_504_);
v_binderType_505_ = lean_ctor_get(v___y_489_, 1);
v_body_506_ = lean_ctor_get(v___y_489_, 2);
v_binderInfo_507_ = lean_ctor_get_uint8(v___y_489_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_505_);
lean_inc_ref(v_post_434_);
lean_inc_ref(v_pre_432_);
v___x_508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_432_, v_post_434_, v_binderType_505_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
lean_inc_ref(v_body_506_);
lean_inc_ref(v_post_434_);
lean_inc_ref(v_pre_432_);
v___x_510_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_432_, v_post_434_, v_body_506_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; size_t v___x_512_; size_t v___x_513_; uint8_t v___x_514_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = lean_ptr_addr(v_binderType_505_);
v___x_513_ = lean_ptr_addr(v_a_509_);
v___x_514_ = lean_usize_dec_eq(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
v___y_457_ = v_a_511_;
v___y_458_ = v_a_509_;
v___y_459_ = v___y_489_;
v___y_460_ = v_binderName_504_;
v___y_461_ = v_binderInfo_507_;
v___y_462_ = v___x_514_;
goto v___jp_456_;
}
else
{
size_t v___x_515_; size_t v___x_516_; uint8_t v___x_517_; 
v___x_515_ = lean_ptr_addr(v_body_506_);
v___x_516_ = lean_ptr_addr(v_a_511_);
v___x_517_ = lean_usize_dec_eq(v___x_515_, v___x_516_);
v___y_457_ = v_a_511_;
v___y_458_ = v_a_509_;
v___y_459_ = v___y_489_;
v___y_460_ = v_binderName_504_;
v___y_461_ = v_binderInfo_507_;
v___y_462_ = v___x_517_;
goto v___jp_456_;
}
}
else
{
lean_dec(v_a_509_);
lean_dec_ref(v___y_489_);
lean_dec(v_binderName_504_);
lean_dec_ref(v_post_434_);
lean_dec_ref(v_pre_432_);
return v___x_510_;
}
}
else
{
lean_dec_ref(v___y_489_);
lean_dec(v_binderName_504_);
lean_dec_ref(v_post_434_);
lean_dec_ref(v_pre_432_);
return v___x_508_;
}
}
case 8:
{
lean_object* v_declName_518_; lean_object* v_type_519_; lean_object* v_value_520_; lean_object* v_body_521_; uint8_t v_nondep_522_; lean_object* v___x_523_; 
v_declName_518_ = lean_ctor_get(v___y_489_, 0);
lean_inc(v_declName_518_);
v_type_519_ = lean_ctor_get(v___y_489_, 1);
v_value_520_ = lean_ctor_get(v___y_489_, 2);
v_body_521_ = lean_ctor_get(v___y_489_, 3);
lean_inc_ref(v_body_521_);
v_nondep_522_ = lean_ctor_get_uint8(v___y_489_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_519_);
lean_inc_ref(v_post_434_);
lean_inc_ref(v_pre_432_);
v___x_523_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_432_, v_post_434_, v_type_519_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref(v___x_523_);
lean_inc_ref(v_value_520_);
lean_inc_ref(v_post_434_);
lean_inc_ref(v_pre_432_);
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_432_, v_post_434_, v_value_520_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref(v___x_525_);
lean_inc_ref(v_body_521_);
lean_inc_ref(v_post_434_);
lean_inc_ref(v_pre_432_);
v___x_527_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_432_, v_post_434_, v_body_521_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; size_t v___x_529_; size_t v___x_530_; uint8_t v___x_531_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref(v___x_527_);
v___x_529_ = lean_ptr_addr(v_type_519_);
v___x_530_ = lean_ptr_addr(v_a_524_);
v___x_531_ = lean_usize_dec_eq(v___x_529_, v___x_530_);
if (v___x_531_ == 0)
{
v___y_440_ = v_nondep_522_;
v___y_441_ = v_body_521_;
v___y_442_ = v___y_489_;
v___y_443_ = v_a_528_;
v___y_444_ = v_a_526_;
v___y_445_ = v_a_524_;
v___y_446_ = v_declName_518_;
v___y_447_ = v___x_531_;
goto v___jp_439_;
}
else
{
size_t v___x_532_; size_t v___x_533_; uint8_t v___x_534_; 
v___x_532_ = lean_ptr_addr(v_value_520_);
v___x_533_ = lean_ptr_addr(v_a_526_);
v___x_534_ = lean_usize_dec_eq(v___x_532_, v___x_533_);
v___y_440_ = v_nondep_522_;
v___y_441_ = v_body_521_;
v___y_442_ = v___y_489_;
v___y_443_ = v_a_528_;
v___y_444_ = v_a_526_;
v___y_445_ = v_a_524_;
v___y_446_ = v_declName_518_;
v___y_447_ = v___x_534_;
goto v___jp_439_;
}
}
else
{
lean_dec(v_a_526_);
lean_dec(v_a_524_);
lean_dec_ref(v_body_521_);
lean_dec(v_declName_518_);
lean_dec_ref(v___y_489_);
lean_dec_ref(v_post_434_);
lean_dec_ref(v_pre_432_);
return v___x_527_;
}
}
else
{
lean_dec(v_a_524_);
lean_dec_ref(v_body_521_);
lean_dec(v_declName_518_);
lean_dec_ref(v___y_489_);
lean_dec_ref(v_post_434_);
lean_dec_ref(v_pre_432_);
return v___x_525_;
}
}
else
{
lean_dec_ref(v_body_521_);
lean_dec(v_declName_518_);
lean_dec_ref(v___y_489_);
lean_dec_ref(v_post_434_);
lean_dec_ref(v_pre_432_);
return v___x_523_;
}
}
case 5:
{
lean_object* v_dummy_535_; lean_object* v_nargs_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_dummy_535_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0);
v_nargs_536_ = l_Lean_Expr_getAppNumArgs(v___y_489_);
lean_inc(v_nargs_536_);
v___x_537_ = lean_mk_array(v_nargs_536_, v_dummy_535_);
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_sub(v_nargs_536_, v___x_538_);
lean_dec(v_nargs_536_);
v___x_540_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_432_, v_post_434_, v___y_489_, v___x_537_, v___x_539_, v___y_435_, v___y_436_, v___y_437_);
return v___x_540_;
}
case 10:
{
lean_object* v_data_541_; lean_object* v_expr_542_; lean_object* v___x_543_; 
v_data_541_ = lean_ctor_get(v___y_489_, 0);
v_expr_542_ = lean_ctor_get(v___y_489_, 1);
lean_inc_ref(v_expr_542_);
lean_inc_ref(v_post_434_);
lean_inc_ref(v_pre_432_);
v___x_543_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_432_, v_post_434_, v_expr_542_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; size_t v___x_545_; size_t v___x_546_; uint8_t v___x_547_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref(v___x_543_);
v___x_545_ = lean_ptr_addr(v_expr_542_);
v___x_546_ = lean_ptr_addr(v_a_544_);
v___x_547_ = lean_usize_dec_eq(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_inc(v_data_541_);
lean_dec_ref(v___y_489_);
v___x_548_ = l_Lean_Expr_mdata___override(v_data_541_, v_a_544_);
v___x_549_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___x_548_, v___y_435_, v___y_436_, v___y_437_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; 
lean_dec(v_a_544_);
v___x_550_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___y_489_, v___y_435_, v___y_436_, v___y_437_);
return v___x_550_;
}
}
else
{
lean_dec_ref(v___y_489_);
lean_dec_ref(v_post_434_);
lean_dec_ref(v_pre_432_);
return v___x_543_;
}
}
case 11:
{
lean_object* v_typeName_551_; lean_object* v_idx_552_; lean_object* v_struct_553_; lean_object* v___x_554_; 
v_typeName_551_ = lean_ctor_get(v___y_489_, 0);
v_idx_552_ = lean_ctor_get(v___y_489_, 1);
v_struct_553_ = lean_ctor_get(v___y_489_, 2);
lean_inc_ref(v_struct_553_);
lean_inc_ref(v_post_434_);
lean_inc_ref(v_pre_432_);
v___x_554_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_432_, v_post_434_, v_struct_553_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; size_t v___x_556_; size_t v___x_557_; uint8_t v___x_558_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref(v___x_554_);
v___x_556_ = lean_ptr_addr(v_struct_553_);
v___x_557_ = lean_ptr_addr(v_a_555_);
v___x_558_ = lean_usize_dec_eq(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_inc(v_idx_552_);
lean_inc(v_typeName_551_);
lean_dec_ref(v___y_489_);
v___x_559_ = l_Lean_Expr_proj___override(v_typeName_551_, v_idx_552_, v_a_555_);
v___x_560_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___x_559_, v___y_435_, v___y_436_, v___y_437_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; 
lean_dec(v_a_555_);
v___x_561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___y_489_, v___y_435_, v___y_436_, v___y_437_);
return v___x_561_;
}
}
else
{
lean_dec_ref(v___y_489_);
lean_dec_ref(v_post_434_);
lean_dec_ref(v_pre_432_);
return v___x_554_;
}
}
default: 
{
lean_object* v___x_562_; 
v___x_562_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___y_489_, v___y_435_, v___y_436_, v___y_437_);
return v___x_562_;
}
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec_ref(v_post_434_);
lean_dec_ref(v_e_433_);
lean_dec_ref(v_pre_432_);
v_a_574_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_483_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_483_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v_post_434_);
lean_dec_ref(v_e_433_);
lean_dec_ref(v_pre_432_);
v_a_582_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_482_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_482_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
v___jp_439_:
{
if (v___y_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref(v___y_442_);
lean_dec_ref(v___y_441_);
v___x_448_ = l_Lean_Expr_letE___override(v___y_446_, v___y_445_, v___y_444_, v___y_443_, v___y_440_);
v___x_449_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___x_448_, v___y_435_, v___y_436_, v___y_437_);
return v___x_449_;
}
else
{
size_t v___x_450_; size_t v___x_451_; uint8_t v___x_452_; 
v___x_450_ = lean_ptr_addr(v___y_441_);
lean_dec_ref(v___y_441_);
v___x_451_ = lean_ptr_addr(v___y_443_);
v___x_452_ = lean_usize_dec_eq(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec_ref(v___y_442_);
v___x_453_ = l_Lean_Expr_letE___override(v___y_446_, v___y_445_, v___y_444_, v___y_443_, v___y_440_);
v___x_454_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___x_453_, v___y_435_, v___y_436_, v___y_437_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; 
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec_ref(v___y_443_);
v___x_455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___y_442_, v___y_435_, v___y_436_, v___y_437_);
return v___x_455_;
}
}
}
v___jp_456_:
{
if (v___y_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec_ref(v___y_459_);
v___x_463_ = l_Lean_Expr_lam___override(v___y_460_, v___y_458_, v___y_457_, v___y_461_);
v___x_464_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___x_463_, v___y_435_, v___y_436_, v___y_437_);
return v___x_464_;
}
else
{
uint8_t v___x_465_; 
v___x_465_ = l_Lean_instBEqBinderInfo_beq(v___y_461_, v___y_461_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec_ref(v___y_459_);
v___x_466_ = l_Lean_Expr_lam___override(v___y_460_, v___y_458_, v___y_457_, v___y_461_);
v___x_467_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___x_466_, v___y_435_, v___y_436_, v___y_437_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; 
lean_dec(v___y_460_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v___y_457_);
v___x_468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___y_459_, v___y_435_, v___y_436_, v___y_437_);
return v___x_468_;
}
}
}
v___jp_469_:
{
if (v___y_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec_ref(v___y_473_);
v___x_476_ = l_Lean_Expr_forallE___override(v___y_474_, v___y_472_, v___y_471_, v___y_470_);
v___x_477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___x_476_, v___y_435_, v___y_436_, v___y_437_);
return v___x_477_;
}
else
{
uint8_t v___x_478_; 
v___x_478_ = l_Lean_instBEqBinderInfo_beq(v___y_470_, v___y_470_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec_ref(v___y_473_);
v___x_479_ = l_Lean_Expr_forallE___override(v___y_474_, v___y_472_, v___y_471_, v___y_470_);
v___x_480_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___x_479_, v___y_435_, v___y_436_, v___y_437_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; 
lean_dec(v___y_474_);
lean_dec_ref(v___y_472_);
lean_dec_ref(v___y_471_);
v___x_481_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_432_, v_post_434_, v___y_473_, v___y_435_, v___y_436_, v___y_437_);
return v___x_481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed(lean_object* v___x_590_, lean_object* v_pre_591_, lean_object* v_e_592_, lean_object* v_post_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(v___x_590_, v_pre_591_, v_e_592_, v_post_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(lean_object* v_pre_599_, lean_object* v_post_600_, lean_object* v_e_601_, lean_object* v_a_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_inc(v_a_602_);
v___x_606_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_606_, 0, lean_box(0));
lean_closure_set(v___x_606_, 1, lean_box(0));
lean_closure_set(v___x_606_, 2, v_a_602_);
v___x_607_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_box(0), v___x_606_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_639_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_639_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_639_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_639_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_a_608_, v_e_601_);
lean_dec(v_a_608_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v___x_613_; lean_object* v___f_614_; lean_object* v___x_615_; 
lean_del_object(v___x_610_);
v___x_613_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_601_);
v___f_614_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_614_, 0, v___x_613_);
lean_closure_set(v___f_614_, 1, v_pre_599_);
lean_closure_set(v___f_614_, 2, v_e_601_);
lean_closure_set(v___f_614_, 3, v_post_600_);
v___x_615_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v___f_614_, v_a_602_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___f_617_; lean_object* v___x_618_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc_n(v_a_616_, 2);
lean_dec_ref(v___x_615_);
lean_inc(v_a_602_);
v___f_617_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_617_, 0, v_a_602_);
lean_closure_set(v___f_617_, 1, v_e_601_);
lean_closure_set(v___f_617_, 2, v_a_616_);
v___x_618_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_box(0), v___f_617_, v___y_603_, v___y_604_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v___x_618_, 0);
lean_dec(v_unused_626_);
v___x_620_ = v___x_618_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_dec(v___x_618_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v_a_616_);
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_616_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_a_616_);
v_a_627_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_618_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_618_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_dec_ref(v_e_601_);
return v___x_615_;
}
}
else
{
lean_object* v_val_635_; lean_object* v___x_637_; 
lean_dec_ref(v_e_601_);
lean_dec_ref(v_post_600_);
lean_dec_ref(v_pre_599_);
v_val_635_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_val_635_);
lean_dec_ref(v___x_612_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v_val_635_);
v___x_637_ = v___x_610_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_val_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_e_601_);
lean_dec_ref(v_post_600_);
lean_dec_ref(v_pre_599_);
v_a_640_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_607_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_607_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(lean_object* v_pre_648_, lean_object* v_post_649_, lean_object* v_e_650_, lean_object* v_a_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; 
lean_inc_ref(v_post_649_);
lean_inc(v___y_653_);
lean_inc_ref(v___y_652_);
lean_inc_ref(v_e_650_);
v___x_655_ = lean_apply_4(v_post_649_, v_e_650_, v___y_652_, v___y_653_, lean_box(0));
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_674_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_674_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_674_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_674_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
switch(lean_obj_tag(v_a_656_))
{
case 0:
{
lean_object* v_e_660_; lean_object* v___x_662_; 
lean_dec_ref(v_e_650_);
lean_dec_ref(v_post_649_);
lean_dec_ref(v_pre_648_);
v_e_660_ = lean_ctor_get(v_a_656_, 0);
lean_inc_ref(v_e_660_);
lean_dec_ref(v_a_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_e_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_e_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
case 1:
{
lean_object* v_e_664_; lean_object* v___x_665_; 
lean_del_object(v___x_658_);
lean_dec_ref(v_e_650_);
v_e_664_ = lean_ctor_get(v_a_656_, 0);
lean_inc_ref(v_e_664_);
lean_dec_ref(v_a_656_);
v___x_665_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_648_, v_post_649_, v_e_664_, v_a_651_, v___y_652_, v___y_653_);
return v___x_665_;
}
default: 
{
lean_object* v_e_x3f_666_; 
lean_dec_ref(v_post_649_);
lean_dec_ref(v_pre_648_);
v_e_x3f_666_ = lean_ctor_get(v_a_656_, 0);
lean_inc(v_e_x3f_666_);
lean_dec_ref(v_a_656_);
if (lean_obj_tag(v_e_x3f_666_) == 0)
{
lean_object* v___x_668_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_e_650_);
v___x_668_ = v___x_658_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_e_650_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
else
{
lean_object* v_val_670_; lean_object* v___x_672_; 
lean_dec_ref(v_e_650_);
v_val_670_ = lean_ctor_get(v_e_x3f_666_, 0);
lean_inc(v_val_670_);
lean_dec_ref(v_e_x3f_666_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_val_670_);
v___x_672_ = v___x_658_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_val_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v_e_650_);
lean_dec_ref(v_post_649_);
lean_dec_ref(v_pre_648_);
v_a_675_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_655_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_655_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_683_, lean_object* v_post_684_, lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_683_, v_post_684_, v_e_685_, v_a_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v_a_686_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_691_, lean_object* v_post_692_, lean_object* v_sz_693_, lean_object* v_i_694_, lean_object* v_bs_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
size_t v_sz_boxed_700_; size_t v_i_boxed_701_; lean_object* v_res_702_; 
v_sz_boxed_700_ = lean_unbox_usize(v_sz_693_);
lean_dec(v_sz_693_);
v_i_boxed_701_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_res_702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_691_, v_post_692_, v_sz_boxed_700_, v_i_boxed_701_, v_bs_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_703_, lean_object* v_post_704_, lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_x_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_703_, v_post_704_, v_x_705_, v_x_706_, v_x_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___boxed(lean_object* v_pre_713_, lean_object* v_post_714_, lean_object* v_e_715_, lean_object* v_a_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_713_, v_post_714_, v_e_715_, v_a_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v_a_716_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_object* v_00_u03b1_721_, lean_object* v_x_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_apply_1(v_x_722_, lean_box(0));
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0___boxed(lean_object* v_00_u03b1_728_, lean_object* v_x_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(v_00_u03b1_728_, v_x_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
return v_res_733_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_box(0);
v___x_735_ = lean_unsigned_to_nat(16u);
v___x_736_ = lean_mk_array(v___x_735_, v___x_734_);
return v___x_736_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___x_737_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1);
v___x_741_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_741_, 0, lean_box(0));
lean_closure_set(v___x_741_, 1, lean_box(0));
lean_closure_set(v___x_741_, 2, v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(lean_object* v_input_742_, lean_object* v_pre_743_, lean_object* v_post_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v___x_751_; 
v___x_748_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2);
v___x_749_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_box(0), v___x_748_, v___y_745_, v___y_746_);
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref(v___x_749_);
v___x_751_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_743_, v_post_744_, v_input_742_, v_a_750_, v___y_745_, v___y_746_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref(v___x_751_);
v___x_753_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_753_, 0, lean_box(0));
lean_closure_set(v___x_753_, 1, lean_box(0));
lean_closure_set(v___x_753_, 2, v_a_750_);
v___x_754_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_box(0), v___x_753_, v___y_745_, v___y_746_);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v___x_754_, 0);
lean_dec(v_unused_762_);
v___x_756_ = v___x_754_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_dec(v___x_754_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v_a_752_);
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_752_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
lean_dec(v_a_750_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___boxed(lean_object* v_input_763_, lean_object* v_pre_764_, lean_object* v_post_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(v_input_763_, v_pre_764_, v_post_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand(lean_object* v_e_771_, lean_object* v_p_772_, uint8_t v_allowOpaque_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___x_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___x_780_; 
v___x_777_ = lean_box(v_allowOpaque_773_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Meta_deltaExpand___lam__0___boxed), 6, 2);
lean_closure_set(v___f_778_, 0, v_p_772_);
lean_closure_set(v___f_778_, 1, v___x_777_);
v___f_779_ = ((lean_object*)(l_Lean_Meta_deltaExpand___closed__0));
v___x_780_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(v_e_771_, v___f_778_, v___f_779_, v_a_774_, v_a_775_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___boxed(lean_object* v_e_781_, lean_object* v_p_782_, lean_object* v_allowOpaque_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
uint8_t v_allowOpaque_boxed_787_; lean_object* v_res_788_; 
v_allowOpaque_boxed_787_ = lean_unbox(v_allowOpaque_783_);
v_res_788_ = l_Lean_Meta_deltaExpand(v_e_781_, v_p_782_, v_allowOpaque_boxed_787_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_789_, lean_object* v_m_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_m_790_, v_a_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_793_, lean_object* v_m_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(v_00_u03b2_793_, v_m_794_, v_a_795_);
lean_dec_ref(v_a_795_);
lean_dec_ref(v_m_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_797_, lean_object* v_ref_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_798_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_803_, lean_object* v_ref_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_803_, v_ref_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_809_, lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_810_, v___y_811_, v___y_812_, v___y_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_816_, lean_object* v_x_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(v_00_u03b1_816_, v_x_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_823_, lean_object* v_m_824_, lean_object* v_a_825_, lean_object* v_b_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v_m_824_, v_a_825_, v_b_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_828_, lean_object* v_a_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_832_, lean_object* v_a_833_, lean_object* v_x_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_832_, v_a_833_, v_x_834_);
lean_dec(v_x_834_);
lean_dec_ref(v_a_833_);
return v_res_835_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_836_, lean_object* v_a_837_, lean_object* v_x_838_){
_start:
{
uint8_t v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___redArg(v_a_837_, v_x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_840_, lean_object* v_a_841_, lean_object* v_x_842_){
_start:
{
uint8_t v_res_843_; lean_object* v_r_844_; 
v_res_843_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_840_, v_a_841_, v_x_842_);
lean_dec(v_x_842_);
lean_dec_ref(v_a_841_);
v_r_844_ = lean_box(v_res_843_);
return v_r_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_845_, lean_object* v_data_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_data_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_848_, lean_object* v_a_849_, lean_object* v_b_850_, lean_object* v_x_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_a_849_, v_b_850_, v_x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_853_, lean_object* v_i_854_, lean_object* v_source_855_, lean_object* v_target_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_854_, v_source_855_, v_target_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(lean_object* v_mvarId_862_, lean_object* v_x_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_862_, v_x_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_a_878_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_869_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_869_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg___boxed(lean_object* v_mvarId_886_, lean_object* v_x_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_886_, v_x_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(lean_object* v_00_u03b1_894_, lean_object* v_mvarId_895_, lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_895_, v_x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___boxed(lean_object* v_00_u03b1_903_, lean_object* v_mvarId_904_, lean_object* v_x_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(v_00_u03b1_903_, v_mvarId_904_, v_x_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lam__0(lean_object* v_mvarId_912_, lean_object* v___x_913_, lean_object* v_p_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
lean_inc(v_mvarId_912_);
v___x_920_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_912_, v___x_913_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v___x_921_; 
lean_dec_ref(v___x_920_);
lean_inc(v_mvarId_912_);
v___x_921_ = l_Lean_MVarId_getType(v_mvarId_912_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; uint8_t v___x_923_; lean_object* v___x_924_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_921_);
v___x_923_ = 0;
v___x_924_ = l_Lean_Meta_deltaExpand(v_a_922_, v_p_914_, v___x_923_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_926_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref(v___x_924_);
v___x_926_ = l_Lean_MVarId_change(v_mvarId_912_, v_a_925_, v___x_923_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_926_;
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_mvarId_912_);
v_a_927_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_924_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_924_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v_p_914_);
lean_dec(v_mvarId_912_);
v_a_935_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_921_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_921_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec_ref(v_p_914_);
lean_dec(v_mvarId_912_);
v_a_943_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_920_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_920_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lam__0___boxed(lean_object* v_mvarId_951_, lean_object* v___x_952_, lean_object* v_p_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_MVarId_deltaTarget___lam__0(v_mvarId_951_, v___x_952_, v_p_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget(lean_object* v_mvarId_963_, lean_object* v_p_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; lean_object* v___f_971_; lean_object* v___x_972_; 
v___x_970_ = ((lean_object*)(l_Lean_MVarId_deltaTarget___closed__1));
lean_inc(v_mvarId_963_);
v___f_971_ = lean_alloc_closure((void*)(l_Lean_MVarId_deltaTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_971_, 0, v_mvarId_963_);
lean_closure_set(v___f_971_, 1, v___x_970_);
lean_closure_set(v___f_971_, 2, v_p_964_);
v___x_972_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_963_, v___f_971_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___boxed(lean_object* v_mvarId_973_, lean_object* v_p_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_MVarId_deltaTarget(v_mvarId_973_, v_p_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lam__0(lean_object* v_mvarId_981_, lean_object* v___x_982_, lean_object* v_fvarId_983_, lean_object* v_p_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; 
lean_inc(v_mvarId_981_);
v___x_990_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_981_, v___x_982_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v___x_991_; 
lean_dec_ref(v___x_990_);
lean_inc(v_fvarId_983_);
v___x_991_ = l_Lean_FVarId_getType___redArg(v_fvarId_983_, v___y_985_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; uint8_t v___x_993_; lean_object* v___x_994_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref(v___x_991_);
v___x_993_ = 0;
v___x_994_ = l_Lean_Meta_deltaExpand(v_a_992_, v_p_984_, v___x_993_, v___y_987_, v___y_988_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref(v___x_994_);
v___x_996_ = l_Lean_MVarId_changeLocalDecl(v_mvarId_981_, v_fvarId_983_, v_a_995_, v___x_993_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
return v___x_996_;
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_fvarId_983_);
lean_dec(v_mvarId_981_);
v_a_997_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_994_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_994_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec_ref(v_p_984_);
lean_dec(v_fvarId_983_);
lean_dec(v_mvarId_981_);
v_a_1005_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_991_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_991_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v_p_984_);
lean_dec(v_fvarId_983_);
lean_dec(v_mvarId_981_);
v_a_1013_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_990_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_990_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lam__0___boxed(lean_object* v_mvarId_1021_, lean_object* v___x_1022_, lean_object* v_fvarId_1023_, lean_object* v_p_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_MVarId_deltaLocalDecl___lam__0(v_mvarId_1021_, v___x_1022_, v_fvarId_1023_, v_p_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl(lean_object* v_mvarId_1031_, lean_object* v_fvarId_1032_, lean_object* v_p_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; lean_object* v___f_1040_; lean_object* v___x_1041_; 
v___x_1039_ = ((lean_object*)(l_Lean_MVarId_deltaTarget___closed__1));
lean_inc(v_mvarId_1031_);
v___f_1040_ = lean_alloc_closure((void*)(l_Lean_MVarId_deltaLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1040_, 0, v_mvarId_1031_);
lean_closure_set(v___f_1040_, 1, v___x_1039_);
lean_closure_set(v___f_1040_, 2, v_fvarId_1032_);
lean_closure_set(v___f_1040_, 3, v_p_1033_);
v___x_1041_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_1031_, v___f_1040_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___boxed(lean_object* v_mvarId_1042_, lean_object* v_fvarId_1043_, lean_object* v_p_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_MVarId_deltaLocalDecl(v_mvarId_1042_, v_fvarId_1043_, v_p_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
return v_res_1050_;
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
