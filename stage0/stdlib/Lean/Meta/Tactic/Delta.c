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
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_10_, 2);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_m_132_, lean_object* v_query_133_, lean_object* v_x_134_, lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
lean_object* v_zero_137_; uint8_t v_isZero_138_; 
v_zero_137_ = lean_unsigned_to_nat(0u);
v_isZero_138_ = lean_nat_dec_eq(v_x_135_, v_zero_137_);
if (v_isZero_138_ == 1)
{
lean_dec(v_x_136_);
lean_dec(v_x_135_);
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(2);
return v___x_139_;
}
else
{
lean_object* v_val_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_val_140_ = lean_ctor_get(v_x_134_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_134_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v_x_134_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_val_140_);
lean_dec(v_x_134_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_val_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
else
{
lean_object* v_keyArray_148_; lean_object* v_valueArray_149_; lean_object* v___x_150_; uint8_t v_isSome_151_; 
v_keyArray_148_ = lean_ctor_get(v_m_132_, 1);
v_valueArray_149_ = lean_ctor_get(v_m_132_, 2);
v___x_150_ = lean_array_fget_borrowed(v_keyArray_148_, v_x_136_);
v_isSome_151_ = lean_noption_is_some(v___x_150_);
if (v_isSome_151_ == 0)
{
lean_dec(v_x_135_);
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v_x_136_);
return v___x_152_;
}
else
{
lean_object* v_val_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
lean_dec(v_x_136_);
v_val_153_ = lean_ctor_get(v_x_134_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_134_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v_x_134_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_val_153_);
lean_dec(v_x_134_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_val_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
else
{
lean_object* v_one_161_; lean_object* v_n_162_; lean_object* v___y_164_; 
v_one_161_ = lean_unsigned_to_nat(1u);
v_n_162_ = lean_nat_sub(v_x_135_, v_one_161_);
lean_dec(v_x_135_);
if (v_isSome_151_ == 0)
{
goto v___jp_170_;
}
else
{
lean_object* v___x_172_; uint8_t v_isSome_173_; 
v___x_172_ = lean_array_fget_borrowed(v_valueArray_149_, v_x_136_);
v_isSome_173_ = lean_noption_is_some(v___x_172_);
if (v_isSome_173_ == 0)
{
goto v___jp_170_;
}
else
{
lean_object* v_val_174_; uint8_t v___x_175_; 
lean_inc(v___x_150_);
v_val_174_ = lean_noption_get(v___x_150_);
v___x_175_ = l_Lean_ExprStructEq_beq(v_val_174_, v_query_133_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
lean_dec(v_val_174_);
v___x_176_ = lean_array_get_size(v_keyArray_148_);
v___x_177_ = lean_nat_add(v_x_136_, v_one_161_);
lean_dec(v_x_136_);
v___x_178_ = lean_nat_dec_lt(v___x_177_, v___x_176_);
if (v___x_178_ == 0)
{
lean_dec(v___x_177_);
v_x_135_ = v_n_162_;
v_x_136_ = v_zero_137_;
goto _start;
}
else
{
v_x_135_ = v_n_162_;
v_x_136_ = v___x_177_;
goto _start;
}
}
else
{
lean_object* v_val_181_; lean_object* v___x_182_; 
lean_dec(v_n_162_);
lean_dec(v_x_134_);
lean_inc(v___x_172_);
v_val_181_ = lean_noption_get(v___x_172_);
v___x_182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_182_, 0, v_x_136_);
lean_ctor_set(v___x_182_, 1, v_val_174_);
lean_ctor_set(v___x_182_, 2, v_val_181_);
return v___x_182_;
}
}
}
v___jp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_165_ = lean_array_get_size(v_keyArray_148_);
v___x_166_ = lean_nat_add(v_x_136_, v_one_161_);
lean_dec(v_x_136_);
v___x_167_ = lean_nat_dec_lt(v___x_166_, v___x_165_);
if (v___x_167_ == 0)
{
lean_dec(v___x_166_);
v_x_134_ = v___y_164_;
v_x_135_ = v_n_162_;
v_x_136_ = v_zero_137_;
goto _start;
}
else
{
v_x_134_ = v___y_164_;
v_x_135_ = v_n_162_;
v_x_136_ = v___x_166_;
goto _start;
}
}
v___jp_170_:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v___x_171_; 
lean_inc(v_x_136_);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v_x_136_);
v___y_164_ = v___x_171_;
goto v___jp_163_;
}
else
{
v___y_164_ = v_x_134_;
goto v___jp_163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_m_183_, lean_object* v_query_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_m_183_, v_query_184_, v_x_185_, v_x_186_, v_x_187_);
lean_dec_ref(v_query_184_);
lean_dec_ref(v_m_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(lean_object* v_m_189_, lean_object* v_query_190_){
_start:
{
lean_object* v_keyArray_191_; lean_object* v___x_192_; uint64_t v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v_fold_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; size_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_keyArray_191_ = lean_ctor_get(v_m_189_, 1);
v___x_192_ = lean_array_get_size(v_keyArray_191_);
v___x_193_ = l_Lean_ExprStructEq_hash(v_query_190_);
v___x_194_ = 32ULL;
v___x_195_ = lean_uint64_shift_right(v___x_193_, v___x_194_);
v_fold_196_ = lean_uint64_xor(v___x_193_, v___x_195_);
v___x_197_ = 16ULL;
v___x_198_ = lean_uint64_shift_right(v_fold_196_, v___x_197_);
v___x_199_ = lean_uint64_xor(v_fold_196_, v___x_198_);
v___x_200_ = lean_uint64_to_usize(v___x_199_);
v___x_201_ = lean_usize_of_nat(v___x_192_);
v___x_202_ = ((size_t)1ULL);
v___x_203_ = lean_usize_sub(v___x_201_, v___x_202_);
v___x_204_ = lean_usize_land(v___x_200_, v___x_203_);
v___x_205_ = lean_usize_to_nat(v___x_204_);
v___x_206_ = lean_box(0);
v___x_207_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_m_189_, v_query_190_, v___x_206_, v___x_192_, v___x_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_m_208_, lean_object* v_query_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v_m_208_, v_query_209_);
lean_dec_ref(v_query_209_);
lean_dec_ref(v_m_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_m_211_, lean_object* v_query_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v_m_211_, v_query_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_index_214_; lean_object* v_key_215_; lean_object* v_value_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
v_index_214_ = lean_ctor_get(v___x_213_, 0);
v_key_215_ = lean_ctor_get(v___x_213_, 1);
v_value_216_ = lean_ctor_get(v___x_213_, 2);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_213_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_value_216_);
lean_inc(v_key_215_);
lean_inc(v_index_214_);
lean_dec(v___x_213_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_index_214_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_key_215_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_value_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v___x_224_; 
lean_dec(v___x_213_);
v___x_224_ = lean_box(1);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_m_225_, lean_object* v_query_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_m_225_, v_query_226_);
lean_dec_ref(v_query_226_);
lean_dec_ref(v_m_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(lean_object* v_m_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_m_228_, v_a_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_value_231_; lean_object* v___x_232_; 
v_value_231_ = lean_ctor_get(v___x_230_, 2);
lean_inc(v_value_231_);
lean_dec_ref_known(v___x_230_, 3);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v_value_231_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; 
v___x_233_ = lean_box(0);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_m_234_, v_a_235_);
lean_dec_ref(v_a_235_);
lean_dec_ref(v_m_234_);
return v_res_236_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = l_Lean_maxRecDepthErrorMessage;
v___x_243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_245_ = l_Lean_MessageData_ofFormat(v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_247_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_248_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v___x_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_249_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v_ref_249_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_254_);
return v_res_256_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_box(0);
v___x_258_ = l_Lean_interruptExceptionId;
v___x_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(lean_object* v_x_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___y_271_; uint8_t v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; uint8_t v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v_fileName_301_; lean_object* v_fileMap_302_; lean_object* v_options_303_; lean_object* v_currRecDepth_304_; lean_object* v_maxRecDepth_305_; lean_object* v_ref_306_; lean_object* v_currNamespace_307_; lean_object* v_openDecls_308_; lean_object* v_initHeartbeats_309_; lean_object* v_maxHeartbeats_310_; lean_object* v_quotContext_311_; lean_object* v_currMacroScope_312_; uint8_t v_diag_313_; lean_object* v_cancelTk_x3f_314_; uint8_t v_suppressElabErrors_315_; lean_object* v_inheritedTraceOptions_316_; 
v_fileName_301_ = lean_ctor_get(v___y_267_, 0);
v_fileMap_302_ = lean_ctor_get(v___y_267_, 1);
v_options_303_ = lean_ctor_get(v___y_267_, 2);
v_currRecDepth_304_ = lean_ctor_get(v___y_267_, 3);
v_maxRecDepth_305_ = lean_ctor_get(v___y_267_, 4);
v_ref_306_ = lean_ctor_get(v___y_267_, 5);
v_currNamespace_307_ = lean_ctor_get(v___y_267_, 6);
v_openDecls_308_ = lean_ctor_get(v___y_267_, 7);
v_initHeartbeats_309_ = lean_ctor_get(v___y_267_, 8);
v_maxHeartbeats_310_ = lean_ctor_get(v___y_267_, 9);
v_quotContext_311_ = lean_ctor_get(v___y_267_, 10);
v_currMacroScope_312_ = lean_ctor_get(v___y_267_, 11);
v_diag_313_ = lean_ctor_get_uint8(v___y_267_, sizeof(void*)*14);
v_cancelTk_x3f_314_ = lean_ctor_get(v___y_267_, 12);
v_suppressElabErrors_315_ = lean_ctor_get_uint8(v___y_267_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_316_ = lean_ctor_get(v___y_267_, 13);
if (lean_obj_tag(v_cancelTk_x3f_314_) == 1)
{
lean_object* v_val_322_; uint8_t v___x_323_; 
v_val_322_ = lean_ctor_get(v_cancelTk_x3f_314_, 0);
v___x_323_ = l_IO_CancelToken_isSet(v_val_322_);
if (v___x_323_ == 0)
{
goto v___jp_317_;
}
else
{
lean_object* v___x_324_; lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v_x_265_);
v___x_324_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
else
{
goto v___jp_317_;
}
v___jp_270_:
{
if (lean_obj_tag(v___y_271_) == 0)
{
return v___y_271_;
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
v_a_272_ = lean_ctor_get(v___y_271_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___y_271_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___y_271_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___y_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
v___jp_280_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_add(v___y_282_, v___x_297_);
lean_inc_ref(v___y_295_);
lean_inc(v___y_294_);
lean_inc(v___y_296_);
lean_inc(v___y_286_);
lean_inc(v___y_293_);
lean_inc(v___y_290_);
lean_inc(v___y_283_);
lean_inc(v___y_288_);
lean_inc(v___y_289_);
lean_inc_ref(v___y_285_);
lean_inc_ref(v___y_287_);
lean_inc_ref(v___y_291_);
v___x_299_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_299_, 0, v___y_291_);
lean_ctor_set(v___x_299_, 1, v___y_287_);
lean_ctor_set(v___x_299_, 2, v___y_285_);
lean_ctor_set(v___x_299_, 3, v___x_298_);
lean_ctor_set(v___x_299_, 4, v___y_289_);
lean_ctor_set(v___x_299_, 5, v___y_284_);
lean_ctor_set(v___x_299_, 6, v___y_288_);
lean_ctor_set(v___x_299_, 7, v___y_283_);
lean_ctor_set(v___x_299_, 8, v___y_290_);
lean_ctor_set(v___x_299_, 9, v___y_293_);
lean_ctor_set(v___x_299_, 10, v___y_286_);
lean_ctor_set(v___x_299_, 11, v___y_296_);
lean_ctor_set(v___x_299_, 12, v___y_294_);
lean_ctor_set(v___x_299_, 13, v___y_295_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*14, v___y_281_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*14 + 1, v___y_292_);
lean_inc(v___y_268_);
lean_inc(v___y_266_);
v___x_300_ = lean_apply_4(v_x_265_, v___y_266_, v___x_299_, v___y_268_, lean_box(0));
v___y_271_ = v___x_300_;
goto v___jp_270_;
}
v___jp_317_:
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_nat_dec_eq(v_maxRecDepth_305_, v___x_318_);
if (v___x_319_ == 0)
{
uint8_t v___x_320_; 
v___x_320_ = lean_nat_dec_eq(v_currRecDepth_304_, v_maxRecDepth_305_);
if (v___x_320_ == 0)
{
lean_inc(v_ref_306_);
v___y_281_ = v_diag_313_;
v___y_282_ = v_currRecDepth_304_;
v___y_283_ = v_openDecls_308_;
v___y_284_ = v_ref_306_;
v___y_285_ = v_options_303_;
v___y_286_ = v_quotContext_311_;
v___y_287_ = v_fileMap_302_;
v___y_288_ = v_currNamespace_307_;
v___y_289_ = v_maxRecDepth_305_;
v___y_290_ = v_initHeartbeats_309_;
v___y_291_ = v_fileName_301_;
v___y_292_ = v_suppressElabErrors_315_;
v___y_293_ = v_maxHeartbeats_310_;
v___y_294_ = v_cancelTk_x3f_314_;
v___y_295_ = v_inheritedTraceOptions_316_;
v___y_296_ = v_currMacroScope_312_;
goto v___jp_280_;
}
else
{
lean_object* v___x_321_; 
lean_dec_ref(v_x_265_);
lean_inc(v_ref_306_);
v___x_321_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_306_);
v___y_271_ = v___x_321_;
goto v___jp_270_;
}
}
else
{
lean_inc(v_ref_306_);
v___y_281_ = v_diag_313_;
v___y_282_ = v_currRecDepth_304_;
v___y_283_ = v_openDecls_308_;
v___y_284_ = v_ref_306_;
v___y_285_ = v_options_303_;
v___y_286_ = v_quotContext_311_;
v___y_287_ = v_fileMap_302_;
v___y_288_ = v_currNamespace_307_;
v___y_289_ = v_maxRecDepth_305_;
v___y_290_ = v_initHeartbeats_309_;
v___y_291_ = v_fileName_301_;
v___y_292_ = v_suppressElabErrors_315_;
v___y_293_ = v_maxHeartbeats_310_;
v___y_294_ = v_cancelTk_x3f_314_;
v___y_295_ = v_inheritedTraceOptions_316_;
v___y_296_ = v_currMacroScope_312_;
goto v___jp_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(lean_object* v_b_339_, lean_object* v_acc_340_, lean_object* v_i_341_){
_start:
{
lean_object* v___y_343_; lean_object* v_keyArray_351_; lean_object* v_valueArray_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_keyArray_351_ = lean_ctor_get(v_b_339_, 1);
v_valueArray_352_ = lean_ctor_get(v_b_339_, 2);
v___x_353_ = lean_array_get_size(v_keyArray_351_);
v___x_354_ = lean_nat_dec_lt(v_i_341_, v___x_353_);
if (v___x_354_ == 0)
{
lean_dec(v_i_341_);
return v_acc_340_;
}
else
{
lean_object* v___x_355_; uint8_t v_isSome_356_; 
v___x_355_ = lean_array_fget_borrowed(v_keyArray_351_, v_i_341_);
v_isSome_356_ = lean_noption_is_some(v___x_355_);
if (v_isSome_356_ == 0)
{
goto v___jp_347_;
}
else
{
lean_object* v___x_357_; uint8_t v_isSome_358_; 
v___x_357_ = lean_array_fget_borrowed(v_valueArray_352_, v_i_341_);
v_isSome_358_ = lean_noption_is_some(v___x_357_);
if (v_isSome_358_ == 0)
{
goto v___jp_347_;
}
else
{
lean_object* v_val_359_; lean_object* v_val_360_; lean_object* v_i_362_; lean_object* v___x_367_; 
lean_inc(v___x_355_);
v_val_359_ = lean_noption_get(v___x_355_);
lean_inc(v___x_357_);
v_val_360_ = lean_noption_get(v___x_357_);
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v_acc_340_, v_val_359_);
switch(lean_obj_tag(v___x_367_))
{
case 0:
{
lean_object* v_index_368_; lean_object* v_size_369_; lean_object* v___x_370_; 
v_index_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_index_368_);
lean_dec_ref_known(v___x_367_, 3);
v_size_369_ = lean_ctor_get(v_acc_340_, 0);
lean_inc(v_size_369_);
v___x_370_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_340_, v_size_369_, v_index_368_, v_val_359_, v_val_360_);
lean_dec(v_index_368_);
v___y_343_ = v___x_370_;
goto v___jp_342_;
}
case 1:
{
lean_object* v_index_371_; 
v_index_371_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_index_371_);
lean_dec_ref_known(v___x_367_, 1);
v_i_362_ = v_index_371_;
goto v___jp_361_;
}
default: 
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_340_, v___x_372_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_index_374_; 
v_index_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_index_374_);
lean_dec_ref_known(v___x_373_, 1);
v_i_362_ = v_index_374_;
goto v___jp_361_;
}
else
{
lean_dec(v_val_360_);
lean_dec(v_val_359_);
v___y_343_ = v_acc_340_;
goto v___jp_342_;
}
}
}
v___jp_361_:
{
lean_object* v_size_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_size_363_ = lean_ctor_get(v_acc_340_, 0);
v___x_364_ = lean_unsigned_to_nat(1u);
v___x_365_ = lean_nat_add(v_size_363_, v___x_364_);
v___x_366_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_340_, v___x_365_, v_i_362_, v_val_359_, v_val_360_);
lean_dec(v_i_362_);
v___y_343_ = v___x_366_;
goto v___jp_342_;
}
}
}
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_add(v_i_341_, v___x_344_);
lean_dec(v_i_341_);
v_acc_340_ = v___y_343_;
v_i_341_ = v___x_345_;
goto _start;
}
v___jp_347_:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_i_341_, v___x_348_);
lean_dec(v_i_341_);
v_i_341_ = v___x_349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13___redArg___boxed(lean_object* v_b_375_, lean_object* v_acc_376_, lean_object* v_i_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_375_, v_acc_376_, v_i_377_);
lean_dec_ref(v_b_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12___redArg(lean_object* v_init_379_, lean_object* v_b_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_380_, v_init_379_, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12___redArg___boxed(lean_object* v_init_383_, lean_object* v_b_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12___redArg(v_init_383_, v_b_384_);
lean_dec_ref(v_b_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7___redArg(lean_object* v_m_386_){
_start:
{
lean_object* v_keyArray_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v_cellCount_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_target_394_; lean_object* v___x_395_; 
v_keyArray_387_ = lean_ctor_get(v_m_386_, 1);
v___x_388_ = lean_array_get_size(v_keyArray_387_);
v___x_389_ = lean_unsigned_to_nat(2u);
v_cellCount_390_ = lean_nat_mul(v___x_388_, v___x_389_);
v___x_391_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_390_);
v___x_392_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_390_);
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_390_);
v_target_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_394_, 0, v___x_391_);
lean_ctor_set(v_target_394_, 1, v___x_392_);
lean_ctor_set(v_target_394_, 2, v___x_393_);
v___x_395_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12___redArg(v_target_394_, v_m_386_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_m_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7___redArg(v_m_396_);
lean_dec_ref(v_m_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(lean_object* v_a_398_, lean_object* v_e_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___y_405_; lean_object* v___y_408_; lean_object* v_i_409_; lean_object* v___y_425_; lean_object* v_i_426_; lean_object* v___y_432_; lean_object* v___x_441_; 
v___x_402_ = lean_st_ref_take(v_a_398_);
v___x_403_ = lean_box(0);
v___x_441_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v___x_402_, v_e_399_);
switch(lean_obj_tag(v___x_441_))
{
case 0:
{
lean_object* v_index_442_; lean_object* v_size_443_; lean_object* v___x_444_; 
v_index_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_index_442_);
lean_dec_ref_known(v___x_441_, 3);
v_size_443_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_size_443_);
v___x_444_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_402_, v_size_443_, v_index_442_, v_e_399_, v_a_400_);
lean_dec(v_index_442_);
v___y_405_ = v___x_444_;
goto v___jp_404_;
}
case 1:
{
lean_object* v_index_445_; lean_object* v_size_446_; lean_object* v_keyArray_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_index_445_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_index_445_);
lean_dec_ref_known(v___x_441_, 1);
v_size_446_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_size_446_);
v_keyArray_447_ = lean_ctor_get(v___x_402_, 1);
lean_inc_ref(v_keyArray_447_);
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = lean_nat_add(v_size_446_, v___x_448_);
lean_dec(v_size_446_);
v___x_450_ = lean_array_get_size(v_keyArray_447_);
lean_dec_ref(v_keyArray_447_);
v___x_451_ = lean_nat_dec_lt(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_dec(v___x_449_);
lean_dec(v_index_445_);
goto v___jp_414_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_452_ = lean_unsigned_to_nat(4u);
v___x_453_ = lean_nat_mul(v___x_449_, v___x_452_);
v___x_454_ = lean_unsigned_to_nat(3u);
v___x_455_ = lean_nat_mul(v___x_450_, v___x_454_);
v___x_456_ = lean_nat_dec_le(v___x_453_, v___x_455_);
lean_dec(v___x_455_);
lean_dec(v___x_453_);
if (v___x_456_ == 0)
{
lean_dec(v___x_449_);
lean_dec(v_index_445_);
goto v___jp_414_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_402_, v___x_449_, v_index_445_, v_e_399_, v_a_400_);
lean_dec(v_index_445_);
v___y_405_ = v___x_457_;
goto v___jp_404_;
}
}
}
default: 
{
lean_object* v_size_458_; lean_object* v_keyArray_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v_size_458_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_size_458_);
v_keyArray_459_ = lean_ctor_get(v___x_402_, 1);
lean_inc_ref(v_keyArray_459_);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_add(v_size_458_, v___x_460_);
lean_dec(v_size_458_);
v___x_462_ = lean_array_get_size(v_keyArray_459_);
lean_dec_ref(v_keyArray_459_);
v___x_463_ = lean_nat_dec_lt(v___x_461_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
lean_dec(v___x_461_);
v___x_464_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7___redArg(v___x_402_);
lean_dec(v___x_402_);
v___y_432_ = v___x_464_;
goto v___jp_431_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_465_ = lean_unsigned_to_nat(4u);
v___x_466_ = lean_nat_mul(v___x_461_, v___x_465_);
lean_dec(v___x_461_);
v___x_467_ = lean_unsigned_to_nat(3u);
v___x_468_ = lean_nat_mul(v___x_462_, v___x_467_);
v___x_469_ = lean_nat_dec_le(v___x_466_, v___x_468_);
lean_dec(v___x_468_);
lean_dec(v___x_466_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7___redArg(v___x_402_);
lean_dec(v___x_402_);
v___y_432_ = v___x_470_;
goto v___jp_431_;
}
else
{
v___y_432_ = v___x_402_;
goto v___jp_431_;
}
}
}
}
v___jp_404_:
{
lean_object* v___x_406_; 
v___x_406_ = lean_st_ref_put(v_a_398_, v___y_405_);
return v___x_403_;
}
v___jp_407_:
{
lean_object* v_size_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_size_410_ = lean_ctor_get(v___y_408_, 0);
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_nat_add(v_size_410_, v___x_411_);
v___x_413_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_408_, v___x_412_, v_i_409_, v_e_399_, v_a_400_);
lean_dec(v_i_409_);
v___y_405_ = v___x_413_;
goto v___jp_404_;
}
v___jp_414_:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7___redArg(v___x_402_);
lean_dec(v___x_402_);
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v___x_415_, v_e_399_);
switch(lean_obj_tag(v___x_416_))
{
case 0:
{
lean_object* v_index_417_; lean_object* v_size_418_; lean_object* v___x_419_; 
v_index_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_index_417_);
lean_dec_ref_known(v___x_416_, 3);
v_size_418_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_size_418_);
v___x_419_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_415_, v_size_418_, v_index_417_, v_e_399_, v_a_400_);
lean_dec(v_index_417_);
v___y_405_ = v___x_419_;
goto v___jp_404_;
}
case 1:
{
lean_object* v_index_420_; 
v_index_420_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_index_420_);
lean_dec_ref_known(v___x_416_, 1);
v___y_408_ = v___x_415_;
v_i_409_ = v_index_420_;
goto v___jp_407_;
}
default: 
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_415_, v___x_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_index_423_; 
v_index_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_index_423_);
lean_dec_ref_known(v___x_422_, 1);
v___y_408_ = v___x_415_;
v_i_409_ = v_index_423_;
goto v___jp_407_;
}
else
{
lean_dec_ref(v_a_400_);
lean_dec_ref(v_e_399_);
v___y_405_ = v___x_415_;
goto v___jp_404_;
}
}
}
}
v___jp_424_:
{
lean_object* v_size_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_size_427_ = lean_ctor_get(v___y_425_, 0);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_add(v_size_427_, v___x_428_);
v___x_430_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_425_, v___x_429_, v_i_426_, v_e_399_, v_a_400_);
lean_dec(v_i_426_);
v___y_405_ = v___x_430_;
goto v___jp_404_;
}
v___jp_431_:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v___y_432_, v_e_399_);
switch(lean_obj_tag(v___x_433_))
{
case 0:
{
lean_object* v_index_434_; lean_object* v_size_435_; lean_object* v___x_436_; 
v_index_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_index_434_);
lean_dec_ref_known(v___x_433_, 3);
v_size_435_ = lean_ctor_get(v___y_432_, 0);
lean_inc(v_size_435_);
v___x_436_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_432_, v_size_435_, v_index_434_, v_e_399_, v_a_400_);
lean_dec(v_index_434_);
v___y_405_ = v___x_436_;
goto v___jp_404_;
}
case 1:
{
lean_object* v_index_437_; 
v_index_437_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_index_437_);
lean_dec_ref_known(v___x_433_, 1);
v___y_425_ = v___y_432_;
v_i_426_ = v_index_437_;
goto v___jp_424_;
}
default: 
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_432_, v___x_438_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_index_440_; 
v_index_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_index_440_);
lean_dec_ref_known(v___x_439_, 1);
v___y_425_ = v___y_432_;
v_i_426_ = v_index_440_;
goto v___jp_424_;
}
else
{
lean_dec_ref(v_a_400_);
lean_dec_ref(v_e_399_);
v___y_405_ = v___y_432_;
goto v___jp_404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed(lean_object* v_a_471_, lean_object* v_e_472_, lean_object* v_a_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(v_a_471_, v_e_472_, v_a_473_);
lean_dec(v_a_471_);
return v_res_475_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_477_; lean_object* v_dummy_478_; 
v___x_477_ = lean_box(0);
v_dummy_478_ = l_Lean_Expr_sort___override(v___x_477_);
return v_dummy_478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(lean_object* v_pre_479_, lean_object* v_post_480_, size_t v_sz_481_, size_t v_i_482_, lean_object* v_bs_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = lean_usize_dec_lt(v_i_482_, v_sz_481_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_dec_ref(v_post_480_);
lean_dec_ref(v_pre_479_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v_bs_483_);
return v___x_489_;
}
else
{
lean_object* v_v_490_; lean_object* v___x_491_; 
v_v_490_ = lean_array_uget_borrowed(v_bs_483_, v_i_482_);
lean_inc(v_v_490_);
lean_inc_ref(v_post_480_);
lean_inc_ref(v_pre_479_);
v___x_491_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_479_, v_post_480_, v_v_490_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_493_; lean_object* v_bs_x27_494_; size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = lean_unsigned_to_nat(0u);
v_bs_x27_494_ = lean_array_uset(v_bs_483_, v_i_482_, v___x_493_);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_add(v_i_482_, v___x_495_);
v___x_497_ = lean_array_uset(v_bs_x27_494_, v_i_482_, v_a_492_);
v_i_482_ = v___x_496_;
v_bs_483_ = v___x_497_;
goto _start;
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref(v_bs_483_);
lean_dec_ref(v_post_480_);
lean_dec_ref(v_pre_479_);
v_a_499_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_491_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_491_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(lean_object* v_pre_507_, lean_object* v_post_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
if (lean_obj_tag(v_x_509_) == 5)
{
lean_object* v_fn_516_; lean_object* v_arg_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_fn_516_ = lean_ctor_get(v_x_509_, 0);
lean_inc_ref(v_fn_516_);
v_arg_517_ = lean_ctor_get(v_x_509_, 1);
lean_inc_ref(v_arg_517_);
lean_dec_ref_known(v_x_509_, 2);
v___x_518_ = lean_array_set(v_x_510_, v_x_511_, v_arg_517_);
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_sub(v_x_511_, v___x_519_);
lean_dec(v_x_511_);
v_x_509_ = v_fn_516_;
v_x_510_ = v___x_518_;
v_x_511_ = v___x_520_;
goto _start;
}
else
{
lean_object* v___x_522_; 
lean_dec(v_x_511_);
lean_inc_ref(v_post_508_);
lean_inc_ref(v_pre_507_);
v___x_522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_507_, v_post_508_, v_x_509_, v___y_512_, v___y_513_, v___y_514_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; size_t v_sz_524_; size_t v___x_525_; lean_object* v___x_526_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v_sz_524_ = lean_array_size(v_x_510_);
v___x_525_ = ((size_t)0ULL);
lean_inc_ref(v_post_508_);
lean_inc_ref(v_pre_507_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_507_, v_post_508_, v_sz_524_, v___x_525_, v_x_510_, v___y_512_, v___y_513_, v___y_514_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = l_Lean_mkAppN(v_a_523_, v_a_527_);
lean_dec(v_a_527_);
v___x_529_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_507_, v_post_508_, v___x_528_, v___y_512_, v___y_513_, v___y_514_);
return v___x_529_;
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec(v_a_523_);
lean_dec_ref(v_post_508_);
lean_dec_ref(v_pre_507_);
v_a_530_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_526_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_526_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
else
{
lean_dec_ref(v_x_510_);
lean_dec_ref(v_post_508_);
lean_dec_ref(v_pre_507_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(lean_object* v___x_538_, lean_object* v_pre_539_, lean_object* v_e_540_, lean_object* v_post_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___y_547_; lean_object* v___y_548_; uint8_t v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; uint8_t v___y_554_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; uint8_t v___y_567_; lean_object* v___y_568_; uint8_t v___y_569_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; uint8_t v___y_581_; uint8_t v___y_582_; lean_object* v___x_589_; 
v___x_589_ = l_Lean_Core_checkSystem(v___x_538_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_590_; 
lean_dec_ref_known(v___x_589_, 1);
lean_inc_ref(v_pre_539_);
lean_inc(v___y_544_);
lean_inc_ref(v___y_543_);
lean_inc_ref(v_e_540_);
v___x_590_ = lean_apply_4(v_pre_539_, v_e_540_, v___y_543_, v___y_544_, lean_box(0));
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_680_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_680_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_680_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_680_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___y_596_; 
switch(lean_obj_tag(v_a_591_))
{
case 0:
{
lean_object* v_e_670_; lean_object* v___x_672_; 
lean_dec_ref(v_post_541_);
lean_dec_ref(v_e_540_);
lean_dec_ref(v_pre_539_);
v_e_670_ = lean_ctor_get(v_a_591_, 0);
lean_inc_ref(v_e_670_);
lean_dec_ref_known(v_a_591_, 1);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v_e_670_);
v___x_672_ = v___x_593_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_e_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
case 1:
{
lean_object* v_e_674_; lean_object* v___x_675_; 
lean_del_object(v___x_593_);
lean_dec_ref(v_e_540_);
v_e_674_ = lean_ctor_get(v_a_591_, 0);
lean_inc_ref(v_e_674_);
lean_dec_ref_known(v_a_591_, 1);
lean_inc_ref(v_post_541_);
lean_inc_ref(v_pre_539_);
v___x_675_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_539_, v_post_541_, v_e_674_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_677_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v_a_676_, v___y_542_, v___y_543_, v___y_544_);
return v___x_677_;
}
else
{
lean_dec_ref(v_post_541_);
lean_dec_ref(v_pre_539_);
return v___x_675_;
}
}
default: 
{
lean_object* v_e_x3f_678_; 
lean_del_object(v___x_593_);
v_e_x3f_678_ = lean_ctor_get(v_a_591_, 0);
lean_inc(v_e_x3f_678_);
lean_dec_ref_known(v_a_591_, 1);
if (lean_obj_tag(v_e_x3f_678_) == 0)
{
v___y_596_ = v_e_540_;
goto v___jp_595_;
}
else
{
lean_object* v_val_679_; 
lean_dec_ref(v_e_540_);
v_val_679_ = lean_ctor_get(v_e_x3f_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v_e_x3f_678_, 1);
v___y_596_ = v_val_679_;
goto v___jp_595_;
}
}
}
v___jp_595_:
{
switch(lean_obj_tag(v___y_596_))
{
case 7:
{
lean_object* v_binderName_597_; lean_object* v_binderType_598_; lean_object* v_body_599_; uint8_t v_binderInfo_600_; lean_object* v___x_601_; 
v_binderName_597_ = lean_ctor_get(v___y_596_, 0);
lean_inc(v_binderName_597_);
v_binderType_598_ = lean_ctor_get(v___y_596_, 1);
v_body_599_ = lean_ctor_get(v___y_596_, 2);
v_binderInfo_600_ = lean_ctor_get_uint8(v___y_596_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_598_);
lean_inc_ref(v_post_541_);
lean_inc_ref(v_pre_539_);
v___x_601_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_539_, v_post_541_, v_binderType_598_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_603_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
lean_inc_ref(v_body_599_);
lean_inc_ref(v_post_541_);
lean_inc_ref(v_pre_539_);
v___x_603_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_539_, v_post_541_, v_body_599_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; size_t v___x_605_; size_t v___x_606_; uint8_t v___x_607_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_603_, 1);
v___x_605_ = lean_ptr_addr(v_binderType_598_);
v___x_606_ = lean_ptr_addr(v_a_602_);
v___x_607_ = lean_usize_dec_eq(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
v___y_577_ = v_binderName_597_;
v___y_578_ = v___y_596_;
v___y_579_ = v_a_604_;
v___y_580_ = v_a_602_;
v___y_581_ = v_binderInfo_600_;
v___y_582_ = v___x_607_;
goto v___jp_576_;
}
else
{
size_t v___x_608_; size_t v___x_609_; uint8_t v___x_610_; 
v___x_608_ = lean_ptr_addr(v_body_599_);
v___x_609_ = lean_ptr_addr(v_a_604_);
v___x_610_ = lean_usize_dec_eq(v___x_608_, v___x_609_);
v___y_577_ = v_binderName_597_;
v___y_578_ = v___y_596_;
v___y_579_ = v_a_604_;
v___y_580_ = v_a_602_;
v___y_581_ = v_binderInfo_600_;
v___y_582_ = v___x_610_;
goto v___jp_576_;
}
}
else
{
lean_dec(v_a_602_);
lean_dec(v_binderName_597_);
lean_dec_ref_known(v___y_596_, 3);
lean_dec_ref(v_post_541_);
lean_dec_ref(v_pre_539_);
return v___x_603_;
}
}
else
{
lean_dec_ref_known(v___y_596_, 3);
lean_dec(v_binderName_597_);
lean_dec_ref(v_post_541_);
lean_dec_ref(v_pre_539_);
return v___x_601_;
}
}
case 6:
{
lean_object* v_binderName_611_; lean_object* v_binderType_612_; lean_object* v_body_613_; uint8_t v_binderInfo_614_; lean_object* v___x_615_; 
v_binderName_611_ = lean_ctor_get(v___y_596_, 0);
lean_inc(v_binderName_611_);
v_binderType_612_ = lean_ctor_get(v___y_596_, 1);
v_body_613_ = lean_ctor_get(v___y_596_, 2);
v_binderInfo_614_ = lean_ctor_get_uint8(v___y_596_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_612_);
lean_inc_ref(v_post_541_);
lean_inc_ref(v_pre_539_);
v___x_615_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_539_, v_post_541_, v_binderType_612_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_617_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
lean_inc_ref(v_body_613_);
lean_inc_ref(v_post_541_);
lean_inc_ref(v_pre_539_);
v___x_617_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_539_, v_post_541_, v_body_613_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; size_t v___x_619_; size_t v___x_620_; uint8_t v___x_621_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_617_, 1);
v___x_619_ = lean_ptr_addr(v_binderType_612_);
v___x_620_ = lean_ptr_addr(v_a_616_);
v___x_621_ = lean_usize_dec_eq(v___x_619_, v___x_620_);
if (v___x_621_ == 0)
{
v___y_564_ = v_binderName_611_;
v___y_565_ = v_a_618_;
v___y_566_ = v___y_596_;
v___y_567_ = v_binderInfo_614_;
v___y_568_ = v_a_616_;
v___y_569_ = v___x_621_;
goto v___jp_563_;
}
else
{
size_t v___x_622_; size_t v___x_623_; uint8_t v___x_624_; 
v___x_622_ = lean_ptr_addr(v_body_613_);
v___x_623_ = lean_ptr_addr(v_a_618_);
v___x_624_ = lean_usize_dec_eq(v___x_622_, v___x_623_);
v___y_564_ = v_binderName_611_;
v___y_565_ = v_a_618_;
v___y_566_ = v___y_596_;
v___y_567_ = v_binderInfo_614_;
v___y_568_ = v_a_616_;
v___y_569_ = v___x_624_;
goto v___jp_563_;
}
}
else
{
lean_dec(v_a_616_);
lean_dec_ref_known(v___y_596_, 3);
lean_dec(v_binderName_611_);
lean_dec_ref(v_post_541_);
lean_dec_ref(v_pre_539_);
return v___x_617_;
}
}
else
{
lean_dec_ref_known(v___y_596_, 3);
lean_dec(v_binderName_611_);
lean_dec_ref(v_post_541_);
lean_dec_ref(v_pre_539_);
return v___x_615_;
}
}
case 8:
{
lean_object* v_declName_625_; lean_object* v_type_626_; lean_object* v_value_627_; lean_object* v_body_628_; uint8_t v_nondep_629_; lean_object* v___x_630_; 
v_declName_625_ = lean_ctor_get(v___y_596_, 0);
lean_inc(v_declName_625_);
v_type_626_ = lean_ctor_get(v___y_596_, 1);
v_value_627_ = lean_ctor_get(v___y_596_, 2);
v_body_628_ = lean_ctor_get(v___y_596_, 3);
lean_inc_ref(v_body_628_);
v_nondep_629_ = lean_ctor_get_uint8(v___y_596_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_626_);
lean_inc_ref(v_post_541_);
lean_inc_ref(v_pre_539_);
v___x_630_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_539_, v_post_541_, v_type_626_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
lean_inc_ref(v_value_627_);
lean_inc_ref(v_post_541_);
lean_inc_ref(v_pre_539_);
v___x_632_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_539_, v_post_541_, v_value_627_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
lean_inc_ref(v_body_628_);
lean_inc_ref(v_post_541_);
lean_inc_ref(v_pre_539_);
v___x_634_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_539_, v_post_541_, v_body_628_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; size_t v___x_636_; size_t v___x_637_; uint8_t v___x_638_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
v___x_636_ = lean_ptr_addr(v_type_626_);
v___x_637_ = lean_ptr_addr(v_a_631_);
v___x_638_ = lean_usize_dec_eq(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
v___y_547_ = v_a_631_;
v___y_548_ = v_a_635_;
v___y_549_ = v_nondep_629_;
v___y_550_ = v_body_628_;
v___y_551_ = v___y_596_;
v___y_552_ = v_a_633_;
v___y_553_ = v_declName_625_;
v___y_554_ = v___x_638_;
goto v___jp_546_;
}
else
{
size_t v___x_639_; size_t v___x_640_; uint8_t v___x_641_; 
v___x_639_ = lean_ptr_addr(v_value_627_);
v___x_640_ = lean_ptr_addr(v_a_633_);
v___x_641_ = lean_usize_dec_eq(v___x_639_, v___x_640_);
v___y_547_ = v_a_631_;
v___y_548_ = v_a_635_;
v___y_549_ = v_nondep_629_;
v___y_550_ = v_body_628_;
v___y_551_ = v___y_596_;
v___y_552_ = v_a_633_;
v___y_553_ = v_declName_625_;
v___y_554_ = v___x_641_;
goto v___jp_546_;
}
}
else
{
lean_dec(v_a_633_);
lean_dec(v_a_631_);
lean_dec_ref(v_body_628_);
lean_dec_ref_known(v___y_596_, 4);
lean_dec(v_declName_625_);
lean_dec_ref(v_post_541_);
lean_dec_ref(v_pre_539_);
return v___x_634_;
}
}
else
{
lean_dec(v_a_631_);
lean_dec_ref(v_body_628_);
lean_dec_ref_known(v___y_596_, 4);
lean_dec(v_declName_625_);
lean_dec_ref(v_post_541_);
lean_dec_ref(v_pre_539_);
return v___x_632_;
}
}
else
{
lean_dec_ref(v_body_628_);
lean_dec_ref_known(v___y_596_, 4);
lean_dec(v_declName_625_);
lean_dec_ref(v_post_541_);
lean_dec_ref(v_pre_539_);
return v___x_630_;
}
}
case 5:
{
lean_object* v_dummy_642_; lean_object* v_nargs_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_dummy_642_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0);
v_nargs_643_ = l_Lean_Expr_getAppNumArgs(v___y_596_);
lean_inc(v_nargs_643_);
v___x_644_ = lean_mk_array(v_nargs_643_, v_dummy_642_);
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = lean_nat_sub(v_nargs_643_, v___x_645_);
lean_dec(v_nargs_643_);
v___x_647_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_539_, v_post_541_, v___y_596_, v___x_644_, v___x_646_, v___y_542_, v___y_543_, v___y_544_);
return v___x_647_;
}
case 10:
{
lean_object* v_data_648_; lean_object* v_expr_649_; lean_object* v___x_650_; 
v_data_648_ = lean_ctor_get(v___y_596_, 0);
v_expr_649_ = lean_ctor_get(v___y_596_, 1);
lean_inc_ref(v_expr_649_);
lean_inc_ref(v_post_541_);
lean_inc_ref(v_pre_539_);
v___x_650_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_539_, v_post_541_, v_expr_649_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; size_t v___x_652_; size_t v___x_653_; uint8_t v___x_654_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = lean_ptr_addr(v_expr_649_);
v___x_653_ = lean_ptr_addr(v_a_651_);
v___x_654_ = lean_usize_dec_eq(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; 
lean_inc(v_data_648_);
lean_dec_ref_known(v___y_596_, 2);
v___x_655_ = l_Lean_Expr_mdata___override(v_data_648_, v_a_651_);
v___x_656_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___x_655_, v___y_542_, v___y_543_, v___y_544_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; 
lean_dec(v_a_651_);
v___x_657_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___y_596_, v___y_542_, v___y_543_, v___y_544_);
return v___x_657_;
}
}
else
{
lean_dec_ref_known(v___y_596_, 2);
lean_dec_ref(v_post_541_);
lean_dec_ref(v_pre_539_);
return v___x_650_;
}
}
case 11:
{
lean_object* v_typeName_658_; lean_object* v_idx_659_; lean_object* v_struct_660_; lean_object* v___x_661_; 
v_typeName_658_ = lean_ctor_get(v___y_596_, 0);
v_idx_659_ = lean_ctor_get(v___y_596_, 1);
v_struct_660_ = lean_ctor_get(v___y_596_, 2);
lean_inc_ref(v_struct_660_);
lean_inc_ref(v_post_541_);
lean_inc_ref(v_pre_539_);
v___x_661_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_539_, v_post_541_, v_struct_660_, v___y_542_, v___y_543_, v___y_544_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; size_t v___x_663_; size_t v___x_664_; uint8_t v___x_665_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = lean_ptr_addr(v_struct_660_);
v___x_664_ = lean_ptr_addr(v_a_662_);
v___x_665_ = lean_usize_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_inc(v_idx_659_);
lean_inc(v_typeName_658_);
lean_dec_ref_known(v___y_596_, 3);
v___x_666_ = l_Lean_Expr_proj___override(v_typeName_658_, v_idx_659_, v_a_662_);
v___x_667_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___x_666_, v___y_542_, v___y_543_, v___y_544_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; 
lean_dec(v_a_662_);
v___x_668_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___y_596_, v___y_542_, v___y_543_, v___y_544_);
return v___x_668_;
}
}
else
{
lean_dec_ref_known(v___y_596_, 3);
lean_dec_ref(v_post_541_);
lean_dec_ref(v_pre_539_);
return v___x_661_;
}
}
default: 
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___y_596_, v___y_542_, v___y_543_, v___y_544_);
return v___x_669_;
}
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_post_541_);
lean_dec_ref(v_e_540_);
lean_dec_ref(v_pre_539_);
v_a_681_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_590_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_590_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v_post_541_);
lean_dec_ref(v_e_540_);
lean_dec_ref(v_pre_539_);
v_a_689_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_589_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_589_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
v___jp_546_:
{
if (v___y_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v___y_551_);
lean_dec_ref(v___y_550_);
v___x_555_ = l_Lean_Expr_letE___override(v___y_553_, v___y_547_, v___y_552_, v___y_548_, v___y_549_);
v___x_556_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___x_555_, v___y_542_, v___y_543_, v___y_544_);
return v___x_556_;
}
else
{
size_t v___x_557_; size_t v___x_558_; uint8_t v___x_559_; 
v___x_557_ = lean_ptr_addr(v___y_550_);
lean_dec_ref(v___y_550_);
v___x_558_ = lean_ptr_addr(v___y_548_);
v___x_559_ = lean_usize_dec_eq(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec_ref(v___y_551_);
v___x_560_ = l_Lean_Expr_letE___override(v___y_553_, v___y_547_, v___y_552_, v___y_548_, v___y_549_);
v___x_561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___x_560_, v___y_542_, v___y_543_, v___y_544_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; 
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v___y_548_);
lean_dec_ref(v___y_547_);
v___x_562_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___y_551_, v___y_542_, v___y_543_, v___y_544_);
return v___x_562_;
}
}
}
v___jp_563_:
{
if (v___y_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref(v___y_566_);
v___x_570_ = l_Lean_Expr_lam___override(v___y_564_, v___y_568_, v___y_565_, v___y_567_);
v___x_571_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___x_570_, v___y_542_, v___y_543_, v___y_544_);
return v___x_571_;
}
else
{
uint8_t v___x_572_; 
v___x_572_ = l_Lean_instBEqBinderInfo_beq(v___y_567_, v___y_567_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v___y_566_);
v___x_573_ = l_Lean_Expr_lam___override(v___y_564_, v___y_568_, v___y_565_, v___y_567_);
v___x_574_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___x_573_, v___y_542_, v___y_543_, v___y_544_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; 
lean_dec_ref(v___y_568_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
v___x_575_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___y_566_, v___y_542_, v___y_543_, v___y_544_);
return v___x_575_;
}
}
}
v___jp_576_:
{
if (v___y_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec_ref(v___y_578_);
v___x_583_ = l_Lean_Expr_forallE___override(v___y_577_, v___y_580_, v___y_579_, v___y_581_);
v___x_584_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___x_583_, v___y_542_, v___y_543_, v___y_544_);
return v___x_584_;
}
else
{
uint8_t v___x_585_; 
v___x_585_ = l_Lean_instBEqBinderInfo_beq(v___y_581_, v___y_581_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec_ref(v___y_578_);
v___x_586_ = l_Lean_Expr_forallE___override(v___y_577_, v___y_580_, v___y_579_, v___y_581_);
v___x_587_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___x_586_, v___y_542_, v___y_543_, v___y_544_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; 
lean_dec_ref(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_577_);
v___x_588_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_539_, v_post_541_, v___y_578_, v___y_542_, v___y_543_, v___y_544_);
return v___x_588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed(lean_object* v___x_697_, lean_object* v_pre_698_, lean_object* v_e_699_, lean_object* v_post_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(v___x_697_, v_pre_698_, v_e_699_, v_post_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(lean_object* v_pre_706_, lean_object* v_post_707_, lean_object* v_e_708_, lean_object* v_a_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_inc(v_a_709_);
v___x_713_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_713_, 0, lean_box(0));
lean_closure_set(v___x_713_, 1, lean_box(0));
lean_closure_set(v___x_713_, 2, v_a_709_);
v___x_714_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_box(0), v___x_713_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_746_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_746_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_746_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_746_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; 
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_a_715_, v_e_708_);
lean_dec(v_a_715_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_720_; lean_object* v___f_721_; lean_object* v___x_722_; 
lean_del_object(v___x_717_);
v___x_720_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_708_);
v___f_721_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_721_, 0, v___x_720_);
lean_closure_set(v___f_721_, 1, v_pre_706_);
lean_closure_set(v___f_721_, 2, v_e_708_);
lean_closure_set(v___f_721_, 3, v_post_707_);
v___x_722_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v___f_721_, v_a_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___f_724_; lean_object* v___x_725_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_n(v_a_723_, 2);
lean_dec_ref_known(v___x_722_, 1);
lean_inc(v_a_709_);
v___f_724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_724_, 0, v_a_709_);
lean_closure_set(v___f_724_, 1, v_e_708_);
lean_closure_set(v___f_724_, 2, v_a_723_);
v___x_725_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_box(0), v___f_724_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v___x_725_, 0);
lean_dec(v_unused_733_);
v___x_727_ = v___x_725_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_dec(v___x_725_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v_a_723_);
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_723_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v_a_723_);
v_a_734_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_725_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_725_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_dec_ref(v_e_708_);
return v___x_722_;
}
}
else
{
lean_object* v_val_742_; lean_object* v___x_744_; 
lean_dec_ref(v_e_708_);
lean_dec_ref(v_post_707_);
lean_dec_ref(v_pre_706_);
v_val_742_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v___x_719_, 1);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v_val_742_);
v___x_744_ = v___x_717_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_val_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec_ref(v_e_708_);
lean_dec_ref(v_post_707_);
lean_dec_ref(v_pre_706_);
v_a_747_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_714_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_714_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(lean_object* v_pre_755_, lean_object* v_post_756_, lean_object* v_e_757_, lean_object* v_a_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
lean_inc_ref(v_post_756_);
lean_inc(v___y_760_);
lean_inc_ref(v___y_759_);
lean_inc_ref(v_e_757_);
v___x_762_ = lean_apply_4(v_post_756_, v_e_757_, v___y_759_, v___y_760_, lean_box(0));
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_781_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_781_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_781_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_781_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
switch(lean_obj_tag(v_a_763_))
{
case 0:
{
lean_object* v_e_767_; lean_object* v___x_769_; 
lean_dec_ref(v_e_757_);
lean_dec_ref(v_post_756_);
lean_dec_ref(v_pre_755_);
v_e_767_ = lean_ctor_get(v_a_763_, 0);
lean_inc_ref(v_e_767_);
lean_dec_ref_known(v_a_763_, 1);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v_e_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_e_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
case 1:
{
lean_object* v_e_771_; lean_object* v___x_772_; 
lean_del_object(v___x_765_);
lean_dec_ref(v_e_757_);
v_e_771_ = lean_ctor_get(v_a_763_, 0);
lean_inc_ref(v_e_771_);
lean_dec_ref_known(v_a_763_, 1);
v___x_772_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_755_, v_post_756_, v_e_771_, v_a_758_, v___y_759_, v___y_760_);
return v___x_772_;
}
default: 
{
lean_object* v_e_x3f_773_; 
lean_dec_ref(v_post_756_);
lean_dec_ref(v_pre_755_);
v_e_x3f_773_ = lean_ctor_get(v_a_763_, 0);
lean_inc(v_e_x3f_773_);
lean_dec_ref_known(v_a_763_, 1);
if (lean_obj_tag(v_e_x3f_773_) == 0)
{
lean_object* v___x_775_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v_e_757_);
v___x_775_ = v___x_765_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_e_757_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
lean_object* v_val_777_; lean_object* v___x_779_; 
lean_dec_ref(v_e_757_);
v_val_777_ = lean_ctor_get(v_e_x3f_773_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v_e_x3f_773_, 1);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v_val_777_);
v___x_779_ = v___x_765_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_val_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec_ref(v_e_757_);
lean_dec_ref(v_post_756_);
lean_dec_ref(v_pre_755_);
v_a_782_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_762_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_762_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_790_, lean_object* v_post_791_, lean_object* v_e_792_, lean_object* v_a_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_790_, v_post_791_, v_e_792_, v_a_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v_a_793_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_798_, lean_object* v_post_799_, lean_object* v_sz_800_, lean_object* v_i_801_, lean_object* v_bs_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
size_t v_sz_boxed_807_; size_t v_i_boxed_808_; lean_object* v_res_809_; 
v_sz_boxed_807_ = lean_unbox_usize(v_sz_800_);
lean_dec(v_sz_800_);
v_i_boxed_808_ = lean_unbox_usize(v_i_801_);
lean_dec(v_i_801_);
v_res_809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_798_, v_post_799_, v_sz_boxed_807_, v_i_boxed_808_, v_bs_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_810_, lean_object* v_post_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_810_, v_post_811_, v_x_812_, v_x_813_, v_x_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___boxed(lean_object* v_pre_820_, lean_object* v_post_821_, lean_object* v_e_822_, lean_object* v_a_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_820_, v_post_821_, v_e_822_, v_a_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v_a_823_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_object* v_00_u03b1_828_, lean_object* v_x_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_apply_1(v_x_829_, lean_box(0));
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0___boxed(lean_object* v_00_u03b1_835_, lean_object* v_x_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(v_00_u03b1_835_, v_x_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_840_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0(void){
_start:
{
lean_object* v_cellCount_841_; lean_object* v___x_842_; 
v_cellCount_841_ = lean_unsigned_to_nat(16u);
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_841_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1(void){
_start:
{
lean_object* v_cellCount_843_; lean_object* v___x_844_; 
v_cellCount_843_ = lean_unsigned_to_nat(16u);
v___x_844_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_843_);
return v___x_844_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_845_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1);
v___x_846_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0);
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v___x_846_);
lean_ctor_set(v___x_848_, 2, v___x_845_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__3(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2);
v___x_850_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_850_, 0, lean_box(0));
lean_closure_set(v___x_850_, 1, lean_box(0));
lean_closure_set(v___x_850_, 2, v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(lean_object* v_input_851_, lean_object* v_pre_852_, lean_object* v_post_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v_a_859_; lean_object* v___x_860_; 
v___x_857_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__3, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__3_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__3);
v___x_858_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_box(0), v___x_857_, v___y_854_, v___y_855_);
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_852_, v_post_853_, v_input_851_, v_a_859_, v___y_854_, v___y_855_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v___x_862_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_862_, 0, lean_box(0));
lean_closure_set(v___x_862_, 1, lean_box(0));
lean_closure_set(v___x_862_, 2, v_a_859_);
v___x_863_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_box(0), v___x_862_, v___y_854_, v___y_855_);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v___x_863_, 0);
lean_dec(v_unused_871_);
v___x_865_ = v___x_863_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_dec(v___x_863_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v_a_861_);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_861_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_dec(v_a_859_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___boxed(lean_object* v_input_872_, lean_object* v_pre_873_, lean_object* v_post_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(v_input_872_, v_pre_873_, v_post_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand(lean_object* v_e_880_, lean_object* v_p_881_, uint8_t v_allowOpaque_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___x_889_; 
v___x_886_ = lean_box(v_allowOpaque_882_);
v___f_887_ = lean_alloc_closure((void*)(l_Lean_Meta_deltaExpand___lam__0___boxed), 6, 2);
lean_closure_set(v___f_887_, 0, v_p_881_);
lean_closure_set(v___f_887_, 1, v___x_886_);
v___f_888_ = ((lean_object*)(l_Lean_Meta_deltaExpand___closed__0));
v___x_889_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(v_e_880_, v___f_887_, v___f_888_, v_a_883_, v_a_884_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___boxed(lean_object* v_e_890_, lean_object* v_p_891_, lean_object* v_allowOpaque_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
uint8_t v_allowOpaque_boxed_896_; lean_object* v_res_897_; 
v_allowOpaque_boxed_896_ = lean_unbox(v_allowOpaque_892_);
v_res_897_ = l_Lean_Meta_deltaExpand(v_e_890_, v_p_891_, v_allowOpaque_boxed_896_, v_a_893_, v_a_894_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_898_, lean_object* v_m_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_m_899_, v_a_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_902_, lean_object* v_m_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(v_00_u03b2_902_, v_m_903_, v_a_904_);
lean_dec_ref(v_a_904_);
lean_dec_ref(v_m_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_906_, lean_object* v_ref_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_907_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_912_, lean_object* v_ref_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_912_, v_ref_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_928_, lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_929_, v___y_930_, v___y_931_, v___y_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_935_, lean_object* v_x_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(v_00_u03b1_935_, v_x_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_942_, lean_object* v_m_943_, lean_object* v_query_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v_m_943_, v_query_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b2_946_, lean_object* v_m_947_, lean_object* v_query_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6(v_00_u03b2_946_, v_m_947_, v_query_948_);
lean_dec_ref(v_query_948_);
lean_dec_ref(v_m_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7(lean_object* v_00_u03b2_950_, lean_object* v_m_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7___redArg(v_m_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b2_953_, lean_object* v_m_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7(v_00_u03b2_953_, v_m_954_);
lean_dec_ref(v_m_954_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_956_, lean_object* v_m_957_, lean_object* v_query_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_m_957_, v_query_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_960_, lean_object* v_m_961_, lean_object* v_query_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_960_, v_m_961_, v_query_962_);
lean_dec_ref(v_query_962_);
lean_dec_ref(v_m_961_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_964_, lean_object* v_m_965_, lean_object* v_query_966_, lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_m_965_, v_query_966_, v_x_967_, v_x_968_, v_x_969_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_972_, lean_object* v_m_973_, lean_object* v_query_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_, lean_object* v_x_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_972_, v_m_973_, v_query_974_, v_x_975_, v_x_976_, v_x_977_, v_x_978_);
lean_dec_ref(v_query_974_);
lean_dec_ref(v_m_973_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12(lean_object* v_00_u03b2_980_, lean_object* v_init_981_, lean_object* v_b_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12___redArg(v_init_981_, v_b_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12___boxed(lean_object* v_00_u03b2_984_, lean_object* v_init_985_, lean_object* v_b_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12(v_00_u03b2_984_, v_init_985_, v_b_986_);
lean_dec_ref(v_b_986_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13(lean_object* v_00_u03b2_988_, lean_object* v_b_989_, lean_object* v_acc_990_, lean_object* v_i_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13___redArg(v_b_989_, v_acc_990_, v_i_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13___boxed(lean_object* v_00_u03b2_993_, lean_object* v_b_994_, lean_object* v_acc_995_, lean_object* v_i_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__7_spec__12_spec__13(v_00_u03b2_993_, v_b_994_, v_acc_995_, v_i_996_);
lean_dec_ref(v_b_994_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(lean_object* v_mvarId_998_, lean_object* v_x_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_998_, v_x_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_a_1014_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1005_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1005_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg___boxed(lean_object* v_mvarId_1022_, lean_object* v_x_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_1022_, v_x_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(lean_object* v_00_u03b1_1030_, lean_object* v_mvarId_1031_, lean_object* v_x_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_1031_, v_x_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___boxed(lean_object* v_00_u03b1_1039_, lean_object* v_mvarId_1040_, lean_object* v_x_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(v_00_u03b1_1039_, v_mvarId_1040_, v_x_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lam__0(lean_object* v_mvarId_1048_, lean_object* v___x_1049_, lean_object* v_p_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
lean_inc(v_mvarId_1048_);
v___x_1056_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1048_, v___x_1049_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1057_; 
lean_dec_ref_known(v___x_1056_, 1);
lean_inc(v_mvarId_1048_);
v___x_1057_ = l_Lean_MVarId_getType(v_mvarId_1048_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v___x_1057_, 1);
v___x_1059_ = 0;
v___x_1060_ = l_Lean_Meta_deltaExpand(v_a_1058_, v_p_1050_, v___x_1059_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
v___x_1062_ = l_Lean_MVarId_change(v_mvarId_1048_, v_a_1061_, v___x_1059_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
return v___x_1062_;
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_mvarId_1048_);
v_a_1063_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1060_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1060_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec_ref(v_p_1050_);
lean_dec(v_mvarId_1048_);
v_a_1071_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1057_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1057_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v_p_1050_);
lean_dec(v_mvarId_1048_);
v_a_1079_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1056_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1056_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lam__0___boxed(lean_object* v_mvarId_1087_, lean_object* v___x_1088_, lean_object* v_p_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_MVarId_deltaTarget___lam__0(v_mvarId_1087_, v___x_1088_, v_p_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget(lean_object* v_mvarId_1099_, lean_object* v_p_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; 
v___x_1106_ = ((lean_object*)(l_Lean_MVarId_deltaTarget___closed__1));
lean_inc(v_mvarId_1099_);
v___f_1107_ = lean_alloc_closure((void*)(l_Lean_MVarId_deltaTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1107_, 0, v_mvarId_1099_);
lean_closure_set(v___f_1107_, 1, v___x_1106_);
lean_closure_set(v___f_1107_, 2, v_p_1100_);
v___x_1108_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_1099_, v___f_1107_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___boxed(lean_object* v_mvarId_1109_, lean_object* v_p_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_MVarId_deltaTarget(v_mvarId_1109_, v_p_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lam__0(lean_object* v_mvarId_1117_, lean_object* v___x_1118_, lean_object* v_fvarId_1119_, lean_object* v_p_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; 
lean_inc(v_mvarId_1117_);
v___x_1126_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1117_, v___x_1118_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; 
lean_dec_ref_known(v___x_1126_, 1);
lean_inc(v_fvarId_1119_);
v___x_1127_ = l_Lean_FVarId_getType___redArg(v_fvarId_1119_, v___y_1121_, v___y_1123_, v___y_1124_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = 0;
v___x_1130_ = l_Lean_Meta_deltaExpand(v_a_1128_, v_p_1120_, v___x_1129_, v___y_1123_, v___y_1124_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = l_Lean_MVarId_changeLocalDecl(v_mvarId_1117_, v_fvarId_1119_, v_a_1131_, v___x_1129_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1132_;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_fvarId_1119_);
lean_dec(v_mvarId_1117_);
v_a_1133_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1130_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1130_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v_p_1120_);
lean_dec(v_fvarId_1119_);
lean_dec(v_mvarId_1117_);
v_a_1141_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1127_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1127_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec_ref(v_p_1120_);
lean_dec(v_fvarId_1119_);
lean_dec(v_mvarId_1117_);
v_a_1149_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1126_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1126_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lam__0___boxed(lean_object* v_mvarId_1157_, lean_object* v___x_1158_, lean_object* v_fvarId_1159_, lean_object* v_p_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_MVarId_deltaLocalDecl___lam__0(v_mvarId_1157_, v___x_1158_, v_fvarId_1159_, v_p_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl(lean_object* v_mvarId_1167_, lean_object* v_fvarId_1168_, lean_object* v_p_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; 
v___x_1175_ = ((lean_object*)(l_Lean_MVarId_deltaTarget___closed__1));
lean_inc(v_mvarId_1167_);
v___f_1176_ = lean_alloc_closure((void*)(l_Lean_MVarId_deltaLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1176_, 0, v_mvarId_1167_);
lean_closure_set(v___f_1176_, 1, v___x_1175_);
lean_closure_set(v___f_1176_, 2, v_fvarId_1168_);
lean_closure_set(v___f_1176_, 3, v_p_1169_);
v___x_1177_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_1167_, v___f_1176_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___boxed(lean_object* v_mvarId_1178_, lean_object* v_fvarId_1179_, lean_object* v_p_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_MVarId_deltaLocalDecl(v_mvarId_1178_, v_fvarId_1179_, v_p_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
return v_res_1186_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
