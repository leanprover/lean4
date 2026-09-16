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
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(lean_object* v_a_165_, lean_object* v_b_166_, lean_object* v_x_167_){
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
v___x_175_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(v_a_165_, v_b_166_, v_tail_170_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(lean_object* v_x_183_, lean_object* v_x_184_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(lean_object* v_i_211_, lean_object* v_source_212_, lean_object* v_target_213_){
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
v_target_219_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_213_, v_es_216_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_data_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_nbuckets_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_224_ = lean_array_get_size(v_data_223_);
v___x_225_ = lean_unsigned_to_nat(2u);
v_nbuckets_226_ = lean_nat_mul(v___x_224_, v___x_225_);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_box(0);
v___x_229_ = lean_mk_array(v_nbuckets_226_, v___x_228_);
v___x_230_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_227_, v_data_223_, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_a_231_, lean_object* v_x_232_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg___boxed(lean_object* v_a_238_, lean_object* v_x_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_a_238_, v_x_239_);
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
v___x_264_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_a_243_, v_bkt_263_);
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
v_val_275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_268_);
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
v___x_284_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(v_a_243_, v_b_244_, v_bkt_263_);
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
v___x_296_ = lean_st_ref_put(v_a_290_, v___x_295_);
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
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_box(0);
v___x_304_ = l_Lean_interruptExceptionId;
v___x_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg(){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg___boxed(lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
return v_res_310_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = l_Lean_maxRecDepthErrorMessage;
v___x_317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_319_ = l_Lean_MessageData_ofFormat(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_321_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_322_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_323_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v_ref_323_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(lean_object* v_x_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___y_337_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; uint8_t v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; uint8_t v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v_fileName_367_; lean_object* v_fileMap_368_; lean_object* v_options_369_; lean_object* v_currRecDepth_370_; lean_object* v_maxRecDepth_371_; lean_object* v_ref_372_; lean_object* v_currNamespace_373_; lean_object* v_openDecls_374_; lean_object* v_initHeartbeats_375_; lean_object* v_maxHeartbeats_376_; lean_object* v_quotContext_377_; lean_object* v_currMacroScope_378_; uint8_t v_diag_379_; lean_object* v_cancelTk_x3f_380_; uint8_t v_suppressElabErrors_381_; lean_object* v_inheritedTraceOptions_382_; 
v_fileName_367_ = lean_ctor_get(v___y_333_, 0);
v_fileMap_368_ = lean_ctor_get(v___y_333_, 1);
v_options_369_ = lean_ctor_get(v___y_333_, 2);
v_currRecDepth_370_ = lean_ctor_get(v___y_333_, 3);
v_maxRecDepth_371_ = lean_ctor_get(v___y_333_, 4);
v_ref_372_ = lean_ctor_get(v___y_333_, 5);
v_currNamespace_373_ = lean_ctor_get(v___y_333_, 6);
v_openDecls_374_ = lean_ctor_get(v___y_333_, 7);
v_initHeartbeats_375_ = lean_ctor_get(v___y_333_, 8);
v_maxHeartbeats_376_ = lean_ctor_get(v___y_333_, 9);
v_quotContext_377_ = lean_ctor_get(v___y_333_, 10);
v_currMacroScope_378_ = lean_ctor_get(v___y_333_, 11);
v_diag_379_ = lean_ctor_get_uint8(v___y_333_, sizeof(void*)*14);
v_cancelTk_x3f_380_ = lean_ctor_get(v___y_333_, 12);
v_suppressElabErrors_381_ = lean_ctor_get_uint8(v___y_333_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_382_ = lean_ctor_get(v___y_333_, 13);
if (lean_obj_tag(v_cancelTk_x3f_380_) == 1)
{
lean_object* v_val_388_; uint8_t v___x_389_; 
v_val_388_ = lean_ctor_get(v_cancelTk_x3f_380_, 0);
v___x_389_ = l_IO_CancelToken_isSet(v_val_388_);
if (v___x_389_ == 0)
{
goto v___jp_383_;
}
else
{
lean_object* v___x_390_; lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec_ref(v_x_331_);
v___x_390_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
goto v___jp_383_;
}
v___jp_336_:
{
if (lean_obj_tag(v___y_337_) == 0)
{
return v___y_337_;
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
v_a_338_ = lean_ctor_get(v___y_337_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___y_337_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___y_337_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___y_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
v___jp_346_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = lean_nat_add(v___y_358_, v___x_363_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_347_);
lean_inc(v___y_352_);
lean_inc(v___y_351_);
lean_inc(v___y_349_);
lean_inc(v___y_350_);
lean_inc(v___y_362_);
lean_inc(v___y_348_);
lean_inc(v___y_361_);
lean_inc_ref(v___y_355_);
lean_inc_ref(v___y_360_);
lean_inc_ref(v___y_359_);
v___x_365_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_365_, 0, v___y_359_);
lean_ctor_set(v___x_365_, 1, v___y_360_);
lean_ctor_set(v___x_365_, 2, v___y_355_);
lean_ctor_set(v___x_365_, 3, v___x_364_);
lean_ctor_set(v___x_365_, 4, v___y_361_);
lean_ctor_set(v___x_365_, 5, v___y_354_);
lean_ctor_set(v___x_365_, 6, v___y_348_);
lean_ctor_set(v___x_365_, 7, v___y_362_);
lean_ctor_set(v___x_365_, 8, v___y_350_);
lean_ctor_set(v___x_365_, 9, v___y_349_);
lean_ctor_set(v___x_365_, 10, v___y_351_);
lean_ctor_set(v___x_365_, 11, v___y_352_);
lean_ctor_set(v___x_365_, 12, v___y_347_);
lean_ctor_set(v___x_365_, 13, v___y_357_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*14, v___y_356_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*14 + 1, v___y_353_);
lean_inc(v___y_334_);
lean_inc(v___y_332_);
v___x_366_ = lean_apply_4(v_x_331_, v___y_332_, v___x_365_, v___y_334_, lean_box(0));
v___y_337_ = v___x_366_;
goto v___jp_336_;
}
v___jp_383_:
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_nat_dec_eq(v_maxRecDepth_371_, v___x_384_);
if (v___x_385_ == 0)
{
uint8_t v___x_386_; 
v___x_386_ = lean_nat_dec_eq(v_currRecDepth_370_, v_maxRecDepth_371_);
if (v___x_386_ == 0)
{
lean_inc(v_ref_372_);
v___y_347_ = v_cancelTk_x3f_380_;
v___y_348_ = v_currNamespace_373_;
v___y_349_ = v_maxHeartbeats_376_;
v___y_350_ = v_initHeartbeats_375_;
v___y_351_ = v_quotContext_377_;
v___y_352_ = v_currMacroScope_378_;
v___y_353_ = v_suppressElabErrors_381_;
v___y_354_ = v_ref_372_;
v___y_355_ = v_options_369_;
v___y_356_ = v_diag_379_;
v___y_357_ = v_inheritedTraceOptions_382_;
v___y_358_ = v_currRecDepth_370_;
v___y_359_ = v_fileName_367_;
v___y_360_ = v_fileMap_368_;
v___y_361_ = v_maxRecDepth_371_;
v___y_362_ = v_openDecls_374_;
goto v___jp_346_;
}
else
{
lean_object* v___x_387_; 
lean_dec_ref(v_x_331_);
lean_inc(v_ref_372_);
v___x_387_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_372_);
v___y_337_ = v___x_387_;
goto v___jp_336_;
}
}
else
{
lean_inc(v_ref_372_);
v___y_347_ = v_cancelTk_x3f_380_;
v___y_348_ = v_currNamespace_373_;
v___y_349_ = v_maxHeartbeats_376_;
v___y_350_ = v_initHeartbeats_375_;
v___y_351_ = v_quotContext_377_;
v___y_352_ = v_currMacroScope_378_;
v___y_353_ = v_suppressElabErrors_381_;
v___y_354_ = v_ref_372_;
v___y_355_ = v_options_369_;
v___y_356_ = v_diag_379_;
v___y_357_ = v_inheritedTraceOptions_382_;
v___y_358_ = v_currRecDepth_370_;
v___y_359_ = v_fileName_367_;
v___y_360_ = v_fileMap_368_;
v___y_361_ = v_maxRecDepth_371_;
v___y_362_ = v_openDecls_374_;
goto v___jp_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
return v_res_404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_406_; lean_object* v_dummy_407_; 
v___x_406_ = lean_box(0);
v_dummy_407_ = l_Lean_Expr_sort___override(v___x_406_);
return v_dummy_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(lean_object* v_pre_408_, lean_object* v_post_409_, size_t v_sz_410_, size_t v_i_411_, lean_object* v_bs_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_lt(v_i_411_, v_sz_410_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
lean_dec_ref(v_post_409_);
lean_dec_ref(v_pre_408_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v_bs_412_);
return v___x_418_;
}
else
{
lean_object* v_v_419_; lean_object* v___x_420_; 
v_v_419_ = lean_array_uget_borrowed(v_bs_412_, v_i_411_);
lean_inc(v_v_419_);
lean_inc_ref(v_post_409_);
lean_inc_ref(v_pre_408_);
v___x_420_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_408_, v_post_409_, v_v_419_, v___y_413_, v___y_414_, v___y_415_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_422_; lean_object* v_bs_x27_423_; size_t v___x_424_; size_t v___x_425_; lean_object* v___x_426_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
v___x_422_ = lean_unsigned_to_nat(0u);
v_bs_x27_423_ = lean_array_uset(v_bs_412_, v_i_411_, v___x_422_);
v___x_424_ = ((size_t)1ULL);
v___x_425_ = lean_usize_add(v_i_411_, v___x_424_);
v___x_426_ = lean_array_uset(v_bs_x27_423_, v_i_411_, v_a_421_);
v_i_411_ = v___x_425_;
v_bs_412_ = v___x_426_;
goto _start;
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v_bs_412_);
lean_dec_ref(v_post_409_);
lean_dec_ref(v_pre_408_);
v_a_428_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_420_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_420_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(lean_object* v_pre_436_, lean_object* v_post_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
if (lean_obj_tag(v_x_438_) == 5)
{
lean_object* v_fn_445_; lean_object* v_arg_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_fn_445_ = lean_ctor_get(v_x_438_, 0);
lean_inc_ref(v_fn_445_);
v_arg_446_ = lean_ctor_get(v_x_438_, 1);
lean_inc_ref(v_arg_446_);
lean_dec_ref_known(v_x_438_, 2);
v___x_447_ = lean_array_set(v_x_439_, v_x_440_, v_arg_446_);
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = lean_nat_sub(v_x_440_, v___x_448_);
lean_dec(v_x_440_);
v_x_438_ = v_fn_445_;
v_x_439_ = v___x_447_;
v_x_440_ = v___x_449_;
goto _start;
}
else
{
lean_object* v___x_451_; 
lean_dec(v_x_440_);
lean_inc_ref(v_post_437_);
lean_inc_ref(v_pre_436_);
v___x_451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_436_, v_post_437_, v_x_438_, v___y_441_, v___y_442_, v___y_443_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; size_t v_sz_453_; size_t v___x_454_; lean_object* v___x_455_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
v_sz_453_ = lean_array_size(v_x_439_);
v___x_454_ = ((size_t)0ULL);
lean_inc_ref(v_post_437_);
lean_inc_ref(v_pre_436_);
v___x_455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_436_, v_post_437_, v_sz_453_, v___x_454_, v_x_439_, v___y_441_, v___y_442_, v___y_443_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_457_ = l_Lean_mkAppN(v_a_452_, v_a_456_);
lean_dec(v_a_456_);
v___x_458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_436_, v_post_437_, v___x_457_, v___y_441_, v___y_442_, v___y_443_);
return v___x_458_;
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_dec(v_a_452_);
lean_dec_ref(v_post_437_);
lean_dec_ref(v_pre_436_);
v_a_459_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_455_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_455_);
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
lean_dec_ref(v_x_439_);
lean_dec_ref(v_post_437_);
lean_dec_ref(v_pre_436_);
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(lean_object* v___x_467_, lean_object* v_pre_468_, lean_object* v_e_469_, lean_object* v_post_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Core_checkSystem(v___x_467_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v___x_476_; 
lean_dec_ref_known(v___x_475_, 1);
lean_inc_ref(v_pre_468_);
lean_inc(v___y_473_);
lean_inc_ref(v___y_472_);
lean_inc_ref(v_e_469_);
v___x_476_ = lean_apply_4(v_pre_468_, v_e_469_, v___y_472_, v___y_473_, lean_box(0));
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_592_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_592_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_592_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_592_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___y_482_; 
switch(lean_obj_tag(v_a_477_))
{
case 0:
{
lean_object* v_e_582_; lean_object* v___x_584_; 
lean_dec_ref(v_post_470_);
lean_dec_ref(v_e_469_);
lean_dec_ref(v_pre_468_);
v_e_582_ = lean_ctor_get(v_a_477_, 0);
lean_inc_ref(v_e_582_);
lean_dec_ref_known(v_a_477_, 1);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v_e_582_);
v___x_584_ = v___x_479_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_e_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
case 1:
{
lean_object* v_e_586_; lean_object* v___x_587_; 
lean_del_object(v___x_479_);
lean_dec_ref(v_e_469_);
v_e_586_ = lean_ctor_get(v_a_477_, 0);
lean_inc_ref(v_e_586_);
lean_dec_ref_known(v_a_477_, 1);
lean_inc_ref(v_post_470_);
lean_inc_ref(v_pre_468_);
v___x_587_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_468_, v_post_470_, v_e_586_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v_a_588_, v___y_471_, v___y_472_, v___y_473_);
return v___x_589_;
}
else
{
lean_dec_ref(v_post_470_);
lean_dec_ref(v_pre_468_);
return v___x_587_;
}
}
default: 
{
lean_object* v_e_x3f_590_; 
lean_del_object(v___x_479_);
v_e_x3f_590_ = lean_ctor_get(v_a_477_, 0);
lean_inc(v_e_x3f_590_);
lean_dec_ref_known(v_a_477_, 1);
if (lean_obj_tag(v_e_x3f_590_) == 0)
{
v___y_482_ = v_e_469_;
goto v___jp_481_;
}
else
{
lean_object* v_val_591_; 
lean_dec_ref(v_e_469_);
v_val_591_ = lean_ctor_get(v_e_x3f_590_, 0);
lean_inc(v_val_591_);
lean_dec_ref_known(v_e_x3f_590_, 1);
v___y_482_ = v_val_591_;
goto v___jp_481_;
}
}
}
v___jp_481_:
{
switch(lean_obj_tag(v___y_482_))
{
case 7:
{
lean_object* v_binderName_483_; lean_object* v_binderType_484_; lean_object* v_body_485_; uint8_t v_binderInfo_486_; lean_object* v___x_487_; 
v_binderName_483_ = lean_ctor_get(v___y_482_, 0);
v_binderType_484_ = lean_ctor_get(v___y_482_, 1);
v_body_485_ = lean_ctor_get(v___y_482_, 2);
v_binderInfo_486_ = lean_ctor_get_uint8(v___y_482_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_484_);
lean_inc_ref(v_post_470_);
lean_inc_ref(v_pre_468_);
v___x_487_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_468_, v_post_470_, v_binderType_484_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_489_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
lean_inc_ref(v_body_485_);
lean_inc_ref(v_post_470_);
lean_inc_ref(v_pre_468_);
v___x_489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_468_, v_post_470_, v_body_485_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; size_t v___x_491_; size_t v___x_492_; uint8_t v___x_493_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v___x_491_ = lean_ptr_addr(v_binderType_484_);
v___x_492_ = lean_ptr_addr(v_a_488_);
v___x_493_ = lean_usize_dec_eq(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_inc(v_binderName_483_);
lean_dec_ref_known(v___y_482_, 3);
v___x_494_ = l_Lean_Expr_forallE___override(v_binderName_483_, v_a_488_, v_a_490_, v_binderInfo_486_);
v___x_495_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___x_494_, v___y_471_, v___y_472_, v___y_473_);
return v___x_495_;
}
else
{
size_t v___x_496_; size_t v___x_497_; uint8_t v___x_498_; 
v___x_496_ = lean_ptr_addr(v_body_485_);
v___x_497_ = lean_ptr_addr(v_a_490_);
v___x_498_ = lean_usize_dec_eq(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_inc(v_binderName_483_);
lean_dec_ref_known(v___y_482_, 3);
v___x_499_ = l_Lean_Expr_forallE___override(v_binderName_483_, v_a_488_, v_a_490_, v_binderInfo_486_);
v___x_500_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___x_499_, v___y_471_, v___y_472_, v___y_473_);
return v___x_500_;
}
else
{
uint8_t v___x_501_; 
v___x_501_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_486_, v_binderInfo_486_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_inc(v_binderName_483_);
lean_dec_ref_known(v___y_482_, 3);
v___x_502_ = l_Lean_Expr_forallE___override(v_binderName_483_, v_a_488_, v_a_490_, v_binderInfo_486_);
v___x_503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___x_502_, v___y_471_, v___y_472_, v___y_473_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; 
lean_dec(v_a_490_);
lean_dec(v_a_488_);
v___x_504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___y_482_, v___y_471_, v___y_472_, v___y_473_);
return v___x_504_;
}
}
}
}
else
{
lean_dec(v_a_488_);
lean_dec_ref_known(v___y_482_, 3);
lean_dec_ref(v_post_470_);
lean_dec_ref(v_pre_468_);
return v___x_489_;
}
}
else
{
lean_dec_ref_known(v___y_482_, 3);
lean_dec_ref(v_post_470_);
lean_dec_ref(v_pre_468_);
return v___x_487_;
}
}
case 6:
{
lean_object* v_binderName_505_; lean_object* v_binderType_506_; lean_object* v_body_507_; uint8_t v_binderInfo_508_; lean_object* v___x_509_; 
v_binderName_505_ = lean_ctor_get(v___y_482_, 0);
v_binderType_506_ = lean_ctor_get(v___y_482_, 1);
v_body_507_ = lean_ctor_get(v___y_482_, 2);
v_binderInfo_508_ = lean_ctor_get_uint8(v___y_482_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_506_);
lean_inc_ref(v_post_470_);
lean_inc_ref(v_pre_468_);
v___x_509_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_468_, v_post_470_, v_binderType_506_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
lean_inc_ref(v_body_507_);
lean_inc_ref(v_post_470_);
lean_inc_ref(v_pre_468_);
v___x_511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_468_, v_post_470_, v_body_507_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = lean_ptr_addr(v_binderType_506_);
v___x_514_ = lean_ptr_addr(v_a_510_);
v___x_515_ = lean_usize_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_inc(v_binderName_505_);
lean_dec_ref_known(v___y_482_, 3);
v___x_516_ = l_Lean_Expr_lam___override(v_binderName_505_, v_a_510_, v_a_512_, v_binderInfo_508_);
v___x_517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___x_516_, v___y_471_, v___y_472_, v___y_473_);
return v___x_517_;
}
else
{
size_t v___x_518_; size_t v___x_519_; uint8_t v___x_520_; 
v___x_518_ = lean_ptr_addr(v_body_507_);
v___x_519_ = lean_ptr_addr(v_a_512_);
v___x_520_ = lean_usize_dec_eq(v___x_518_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_inc(v_binderName_505_);
lean_dec_ref_known(v___y_482_, 3);
v___x_521_ = l_Lean_Expr_lam___override(v_binderName_505_, v_a_510_, v_a_512_, v_binderInfo_508_);
v___x_522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___x_521_, v___y_471_, v___y_472_, v___y_473_);
return v___x_522_;
}
else
{
uint8_t v___x_523_; 
v___x_523_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_508_, v_binderInfo_508_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_inc(v_binderName_505_);
lean_dec_ref_known(v___y_482_, 3);
v___x_524_ = l_Lean_Expr_lam___override(v_binderName_505_, v_a_510_, v_a_512_, v_binderInfo_508_);
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___x_524_, v___y_471_, v___y_472_, v___y_473_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; 
lean_dec(v_a_512_);
lean_dec(v_a_510_);
v___x_526_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___y_482_, v___y_471_, v___y_472_, v___y_473_);
return v___x_526_;
}
}
}
}
else
{
lean_dec(v_a_510_);
lean_dec_ref_known(v___y_482_, 3);
lean_dec_ref(v_post_470_);
lean_dec_ref(v_pre_468_);
return v___x_511_;
}
}
else
{
lean_dec_ref_known(v___y_482_, 3);
lean_dec_ref(v_post_470_);
lean_dec_ref(v_pre_468_);
return v___x_509_;
}
}
case 8:
{
lean_object* v_declName_527_; lean_object* v_type_528_; lean_object* v_value_529_; lean_object* v_body_530_; uint8_t v_nondep_531_; lean_object* v___x_532_; 
v_declName_527_ = lean_ctor_get(v___y_482_, 0);
v_type_528_ = lean_ctor_get(v___y_482_, 1);
v_value_529_ = lean_ctor_get(v___y_482_, 2);
v_body_530_ = lean_ctor_get(v___y_482_, 3);
v_nondep_531_ = lean_ctor_get_uint8(v___y_482_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_528_);
lean_inc_ref(v_post_470_);
lean_inc_ref(v_pre_468_);
v___x_532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_468_, v_post_470_, v_type_528_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
lean_inc_ref(v_value_529_);
lean_inc_ref(v_post_470_);
lean_inc_ref(v_pre_468_);
v___x_534_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_468_, v_post_470_, v_value_529_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
lean_inc_ref(v_body_530_);
lean_inc_ref(v_post_470_);
lean_inc_ref(v_pre_468_);
v___x_536_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_468_, v_post_470_, v_body_530_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; size_t v___x_538_; size_t v___x_539_; uint8_t v___x_540_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v___x_536_, 1);
v___x_538_ = lean_ptr_addr(v_type_528_);
v___x_539_ = lean_ptr_addr(v_a_533_);
v___x_540_ = lean_usize_dec_eq(v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_inc(v_declName_527_);
lean_dec_ref_known(v___y_482_, 4);
v___x_541_ = l_Lean_Expr_letE___override(v_declName_527_, v_a_533_, v_a_535_, v_a_537_, v_nondep_531_);
v___x_542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___x_541_, v___y_471_, v___y_472_, v___y_473_);
return v___x_542_;
}
else
{
size_t v___x_543_; size_t v___x_544_; uint8_t v___x_545_; 
v___x_543_ = lean_ptr_addr(v_value_529_);
v___x_544_ = lean_ptr_addr(v_a_535_);
v___x_545_ = lean_usize_dec_eq(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_inc(v_declName_527_);
lean_dec_ref_known(v___y_482_, 4);
v___x_546_ = l_Lean_Expr_letE___override(v_declName_527_, v_a_533_, v_a_535_, v_a_537_, v_nondep_531_);
v___x_547_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___x_546_, v___y_471_, v___y_472_, v___y_473_);
return v___x_547_;
}
else
{
size_t v___x_548_; size_t v___x_549_; uint8_t v___x_550_; 
v___x_548_ = lean_ptr_addr(v_body_530_);
v___x_549_ = lean_ptr_addr(v_a_537_);
v___x_550_ = lean_usize_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
lean_inc(v_declName_527_);
lean_dec_ref_known(v___y_482_, 4);
v___x_551_ = l_Lean_Expr_letE___override(v_declName_527_, v_a_533_, v_a_535_, v_a_537_, v_nondep_531_);
v___x_552_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___x_551_, v___y_471_, v___y_472_, v___y_473_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; 
lean_dec(v_a_537_);
lean_dec(v_a_535_);
lean_dec(v_a_533_);
v___x_553_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___y_482_, v___y_471_, v___y_472_, v___y_473_);
return v___x_553_;
}
}
}
}
else
{
lean_dec(v_a_535_);
lean_dec(v_a_533_);
lean_dec_ref_known(v___y_482_, 4);
lean_dec_ref(v_post_470_);
lean_dec_ref(v_pre_468_);
return v___x_536_;
}
}
else
{
lean_dec(v_a_533_);
lean_dec_ref_known(v___y_482_, 4);
lean_dec_ref(v_post_470_);
lean_dec_ref(v_pre_468_);
return v___x_534_;
}
}
else
{
lean_dec_ref_known(v___y_482_, 4);
lean_dec_ref(v_post_470_);
lean_dec_ref(v_pre_468_);
return v___x_532_;
}
}
case 5:
{
lean_object* v_dummy_554_; lean_object* v_nargs_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_dummy_554_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___closed__0);
v_nargs_555_ = l_Lean_Expr_getAppNumArgs(v___y_482_);
lean_inc(v_nargs_555_);
v___x_556_ = lean_mk_array(v_nargs_555_, v_dummy_554_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_sub(v_nargs_555_, v___x_557_);
lean_dec(v_nargs_555_);
v___x_559_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_468_, v_post_470_, v___y_482_, v___x_556_, v___x_558_, v___y_471_, v___y_472_, v___y_473_);
return v___x_559_;
}
case 10:
{
lean_object* v_data_560_; lean_object* v_expr_561_; lean_object* v___x_562_; 
v_data_560_ = lean_ctor_get(v___y_482_, 0);
v_expr_561_ = lean_ctor_get(v___y_482_, 1);
lean_inc_ref(v_expr_561_);
lean_inc_ref(v_post_470_);
lean_inc_ref(v_pre_468_);
v___x_562_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_468_, v_post_470_, v_expr_561_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; size_t v___x_564_; size_t v___x_565_; uint8_t v___x_566_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
v___x_564_ = lean_ptr_addr(v_expr_561_);
v___x_565_ = lean_ptr_addr(v_a_563_);
v___x_566_ = lean_usize_dec_eq(v___x_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_inc(v_data_560_);
lean_dec_ref_known(v___y_482_, 2);
v___x_567_ = l_Lean_Expr_mdata___override(v_data_560_, v_a_563_);
v___x_568_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___x_567_, v___y_471_, v___y_472_, v___y_473_);
return v___x_568_;
}
else
{
lean_object* v___x_569_; 
lean_dec(v_a_563_);
v___x_569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___y_482_, v___y_471_, v___y_472_, v___y_473_);
return v___x_569_;
}
}
else
{
lean_dec_ref_known(v___y_482_, 2);
lean_dec_ref(v_post_470_);
lean_dec_ref(v_pre_468_);
return v___x_562_;
}
}
case 11:
{
lean_object* v_typeName_570_; lean_object* v_idx_571_; lean_object* v_struct_572_; lean_object* v___x_573_; 
v_typeName_570_ = lean_ctor_get(v___y_482_, 0);
v_idx_571_ = lean_ctor_get(v___y_482_, 1);
v_struct_572_ = lean_ctor_get(v___y_482_, 2);
lean_inc_ref(v_struct_572_);
lean_inc_ref(v_post_470_);
lean_inc_ref(v_pre_468_);
v___x_573_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_468_, v_post_470_, v_struct_572_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; size_t v___x_575_; size_t v___x_576_; uint8_t v___x_577_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v___x_575_ = lean_ptr_addr(v_struct_572_);
v___x_576_ = lean_ptr_addr(v_a_574_);
v___x_577_ = lean_usize_dec_eq(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_inc(v_idx_571_);
lean_inc(v_typeName_570_);
lean_dec_ref_known(v___y_482_, 3);
v___x_578_ = l_Lean_Expr_proj___override(v_typeName_570_, v_idx_571_, v_a_574_);
v___x_579_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___x_578_, v___y_471_, v___y_472_, v___y_473_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; 
lean_dec(v_a_574_);
v___x_580_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___y_482_, v___y_471_, v___y_472_, v___y_473_);
return v___x_580_;
}
}
else
{
lean_dec_ref_known(v___y_482_, 3);
lean_dec_ref(v_post_470_);
lean_dec_ref(v_pre_468_);
return v___x_573_;
}
}
default: 
{
lean_object* v___x_581_; 
v___x_581_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_468_, v_post_470_, v___y_482_, v___y_471_, v___y_472_, v___y_473_);
return v___x_581_;
}
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v_post_470_);
lean_dec_ref(v_e_469_);
lean_dec_ref(v_pre_468_);
v_a_593_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_476_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_476_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_post_470_);
lean_dec_ref(v_e_469_);
lean_dec_ref(v_pre_468_);
v_a_601_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_475_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_475_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed(lean_object* v___x_609_, lean_object* v_pre_610_, lean_object* v_e_611_, lean_object* v_post_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1(v___x_609_, v_pre_610_, v_e_611_, v_post_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(lean_object* v_pre_618_, lean_object* v_post_619_, lean_object* v_e_620_, lean_object* v_a_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_inc(v_a_621_);
v___x_625_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_625_, 0, lean_box(0));
lean_closure_set(v___x_625_, 1, lean_box(0));
lean_closure_set(v___x_625_, 2, v_a_621_);
v___x_626_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_box(0), v___x_625_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_658_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_658_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_658_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_658_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_a_627_, v_e_620_);
lean_dec(v_a_627_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v___x_632_; lean_object* v___f_633_; lean_object* v___x_634_; 
lean_del_object(v___x_629_);
v___x_632_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_620_);
v___f_633_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_633_, 0, v___x_632_);
lean_closure_set(v___f_633_, 1, v_pre_618_);
lean_closure_set(v___f_633_, 2, v_e_620_);
lean_closure_set(v___f_633_, 3, v_post_619_);
v___x_634_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v___f_633_, v_a_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___f_636_; lean_object* v___x_637_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc_n(v_a_635_, 2);
lean_dec_ref_known(v___x_634_, 1);
lean_inc(v_a_621_);
v___f_636_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_636_, 0, v_a_621_);
lean_closure_set(v___f_636_, 1, v_e_620_);
lean_closure_set(v___f_636_, 2, v_a_635_);
v___x_637_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___lam__0(lean_box(0), v___f_636_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v___x_637_, 0);
lean_dec(v_unused_645_);
v___x_639_ = v___x_637_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_dec(v___x_637_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v_a_635_);
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_635_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_a_635_);
v_a_646_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_637_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_637_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_dec_ref(v_e_620_);
return v___x_634_;
}
}
else
{
lean_object* v_val_654_; lean_object* v___x_656_; 
lean_dec_ref(v_e_620_);
lean_dec_ref(v_post_619_);
lean_dec_ref(v_pre_618_);
v_val_654_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v___x_631_, 1);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v_val_654_);
v___x_656_ = v___x_629_;
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
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec_ref(v_e_620_);
lean_dec_ref(v_post_619_);
lean_dec_ref(v_pre_618_);
v_a_659_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_626_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_626_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(lean_object* v_pre_667_, lean_object* v_post_668_, lean_object* v_e_669_, lean_object* v_a_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; 
lean_inc_ref(v_post_668_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
lean_inc_ref(v_e_669_);
v___x_674_ = lean_apply_4(v_post_668_, v_e_669_, v___y_671_, v___y_672_, lean_box(0));
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_693_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_693_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_693_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_693_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
switch(lean_obj_tag(v_a_675_))
{
case 0:
{
lean_object* v_e_679_; lean_object* v___x_681_; 
lean_dec_ref(v_e_669_);
lean_dec_ref(v_post_668_);
lean_dec_ref(v_pre_667_);
v_e_679_ = lean_ctor_get(v_a_675_, 0);
lean_inc_ref(v_e_679_);
lean_dec_ref_known(v_a_675_, 1);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v_e_679_);
v___x_681_ = v___x_677_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_e_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
case 1:
{
lean_object* v_e_683_; lean_object* v___x_684_; 
lean_del_object(v___x_677_);
lean_dec_ref(v_e_669_);
v_e_683_ = lean_ctor_get(v_a_675_, 0);
lean_inc_ref(v_e_683_);
lean_dec_ref_known(v_a_675_, 1);
v___x_684_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_667_, v_post_668_, v_e_683_, v_a_670_, v___y_671_, v___y_672_);
return v___x_684_;
}
default: 
{
lean_object* v_e_x3f_685_; 
lean_dec_ref(v_post_668_);
lean_dec_ref(v_pre_667_);
v_e_x3f_685_ = lean_ctor_get(v_a_675_, 0);
lean_inc(v_e_x3f_685_);
lean_dec_ref_known(v_a_675_, 1);
if (lean_obj_tag(v_e_x3f_685_) == 0)
{
lean_object* v___x_687_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v_e_669_);
v___x_687_ = v___x_677_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_e_669_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
else
{
lean_object* v_val_689_; lean_object* v___x_691_; 
lean_dec_ref(v_e_669_);
v_val_689_ = lean_ctor_get(v_e_x3f_685_, 0);
lean_inc(v_val_689_);
lean_dec_ref_known(v_e_x3f_685_, 1);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v_val_689_);
v___x_691_ = v___x_677_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_val_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v_e_669_);
lean_dec_ref(v_post_668_);
lean_dec_ref(v_pre_667_);
v_a_694_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_674_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_674_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_702_, lean_object* v_post_703_, lean_object* v_e_704_, lean_object* v_a_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__2(v_pre_702_, v_post_703_, v_e_704_, v_a_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v_a_705_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_710_, lean_object* v_post_711_, lean_object* v_sz_712_, lean_object* v_i_713_, lean_object* v_bs_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
size_t v_sz_boxed_719_; size_t v_i_boxed_720_; lean_object* v_res_721_; 
v_sz_boxed_719_ = lean_unbox_usize(v_sz_712_);
lean_dec(v_sz_712_);
v_i_boxed_720_ = lean_unbox_usize(v_i_713_);
lean_dec(v_i_713_);
v_res_721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__1(v_pre_710_, v_post_711_, v_sz_boxed_719_, v_i_boxed_720_, v_bs_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_722_, lean_object* v_post_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__4(v_pre_722_, v_post_723_, v_x_724_, v_x_725_, v_x_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0___boxed(lean_object* v_pre_732_, lean_object* v_post_733_, lean_object* v_e_734_, lean_object* v_a_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_732_, v_post_733_, v_e_734_, v_a_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v_a_735_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_object* v_00_u03b1_740_, lean_object* v_x_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_apply_1(v_x_741_, lean_box(0));
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0___boxed(lean_object* v_00_u03b1_747_, lean_object* v_x_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(v_00_u03b1_747_, v_x_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
return v_res_752_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_box(0);
v___x_754_ = lean_unsigned_to_nat(16u);
v___x_755_ = lean_mk_array(v___x_754_, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__0);
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v___x_756_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__1);
v___x_760_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_760_, 0, lean_box(0));
lean_closure_set(v___x_760_, 1, lean_box(0));
lean_closure_set(v___x_760_, 2, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(lean_object* v_input_761_, lean_object* v_pre_762_, lean_object* v_post_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_a_769_; lean_object* v___x_770_; 
v___x_767_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___closed__2);
v___x_768_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_box(0), v___x_767_, v___y_764_, v___y_765_);
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___x_768_);
v___x_770_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0(v_pre_762_, v_post_763_, v_input_761_, v_a_769_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_772_, 0, lean_box(0));
lean_closure_set(v___x_772_, 1, lean_box(0));
lean_closure_set(v___x_772_, 2, v_a_769_);
v___x_773_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___lam__0(lean_box(0), v___x_772_, v___y_764_, v___y_765_);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_773_, 0);
lean_dec(v_unused_781_);
v___x_775_ = v___x_773_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_dec(v___x_773_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v_a_771_);
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_771_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
else
{
lean_dec(v_a_769_);
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0___boxed(lean_object* v_input_782_, lean_object* v_pre_783_, lean_object* v_post_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(v_input_782_, v_pre_783_, v_post_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand(lean_object* v_e_790_, lean_object* v_p_791_, uint8_t v_allowOpaque_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___x_799_; 
v___x_796_ = lean_box(v_allowOpaque_792_);
v___f_797_ = lean_alloc_closure((void*)(l_Lean_Meta_deltaExpand___lam__0___boxed), 6, 2);
lean_closure_set(v___f_797_, 0, v_p_791_);
lean_closure_set(v___f_797_, 1, v___x_796_);
v___f_798_ = ((lean_object*)(l_Lean_Meta_deltaExpand___closed__0));
v___x_799_ = l_Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0(v_e_790_, v___f_797_, v___f_798_, v_a_793_, v_a_794_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___boxed(lean_object* v_e_800_, lean_object* v_p_801_, lean_object* v_allowOpaque_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
uint8_t v_allowOpaque_boxed_806_; lean_object* v_res_807_; 
v_allowOpaque_boxed_806_ = lean_unbox(v_allowOpaque_802_);
v_res_807_ = l_Lean_Meta_deltaExpand(v_e_800_, v_p_801_, v_allowOpaque_boxed_806_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_808_, lean_object* v_m_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___redArg(v_m_809_, v_a_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_812_, lean_object* v_m_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3(v_00_u03b2_812_, v_m_813_, v_a_814_);
lean_dec_ref(v_a_814_);
lean_dec_ref(v_m_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_816_, lean_object* v_ref_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_817_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_822_, lean_object* v_ref_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_822_, v_ref_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8(lean_object* v_00_u03b1_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___redArg();
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8___boxed(lean_object* v_00_u03b1_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_838_, lean_object* v_x_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___redArg(v_x_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_845_, lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__5(v_00_u03b1_845_, v_x_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_852_, lean_object* v_m_853_, lean_object* v_a_854_, lean_object* v_b_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6___redArg(v_m_853_, v_a_854_, v_b_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_857_, lean_object* v_a_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___redArg(v_a_858_, v_x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_861_, lean_object* v_a_862_, lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_861_, v_a_862_, v_x_863_);
lean_dec(v_x_863_);
lean_dec_ref(v_a_862_);
return v_res_864_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_865_, lean_object* v_a_866_, lean_object* v_x_867_){
_start:
{
uint8_t v___x_868_; 
v___x_868_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___redArg(v_a_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10___boxed(lean_object* v_00_u03b2_869_, lean_object* v_a_870_, lean_object* v_x_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_869_, v_a_870_, v_x_871_);
lean_dec(v_x_871_);
lean_dec_ref(v_a_870_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_874_, lean_object* v_data_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11___redArg(v_data_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12(lean_object* v_00_u03b2_877_, lean_object* v_a_878_, lean_object* v_b_879_, lean_object* v_x_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__12___redArg(v_a_878_, v_b_879_, v_x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12(lean_object* v_00_u03b2_882_, lean_object* v_i_883_, lean_object* v_source_884_, lean_object* v_target_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_883_, v_source_884_, v_target_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_deltaExpand_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_888_, v_x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(lean_object* v_mvarId_891_, lean_object* v_x_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_891_, v_x_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_a_907_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_898_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_898_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg___boxed(lean_object* v_mvarId_915_, lean_object* v_x_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_915_, v_x_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(lean_object* v_00_u03b1_923_, lean_object* v_mvarId_924_, lean_object* v_x_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_924_, v_x_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___boxed(lean_object* v_00_u03b1_932_, lean_object* v_mvarId_933_, lean_object* v_x_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0(v_00_u03b1_932_, v_mvarId_933_, v_x_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lam__0(lean_object* v_mvarId_941_, lean_object* v___x_942_, lean_object* v_p_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; 
lean_inc(v_mvarId_941_);
v___x_949_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_941_, v___x_942_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v___x_950_; 
lean_dec_ref_known(v___x_949_, 1);
lean_inc(v_mvarId_941_);
v___x_950_ = l_Lean_MVarId_getType(v_mvarId_941_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; uint8_t v___x_952_; lean_object* v___x_953_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = 0;
v___x_953_ = l_Lean_Meta_deltaExpand(v_a_951_, v_p_943_, v___x_952_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = l_Lean_MVarId_change(v_mvarId_941_, v_a_954_, v___x_952_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v___x_955_;
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec(v_mvarId_941_);
v_a_956_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_953_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_953_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec_ref(v_p_943_);
lean_dec(v_mvarId_941_);
v_a_964_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_950_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_950_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v_p_943_);
lean_dec(v_mvarId_941_);
v_a_972_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_949_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_949_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lam__0___boxed(lean_object* v_mvarId_980_, lean_object* v___x_981_, lean_object* v_p_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_MVarId_deltaTarget___lam__0(v_mvarId_980_, v___x_981_, v_p_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget(lean_object* v_mvarId_992_, lean_object* v_p_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v___x_999_; lean_object* v___f_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((lean_object*)(l_Lean_MVarId_deltaTarget___closed__1));
lean_inc(v_mvarId_992_);
v___f_1000_ = lean_alloc_closure((void*)(l_Lean_MVarId_deltaTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1000_, 0, v_mvarId_992_);
lean_closure_set(v___f_1000_, 1, v___x_999_);
lean_closure_set(v___f_1000_, 2, v_p_993_);
v___x_1001_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_992_, v___f_1000_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___boxed(lean_object* v_mvarId_1002_, lean_object* v_p_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_MVarId_deltaTarget(v_mvarId_1002_, v_p_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lam__0(lean_object* v_mvarId_1010_, lean_object* v___x_1011_, lean_object* v_fvarId_1012_, lean_object* v_p_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; 
lean_inc(v_mvarId_1010_);
v___x_1019_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1010_, v___x_1011_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v___x_1020_; 
lean_dec_ref_known(v___x_1019_, 1);
lean_inc(v_fvarId_1012_);
v___x_1020_ = l_Lean_FVarId_getType___redArg(v_fvarId_1012_, v___y_1014_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = 0;
v___x_1023_ = l_Lean_Meta_deltaExpand(v_a_1021_, v_p_1013_, v___x_1022_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1025_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v___x_1025_ = l_Lean_MVarId_changeLocalDecl(v_mvarId_1010_, v_fvarId_1012_, v_a_1024_, v___x_1022_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
return v___x_1025_;
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec(v_fvarId_1012_);
lean_dec(v_mvarId_1010_);
v_a_1026_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1023_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1023_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_p_1013_);
lean_dec(v_fvarId_1012_);
lean_dec(v_mvarId_1010_);
v_a_1034_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1020_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1020_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_p_1013_);
lean_dec(v_fvarId_1012_);
lean_dec(v_mvarId_1010_);
v_a_1042_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1019_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1019_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lam__0___boxed(lean_object* v_mvarId_1050_, lean_object* v___x_1051_, lean_object* v_fvarId_1052_, lean_object* v_p_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_MVarId_deltaLocalDecl___lam__0(v_mvarId_1050_, v___x_1051_, v_fvarId_1052_, v_p_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl(lean_object* v_mvarId_1060_, lean_object* v_fvarId_1061_, lean_object* v_p_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___x_1070_; 
v___x_1068_ = ((lean_object*)(l_Lean_MVarId_deltaTarget___closed__1));
lean_inc(v_mvarId_1060_);
v___f_1069_ = lean_alloc_closure((void*)(l_Lean_MVarId_deltaLocalDecl___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1069_, 0, v_mvarId_1060_);
lean_closure_set(v___f_1069_, 1, v___x_1068_);
lean_closure_set(v___f_1069_, 2, v_fvarId_1061_);
lean_closure_set(v___f_1069_, 3, v_p_1062_);
v___x_1070_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_deltaTarget_spec__0___redArg(v_mvarId_1060_, v___f_1069_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___boxed(lean_object* v_mvarId_1071_, lean_object* v_fvarId_1072_, lean_object* v_p_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_MVarId_deltaLocalDecl(v_mvarId_1071_, v_fvarId_1072_, v_p_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
return v_res_1079_;
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
