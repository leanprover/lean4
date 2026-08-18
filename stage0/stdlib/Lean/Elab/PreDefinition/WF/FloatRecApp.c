// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.FloatRecApp
// Imports: public import Lean.Meta.Transform public import Lean.Elab.RecAppSyntax
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_MData_isRecApp(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_WF_floatRecApp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_WF_floatRecApp___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_floatRecApp___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_WF_floatRecApp___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_floatRecApp___lam__1___closed__0;
static const lean_string_object l_Lean_Elab_WF_floatRecApp___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Elab.PreDefinition.WF.FloatRecApp"};
static const lean_object* l_Lean_Elab_WF_floatRecApp___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_WF_floatRecApp___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_WF_floatRecApp___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Elab.WF.floatRecApp"};
static const lean_object* l_Lean_Elab_WF_floatRecApp___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_WF_floatRecApp___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_WF_floatRecApp___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Elab_WF_floatRecApp___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_WF_floatRecApp___lam__1___closed__3_value;
static lean_once_cell_t l_Lean_Elab_WF_floatRecApp___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_floatRecApp___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2;
static lean_once_cell_t l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_WF_floatRecApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_WF_floatRecApp___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_WF_floatRecApp___closed__0 = (const lean_object*)&l_Lean_Elab_WF_floatRecApp___closed__0_value;
static const lean_closure_object l_Lean_Elab_WF_floatRecApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_WF_floatRecApp___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_WF_floatRecApp___closed__1 = (const lean_object*)&l_Lean_Elab_WF_floatRecApp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___f_6_; lean_object* v___x_587__overap_7_; lean_object* v___x_8_; 
v___f_6_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___closed__0));
v___x_587__overap_7_ = lean_panic_fn_borrowed(v___f_6_, v_msg_2_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_8_ = lean_apply_3(v___x_587__overap_7_, v___y_3_, v___y_4_, lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___boxed(lean_object* v_msg_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0(v_msg_9_, v___y_10_, v___y_11_);
lean_dec(v___y_11_);
lean_dec_ref(v___y_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lam__0(lean_object* v_x_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___lam__0___closed__0));
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lam__0___boxed(lean_object* v_x_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Elab_WF_floatRecApp___lam__0(v_x_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec_ref(v_x_22_);
return v_res_26_;
}
}
static lean_object* _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v_dummy_28_; 
v___x_27_ = lean_box(0);
v_dummy_28_ = l_Lean_Expr_sort___override(v___x_27_);
return v_dummy_28_;
}
}
static lean_object* _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__4(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_32_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___lam__1___closed__3));
v___x_33_ = lean_unsigned_to_nat(39u);
v___x_34_ = lean_unsigned_to_nat(36u);
v___x_35_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___lam__1___closed__2));
v___x_36_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___lam__1___closed__1));
v___x_37_ = l_mkPanicMessageWithDecl(v___x_36_, v___x_35_, v___x_34_, v___x_33_, v___x_32_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lam__1(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
uint8_t v___y_46_; uint8_t v___x_71_; 
v___x_71_ = l_Lean_Expr_isApp(v_e_38_);
if (v___x_71_ == 0)
{
v___y_46_ = v___x_71_;
goto v___jp_45_;
}
else
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = l_Lean_Expr_getAppFn(v_e_38_);
v___x_73_ = l_Lean_Expr_isMData(v___x_72_);
lean_dec_ref(v___x_72_);
v___y_46_ = v___x_73_;
goto v___jp_45_;
}
v___jp_42_:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___lam__0___closed__0));
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
return v___x_44_;
}
v___jp_45_:
{
if (v___y_46_ == 0)
{
lean_dec_ref(v_e_38_);
goto v___jp_42_;
}
else
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Expr_getAppFn(v_e_38_);
if (lean_obj_tag(v___x_47_) == 10)
{
lean_object* v_data_48_; lean_object* v_expr_49_; uint8_t v___x_50_; 
v_data_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_data_48_);
v_expr_49_ = lean_ctor_get(v___x_47_, 1);
lean_inc_ref(v_expr_49_);
lean_dec_ref_known(v___x_47_, 2);
v___x_50_ = l_Lean_MData_isRecApp(v_data_48_);
if (v___x_50_ == 0)
{
lean_dec_ref(v_expr_49_);
lean_dec(v_data_48_);
lean_dec_ref(v_e_38_);
goto v___jp_42_;
}
else
{
lean_object* v_dummy_51_; lean_object* v_nargs_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_dummy_51_ = lean_obj_once(&l_Lean_Elab_WF_floatRecApp___lam__1___closed__0, &l_Lean_Elab_WF_floatRecApp___lam__1___closed__0_once, _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__0);
v_nargs_52_ = l_Lean_Expr_getAppNumArgs(v_e_38_);
lean_inc(v_nargs_52_);
v___x_53_ = lean_mk_array(v_nargs_52_, v_dummy_51_);
v___x_54_ = lean_unsigned_to_nat(1u);
v___x_55_ = lean_nat_sub(v_nargs_52_, v___x_54_);
lean_dec(v_nargs_52_);
v___x_56_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_38_, v___x_53_, v___x_55_);
v___x_57_ = l_Lean_Expr_beta(v_expr_49_, v___x_56_);
v___x_58_ = l_Lean_Expr_mdata___override(v_data_48_, v___x_57_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
else
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec_ref(v___x_47_);
lean_dec_ref(v_e_38_);
v___x_61_ = lean_obj_once(&l_Lean_Elab_WF_floatRecApp___lam__1___closed__4, &l_Lean_Elab_WF_floatRecApp___lam__1___closed__4_once, _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__4);
v___x_62_ = l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0(v___x_61_, v___y_39_, v___y_40_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_dec_ref_known(v___x_62_, 1);
goto v___jp_42_;
}
else
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___lam__1___boxed(lean_object* v_e_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Elab_WF_floatRecApp___lam__1(v_e_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_object* v_00_u03b1_79_, lean_object* v_x_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_apply_1(v_x_80_, lean_box(0));
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0___boxed(lean_object* v_00_u03b1_86_, lean_object* v_x_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(v_00_u03b1_86_, v_x_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_m_92_, lean_object* v_query_93_, lean_object* v_x_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
lean_object* v_zero_97_; uint8_t v_isZero_98_; 
v_zero_97_ = lean_unsigned_to_nat(0u);
v_isZero_98_ = lean_nat_dec_eq(v_x_95_, v_zero_97_);
if (v_isZero_98_ == 1)
{
lean_dec(v_x_96_);
lean_dec(v_x_95_);
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_box(2);
return v___x_99_;
}
else
{
lean_object* v_val_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
v_val_100_ = lean_ctor_get(v_x_94_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v_x_94_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_val_100_);
lean_dec(v_x_94_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_val_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
else
{
lean_object* v_keyArray_108_; lean_object* v_valueArray_109_; lean_object* v___x_110_; uint8_t v_isSome_111_; 
v_keyArray_108_ = lean_ctor_get(v_m_92_, 1);
v_valueArray_109_ = lean_ctor_get(v_m_92_, 2);
v___x_110_ = lean_array_fget_borrowed(v_keyArray_108_, v_x_96_);
v_isSome_111_ = lean_noption_is_some(v___x_110_);
if (v_isSome_111_ == 0)
{
lean_dec(v_x_95_);
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v_x_96_);
return v___x_112_;
}
else
{
lean_object* v_val_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
lean_dec(v_x_96_);
v_val_113_ = lean_ctor_get(v_x_94_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_94_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v_x_94_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_val_113_);
lean_dec(v_x_94_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_val_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
else
{
lean_object* v_one_121_; lean_object* v_n_122_; lean_object* v___y_124_; 
v_one_121_ = lean_unsigned_to_nat(1u);
v_n_122_ = lean_nat_sub(v_x_95_, v_one_121_);
lean_dec(v_x_95_);
if (v_isSome_111_ == 0)
{
goto v___jp_130_;
}
else
{
lean_object* v___x_132_; uint8_t v_isSome_133_; 
v___x_132_ = lean_array_fget_borrowed(v_valueArray_109_, v_x_96_);
v_isSome_133_ = lean_noption_is_some(v___x_132_);
if (v_isSome_133_ == 0)
{
goto v___jp_130_;
}
else
{
lean_object* v_val_134_; uint8_t v___x_135_; 
lean_inc(v___x_110_);
v_val_134_ = lean_noption_get(v___x_110_);
v___x_135_ = l_Lean_ExprStructEq_beq(v_val_134_, v_query_93_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
lean_dec(v_val_134_);
v___x_136_ = lean_array_get_size(v_keyArray_108_);
v___x_137_ = lean_nat_add(v_x_96_, v_one_121_);
lean_dec(v_x_96_);
v___x_138_ = lean_nat_dec_lt(v___x_137_, v___x_136_);
if (v___x_138_ == 0)
{
lean_dec(v___x_137_);
v_x_95_ = v_n_122_;
v_x_96_ = v_zero_97_;
goto _start;
}
else
{
v_x_95_ = v_n_122_;
v_x_96_ = v___x_137_;
goto _start;
}
}
else
{
lean_object* v_val_141_; lean_object* v___x_142_; 
lean_dec(v_n_122_);
lean_dec(v_x_94_);
lean_inc(v___x_132_);
v_val_141_ = lean_noption_get(v___x_132_);
v___x_142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_142_, 0, v_x_96_);
lean_ctor_set(v___x_142_, 1, v_val_134_);
lean_ctor_set(v___x_142_, 2, v_val_141_);
return v___x_142_;
}
}
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = lean_array_get_size(v_keyArray_108_);
v___x_126_ = lean_nat_add(v_x_96_, v_one_121_);
lean_dec(v_x_96_);
v___x_127_ = lean_nat_dec_lt(v___x_126_, v___x_125_);
if (v___x_127_ == 0)
{
lean_dec(v___x_126_);
v_x_94_ = v___y_124_;
v_x_95_ = v_n_122_;
v_x_96_ = v_zero_97_;
goto _start;
}
else
{
v_x_94_ = v___y_124_;
v_x_95_ = v_n_122_;
v_x_96_ = v___x_126_;
goto _start;
}
}
v___jp_130_:
{
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v___x_131_; 
lean_inc(v_x_96_);
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v_x_96_);
v___y_124_ = v___x_131_;
goto v___jp_123_;
}
else
{
v___y_124_ = v_x_94_;
goto v___jp_123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_m_143_, lean_object* v_query_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_m_143_, v_query_144_, v_x_145_, v_x_146_, v_x_147_);
lean_dec_ref(v_query_144_);
lean_dec_ref(v_m_143_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(lean_object* v_m_149_, lean_object* v_query_150_){
_start:
{
lean_object* v_keyArray_151_; lean_object* v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; uint64_t v___x_155_; uint64_t v_fold_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_keyArray_151_ = lean_ctor_get(v_m_149_, 1);
v___x_152_ = lean_array_get_size(v_keyArray_151_);
v___x_153_ = l_Lean_ExprStructEq_hash(v_query_150_);
v___x_154_ = 32ULL;
v___x_155_ = lean_uint64_shift_right(v___x_153_, v___x_154_);
v_fold_156_ = lean_uint64_xor(v___x_153_, v___x_155_);
v___x_157_ = 16ULL;
v___x_158_ = lean_uint64_shift_right(v_fold_156_, v___x_157_);
v___x_159_ = lean_uint64_xor(v_fold_156_, v___x_158_);
v___x_160_ = lean_uint64_to_usize(v___x_159_);
v___x_161_ = lean_usize_of_nat(v___x_152_);
v___x_162_ = ((size_t)1ULL);
v___x_163_ = lean_usize_sub(v___x_161_, v___x_162_);
v___x_164_ = lean_usize_land(v___x_160_, v___x_163_);
v___x_165_ = lean_usize_to_nat(v___x_164_);
v___x_166_ = lean_box(0);
v___x_167_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_m_149_, v_query_150_, v___x_166_, v___x_152_, v___x_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg___boxed(lean_object* v_m_168_, lean_object* v_query_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v_m_168_, v_query_169_);
lean_dec_ref(v_query_169_);
lean_dec_ref(v_m_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_m_171_, lean_object* v_query_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v_m_171_, v_query_172_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_index_174_; lean_object* v_key_175_; lean_object* v_value_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
v_index_174_ = lean_ctor_get(v___x_173_, 0);
v_key_175_ = lean_ctor_get(v___x_173_, 1);
v_value_176_ = lean_ctor_get(v___x_173_, 2);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_173_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_value_176_);
lean_inc(v_key_175_);
lean_inc(v_index_174_);
lean_dec(v___x_173_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_index_174_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_key_175_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_value_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_object* v___x_184_; 
lean_dec(v___x_173_);
v___x_184_ = lean_box(1);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg___boxed(lean_object* v_m_185_, lean_object* v_query_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_m_185_, v_query_186_);
lean_dec_ref(v_query_186_);
lean_dec_ref(v_m_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(lean_object* v_m_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_m_188_, v_a_189_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_value_191_; lean_object* v___x_192_; 
v_value_191_ = lean_ctor_get(v___x_190_, 2);
lean_inc(v_value_191_);
lean_dec_ref_known(v___x_190_, 3);
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_value_191_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = lean_box(0);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_m_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_m_194_, v_a_195_);
lean_dec_ref(v_a_195_);
lean_dec_ref(v_m_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14___redArg(lean_object* v_b_197_, lean_object* v_acc_198_, lean_object* v_i_199_){
_start:
{
lean_object* v___y_201_; lean_object* v_keyArray_209_; lean_object* v_valueArray_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_keyArray_209_ = lean_ctor_get(v_b_197_, 1);
v_valueArray_210_ = lean_ctor_get(v_b_197_, 2);
v___x_211_ = lean_array_get_size(v_keyArray_209_);
v___x_212_ = lean_nat_dec_lt(v_i_199_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec(v_i_199_);
return v_acc_198_;
}
else
{
lean_object* v___x_213_; uint8_t v_isSome_214_; 
v___x_213_ = lean_array_fget_borrowed(v_keyArray_209_, v_i_199_);
v_isSome_214_ = lean_noption_is_some(v___x_213_);
if (v_isSome_214_ == 0)
{
goto v___jp_205_;
}
else
{
lean_object* v___x_215_; uint8_t v_isSome_216_; 
v___x_215_ = lean_array_fget_borrowed(v_valueArray_210_, v_i_199_);
v_isSome_216_ = lean_noption_is_some(v___x_215_);
if (v_isSome_216_ == 0)
{
goto v___jp_205_;
}
else
{
lean_object* v_val_217_; lean_object* v_val_218_; lean_object* v_i_220_; lean_object* v___x_225_; 
lean_inc(v___x_213_);
v_val_217_ = lean_noption_get(v___x_213_);
lean_inc(v___x_215_);
v_val_218_ = lean_noption_get(v___x_215_);
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v_acc_198_, v_val_217_);
switch(lean_obj_tag(v___x_225_))
{
case 0:
{
lean_object* v_index_226_; lean_object* v_size_227_; lean_object* v___x_228_; 
v_index_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_index_226_);
lean_dec_ref_known(v___x_225_, 3);
v_size_227_ = lean_ctor_get(v_acc_198_, 0);
lean_inc(v_size_227_);
v___x_228_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_198_, v_size_227_, v_index_226_, v_val_217_, v_val_218_);
lean_dec(v_index_226_);
v___y_201_ = v___x_228_;
goto v___jp_200_;
}
case 1:
{
lean_object* v_index_229_; 
v_index_229_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_index_229_);
lean_dec_ref_known(v___x_225_, 1);
v_i_220_ = v_index_229_;
goto v___jp_219_;
}
default: 
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_198_, v___x_230_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_index_232_; 
v_index_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_index_232_);
lean_dec_ref_known(v___x_231_, 1);
v_i_220_ = v_index_232_;
goto v___jp_219_;
}
else
{
lean_dec(v_val_218_);
lean_dec(v_val_217_);
v___y_201_ = v_acc_198_;
goto v___jp_200_;
}
}
}
v___jp_219_:
{
lean_object* v_size_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_size_221_ = lean_ctor_get(v_acc_198_, 0);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_add(v_size_221_, v___x_222_);
v___x_224_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_198_, v___x_223_, v_i_220_, v_val_217_, v_val_218_);
lean_dec(v_i_220_);
v___y_201_ = v___x_224_;
goto v___jp_200_;
}
}
}
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_add(v_i_199_, v___x_202_);
lean_dec(v_i_199_);
v_acc_198_ = v___y_201_;
v_i_199_ = v___x_203_;
goto _start;
}
v___jp_205_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_add(v_i_199_, v___x_206_);
lean_dec(v_i_199_);
v_i_199_ = v___x_207_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14___redArg___boxed(lean_object* v_b_233_, lean_object* v_acc_234_, lean_object* v_i_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14___redArg(v_b_233_, v_acc_234_, v_i_235_);
lean_dec_ref(v_b_233_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13___redArg(lean_object* v_init_237_, lean_object* v_b_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14___redArg(v_b_238_, v_init_237_, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13___redArg___boxed(lean_object* v_init_241_, lean_object* v_b_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13___redArg(v_init_241_, v_b_242_);
lean_dec_ref(v_b_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8___redArg(lean_object* v_m_244_){
_start:
{
lean_object* v_keyArray_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_cellCount_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_target_252_; lean_object* v___x_253_; 
v_keyArray_245_ = lean_ctor_get(v_m_244_, 1);
v___x_246_ = lean_array_get_size(v_keyArray_245_);
v___x_247_ = lean_unsigned_to_nat(2u);
v_cellCount_248_ = lean_nat_mul(v___x_246_, v___x_247_);
v___x_249_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_248_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_248_);
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_248_);
v_target_252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_252_, 0, v___x_249_);
lean_ctor_set(v_target_252_, 1, v___x_250_);
lean_ctor_set(v_target_252_, 2, v___x_251_);
v___x_253_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13___redArg(v_target_252_, v_m_244_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8___redArg___boxed(lean_object* v_m_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8___redArg(v_m_254_);
lean_dec_ref(v_m_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2(lean_object* v_a_256_, lean_object* v_e_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___y_263_; lean_object* v___y_266_; lean_object* v_i_267_; lean_object* v___y_283_; lean_object* v_i_284_; lean_object* v___y_290_; lean_object* v___x_299_; 
v___x_260_ = lean_st_ref_take(v_a_256_);
v___x_261_ = lean_box(0);
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v___x_260_, v_e_257_);
switch(lean_obj_tag(v___x_299_))
{
case 0:
{
lean_object* v_index_300_; lean_object* v_size_301_; lean_object* v___x_302_; 
v_index_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_index_300_);
lean_dec_ref_known(v___x_299_, 3);
v_size_301_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_size_301_);
v___x_302_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_260_, v_size_301_, v_index_300_, v_e_257_, v_a_258_);
lean_dec(v_index_300_);
v___y_263_ = v___x_302_;
goto v___jp_262_;
}
case 1:
{
lean_object* v_index_303_; lean_object* v_size_304_; lean_object* v_keyArray_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_index_303_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_index_303_);
lean_dec_ref_known(v___x_299_, 1);
v_size_304_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_size_304_);
v_keyArray_305_ = lean_ctor_get(v___x_260_, 1);
lean_inc_ref(v_keyArray_305_);
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = lean_nat_add(v_size_304_, v___x_306_);
lean_dec(v_size_304_);
v___x_308_ = lean_array_get_size(v_keyArray_305_);
lean_dec_ref(v_keyArray_305_);
v___x_309_ = lean_nat_dec_lt(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_dec(v___x_307_);
lean_dec(v_index_303_);
goto v___jp_272_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_310_ = lean_unsigned_to_nat(4u);
v___x_311_ = lean_nat_mul(v___x_307_, v___x_310_);
v___x_312_ = lean_unsigned_to_nat(3u);
v___x_313_ = lean_nat_mul(v___x_308_, v___x_312_);
v___x_314_ = lean_nat_dec_le(v___x_311_, v___x_313_);
lean_dec(v___x_313_);
lean_dec(v___x_311_);
if (v___x_314_ == 0)
{
lean_dec(v___x_307_);
lean_dec(v_index_303_);
goto v___jp_272_;
}
else
{
lean_object* v___x_315_; 
v___x_315_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_260_, v___x_307_, v_index_303_, v_e_257_, v_a_258_);
lean_dec(v_index_303_);
v___y_263_ = v___x_315_;
goto v___jp_262_;
}
}
}
default: 
{
lean_object* v_size_316_; lean_object* v_keyArray_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_size_316_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_size_316_);
v_keyArray_317_ = lean_ctor_get(v___x_260_, 1);
lean_inc_ref(v_keyArray_317_);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_add(v_size_316_, v___x_318_);
lean_dec(v_size_316_);
v___x_320_ = lean_array_get_size(v_keyArray_317_);
lean_dec_ref(v_keyArray_317_);
v___x_321_ = lean_nat_dec_lt(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v___x_319_);
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8___redArg(v___x_260_);
lean_dec(v___x_260_);
v___y_290_ = v___x_322_;
goto v___jp_289_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_323_ = lean_unsigned_to_nat(4u);
v___x_324_ = lean_nat_mul(v___x_319_, v___x_323_);
lean_dec(v___x_319_);
v___x_325_ = lean_unsigned_to_nat(3u);
v___x_326_ = lean_nat_mul(v___x_320_, v___x_325_);
v___x_327_ = lean_nat_dec_le(v___x_324_, v___x_326_);
lean_dec(v___x_326_);
lean_dec(v___x_324_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8___redArg(v___x_260_);
lean_dec(v___x_260_);
v___y_290_ = v___x_328_;
goto v___jp_289_;
}
else
{
v___y_290_ = v___x_260_;
goto v___jp_289_;
}
}
}
}
v___jp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = lean_st_ref_put(v_a_256_, v___y_263_);
return v___x_261_;
}
v___jp_265_:
{
lean_object* v_size_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_size_268_ = lean_ctor_get(v___y_266_, 0);
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_add(v_size_268_, v___x_269_);
v___x_271_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_266_, v___x_270_, v_i_267_, v_e_257_, v_a_258_);
lean_dec(v_i_267_);
v___y_263_ = v___x_271_;
goto v___jp_262_;
}
v___jp_272_:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8___redArg(v___x_260_);
lean_dec(v___x_260_);
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v___x_273_, v_e_257_);
switch(lean_obj_tag(v___x_274_))
{
case 0:
{
lean_object* v_index_275_; lean_object* v_size_276_; lean_object* v___x_277_; 
v_index_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_index_275_);
lean_dec_ref_known(v___x_274_, 3);
v_size_276_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_size_276_);
v___x_277_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_273_, v_size_276_, v_index_275_, v_e_257_, v_a_258_);
lean_dec(v_index_275_);
v___y_263_ = v___x_277_;
goto v___jp_262_;
}
case 1:
{
lean_object* v_index_278_; 
v_index_278_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_index_278_);
lean_dec_ref_known(v___x_274_, 1);
v___y_266_ = v___x_273_;
v_i_267_ = v_index_278_;
goto v___jp_265_;
}
default: 
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_273_, v___x_279_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_index_281_; 
v_index_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_index_281_);
lean_dec_ref_known(v___x_280_, 1);
v___y_266_ = v___x_273_;
v_i_267_ = v_index_281_;
goto v___jp_265_;
}
else
{
lean_dec_ref(v_a_258_);
lean_dec_ref(v_e_257_);
v___y_263_ = v___x_273_;
goto v___jp_262_;
}
}
}
}
v___jp_282_:
{
lean_object* v_size_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_size_285_ = lean_ctor_get(v___y_283_, 0);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_add(v_size_285_, v___x_286_);
v___x_288_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_283_, v___x_287_, v_i_284_, v_e_257_, v_a_258_);
lean_dec(v_i_284_);
v___y_263_ = v___x_288_;
goto v___jp_262_;
}
v___jp_289_:
{
lean_object* v___x_291_; 
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v___y_290_, v_e_257_);
switch(lean_obj_tag(v___x_291_))
{
case 0:
{
lean_object* v_index_292_; lean_object* v_size_293_; lean_object* v___x_294_; 
v_index_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_index_292_);
lean_dec_ref_known(v___x_291_, 3);
v_size_293_ = lean_ctor_get(v___y_290_, 0);
lean_inc(v_size_293_);
v___x_294_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_290_, v_size_293_, v_index_292_, v_e_257_, v_a_258_);
lean_dec(v_index_292_);
v___y_263_ = v___x_294_;
goto v___jp_262_;
}
case 1:
{
lean_object* v_index_295_; 
v_index_295_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_index_295_);
lean_dec_ref_known(v___x_291_, 1);
v___y_283_ = v___y_290_;
v_i_284_ = v_index_295_;
goto v___jp_282_;
}
default: 
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_290_, v___x_296_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_index_298_; 
v_index_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_index_298_);
lean_dec_ref_known(v___x_297_, 1);
v___y_283_ = v___y_290_;
v_i_284_ = v_index_298_;
goto v___jp_282_;
}
else
{
lean_dec_ref(v_a_258_);
lean_dec_ref(v_e_257_);
v___y_263_ = v___y_290_;
goto v___jp_262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2___boxed(lean_object* v_a_329_, lean_object* v_e_330_, lean_object* v_a_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2(v_a_329_, v_e_330_, v_a_331_);
lean_dec(v_a_329_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_334_, lean_object* v_x_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_apply_1(v_x_335_, lean_box(0));
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_341_, lean_object* v_x_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(v_00_u03b1_341_, v_x_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_346_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = l_Lean_maxRecDepthErrorMessage;
v___x_353_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3);
v___x_355_ = l_Lean_MessageData_ofFormat(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4);
v___x_357_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2));
v___x_358_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_ref_359_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_ref_359_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_ref_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_364_);
return v_res_366_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_box(0);
v___x_368_ = l_Lean_interruptExceptionId;
v___x_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg(){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(lean_object* v_x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___y_381_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; uint8_t v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; uint8_t v___y_406_; lean_object* v_fileName_411_; lean_object* v_fileMap_412_; lean_object* v_options_413_; lean_object* v_currRecDepth_414_; lean_object* v_maxRecDepth_415_; lean_object* v_ref_416_; lean_object* v_currNamespace_417_; lean_object* v_openDecls_418_; lean_object* v_initHeartbeats_419_; lean_object* v_maxHeartbeats_420_; lean_object* v_quotContext_421_; lean_object* v_currMacroScope_422_; uint8_t v_diag_423_; lean_object* v_cancelTk_x3f_424_; uint8_t v_suppressElabErrors_425_; lean_object* v_inheritedTraceOptions_426_; 
v_fileName_411_ = lean_ctor_get(v___y_377_, 0);
v_fileMap_412_ = lean_ctor_get(v___y_377_, 1);
v_options_413_ = lean_ctor_get(v___y_377_, 2);
v_currRecDepth_414_ = lean_ctor_get(v___y_377_, 3);
v_maxRecDepth_415_ = lean_ctor_get(v___y_377_, 4);
v_ref_416_ = lean_ctor_get(v___y_377_, 5);
v_currNamespace_417_ = lean_ctor_get(v___y_377_, 6);
v_openDecls_418_ = lean_ctor_get(v___y_377_, 7);
v_initHeartbeats_419_ = lean_ctor_get(v___y_377_, 8);
v_maxHeartbeats_420_ = lean_ctor_get(v___y_377_, 9);
v_quotContext_421_ = lean_ctor_get(v___y_377_, 10);
v_currMacroScope_422_ = lean_ctor_get(v___y_377_, 11);
v_diag_423_ = lean_ctor_get_uint8(v___y_377_, sizeof(void*)*14);
v_cancelTk_x3f_424_ = lean_ctor_get(v___y_377_, 12);
v_suppressElabErrors_425_ = lean_ctor_get_uint8(v___y_377_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_426_ = lean_ctor_get(v___y_377_, 13);
if (lean_obj_tag(v_cancelTk_x3f_424_) == 1)
{
lean_object* v_val_432_; uint8_t v___x_433_; 
v_val_432_ = lean_ctor_get(v_cancelTk_x3f_424_, 0);
v___x_433_ = l_IO_CancelToken_isSet(v_val_432_);
if (v___x_433_ == 0)
{
goto v___jp_427_;
}
else
{
lean_object* v___x_434_; lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec_ref(v_x_375_);
v___x_434_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
else
{
goto v___jp_427_;
}
v___jp_380_:
{
if (lean_obj_tag(v___y_381_) == 0)
{
return v___y_381_;
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_a_382_ = lean_ctor_get(v___y_381_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___y_381_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___y_381_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___y_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
v___jp_390_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_nat_add(v___y_405_, v___x_407_);
lean_inc_ref(v___y_403_);
lean_inc(v___y_398_);
lean_inc(v___y_396_);
lean_inc(v___y_400_);
lean_inc(v___y_395_);
lean_inc(v___y_394_);
lean_inc(v___y_392_);
lean_inc(v___y_393_);
lean_inc(v___y_397_);
lean_inc_ref(v___y_401_);
lean_inc_ref(v___y_404_);
lean_inc_ref(v___y_391_);
v___x_409_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_409_, 0, v___y_391_);
lean_ctor_set(v___x_409_, 1, v___y_404_);
lean_ctor_set(v___x_409_, 2, v___y_401_);
lean_ctor_set(v___x_409_, 3, v___x_408_);
lean_ctor_set(v___x_409_, 4, v___y_397_);
lean_ctor_set(v___x_409_, 5, v___y_402_);
lean_ctor_set(v___x_409_, 6, v___y_393_);
lean_ctor_set(v___x_409_, 7, v___y_392_);
lean_ctor_set(v___x_409_, 8, v___y_394_);
lean_ctor_set(v___x_409_, 9, v___y_395_);
lean_ctor_set(v___x_409_, 10, v___y_400_);
lean_ctor_set(v___x_409_, 11, v___y_396_);
lean_ctor_set(v___x_409_, 12, v___y_398_);
lean_ctor_set(v___x_409_, 13, v___y_403_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*14, v___y_406_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*14 + 1, v___y_399_);
lean_inc(v___y_378_);
lean_inc(v___y_376_);
v___x_410_ = lean_apply_4(v_x_375_, v___y_376_, v___x_409_, v___y_378_, lean_box(0));
v___y_381_ = v___x_410_;
goto v___jp_380_;
}
v___jp_427_:
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_nat_dec_eq(v_maxRecDepth_415_, v___x_428_);
if (v___x_429_ == 0)
{
uint8_t v___x_430_; 
v___x_430_ = lean_nat_dec_eq(v_currRecDepth_414_, v_maxRecDepth_415_);
if (v___x_430_ == 0)
{
lean_inc(v_ref_416_);
v___y_391_ = v_fileName_411_;
v___y_392_ = v_openDecls_418_;
v___y_393_ = v_currNamespace_417_;
v___y_394_ = v_initHeartbeats_419_;
v___y_395_ = v_maxHeartbeats_420_;
v___y_396_ = v_currMacroScope_422_;
v___y_397_ = v_maxRecDepth_415_;
v___y_398_ = v_cancelTk_x3f_424_;
v___y_399_ = v_suppressElabErrors_425_;
v___y_400_ = v_quotContext_421_;
v___y_401_ = v_options_413_;
v___y_402_ = v_ref_416_;
v___y_403_ = v_inheritedTraceOptions_426_;
v___y_404_ = v_fileMap_412_;
v___y_405_ = v_currRecDepth_414_;
v___y_406_ = v_diag_423_;
goto v___jp_390_;
}
else
{
lean_object* v___x_431_; 
lean_dec_ref(v_x_375_);
lean_inc(v_ref_416_);
v___x_431_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_416_);
v___y_381_ = v___x_431_;
goto v___jp_380_;
}
}
else
{
lean_inc(v_ref_416_);
v___y_391_ = v_fileName_411_;
v___y_392_ = v_openDecls_418_;
v___y_393_ = v_currNamespace_417_;
v___y_394_ = v_initHeartbeats_419_;
v___y_395_ = v_maxHeartbeats_420_;
v___y_396_ = v_currMacroScope_422_;
v___y_397_ = v_maxRecDepth_415_;
v___y_398_ = v_cancelTk_x3f_424_;
v___y_399_ = v_suppressElabErrors_425_;
v___y_400_ = v_quotContext_421_;
v___y_401_ = v_options_413_;
v___y_402_ = v_ref_416_;
v___y_403_ = v_inheritedTraceOptions_426_;
v___y_404_ = v_fileMap_412_;
v___y_405_ = v_currRecDepth_414_;
v___y_406_ = v_diag_423_;
goto v___jp_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(lean_object* v_pre_450_, lean_object* v_post_451_, size_t v_sz_452_, size_t v_i_453_, lean_object* v_bs_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_usize_dec_lt(v_i_453_, v_sz_452_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec_ref(v_post_451_);
lean_dec_ref(v_pre_450_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v_bs_454_);
return v___x_460_;
}
else
{
lean_object* v_v_461_; lean_object* v___x_462_; 
v_v_461_ = lean_array_uget_borrowed(v_bs_454_, v_i_453_);
lean_inc(v_v_461_);
lean_inc_ref(v_post_451_);
lean_inc_ref(v_pre_450_);
v___x_462_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_450_, v_post_451_, v_v_461_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; lean_object* v_bs_x27_465_; size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = lean_unsigned_to_nat(0u);
v_bs_x27_465_ = lean_array_uset(v_bs_454_, v_i_453_, v___x_464_);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_add(v_i_453_, v___x_466_);
v___x_468_ = lean_array_uset(v_bs_x27_465_, v_i_453_, v_a_463_);
v_i_453_ = v___x_467_;
v_bs_454_ = v___x_468_;
goto _start;
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec_ref(v_bs_454_);
lean_dec_ref(v_post_451_);
lean_dec_ref(v_pre_450_);
v_a_470_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_462_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_462_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(lean_object* v_pre_478_, lean_object* v_post_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
if (lean_obj_tag(v_x_480_) == 5)
{
lean_object* v_fn_487_; lean_object* v_arg_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_fn_487_ = lean_ctor_get(v_x_480_, 0);
lean_inc_ref(v_fn_487_);
v_arg_488_ = lean_ctor_get(v_x_480_, 1);
lean_inc_ref(v_arg_488_);
lean_dec_ref_known(v_x_480_, 2);
v___x_489_ = lean_array_set(v_x_481_, v_x_482_, v_arg_488_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_sub(v_x_482_, v___x_490_);
lean_dec(v_x_482_);
v_x_480_ = v_fn_487_;
v_x_481_ = v___x_489_;
v_x_482_ = v___x_491_;
goto _start;
}
else
{
lean_object* v___x_493_; 
lean_dec(v_x_482_);
lean_inc_ref(v_post_479_);
lean_inc_ref(v_pre_478_);
v___x_493_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_478_, v_post_479_, v_x_480_, v___y_483_, v___y_484_, v___y_485_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; size_t v_sz_495_; size_t v___x_496_; lean_object* v___x_497_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v_sz_495_ = lean_array_size(v_x_481_);
v___x_496_ = ((size_t)0ULL);
lean_inc_ref(v_post_479_);
lean_inc_ref(v_pre_478_);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_478_, v_post_479_, v_sz_495_, v___x_496_, v_x_481_, v___y_483_, v___y_484_, v___y_485_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = l_Lean_mkAppN(v_a_494_, v_a_498_);
lean_dec(v_a_498_);
v___x_500_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_478_, v_post_479_, v___x_499_, v___y_483_, v___y_484_, v___y_485_);
return v___x_500_;
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_a_494_);
lean_dec_ref(v_post_479_);
lean_dec_ref(v_pre_478_);
v_a_501_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_497_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_dec_ref(v_x_481_);
lean_dec_ref(v_post_479_);
lean_dec_ref(v_pre_478_);
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(lean_object* v___x_509_, lean_object* v_pre_510_, lean_object* v_e_511_, lean_object* v_post_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; uint8_t v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; uint8_t v___y_525_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; uint8_t v___y_539_; uint8_t v___y_540_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; uint8_t v___y_551_; lean_object* v___y_552_; uint8_t v___y_553_; lean_object* v___x_560_; 
v___x_560_ = l_Lean_Core_checkSystem(v___x_509_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___x_561_; 
lean_dec_ref_known(v___x_560_, 1);
lean_inc_ref(v_pre_510_);
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
lean_inc_ref(v_e_511_);
v___x_561_ = lean_apply_4(v_pre_510_, v_e_511_, v___y_514_, v___y_515_, lean_box(0));
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_651_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_651_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_651_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_651_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___y_567_; 
switch(lean_obj_tag(v_a_562_))
{
case 0:
{
lean_object* v_e_641_; lean_object* v___x_643_; 
lean_dec_ref(v_post_512_);
lean_dec_ref(v_e_511_);
lean_dec_ref(v_pre_510_);
v_e_641_ = lean_ctor_get(v_a_562_, 0);
lean_inc_ref(v_e_641_);
lean_dec_ref_known(v_a_562_, 1);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v_e_641_);
v___x_643_ = v___x_564_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_e_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
case 1:
{
lean_object* v_e_645_; lean_object* v___x_646_; 
lean_del_object(v___x_564_);
lean_dec_ref(v_e_511_);
v_e_645_ = lean_ctor_get(v_a_562_, 0);
lean_inc_ref(v_e_645_);
lean_dec_ref_known(v_a_562_, 1);
lean_inc_ref(v_post_512_);
lean_inc_ref(v_pre_510_);
v___x_646_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_510_, v_post_512_, v_e_645_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v_a_647_, v___y_513_, v___y_514_, v___y_515_);
return v___x_648_;
}
else
{
lean_dec_ref(v_post_512_);
lean_dec_ref(v_pre_510_);
return v___x_646_;
}
}
default: 
{
lean_object* v_e_x3f_649_; 
lean_del_object(v___x_564_);
v_e_x3f_649_ = lean_ctor_get(v_a_562_, 0);
lean_inc(v_e_x3f_649_);
lean_dec_ref_known(v_a_562_, 1);
if (lean_obj_tag(v_e_x3f_649_) == 0)
{
v___y_567_ = v_e_511_;
goto v___jp_566_;
}
else
{
lean_object* v_val_650_; 
lean_dec_ref(v_e_511_);
v_val_650_ = lean_ctor_get(v_e_x3f_649_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v_e_x3f_649_, 1);
v___y_567_ = v_val_650_;
goto v___jp_566_;
}
}
}
v___jp_566_:
{
switch(lean_obj_tag(v___y_567_))
{
case 7:
{
lean_object* v_binderName_568_; lean_object* v_binderType_569_; lean_object* v_body_570_; uint8_t v_binderInfo_571_; lean_object* v___x_572_; 
v_binderName_568_ = lean_ctor_get(v___y_567_, 0);
lean_inc(v_binderName_568_);
v_binderType_569_ = lean_ctor_get(v___y_567_, 1);
v_body_570_ = lean_ctor_get(v___y_567_, 2);
v_binderInfo_571_ = lean_ctor_get_uint8(v___y_567_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_569_);
lean_inc_ref(v_post_512_);
lean_inc_ref(v_pre_510_);
v___x_572_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_510_, v_post_512_, v_binderType_569_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
lean_inc_ref(v_body_570_);
lean_inc_ref(v_post_512_);
lean_inc_ref(v_pre_510_);
v___x_574_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_510_, v_post_512_, v_body_570_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; size_t v___x_576_; size_t v___x_577_; uint8_t v___x_578_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = lean_ptr_addr(v_binderType_569_);
v___x_577_ = lean_ptr_addr(v_a_573_);
v___x_578_ = lean_usize_dec_eq(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
v___y_548_ = v___y_567_;
v___y_549_ = v_a_573_;
v___y_550_ = v_binderName_568_;
v___y_551_ = v_binderInfo_571_;
v___y_552_ = v_a_575_;
v___y_553_ = v___x_578_;
goto v___jp_547_;
}
else
{
size_t v___x_579_; size_t v___x_580_; uint8_t v___x_581_; 
v___x_579_ = lean_ptr_addr(v_body_570_);
v___x_580_ = lean_ptr_addr(v_a_575_);
v___x_581_ = lean_usize_dec_eq(v___x_579_, v___x_580_);
v___y_548_ = v___y_567_;
v___y_549_ = v_a_573_;
v___y_550_ = v_binderName_568_;
v___y_551_ = v_binderInfo_571_;
v___y_552_ = v_a_575_;
v___y_553_ = v___x_581_;
goto v___jp_547_;
}
}
else
{
lean_dec(v_a_573_);
lean_dec_ref_known(v___y_567_, 3);
lean_dec(v_binderName_568_);
lean_dec_ref(v_post_512_);
lean_dec_ref(v_pre_510_);
return v___x_574_;
}
}
else
{
lean_dec(v_binderName_568_);
lean_dec_ref_known(v___y_567_, 3);
lean_dec_ref(v_post_512_);
lean_dec_ref(v_pre_510_);
return v___x_572_;
}
}
case 6:
{
lean_object* v_binderName_582_; lean_object* v_binderType_583_; lean_object* v_body_584_; uint8_t v_binderInfo_585_; lean_object* v___x_586_; 
v_binderName_582_ = lean_ctor_get(v___y_567_, 0);
lean_inc(v_binderName_582_);
v_binderType_583_ = lean_ctor_get(v___y_567_, 1);
v_body_584_ = lean_ctor_get(v___y_567_, 2);
v_binderInfo_585_ = lean_ctor_get_uint8(v___y_567_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_583_);
lean_inc_ref(v_post_512_);
lean_inc_ref(v_pre_510_);
v___x_586_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_510_, v_post_512_, v_binderType_583_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
lean_inc_ref(v_body_584_);
lean_inc_ref(v_post_512_);
lean_inc_ref(v_pre_510_);
v___x_588_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_510_, v_post_512_, v_body_584_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; size_t v___x_590_; size_t v___x_591_; uint8_t v___x_592_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = lean_ptr_addr(v_binderType_583_);
v___x_591_ = lean_ptr_addr(v_a_587_);
v___x_592_ = lean_usize_dec_eq(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
v___y_535_ = v_binderName_582_;
v___y_536_ = v_a_587_;
v___y_537_ = v___y_567_;
v___y_538_ = v_a_589_;
v___y_539_ = v_binderInfo_585_;
v___y_540_ = v___x_592_;
goto v___jp_534_;
}
else
{
size_t v___x_593_; size_t v___x_594_; uint8_t v___x_595_; 
v___x_593_ = lean_ptr_addr(v_body_584_);
v___x_594_ = lean_ptr_addr(v_a_589_);
v___x_595_ = lean_usize_dec_eq(v___x_593_, v___x_594_);
v___y_535_ = v_binderName_582_;
v___y_536_ = v_a_587_;
v___y_537_ = v___y_567_;
v___y_538_ = v_a_589_;
v___y_539_ = v_binderInfo_585_;
v___y_540_ = v___x_595_;
goto v___jp_534_;
}
}
else
{
lean_dec(v_a_587_);
lean_dec_ref_known(v___y_567_, 3);
lean_dec(v_binderName_582_);
lean_dec_ref(v_post_512_);
lean_dec_ref(v_pre_510_);
return v___x_588_;
}
}
else
{
lean_dec(v_binderName_582_);
lean_dec_ref_known(v___y_567_, 3);
lean_dec_ref(v_post_512_);
lean_dec_ref(v_pre_510_);
return v___x_586_;
}
}
case 8:
{
lean_object* v_declName_596_; lean_object* v_type_597_; lean_object* v_value_598_; lean_object* v_body_599_; uint8_t v_nondep_600_; lean_object* v___x_601_; 
v_declName_596_ = lean_ctor_get(v___y_567_, 0);
lean_inc(v_declName_596_);
v_type_597_ = lean_ctor_get(v___y_567_, 1);
v_value_598_ = lean_ctor_get(v___y_567_, 2);
v_body_599_ = lean_ctor_get(v___y_567_, 3);
lean_inc_ref(v_body_599_);
v_nondep_600_ = lean_ctor_get_uint8(v___y_567_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_597_);
lean_inc_ref(v_post_512_);
lean_inc_ref(v_pre_510_);
v___x_601_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_510_, v_post_512_, v_type_597_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_603_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
lean_inc_ref(v_value_598_);
lean_inc_ref(v_post_512_);
lean_inc_ref(v_pre_510_);
v___x_603_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_510_, v_post_512_, v_value_598_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_605_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_603_, 1);
lean_inc_ref(v_body_599_);
lean_inc_ref(v_post_512_);
lean_inc_ref(v_pre_510_);
v___x_605_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_510_, v_post_512_, v_body_599_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; size_t v___x_607_; size_t v___x_608_; uint8_t v___x_609_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v___x_605_, 1);
v___x_607_ = lean_ptr_addr(v_type_597_);
v___x_608_ = lean_ptr_addr(v_a_602_);
v___x_609_ = lean_usize_dec_eq(v___x_607_, v___x_608_);
if (v___x_609_ == 0)
{
v___y_518_ = v___y_567_;
v___y_519_ = v_a_602_;
v___y_520_ = v_a_604_;
v___y_521_ = v_a_606_;
v___y_522_ = v_nondep_600_;
v___y_523_ = v_declName_596_;
v___y_524_ = v_body_599_;
v___y_525_ = v___x_609_;
goto v___jp_517_;
}
else
{
size_t v___x_610_; size_t v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_ptr_addr(v_value_598_);
v___x_611_ = lean_ptr_addr(v_a_604_);
v___x_612_ = lean_usize_dec_eq(v___x_610_, v___x_611_);
v___y_518_ = v___y_567_;
v___y_519_ = v_a_602_;
v___y_520_ = v_a_604_;
v___y_521_ = v_a_606_;
v___y_522_ = v_nondep_600_;
v___y_523_ = v_declName_596_;
v___y_524_ = v_body_599_;
v___y_525_ = v___x_612_;
goto v___jp_517_;
}
}
else
{
lean_dec(v_a_604_);
lean_dec(v_a_602_);
lean_dec_ref(v_body_599_);
lean_dec(v_declName_596_);
lean_dec_ref_known(v___y_567_, 4);
lean_dec_ref(v_post_512_);
lean_dec_ref(v_pre_510_);
return v___x_605_;
}
}
else
{
lean_dec(v_a_602_);
lean_dec_ref(v_body_599_);
lean_dec_ref_known(v___y_567_, 4);
lean_dec(v_declName_596_);
lean_dec_ref(v_post_512_);
lean_dec_ref(v_pre_510_);
return v___x_603_;
}
}
else
{
lean_dec_ref(v_body_599_);
lean_dec_ref_known(v___y_567_, 4);
lean_dec(v_declName_596_);
lean_dec_ref(v_post_512_);
lean_dec_ref(v_pre_510_);
return v___x_601_;
}
}
case 5:
{
lean_object* v_dummy_613_; lean_object* v_nargs_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_dummy_613_ = lean_obj_once(&l_Lean_Elab_WF_floatRecApp___lam__1___closed__0, &l_Lean_Elab_WF_floatRecApp___lam__1___closed__0_once, _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__0);
v_nargs_614_ = l_Lean_Expr_getAppNumArgs(v___y_567_);
lean_inc(v_nargs_614_);
v___x_615_ = lean_mk_array(v_nargs_614_, v_dummy_613_);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_sub(v_nargs_614_, v___x_616_);
lean_dec(v_nargs_614_);
v___x_618_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_510_, v_post_512_, v___y_567_, v___x_615_, v___x_617_, v___y_513_, v___y_514_, v___y_515_);
return v___x_618_;
}
case 10:
{
lean_object* v_data_619_; lean_object* v_expr_620_; lean_object* v___x_621_; 
v_data_619_ = lean_ctor_get(v___y_567_, 0);
v_expr_620_ = lean_ctor_get(v___y_567_, 1);
lean_inc_ref(v_expr_620_);
lean_inc_ref(v_post_512_);
lean_inc_ref(v_pre_510_);
v___x_621_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_510_, v_post_512_, v_expr_620_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; size_t v___x_623_; size_t v___x_624_; uint8_t v___x_625_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = lean_ptr_addr(v_expr_620_);
v___x_624_ = lean_ptr_addr(v_a_622_);
v___x_625_ = lean_usize_dec_eq(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_inc(v_data_619_);
lean_dec_ref_known(v___y_567_, 2);
v___x_626_ = l_Lean_Expr_mdata___override(v_data_619_, v_a_622_);
v___x_627_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___x_626_, v___y_513_, v___y_514_, v___y_515_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; 
lean_dec(v_a_622_);
v___x_628_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___y_567_, v___y_513_, v___y_514_, v___y_515_);
return v___x_628_;
}
}
else
{
lean_dec_ref_known(v___y_567_, 2);
lean_dec_ref(v_post_512_);
lean_dec_ref(v_pre_510_);
return v___x_621_;
}
}
case 11:
{
lean_object* v_typeName_629_; lean_object* v_idx_630_; lean_object* v_struct_631_; lean_object* v___x_632_; 
v_typeName_629_ = lean_ctor_get(v___y_567_, 0);
v_idx_630_ = lean_ctor_get(v___y_567_, 1);
v_struct_631_ = lean_ctor_get(v___y_567_, 2);
lean_inc_ref(v_struct_631_);
lean_inc_ref(v_post_512_);
lean_inc_ref(v_pre_510_);
v___x_632_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_510_, v_post_512_, v_struct_631_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; size_t v___x_634_; size_t v___x_635_; uint8_t v___x_636_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = lean_ptr_addr(v_struct_631_);
v___x_635_ = lean_ptr_addr(v_a_633_);
v___x_636_ = lean_usize_dec_eq(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_inc(v_idx_630_);
lean_inc(v_typeName_629_);
lean_dec_ref_known(v___y_567_, 3);
v___x_637_ = l_Lean_Expr_proj___override(v_typeName_629_, v_idx_630_, v_a_633_);
v___x_638_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___x_637_, v___y_513_, v___y_514_, v___y_515_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
lean_dec(v_a_633_);
v___x_639_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___y_567_, v___y_513_, v___y_514_, v___y_515_);
return v___x_639_;
}
}
else
{
lean_dec_ref_known(v___y_567_, 3);
lean_dec_ref(v_post_512_);
lean_dec_ref(v_pre_510_);
return v___x_632_;
}
}
default: 
{
lean_object* v___x_640_; 
v___x_640_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___y_567_, v___y_513_, v___y_514_, v___y_515_);
return v___x_640_;
}
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v_post_512_);
lean_dec_ref(v_e_511_);
lean_dec_ref(v_pre_510_);
v_a_652_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_561_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_561_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_post_512_);
lean_dec_ref(v_e_511_);
lean_dec_ref(v_pre_510_);
v_a_660_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_560_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_560_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
v___jp_517_:
{
if (v___y_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec_ref(v___y_524_);
lean_dec_ref(v___y_518_);
v___x_526_ = l_Lean_Expr_letE___override(v___y_523_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
v___x_527_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___x_526_, v___y_513_, v___y_514_, v___y_515_);
return v___x_527_;
}
else
{
size_t v___x_528_; size_t v___x_529_; uint8_t v___x_530_; 
v___x_528_ = lean_ptr_addr(v___y_524_);
lean_dec_ref(v___y_524_);
v___x_529_ = lean_ptr_addr(v___y_521_);
v___x_530_ = lean_usize_dec_eq(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec_ref(v___y_518_);
v___x_531_ = l_Lean_Expr_letE___override(v___y_523_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
v___x_532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___x_531_, v___y_513_, v___y_514_, v___y_515_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; 
lean_dec(v___y_523_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec_ref(v___y_519_);
v___x_533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___y_518_, v___y_513_, v___y_514_, v___y_515_);
return v___x_533_;
}
}
}
v___jp_534_:
{
if (v___y_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec_ref(v___y_537_);
v___x_541_ = l_Lean_Expr_lam___override(v___y_535_, v___y_536_, v___y_538_, v___y_539_);
v___x_542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___x_541_, v___y_513_, v___y_514_, v___y_515_);
return v___x_542_;
}
else
{
uint8_t v___x_543_; 
v___x_543_ = l_Lean_instBEqBinderInfo_beq(v___y_539_, v___y_539_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec_ref(v___y_537_);
v___x_544_ = l_Lean_Expr_lam___override(v___y_535_, v___y_536_, v___y_538_, v___y_539_);
v___x_545_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___x_544_, v___y_513_, v___y_514_, v___y_515_);
return v___x_545_;
}
else
{
lean_object* v___x_546_; 
lean_dec_ref(v___y_538_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
v___x_546_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___y_537_, v___y_513_, v___y_514_, v___y_515_);
return v___x_546_;
}
}
}
v___jp_547_:
{
if (v___y_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v___y_548_);
v___x_554_ = l_Lean_Expr_forallE___override(v___y_550_, v___y_549_, v___y_552_, v___y_551_);
v___x_555_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___x_554_, v___y_513_, v___y_514_, v___y_515_);
return v___x_555_;
}
else
{
uint8_t v___x_556_; 
v___x_556_ = l_Lean_instBEqBinderInfo_beq(v___y_551_, v___y_551_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec_ref(v___y_548_);
v___x_557_ = l_Lean_Expr_forallE___override(v___y_550_, v___y_549_, v___y_552_, v___y_551_);
v___x_558_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___x_557_, v___y_513_, v___y_514_, v___y_515_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; 
lean_dec_ref(v___y_552_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
v___x_559_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_510_, v_post_512_, v___y_548_, v___y_513_, v___y_514_, v___y_515_);
return v___x_559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed(lean_object* v___x_668_, lean_object* v_pre_669_, lean_object* v_e_670_, lean_object* v_post_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(v___x_668_, v_pre_669_, v_e_670_, v_post_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(lean_object* v_pre_677_, lean_object* v_post_678_, lean_object* v_e_679_, lean_object* v_a_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
lean_inc(v_a_680_);
v___x_684_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_684_, 0, lean_box(0));
lean_closure_set(v___x_684_, 1, lean_box(0));
lean_closure_set(v___x_684_, 2, v_a_680_);
v___x_685_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_box(0), v___x_684_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_717_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_717_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_717_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_717_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_a_686_, v_e_679_);
lean_dec(v_a_686_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v___x_691_; lean_object* v___f_692_; lean_object* v___x_693_; 
lean_del_object(v___x_688_);
v___x_691_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___closed__0));
lean_inc_ref(v_e_679_);
v___f_692_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_692_, 0, v___x_691_);
lean_closure_set(v___f_692_, 1, v_pre_677_);
lean_closure_set(v___f_692_, 2, v_e_679_);
lean_closure_set(v___f_692_, 3, v_post_678_);
v___x_693_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v___f_692_, v_a_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___f_695_; lean_object* v___x_696_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc_n(v_a_694_, 2);
lean_dec_ref_known(v___x_693_, 1);
lean_inc(v_a_680_);
v___f_695_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_695_, 0, v_a_680_);
lean_closure_set(v___f_695_, 1, v_e_679_);
lean_closure_set(v___f_695_, 2, v_a_694_);
v___x_696_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_box(0), v___f_695_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v___x_696_, 0);
lean_dec(v_unused_704_);
v___x_698_ = v___x_696_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_dec(v___x_696_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_a_694_);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_694_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_a_694_);
v_a_705_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_696_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_696_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_dec_ref(v_e_679_);
return v___x_693_;
}
}
else
{
lean_object* v_val_713_; lean_object* v___x_715_; 
lean_dec_ref(v_e_679_);
lean_dec_ref(v_post_678_);
lean_dec_ref(v_pre_677_);
v_val_713_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_val_713_);
lean_dec_ref_known(v___x_690_, 1);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v_val_713_);
v___x_715_ = v___x_688_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_val_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v_e_679_);
lean_dec_ref(v_post_678_);
lean_dec_ref(v_pre_677_);
v_a_718_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_685_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_685_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(lean_object* v_pre_726_, lean_object* v_post_727_, lean_object* v_e_728_, lean_object* v_a_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; 
lean_inc_ref(v_post_727_);
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
lean_inc_ref(v_e_728_);
v___x_733_ = lean_apply_4(v_post_727_, v_e_728_, v___y_730_, v___y_731_, lean_box(0));
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_752_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_752_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_752_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_752_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
switch(lean_obj_tag(v_a_734_))
{
case 0:
{
lean_object* v_e_738_; lean_object* v___x_740_; 
lean_dec_ref(v_e_728_);
lean_dec_ref(v_post_727_);
lean_dec_ref(v_pre_726_);
v_e_738_ = lean_ctor_get(v_a_734_, 0);
lean_inc_ref(v_e_738_);
lean_dec_ref_known(v_a_734_, 1);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v_e_738_);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_e_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
case 1:
{
lean_object* v_e_742_; lean_object* v___x_743_; 
lean_del_object(v___x_736_);
lean_dec_ref(v_e_728_);
v_e_742_ = lean_ctor_get(v_a_734_, 0);
lean_inc_ref(v_e_742_);
lean_dec_ref_known(v_a_734_, 1);
v___x_743_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_726_, v_post_727_, v_e_742_, v_a_729_, v___y_730_, v___y_731_);
return v___x_743_;
}
default: 
{
lean_object* v_e_x3f_744_; 
lean_dec_ref(v_post_727_);
lean_dec_ref(v_pre_726_);
v_e_x3f_744_ = lean_ctor_get(v_a_734_, 0);
lean_inc(v_e_x3f_744_);
lean_dec_ref_known(v_a_734_, 1);
if (lean_obj_tag(v_e_x3f_744_) == 0)
{
lean_object* v___x_746_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v_e_728_);
v___x_746_ = v___x_736_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_e_728_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v_val_748_; lean_object* v___x_750_; 
lean_dec_ref(v_e_728_);
v_val_748_ = lean_ctor_get(v_e_x3f_744_, 0);
lean_inc(v_val_748_);
lean_dec_ref_known(v_e_x3f_744_, 1);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v_val_748_);
v___x_750_ = v___x_736_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_val_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v_e_728_);
lean_dec_ref(v_post_727_);
lean_dec_ref(v_pre_726_);
v_a_753_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_733_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_733_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_761_, lean_object* v_post_762_, lean_object* v_e_763_, lean_object* v_a_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_761_, v_post_762_, v_e_763_, v_a_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v_a_764_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_769_, lean_object* v_post_770_, lean_object* v_sz_771_, lean_object* v_i_772_, lean_object* v_bs_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
size_t v_sz_boxed_778_; size_t v_i_boxed_779_; lean_object* v_res_780_; 
v_sz_boxed_778_ = lean_unbox_usize(v_sz_771_);
lean_dec(v_sz_771_);
v_i_boxed_779_ = lean_unbox_usize(v_i_772_);
lean_dec(v_i_772_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_769_, v_post_770_, v_sz_boxed_778_, v_i_boxed_779_, v_bs_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_781_, lean_object* v_post_782_, lean_object* v_x_783_, lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_781_, v_post_782_, v_x_783_, v_x_784_, v_x_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___boxed(lean_object* v_pre_791_, lean_object* v_post_792_, lean_object* v_e_793_, lean_object* v_a_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_791_, v_post_792_, v_e_793_, v_a_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v_a_794_);
return v_res_798_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0(void){
_start:
{
lean_object* v_cellCount_799_; lean_object* v___x_800_; 
v_cellCount_799_ = lean_unsigned_to_nat(16u);
v___x_800_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_799_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1(void){
_start:
{
lean_object* v_cellCount_801_; lean_object* v___x_802_; 
v_cellCount_801_ = lean_unsigned_to_nat(16u);
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_801_);
return v___x_802_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_803_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1);
v___x_804_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0);
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___x_804_);
lean_ctor_set(v___x_806_, 2, v___x_803_);
return v___x_806_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__3(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2);
v___x_808_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_808_, 0, lean_box(0));
lean_closure_set(v___x_808_, 1, lean_box(0));
lean_closure_set(v___x_808_, 2, v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(lean_object* v_input_809_, lean_object* v_pre_810_, lean_object* v_post_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_a_817_; lean_object* v___x_818_; 
v___x_815_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__3, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__3_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__3);
v___x_816_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_box(0), v___x_815_, v___y_812_, v___y_813_);
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___x_816_);
v___x_818_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_810_, v_post_811_, v_input_809_, v_a_817_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_820_, 0, lean_box(0));
lean_closure_set(v___x_820_, 1, lean_box(0));
lean_closure_set(v___x_820_, 2, v_a_817_);
v___x_821_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_box(0), v___x_820_, v___y_812_, v___y_813_);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v___x_821_, 0);
lean_dec(v_unused_829_);
v___x_823_ = v___x_821_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_dec(v___x_821_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v_a_819_);
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_819_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_dec(v_a_817_);
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___boxed(lean_object* v_input_830_, lean_object* v_pre_831_, lean_object* v_post_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(v_input_830_, v_pre_831_, v_post_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp(lean_object* v_e_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___x_845_; 
v___f_843_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___closed__0));
v___f_844_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___closed__1));
v___x_845_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(v_e_839_, v___f_843_, v___f_844_, v_a_840_, v_a_841_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___boxed(lean_object* v_e_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Elab_WF_floatRecApp(v_e_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_851_, lean_object* v_m_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_m_852_, v_a_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_855_, lean_object* v_m_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(v_00_u03b2_855_, v_m_856_, v_a_857_);
lean_dec_ref(v_a_857_);
lean_dec_ref(v_m_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_859_, lean_object* v_ref_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_860_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_865_, lean_object* v_ref_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_865_, v_ref_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(lean_object* v_00_u03b1_881_, lean_object* v_x_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_882_, v___y_883_, v___y_884_, v___y_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b1_888_, lean_object* v_x_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(v_00_u03b1_888_, v_x_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_895_, lean_object* v_m_896_, lean_object* v_query_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v_m_896_, v_query_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___boxed(lean_object* v_00_u03b2_899_, lean_object* v_m_900_, lean_object* v_query_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7(v_00_u03b2_899_, v_m_900_, v_query_901_);
lean_dec_ref(v_query_901_);
lean_dec_ref(v_m_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8(lean_object* v_00_u03b2_903_, lean_object* v_m_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8___redArg(v_m_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8___boxed(lean_object* v_00_u03b2_906_, lean_object* v_m_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8(v_00_u03b2_906_, v_m_907_);
lean_dec_ref(v_m_907_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_909_, lean_object* v_m_910_, lean_object* v_query_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_m_910_, v_query_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_00_u03b2_913_, lean_object* v_m_914_, lean_object* v_query_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_913_, v_m_914_, v_query_915_);
lean_dec_ref(v_query_915_);
lean_dec_ref(v_m_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_917_, lean_object* v_m_918_, lean_object* v_query_919_, lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v_x_922_, lean_object* v_x_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_m_918_, v_query_919_, v_x_920_, v_x_921_, v_x_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_925_, lean_object* v_m_926_, lean_object* v_query_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_925_, v_m_926_, v_query_927_, v_x_928_, v_x_929_, v_x_930_, v_x_931_);
lean_dec_ref(v_query_927_);
lean_dec_ref(v_m_926_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13(lean_object* v_00_u03b2_933_, lean_object* v_init_934_, lean_object* v_b_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13___redArg(v_init_934_, v_b_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13___boxed(lean_object* v_00_u03b2_937_, lean_object* v_init_938_, lean_object* v_b_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13(v_00_u03b2_937_, v_init_938_, v_b_939_);
lean_dec_ref(v_b_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14(lean_object* v_00_u03b2_941_, lean_object* v_b_942_, lean_object* v_acc_943_, lean_object* v_i_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14___redArg(v_b_942_, v_acc_943_, v_i_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14___boxed(lean_object* v_00_u03b2_946_, lean_object* v_b_947_, lean_object* v_acc_948_, lean_object* v_i_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__8_spec__13_spec__14(v_00_u03b2_946_, v_b_947_, v_acc_948_, v_i_949_);
lean_dec_ref(v_b_947_);
return v_res_950_;
}
}
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_RecAppSyntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_RecAppSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_RecAppSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
}
#ifdef __cplusplus
}
#endif
