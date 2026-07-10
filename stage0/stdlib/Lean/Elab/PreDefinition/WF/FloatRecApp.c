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
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_IO_CancelToken_isSet(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(lean_object* v_a_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v_key_95_; lean_object* v_value_96_; lean_object* v_tail_97_; uint8_t v___x_98_; 
v_key_95_ = lean_ctor_get(v_x_93_, 0);
v_value_96_ = lean_ctor_get(v_x_93_, 1);
v_tail_97_ = lean_ctor_get(v_x_93_, 2);
v___x_98_ = l_Lean_ExprStructEq_beq(v_key_95_, v_a_92_);
if (v___x_98_ == 0)
{
v_x_93_ = v_tail_97_;
goto _start;
}
else
{
lean_object* v___x_100_; 
lean_inc(v_value_96_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v_value_96_);
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg___boxed(lean_object* v_a_101_, lean_object* v_x_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_a_101_, v_x_102_);
lean_dec(v_x_102_);
lean_dec_ref(v_a_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(lean_object* v_m_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_buckets_106_; lean_object* v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v_fold_111_; uint64_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; size_t v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_buckets_106_ = lean_ctor_get(v_m_104_, 1);
v___x_107_ = lean_array_get_size(v_buckets_106_);
v___x_108_ = l_Lean_ExprStructEq_hash(v_a_105_);
v___x_109_ = 32ULL;
v___x_110_ = lean_uint64_shift_right(v___x_108_, v___x_109_);
v_fold_111_ = lean_uint64_xor(v___x_108_, v___x_110_);
v___x_112_ = 16ULL;
v___x_113_ = lean_uint64_shift_right(v_fold_111_, v___x_112_);
v___x_114_ = lean_uint64_xor(v_fold_111_, v___x_113_);
v___x_115_ = lean_uint64_to_usize(v___x_114_);
v___x_116_ = lean_usize_of_nat(v___x_107_);
v___x_117_ = ((size_t)1ULL);
v___x_118_ = lean_usize_sub(v___x_116_, v___x_117_);
v___x_119_ = lean_usize_land(v___x_115_, v___x_118_);
v___x_120_ = lean_array_uget_borrowed(v_buckets_106_, v___x_119_);
v___x_121_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_a_105_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_m_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_m_122_, v_a_123_);
lean_dec_ref(v_a_123_);
lean_dec_ref(v_m_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
return v_x_125_;
}
else
{
lean_object* v_key_127_; lean_object* v_value_128_; lean_object* v_tail_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_152_; 
v_key_127_ = lean_ctor_get(v_x_126_, 0);
v_value_128_ = lean_ctor_get(v_x_126_, 1);
v_tail_129_ = lean_ctor_get(v_x_126_, 2);
v_isSharedCheck_152_ = !lean_is_exclusive(v_x_126_);
if (v_isSharedCheck_152_ == 0)
{
v___x_131_ = v_x_126_;
v_isShared_132_ = v_isSharedCheck_152_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_tail_129_);
lean_inc(v_value_128_);
lean_inc(v_key_127_);
lean_dec(v_x_126_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_152_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v_fold_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_133_ = lean_array_get_size(v_x_125_);
v___x_134_ = l_Lean_ExprStructEq_hash(v_key_127_);
v___x_135_ = 32ULL;
v___x_136_ = lean_uint64_shift_right(v___x_134_, v___x_135_);
v_fold_137_ = lean_uint64_xor(v___x_134_, v___x_136_);
v___x_138_ = 16ULL;
v___x_139_ = lean_uint64_shift_right(v_fold_137_, v___x_138_);
v___x_140_ = lean_uint64_xor(v_fold_137_, v___x_139_);
v___x_141_ = lean_uint64_to_usize(v___x_140_);
v___x_142_ = lean_usize_of_nat(v___x_133_);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_sub(v___x_142_, v___x_143_);
v___x_145_ = lean_usize_land(v___x_141_, v___x_144_);
v___x_146_ = lean_array_uget_borrowed(v_x_125_, v___x_145_);
lean_inc(v___x_146_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 2, v___x_146_);
v___x_148_ = v___x_131_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_key_127_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_value_128_);
lean_ctor_set(v_reuseFailAlloc_151_, 2, v___x_146_);
v___x_148_ = v_reuseFailAlloc_151_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; 
v___x_149_ = lean_array_uset(v_x_125_, v___x_145_, v___x_148_);
v_x_125_ = v___x_149_;
v_x_126_ = v_tail_129_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(lean_object* v_i_153_, lean_object* v_source_154_, lean_object* v_target_155_){
_start:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_array_get_size(v_source_154_);
v___x_157_ = lean_nat_dec_lt(v_i_153_, v___x_156_);
if (v___x_157_ == 0)
{
lean_dec_ref(v_source_154_);
lean_dec(v_i_153_);
return v_target_155_;
}
else
{
lean_object* v_es_158_; lean_object* v___x_159_; lean_object* v_source_160_; lean_object* v_target_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_es_158_ = lean_array_fget(v_source_154_, v_i_153_);
v___x_159_ = lean_box(0);
v_source_160_ = lean_array_fset(v_source_154_, v_i_153_, v___x_159_);
v_target_161_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_target_155_, v_es_158_);
v___x_162_ = lean_unsigned_to_nat(1u);
v___x_163_ = lean_nat_add(v_i_153_, v___x_162_);
lean_dec(v_i_153_);
v_i_153_ = v___x_163_;
v_source_154_ = v_source_160_;
v_target_155_ = v_target_161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(lean_object* v_data_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_nbuckets_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_166_ = lean_array_get_size(v_data_165_);
v___x_167_ = lean_unsigned_to_nat(2u);
v_nbuckets_168_ = lean_nat_mul(v___x_166_, v___x_167_);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_box(0);
v___x_171_ = lean_mk_array(v_nbuckets_168_, v___x_170_);
v___x_172_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v___x_169_, v_data_165_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_a_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
uint8_t v___x_175_; 
v___x_175_ = 0;
return v___x_175_;
}
else
{
lean_object* v_key_176_; lean_object* v_tail_177_; uint8_t v___x_178_; 
v_key_176_ = lean_ctor_get(v_x_174_, 0);
v_tail_177_ = lean_ctor_get(v_x_174_, 2);
v___x_178_ = l_Lean_ExprStructEq_beq(v_key_176_, v_a_173_);
if (v___x_178_ == 0)
{
v_x_174_ = v_tail_177_;
goto _start;
}
else
{
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_a_180_, lean_object* v_x_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_a_180_, v_x_181_);
lean_dec(v_x_181_);
lean_dec_ref(v_a_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(lean_object* v_a_184_, lean_object* v_b_185_, lean_object* v_x_186_){
_start:
{
if (lean_obj_tag(v_x_186_) == 0)
{
lean_dec(v_b_185_);
lean_dec_ref(v_a_184_);
return v_x_186_;
}
else
{
lean_object* v_key_187_; lean_object* v_value_188_; lean_object* v_tail_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_201_; 
v_key_187_ = lean_ctor_get(v_x_186_, 0);
v_value_188_ = lean_ctor_get(v_x_186_, 1);
v_tail_189_ = lean_ctor_get(v_x_186_, 2);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_186_);
if (v_isSharedCheck_201_ == 0)
{
v___x_191_ = v_x_186_;
v_isShared_192_ = v_isSharedCheck_201_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_tail_189_);
lean_inc(v_value_188_);
lean_inc(v_key_187_);
lean_dec(v_x_186_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_201_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
uint8_t v___x_193_; 
v___x_193_ = l_Lean_ExprStructEq_beq(v_key_187_, v_a_184_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(v_a_184_, v_b_185_, v_tail_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 2, v___x_194_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_key_187_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_value_188_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
else
{
lean_object* v___x_199_; 
lean_dec(v_value_188_);
lean_dec(v_key_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v_b_185_);
lean_ctor_set(v___x_191_, 0, v_a_184_);
v___x_199_ = v___x_191_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_184_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_b_185_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_tail_189_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(lean_object* v_m_202_, lean_object* v_a_203_, lean_object* v_b_204_){
_start:
{
lean_object* v_size_205_; lean_object* v_buckets_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_249_; 
v_size_205_ = lean_ctor_get(v_m_202_, 0);
v_buckets_206_ = lean_ctor_get(v_m_202_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v_m_202_);
if (v_isSharedCheck_249_ == 0)
{
v___x_208_ = v_m_202_;
v_isShared_209_ = v_isSharedCheck_249_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_buckets_206_);
lean_inc(v_size_205_);
lean_dec(v_m_202_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_249_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v_fold_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; lean_object* v_bkt_223_; uint8_t v___x_224_; 
v___x_210_ = lean_array_get_size(v_buckets_206_);
v___x_211_ = l_Lean_ExprStructEq_hash(v_a_203_);
v___x_212_ = 32ULL;
v___x_213_ = lean_uint64_shift_right(v___x_211_, v___x_212_);
v_fold_214_ = lean_uint64_xor(v___x_211_, v___x_213_);
v___x_215_ = 16ULL;
v___x_216_ = lean_uint64_shift_right(v_fold_214_, v___x_215_);
v___x_217_ = lean_uint64_xor(v_fold_214_, v___x_216_);
v___x_218_ = lean_uint64_to_usize(v___x_217_);
v___x_219_ = lean_usize_of_nat(v___x_210_);
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_sub(v___x_219_, v___x_220_);
v___x_222_ = lean_usize_land(v___x_218_, v___x_221_);
v_bkt_223_ = lean_array_uget_borrowed(v_buckets_206_, v___x_222_);
v___x_224_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_a_203_, v_bkt_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v_size_x27_226_; lean_object* v___x_227_; lean_object* v_buckets_x27_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v_size_x27_226_ = lean_nat_add(v_size_205_, v___x_225_);
lean_dec(v_size_205_);
lean_inc(v_bkt_223_);
v___x_227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_227_, 0, v_a_203_);
lean_ctor_set(v___x_227_, 1, v_b_204_);
lean_ctor_set(v___x_227_, 2, v_bkt_223_);
v_buckets_x27_228_ = lean_array_uset(v_buckets_206_, v___x_222_, v___x_227_);
v___x_229_ = lean_unsigned_to_nat(4u);
v___x_230_ = lean_nat_mul(v_size_x27_226_, v___x_229_);
v___x_231_ = lean_unsigned_to_nat(3u);
v___x_232_ = lean_nat_div(v___x_230_, v___x_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_array_get_size(v_buckets_x27_228_);
v___x_234_ = lean_nat_dec_le(v___x_232_, v___x_233_);
lean_dec(v___x_232_);
if (v___x_234_ == 0)
{
lean_object* v_val_235_; lean_object* v___x_237_; 
v_val_235_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(v_buckets_x27_228_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v_val_235_);
lean_ctor_set(v___x_208_, 0, v_size_x27_226_);
v___x_237_ = v___x_208_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_size_x27_226_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_val_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
else
{
lean_object* v___x_240_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v_buckets_x27_228_);
lean_ctor_set(v___x_208_, 0, v_size_x27_226_);
v___x_240_ = v___x_208_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_size_x27_226_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_buckets_x27_228_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
else
{
lean_object* v___x_242_; lean_object* v_buckets_x27_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
lean_inc(v_bkt_223_);
v___x_242_ = lean_box(0);
v_buckets_x27_243_ = lean_array_uset(v_buckets_206_, v___x_222_, v___x_242_);
v___x_244_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(v_a_203_, v_b_204_, v_bkt_223_);
v___x_245_ = lean_array_uset(v_buckets_x27_243_, v___x_222_, v___x_244_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_245_);
v___x_247_ = v___x_208_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_size_205_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2(lean_object* v_a_250_, lean_object* v_e_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = lean_st_ref_take(v_a_250_);
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v___x_254_, v_e_251_, v_a_252_);
v___x_256_ = lean_st_ref_set(v_a_250_, v___x_255_);
v___x_257_ = lean_box(0);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2___boxed(lean_object* v_a_258_, lean_object* v_e_259_, lean_object* v_a_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2(v_a_258_, v_e_259_, v_a_260_);
lean_dec(v_a_258_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_263_, lean_object* v_x_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_apply_1(v_x_264_, lean_box(0));
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_270_, lean_object* v_x_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(v_00_u03b1_270_, v_x_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_275_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = l_Lean_maxRecDepthErrorMessage;
v___x_282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3);
v___x_284_ = l_Lean_MessageData_ofFormat(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4);
v___x_286_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2));
v___x_287_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_ref_288_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_ref_288_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_ref_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_293_);
return v_res_295_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_box(0);
v___x_297_ = l_Lean_interruptExceptionId;
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg(){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(lean_object* v_x_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___y_310_; lean_object* v___y_320_; uint8_t v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; uint8_t v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; uint8_t v___y_336_; lean_object* v_fileName_342_; lean_object* v_fileMap_343_; lean_object* v_options_344_; lean_object* v_currRecDepth_345_; lean_object* v_maxRecDepth_346_; lean_object* v_ref_347_; lean_object* v_currNamespace_348_; lean_object* v_openDecls_349_; lean_object* v_initHeartbeats_350_; lean_object* v_maxHeartbeats_351_; lean_object* v_quotContext_352_; lean_object* v_currMacroScope_353_; uint8_t v_diag_354_; lean_object* v_cancelTk_x3f_355_; uint8_t v_suppressElabErrors_356_; lean_object* v_inheritedTraceOptions_357_; 
v_fileName_342_ = lean_ctor_get(v___y_306_, 0);
v_fileMap_343_ = lean_ctor_get(v___y_306_, 1);
v_options_344_ = lean_ctor_get(v___y_306_, 2);
v_currRecDepth_345_ = lean_ctor_get(v___y_306_, 3);
v_maxRecDepth_346_ = lean_ctor_get(v___y_306_, 4);
v_ref_347_ = lean_ctor_get(v___y_306_, 5);
v_currNamespace_348_ = lean_ctor_get(v___y_306_, 6);
v_openDecls_349_ = lean_ctor_get(v___y_306_, 7);
v_initHeartbeats_350_ = lean_ctor_get(v___y_306_, 8);
v_maxHeartbeats_351_ = lean_ctor_get(v___y_306_, 9);
v_quotContext_352_ = lean_ctor_get(v___y_306_, 10);
v_currMacroScope_353_ = lean_ctor_get(v___y_306_, 11);
v_diag_354_ = lean_ctor_get_uint8(v___y_306_, sizeof(void*)*14);
v_cancelTk_x3f_355_ = lean_ctor_get(v___y_306_, 12);
v_suppressElabErrors_356_ = lean_ctor_get_uint8(v___y_306_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_357_ = lean_ctor_get(v___y_306_, 13);
if (lean_obj_tag(v_cancelTk_x3f_355_) == 1)
{
lean_object* v_val_363_; uint8_t v___x_364_; 
v_val_363_ = lean_ctor_get(v_cancelTk_x3f_355_, 0);
v___x_364_ = l_IO_CancelToken_isSet(v_val_363_);
if (v___x_364_ == 0)
{
goto v___jp_358_;
}
else
{
lean_object* v___x_365_; lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v_x_304_);
v___x_365_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
goto v___jp_358_;
}
v___jp_309_:
{
if (lean_obj_tag(v___y_310_) == 0)
{
return v___y_310_;
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_a_311_ = lean_ctor_get(v___y_310_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___y_310_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___y_310_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___y_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
v___jp_319_:
{
if (v___y_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = lean_nat_add(v___y_327_, v___x_337_);
lean_inc_ref(v___y_320_);
lean_inc(v___y_324_);
lean_inc(v___y_323_);
lean_inc(v___y_329_);
lean_inc(v___y_325_);
lean_inc(v___y_333_);
lean_inc(v___y_322_);
lean_inc(v___y_331_);
lean_inc(v___y_330_);
lean_inc(v___y_334_);
lean_inc_ref(v___y_335_);
lean_inc_ref(v___y_328_);
lean_inc_ref(v___y_332_);
v___x_339_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_339_, 0, v___y_332_);
lean_ctor_set(v___x_339_, 1, v___y_328_);
lean_ctor_set(v___x_339_, 2, v___y_335_);
lean_ctor_set(v___x_339_, 3, v___x_338_);
lean_ctor_set(v___x_339_, 4, v___y_334_);
lean_ctor_set(v___x_339_, 5, v___y_330_);
lean_ctor_set(v___x_339_, 6, v___y_331_);
lean_ctor_set(v___x_339_, 7, v___y_322_);
lean_ctor_set(v___x_339_, 8, v___y_333_);
lean_ctor_set(v___x_339_, 9, v___y_325_);
lean_ctor_set(v___x_339_, 10, v___y_329_);
lean_ctor_set(v___x_339_, 11, v___y_323_);
lean_ctor_set(v___x_339_, 12, v___y_324_);
lean_ctor_set(v___x_339_, 13, v___y_320_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*14, v___y_326_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*14 + 1, v___y_321_);
lean_inc(v___y_307_);
lean_inc(v___y_305_);
v___x_340_ = lean_apply_4(v_x_304_, v___y_305_, v___x_339_, v___y_307_, lean_box(0));
v___y_310_ = v___x_340_;
goto v___jp_309_;
}
else
{
lean_object* v___x_341_; 
lean_dec_ref(v_x_304_);
lean_inc(v___y_330_);
v___x_341_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v___y_330_);
v___y_310_ = v___x_341_;
goto v___jp_309_;
}
}
v___jp_358_:
{
lean_object* v___x_359_; uint8_t v___x_360_; uint8_t v___x_361_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_nat_dec_eq(v_maxRecDepth_346_, v___x_359_);
v___x_361_ = lean_bool_not(v___x_360_);
if (v___x_361_ == 0)
{
v___y_320_ = v_inheritedTraceOptions_357_;
v___y_321_ = v_suppressElabErrors_356_;
v___y_322_ = v_openDecls_349_;
v___y_323_ = v_currMacroScope_353_;
v___y_324_ = v_cancelTk_x3f_355_;
v___y_325_ = v_maxHeartbeats_351_;
v___y_326_ = v_diag_354_;
v___y_327_ = v_currRecDepth_345_;
v___y_328_ = v_fileMap_343_;
v___y_329_ = v_quotContext_352_;
v___y_330_ = v_ref_347_;
v___y_331_ = v_currNamespace_348_;
v___y_332_ = v_fileName_342_;
v___y_333_ = v_initHeartbeats_350_;
v___y_334_ = v_maxRecDepth_346_;
v___y_335_ = v_options_344_;
v___y_336_ = v___x_361_;
goto v___jp_319_;
}
else
{
uint8_t v___x_362_; 
v___x_362_ = lean_nat_dec_eq(v_currRecDepth_345_, v_maxRecDepth_346_);
v___y_320_ = v_inheritedTraceOptions_357_;
v___y_321_ = v_suppressElabErrors_356_;
v___y_322_ = v_openDecls_349_;
v___y_323_ = v_currMacroScope_353_;
v___y_324_ = v_cancelTk_x3f_355_;
v___y_325_ = v_maxHeartbeats_351_;
v___y_326_ = v_diag_354_;
v___y_327_ = v_currRecDepth_345_;
v___y_328_ = v_fileMap_343_;
v___y_329_ = v_quotContext_352_;
v___y_330_ = v_ref_347_;
v___y_331_ = v_currNamespace_348_;
v___y_332_ = v_fileName_342_;
v___y_333_ = v_initHeartbeats_350_;
v___y_334_ = v_maxRecDepth_346_;
v___y_335_ = v_options_344_;
v___y_336_ = v___x_362_;
goto v___jp_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(lean_object* v_pre_381_, lean_object* v_post_382_, size_t v_sz_383_, size_t v_i_384_, lean_object* v_bs_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
uint8_t v___x_390_; 
v___x_390_ = lean_usize_dec_lt(v_i_384_, v_sz_383_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_dec_ref(v_post_382_);
lean_dec_ref(v_pre_381_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v_bs_385_);
return v___x_391_;
}
else
{
lean_object* v_v_392_; lean_object* v___x_393_; 
v_v_392_ = lean_array_uget_borrowed(v_bs_385_, v_i_384_);
lean_inc(v_v_392_);
lean_inc_ref(v_post_382_);
lean_inc_ref(v_pre_381_);
v___x_393_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_381_, v_post_382_, v_v_392_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_395_; lean_object* v_bs_x27_396_; size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_393_, 1);
v___x_395_ = lean_unsigned_to_nat(0u);
v_bs_x27_396_ = lean_array_uset(v_bs_385_, v_i_384_, v___x_395_);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_add(v_i_384_, v___x_397_);
v___x_399_ = lean_array_uset(v_bs_x27_396_, v_i_384_, v_a_394_);
v_i_384_ = v___x_398_;
v_bs_385_ = v___x_399_;
goto _start;
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref(v_bs_385_);
lean_dec_ref(v_post_382_);
lean_dec_ref(v_pre_381_);
v_a_401_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_393_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_393_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(lean_object* v_pre_409_, lean_object* v_post_410_, lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
if (lean_obj_tag(v_x_411_) == 5)
{
lean_object* v_fn_418_; lean_object* v_arg_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_fn_418_ = lean_ctor_get(v_x_411_, 0);
lean_inc_ref(v_fn_418_);
v_arg_419_ = lean_ctor_get(v_x_411_, 1);
lean_inc_ref(v_arg_419_);
lean_dec_ref_known(v_x_411_, 2);
v___x_420_ = lean_array_set(v_x_412_, v_x_413_, v_arg_419_);
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_sub(v_x_413_, v___x_421_);
lean_dec(v_x_413_);
v_x_411_ = v_fn_418_;
v_x_412_ = v___x_420_;
v_x_413_ = v___x_422_;
goto _start;
}
else
{
lean_object* v___x_424_; 
lean_dec(v_x_413_);
lean_inc_ref(v_post_410_);
lean_inc_ref(v_pre_409_);
v___x_424_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_409_, v_post_410_, v_x_411_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; size_t v_sz_426_; size_t v___x_427_; lean_object* v___x_428_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v_sz_426_ = lean_array_size(v_x_412_);
v___x_427_ = ((size_t)0ULL);
lean_inc_ref(v_post_410_);
lean_inc_ref(v_pre_409_);
v___x_428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_409_, v_post_410_, v_sz_426_, v___x_427_, v_x_412_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
v___x_430_ = l_Lean_mkAppN(v_a_425_, v_a_429_);
lean_dec(v_a_429_);
v___x_431_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_409_, v_post_410_, v___x_430_, v___y_414_, v___y_415_, v___y_416_);
return v___x_431_;
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v_a_425_);
lean_dec_ref(v_post_410_);
lean_dec_ref(v_pre_409_);
v_a_432_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_428_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_428_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
else
{
lean_dec_ref(v_x_412_);
lean_dec_ref(v_post_410_);
lean_dec_ref(v_pre_409_);
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(lean_object* v___x_440_, lean_object* v_pre_441_, lean_object* v_e_442_, lean_object* v_post_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; uint8_t v___y_452_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; uint8_t v___y_456_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; uint8_t v___y_469_; lean_object* v___y_470_; uint8_t v___y_471_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; uint8_t v___y_482_; lean_object* v___y_483_; uint8_t v___y_484_; lean_object* v___x_491_; 
v___x_491_ = l_Lean_Core_checkSystem(v___x_440_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_492_; 
lean_dec_ref_known(v___x_491_, 1);
lean_inc_ref(v_pre_441_);
lean_inc(v___y_446_);
lean_inc_ref(v___y_445_);
lean_inc_ref(v_e_442_);
v___x_492_ = lean_apply_4(v_pre_441_, v_e_442_, v___y_445_, v___y_446_, lean_box(0));
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_582_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_582_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_582_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_582_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___y_498_; 
switch(lean_obj_tag(v_a_493_))
{
case 0:
{
lean_object* v_e_572_; lean_object* v___x_574_; 
lean_dec_ref(v_post_443_);
lean_dec_ref(v_e_442_);
lean_dec_ref(v_pre_441_);
v_e_572_ = lean_ctor_get(v_a_493_, 0);
lean_inc_ref(v_e_572_);
lean_dec_ref_known(v_a_493_, 1);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v_e_572_);
v___x_574_ = v___x_495_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_e_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
case 1:
{
lean_object* v_e_576_; lean_object* v___x_577_; 
lean_del_object(v___x_495_);
lean_dec_ref(v_e_442_);
v_e_576_ = lean_ctor_get(v_a_493_, 0);
lean_inc_ref(v_e_576_);
lean_dec_ref_known(v_a_493_, 1);
lean_inc_ref(v_post_443_);
lean_inc_ref(v_pre_441_);
v___x_577_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_441_, v_post_443_, v_e_576_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_579_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_577_, 1);
v___x_579_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v_a_578_, v___y_444_, v___y_445_, v___y_446_);
return v___x_579_;
}
else
{
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_441_);
return v___x_577_;
}
}
default: 
{
lean_object* v_e_x3f_580_; 
lean_del_object(v___x_495_);
v_e_x3f_580_ = lean_ctor_get(v_a_493_, 0);
lean_inc(v_e_x3f_580_);
lean_dec_ref_known(v_a_493_, 1);
if (lean_obj_tag(v_e_x3f_580_) == 0)
{
v___y_498_ = v_e_442_;
goto v___jp_497_;
}
else
{
lean_object* v_val_581_; 
lean_dec_ref(v_e_442_);
v_val_581_ = lean_ctor_get(v_e_x3f_580_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v_e_x3f_580_, 1);
v___y_498_ = v_val_581_;
goto v___jp_497_;
}
}
}
v___jp_497_:
{
switch(lean_obj_tag(v___y_498_))
{
case 7:
{
lean_object* v_binderName_499_; lean_object* v_binderType_500_; lean_object* v_body_501_; uint8_t v_binderInfo_502_; lean_object* v___x_503_; 
v_binderName_499_ = lean_ctor_get(v___y_498_, 0);
lean_inc(v_binderName_499_);
v_binderType_500_ = lean_ctor_get(v___y_498_, 1);
v_body_501_ = lean_ctor_get(v___y_498_, 2);
v_binderInfo_502_ = lean_ctor_get_uint8(v___y_498_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_500_);
lean_inc_ref(v_post_443_);
lean_inc_ref(v_pre_441_);
v___x_503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_441_, v_post_443_, v_binderType_500_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
lean_inc_ref(v_body_501_);
lean_inc_ref(v_post_443_);
lean_inc_ref(v_pre_441_);
v___x_505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_441_, v_post_443_, v_body_501_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; size_t v___x_507_; size_t v___x_508_; uint8_t v___x_509_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = lean_ptr_addr(v_binderType_500_);
v___x_508_ = lean_ptr_addr(v_a_504_);
v___x_509_ = lean_usize_dec_eq(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
v___y_479_ = v_binderName_499_;
v___y_480_ = v___y_498_;
v___y_481_ = v_a_506_;
v___y_482_ = v_binderInfo_502_;
v___y_483_ = v_a_504_;
v___y_484_ = v___x_509_;
goto v___jp_478_;
}
else
{
size_t v___x_510_; size_t v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_ptr_addr(v_body_501_);
v___x_511_ = lean_ptr_addr(v_a_506_);
v___x_512_ = lean_usize_dec_eq(v___x_510_, v___x_511_);
v___y_479_ = v_binderName_499_;
v___y_480_ = v___y_498_;
v___y_481_ = v_a_506_;
v___y_482_ = v_binderInfo_502_;
v___y_483_ = v_a_504_;
v___y_484_ = v___x_512_;
goto v___jp_478_;
}
}
else
{
lean_dec(v_a_504_);
lean_dec(v_binderName_499_);
lean_dec_ref_known(v___y_498_, 3);
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_441_);
return v___x_505_;
}
}
else
{
lean_dec_ref_known(v___y_498_, 3);
lean_dec(v_binderName_499_);
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_441_);
return v___x_503_;
}
}
case 6:
{
lean_object* v_binderName_513_; lean_object* v_binderType_514_; lean_object* v_body_515_; uint8_t v_binderInfo_516_; lean_object* v___x_517_; 
v_binderName_513_ = lean_ctor_get(v___y_498_, 0);
lean_inc(v_binderName_513_);
v_binderType_514_ = lean_ctor_get(v___y_498_, 1);
v_body_515_ = lean_ctor_get(v___y_498_, 2);
v_binderInfo_516_ = lean_ctor_get_uint8(v___y_498_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_514_);
lean_inc_ref(v_post_443_);
lean_inc_ref(v_pre_441_);
v___x_517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_441_, v_post_443_, v_binderType_514_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_519_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
lean_inc_ref(v_body_515_);
lean_inc_ref(v_post_443_);
lean_inc_ref(v_pre_441_);
v___x_519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_441_, v_post_443_, v_body_515_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; size_t v___x_521_; size_t v___x_522_; uint8_t v___x_523_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = lean_ptr_addr(v_binderType_514_);
v___x_522_ = lean_ptr_addr(v_a_518_);
v___x_523_ = lean_usize_dec_eq(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
v___y_466_ = v_a_520_;
v___y_467_ = v___y_498_;
v___y_468_ = v_a_518_;
v___y_469_ = v_binderInfo_516_;
v___y_470_ = v_binderName_513_;
v___y_471_ = v___x_523_;
goto v___jp_465_;
}
else
{
size_t v___x_524_; size_t v___x_525_; uint8_t v___x_526_; 
v___x_524_ = lean_ptr_addr(v_body_515_);
v___x_525_ = lean_ptr_addr(v_a_520_);
v___x_526_ = lean_usize_dec_eq(v___x_524_, v___x_525_);
v___y_466_ = v_a_520_;
v___y_467_ = v___y_498_;
v___y_468_ = v_a_518_;
v___y_469_ = v_binderInfo_516_;
v___y_470_ = v_binderName_513_;
v___y_471_ = v___x_526_;
goto v___jp_465_;
}
}
else
{
lean_dec(v_a_518_);
lean_dec(v_binderName_513_);
lean_dec_ref_known(v___y_498_, 3);
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_441_);
return v___x_519_;
}
}
else
{
lean_dec(v_binderName_513_);
lean_dec_ref_known(v___y_498_, 3);
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_441_);
return v___x_517_;
}
}
case 8:
{
lean_object* v_declName_527_; lean_object* v_type_528_; lean_object* v_value_529_; lean_object* v_body_530_; uint8_t v_nondep_531_; lean_object* v___x_532_; 
v_declName_527_ = lean_ctor_get(v___y_498_, 0);
lean_inc(v_declName_527_);
v_type_528_ = lean_ctor_get(v___y_498_, 1);
v_value_529_ = lean_ctor_get(v___y_498_, 2);
v_body_530_ = lean_ctor_get(v___y_498_, 3);
lean_inc_ref(v_body_530_);
v_nondep_531_ = lean_ctor_get_uint8(v___y_498_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_528_);
lean_inc_ref(v_post_443_);
lean_inc_ref(v_pre_441_);
v___x_532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_441_, v_post_443_, v_type_528_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
lean_inc_ref(v_value_529_);
lean_inc_ref(v_post_443_);
lean_inc_ref(v_pre_441_);
v___x_534_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_441_, v_post_443_, v_value_529_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_534_, 1);
lean_inc_ref(v_body_530_);
lean_inc_ref(v_post_443_);
lean_inc_ref(v_pre_441_);
v___x_536_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_441_, v_post_443_, v_body_530_, v___y_444_, v___y_445_, v___y_446_);
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
v___y_449_ = v_declName_527_;
v___y_450_ = v___y_498_;
v___y_451_ = v_a_537_;
v___y_452_ = v_nondep_531_;
v___y_453_ = v_a_535_;
v___y_454_ = v_a_533_;
v___y_455_ = v_body_530_;
v___y_456_ = v___x_540_;
goto v___jp_448_;
}
else
{
size_t v___x_541_; size_t v___x_542_; uint8_t v___x_543_; 
v___x_541_ = lean_ptr_addr(v_value_529_);
v___x_542_ = lean_ptr_addr(v_a_535_);
v___x_543_ = lean_usize_dec_eq(v___x_541_, v___x_542_);
v___y_449_ = v_declName_527_;
v___y_450_ = v___y_498_;
v___y_451_ = v_a_537_;
v___y_452_ = v_nondep_531_;
v___y_453_ = v_a_535_;
v___y_454_ = v_a_533_;
v___y_455_ = v_body_530_;
v___y_456_ = v___x_543_;
goto v___jp_448_;
}
}
else
{
lean_dec(v_a_535_);
lean_dec(v_a_533_);
lean_dec_ref(v_body_530_);
lean_dec_ref_known(v___y_498_, 4);
lean_dec(v_declName_527_);
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_441_);
return v___x_536_;
}
}
else
{
lean_dec(v_a_533_);
lean_dec_ref(v_body_530_);
lean_dec(v_declName_527_);
lean_dec_ref_known(v___y_498_, 4);
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_441_);
return v___x_534_;
}
}
else
{
lean_dec_ref(v_body_530_);
lean_dec_ref_known(v___y_498_, 4);
lean_dec(v_declName_527_);
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_441_);
return v___x_532_;
}
}
case 5:
{
lean_object* v_dummy_544_; lean_object* v_nargs_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_dummy_544_ = lean_obj_once(&l_Lean_Elab_WF_floatRecApp___lam__1___closed__0, &l_Lean_Elab_WF_floatRecApp___lam__1___closed__0_once, _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__0);
v_nargs_545_ = l_Lean_Expr_getAppNumArgs(v___y_498_);
lean_inc(v_nargs_545_);
v___x_546_ = lean_mk_array(v_nargs_545_, v_dummy_544_);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_sub(v_nargs_545_, v___x_547_);
lean_dec(v_nargs_545_);
v___x_549_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_441_, v_post_443_, v___y_498_, v___x_546_, v___x_548_, v___y_444_, v___y_445_, v___y_446_);
return v___x_549_;
}
case 10:
{
lean_object* v_data_550_; lean_object* v_expr_551_; lean_object* v___x_552_; 
v_data_550_ = lean_ctor_get(v___y_498_, 0);
v_expr_551_ = lean_ctor_get(v___y_498_, 1);
lean_inc_ref(v_expr_551_);
lean_inc_ref(v_post_443_);
lean_inc_ref(v_pre_441_);
v___x_552_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_441_, v_post_443_, v_expr_551_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; size_t v___x_554_; size_t v___x_555_; uint8_t v___x_556_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v___x_554_ = lean_ptr_addr(v_expr_551_);
v___x_555_ = lean_ptr_addr(v_a_553_);
v___x_556_ = lean_usize_dec_eq(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_inc(v_data_550_);
lean_dec_ref_known(v___y_498_, 2);
v___x_557_ = l_Lean_Expr_mdata___override(v_data_550_, v_a_553_);
v___x_558_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___x_557_, v___y_444_, v___y_445_, v___y_446_);
return v___x_558_;
}
else
{
lean_object* v___x_559_; 
lean_dec(v_a_553_);
v___x_559_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___y_498_, v___y_444_, v___y_445_, v___y_446_);
return v___x_559_;
}
}
else
{
lean_dec_ref_known(v___y_498_, 2);
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_441_);
return v___x_552_;
}
}
case 11:
{
lean_object* v_typeName_560_; lean_object* v_idx_561_; lean_object* v_struct_562_; lean_object* v___x_563_; 
v_typeName_560_ = lean_ctor_get(v___y_498_, 0);
v_idx_561_ = lean_ctor_get(v___y_498_, 1);
v_struct_562_ = lean_ctor_get(v___y_498_, 2);
lean_inc_ref(v_struct_562_);
lean_inc_ref(v_post_443_);
lean_inc_ref(v_pre_441_);
v___x_563_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_441_, v_post_443_, v_struct_562_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; size_t v___x_565_; size_t v___x_566_; uint8_t v___x_567_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
v___x_565_ = lean_ptr_addr(v_struct_562_);
v___x_566_ = lean_ptr_addr(v_a_564_);
v___x_567_ = lean_usize_dec_eq(v___x_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_inc(v_idx_561_);
lean_inc(v_typeName_560_);
lean_dec_ref_known(v___y_498_, 3);
v___x_568_ = l_Lean_Expr_proj___override(v_typeName_560_, v_idx_561_, v_a_564_);
v___x_569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___x_568_, v___y_444_, v___y_445_, v___y_446_);
return v___x_569_;
}
else
{
lean_object* v___x_570_; 
lean_dec(v_a_564_);
v___x_570_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___y_498_, v___y_444_, v___y_445_, v___y_446_);
return v___x_570_;
}
}
else
{
lean_dec_ref_known(v___y_498_, 3);
lean_dec_ref(v_post_443_);
lean_dec_ref(v_pre_441_);
return v___x_563_;
}
}
default: 
{
lean_object* v___x_571_; 
v___x_571_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___y_498_, v___y_444_, v___y_445_, v___y_446_);
return v___x_571_;
}
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v_post_443_);
lean_dec_ref(v_e_442_);
lean_dec_ref(v_pre_441_);
v_a_583_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_492_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_492_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec_ref(v_post_443_);
lean_dec_ref(v_e_442_);
lean_dec_ref(v_pre_441_);
v_a_591_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_491_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_491_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
v___jp_448_:
{
if (v___y_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec_ref(v___y_455_);
lean_dec_ref(v___y_450_);
v___x_457_ = l_Lean_Expr_letE___override(v___y_449_, v___y_454_, v___y_453_, v___y_451_, v___y_452_);
v___x_458_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___x_457_, v___y_444_, v___y_445_, v___y_446_);
return v___x_458_;
}
else
{
size_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v___x_459_ = lean_ptr_addr(v___y_455_);
lean_dec_ref(v___y_455_);
v___x_460_ = lean_ptr_addr(v___y_451_);
v___x_461_ = lean_usize_dec_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec_ref(v___y_450_);
v___x_462_ = l_Lean_Expr_letE___override(v___y_449_, v___y_454_, v___y_453_, v___y_451_, v___y_452_);
v___x_463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___x_462_, v___y_444_, v___y_445_, v___y_446_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; 
lean_dec_ref(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_449_);
v___x_464_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___y_450_, v___y_444_, v___y_445_, v___y_446_);
return v___x_464_;
}
}
}
v___jp_465_:
{
if (v___y_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_dec_ref(v___y_467_);
v___x_472_ = l_Lean_Expr_lam___override(v___y_470_, v___y_468_, v___y_466_, v___y_469_);
v___x_473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___x_472_, v___y_444_, v___y_445_, v___y_446_);
return v___x_473_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = l_Lean_instBEqBinderInfo_beq(v___y_469_, v___y_469_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec_ref(v___y_467_);
v___x_475_ = l_Lean_Expr_lam___override(v___y_470_, v___y_468_, v___y_466_, v___y_469_);
v___x_476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___x_475_, v___y_444_, v___y_445_, v___y_446_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; 
lean_dec(v___y_470_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v___y_466_);
v___x_477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___y_467_, v___y_444_, v___y_445_, v___y_446_);
return v___x_477_;
}
}
}
v___jp_478_:
{
if (v___y_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec_ref(v___y_480_);
v___x_485_ = l_Lean_Expr_forallE___override(v___y_479_, v___y_483_, v___y_481_, v___y_482_);
v___x_486_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___x_485_, v___y_444_, v___y_445_, v___y_446_);
return v___x_486_;
}
else
{
uint8_t v___x_487_; 
v___x_487_ = l_Lean_instBEqBinderInfo_beq(v___y_482_, v___y_482_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec_ref(v___y_480_);
v___x_488_ = l_Lean_Expr_forallE___override(v___y_479_, v___y_483_, v___y_481_, v___y_482_);
v___x_489_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___x_488_, v___y_444_, v___y_445_, v___y_446_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; 
lean_dec_ref(v___y_483_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_479_);
v___x_490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_441_, v_post_443_, v___y_480_, v___y_444_, v___y_445_, v___y_446_);
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed(lean_object* v___x_599_, lean_object* v_pre_600_, lean_object* v_e_601_, lean_object* v_post_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(v___x_599_, v_pre_600_, v_e_601_, v_post_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(lean_object* v_pre_608_, lean_object* v_post_609_, lean_object* v_e_610_, lean_object* v_a_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_inc(v_a_611_);
v___x_615_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_615_, 0, lean_box(0));
lean_closure_set(v___x_615_, 1, lean_box(0));
lean_closure_set(v___x_615_, 2, v_a_611_);
v___x_616_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_box(0), v___x_615_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_648_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_648_ == 0)
{
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_648_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_648_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; 
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_a_617_, v_e_610_);
lean_dec(v_a_617_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v___x_622_; lean_object* v___f_623_; lean_object* v___x_624_; 
lean_del_object(v___x_619_);
v___x_622_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___closed__0));
lean_inc_ref(v_e_610_);
v___f_623_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_623_, 0, v___x_622_);
lean_closure_set(v___f_623_, 1, v_pre_608_);
lean_closure_set(v___f_623_, 2, v_e_610_);
lean_closure_set(v___f_623_, 3, v_post_609_);
v___x_624_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v___f_623_, v_a_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___f_626_; lean_object* v___x_627_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc_n(v_a_625_, 2);
lean_dec_ref_known(v___x_624_, 1);
lean_inc(v_a_611_);
v___f_626_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_626_, 0, v_a_611_);
lean_closure_set(v___f_626_, 1, v_e_610_);
lean_closure_set(v___f_626_, 2, v_a_625_);
v___x_627_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_box(0), v___f_626_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v___x_627_, 0);
lean_dec(v_unused_635_);
v___x_629_ = v___x_627_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_dec(v___x_627_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v_a_625_);
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_625_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec(v_a_625_);
v_a_636_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_627_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_627_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_dec_ref(v_e_610_);
return v___x_624_;
}
}
else
{
lean_object* v_val_644_; lean_object* v___x_646_; 
lean_dec_ref(v_e_610_);
lean_dec_ref(v_post_609_);
lean_dec_ref(v_pre_608_);
v_val_644_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v___x_621_, 1);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v_val_644_);
v___x_646_ = v___x_619_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_val_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v_e_610_);
lean_dec_ref(v_post_609_);
lean_dec_ref(v_pre_608_);
v_a_649_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_616_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_616_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(lean_object* v_pre_657_, lean_object* v_post_658_, lean_object* v_e_659_, lean_object* v_a_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; 
lean_inc_ref(v_post_658_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc_ref(v_e_659_);
v___x_664_ = lean_apply_4(v_post_658_, v_e_659_, v___y_661_, v___y_662_, lean_box(0));
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_683_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_683_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_683_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_683_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
switch(lean_obj_tag(v_a_665_))
{
case 0:
{
lean_object* v_e_669_; lean_object* v___x_671_; 
lean_dec_ref(v_e_659_);
lean_dec_ref(v_post_658_);
lean_dec_ref(v_pre_657_);
v_e_669_ = lean_ctor_get(v_a_665_, 0);
lean_inc_ref(v_e_669_);
lean_dec_ref_known(v_a_665_, 1);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v_e_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_e_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
case 1:
{
lean_object* v_e_673_; lean_object* v___x_674_; 
lean_del_object(v___x_667_);
lean_dec_ref(v_e_659_);
v_e_673_ = lean_ctor_get(v_a_665_, 0);
lean_inc_ref(v_e_673_);
lean_dec_ref_known(v_a_665_, 1);
v___x_674_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_657_, v_post_658_, v_e_673_, v_a_660_, v___y_661_, v___y_662_);
return v___x_674_;
}
default: 
{
lean_object* v_e_x3f_675_; 
lean_dec_ref(v_post_658_);
lean_dec_ref(v_pre_657_);
v_e_x3f_675_ = lean_ctor_get(v_a_665_, 0);
lean_inc(v_e_x3f_675_);
lean_dec_ref_known(v_a_665_, 1);
if (lean_obj_tag(v_e_x3f_675_) == 0)
{
lean_object* v___x_677_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v_e_659_);
v___x_677_ = v___x_667_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_e_659_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
else
{
lean_object* v_val_679_; lean_object* v___x_681_; 
lean_dec_ref(v_e_659_);
v_val_679_ = lean_ctor_get(v_e_x3f_675_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v_e_x3f_675_, 1);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v_val_679_);
v___x_681_ = v___x_667_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_val_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v_e_659_);
lean_dec_ref(v_post_658_);
lean_dec_ref(v_pre_657_);
v_a_684_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_664_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_664_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_692_, lean_object* v_post_693_, lean_object* v_e_694_, lean_object* v_a_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_692_, v_post_693_, v_e_694_, v_a_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v_a_695_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_700_, lean_object* v_post_701_, lean_object* v_sz_702_, lean_object* v_i_703_, lean_object* v_bs_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
size_t v_sz_boxed_709_; size_t v_i_boxed_710_; lean_object* v_res_711_; 
v_sz_boxed_709_ = lean_unbox_usize(v_sz_702_);
lean_dec(v_sz_702_);
v_i_boxed_710_ = lean_unbox_usize(v_i_703_);
lean_dec(v_i_703_);
v_res_711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_700_, v_post_701_, v_sz_boxed_709_, v_i_boxed_710_, v_bs_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_712_, lean_object* v_post_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_712_, v_post_713_, v_x_714_, v_x_715_, v_x_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___boxed(lean_object* v_pre_722_, lean_object* v_post_723_, lean_object* v_e_724_, lean_object* v_a_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_722_, v_post_723_, v_e_724_, v_a_725_, v___y_726_, v___y_727_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v_a_725_);
return v_res_729_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = lean_box(0);
v___x_731_ = lean_unsigned_to_nat(16u);
v___x_732_ = lean_mk_array(v___x_731_, v___x_730_);
return v___x_732_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0);
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v___x_733_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1);
v___x_737_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_737_, 0, lean_box(0));
lean_closure_set(v___x_737_, 1, lean_box(0));
lean_closure_set(v___x_737_, 2, v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(lean_object* v_input_738_, lean_object* v_pre_739_, lean_object* v_post_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_a_746_; lean_object* v___x_747_; 
v___x_744_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2);
v___x_745_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_box(0), v___x_744_, v___y_741_, v___y_742_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref(v___x_745_);
v___x_747_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_739_, v_post_740_, v_input_738_, v_a_746_, v___y_741_, v___y_742_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v___x_749_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_749_, 0, lean_box(0));
lean_closure_set(v___x_749_, 1, lean_box(0));
lean_closure_set(v___x_749_, 2, v_a_746_);
v___x_750_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_box(0), v___x_749_, v___y_741_, v___y_742_);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v___x_750_, 0);
lean_dec(v_unused_758_);
v___x_752_ = v___x_750_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_dec(v___x_750_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v_a_748_);
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_748_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_dec(v_a_746_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___boxed(lean_object* v_input_759_, lean_object* v_pre_760_, lean_object* v_post_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(v_input_759_, v_pre_760_, v_post_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp(lean_object* v_e_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___x_774_; 
v___f_772_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___closed__0));
v___f_773_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___closed__1));
v___x_774_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(v_e_768_, v___f_772_, v___f_773_, v_a_769_, v_a_770_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___boxed(lean_object* v_e_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Elab_WF_floatRecApp(v_e_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_780_, lean_object* v_m_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_m_781_, v_a_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_784_, lean_object* v_m_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(v_00_u03b2_784_, v_m_785_, v_a_786_);
lean_dec_ref(v_a_786_);
lean_dec_ref(v_m_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_788_, lean_object* v_ref_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_789_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_794_, lean_object* v_ref_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_794_, v_ref_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(lean_object* v_00_u03b1_810_, lean_object* v_x_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_811_, v___y_812_, v___y_813_, v___y_814_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b1_817_, lean_object* v_x_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(v_00_u03b1_817_, v_x_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_824_, lean_object* v_m_825_, lean_object* v_a_826_, lean_object* v_b_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v_m_825_, v_a_826_, v_b_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_829_, lean_object* v_a_830_, lean_object* v_x_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_a_830_, v_x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_00_u03b2_833_, lean_object* v_a_834_, lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_833_, v_a_834_, v_x_835_);
lean_dec(v_x_835_);
lean_dec_ref(v_a_834_);
return v_res_836_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_837_, lean_object* v_a_838_, lean_object* v_x_839_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_a_838_, v_x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_841_, lean_object* v_a_842_, lean_object* v_x_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_841_, v_a_842_, v_x_843_);
lean_dec(v_x_843_);
lean_dec_ref(v_a_842_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_846_, lean_object* v_data_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(v_data_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13(lean_object* v_00_u03b2_849_, lean_object* v_a_850_, lean_object* v_b_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(v_a_850_, v_b_851_, v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13(lean_object* v_00_u03b2_854_, lean_object* v_i_855_, lean_object* v_source_856_, lean_object* v_target_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v_i_855_, v_source_856_, v_target_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_x_860_, v_x_861_);
return v___x_862_;
}
}
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_RecAppSyntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
