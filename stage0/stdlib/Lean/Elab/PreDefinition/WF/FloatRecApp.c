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
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* v___f_6_; lean_object* v___x_443__overap_7_; lean_object* v___x_8_; 
v___f_6_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___closed__0));
v___x_443__overap_7_ = lean_panic_fn_borrowed(v___f_6_, v_msg_2_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_8_ = lean_apply_3(v___x_443__overap_7_, v___y_3_, v___y_4_, lean_box(0));
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
v___x_256_ = lean_st_ref_put(v_a_250_, v___x_255_);
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
lean_object* v___y_310_; uint8_t v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; uint8_t v___y_323_; lean_object* v___y_324_; lean_object* v_toCold_329_; lean_object* v_currRecDepth_330_; lean_object* v_ref_331_; uint8_t v_diag_332_; uint8_t v_suppressElabErrors_333_; lean_object* v_maxRecDepth_334_; lean_object* v_cancelTk_x3f_335_; 
v_toCold_329_ = lean_ctor_get(v___y_306_, 0);
v_currRecDepth_330_ = lean_ctor_get(v___y_306_, 1);
v_ref_331_ = lean_ctor_get(v___y_306_, 2);
v_diag_332_ = lean_ctor_get_uint8(v___y_306_, sizeof(void*)*3);
v_suppressElabErrors_333_ = lean_ctor_get_uint8(v___y_306_, sizeof(void*)*3 + 1);
v_maxRecDepth_334_ = lean_ctor_get(v_toCold_329_, 3);
v_cancelTk_x3f_335_ = lean_ctor_get(v_toCold_329_, 10);
if (lean_obj_tag(v_cancelTk_x3f_335_) == 1)
{
lean_object* v_val_341_; uint8_t v___x_342_; 
v_val_341_ = lean_ctor_get(v_cancelTk_x3f_335_, 0);
v___x_342_ = l_IO_CancelToken_isSet(v_val_341_);
if (v___x_342_ == 0)
{
goto v___jp_336_;
}
else
{
lean_object* v___x_343_; lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref(v_x_304_);
v___x_343_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
goto v___jp_336_;
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
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_nat_add(v___y_322_, v___x_325_);
lean_inc_ref(v___y_324_);
v___x_327_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_327_, 0, v___y_324_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
lean_ctor_set(v___x_327_, 2, v___y_321_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*3, v___y_320_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*3 + 1, v___y_323_);
lean_inc(v___y_307_);
lean_inc(v___y_305_);
v___x_328_ = lean_apply_4(v_x_304_, v___y_305_, v___x_327_, v___y_307_, lean_box(0));
v___y_310_ = v___x_328_;
goto v___jp_309_;
}
v___jp_336_:
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_nat_dec_eq(v_maxRecDepth_334_, v___x_337_);
if (v___x_338_ == 0)
{
uint8_t v___x_339_; 
v___x_339_ = lean_nat_dec_eq(v_currRecDepth_330_, v_maxRecDepth_334_);
if (v___x_339_ == 0)
{
lean_inc(v_ref_331_);
v___y_320_ = v_diag_332_;
v___y_321_ = v_ref_331_;
v___y_322_ = v_currRecDepth_330_;
v___y_323_ = v_suppressElabErrors_333_;
v___y_324_ = v_toCold_329_;
goto v___jp_319_;
}
else
{
lean_object* v___x_340_; 
lean_dec_ref(v_x_304_);
lean_inc(v_ref_331_);
v___x_340_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_331_);
v___y_310_ = v___x_340_;
goto v___jp_309_;
}
}
else
{
lean_inc(v_ref_331_);
v___y_320_ = v_diag_332_;
v___y_321_ = v_ref_331_;
v___y_322_ = v_currRecDepth_330_;
v___y_323_ = v_suppressElabErrors_333_;
v___y_324_ = v_toCold_329_;
goto v___jp_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_x_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(lean_object* v_pre_359_, lean_object* v_post_360_, size_t v_sz_361_, size_t v_i_362_, lean_object* v_bs_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
uint8_t v___x_368_; 
v___x_368_ = lean_usize_dec_lt(v_i_362_, v_sz_361_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_dec_ref(v_post_360_);
lean_dec_ref(v_pre_359_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v_bs_363_);
return v___x_369_;
}
else
{
lean_object* v_v_370_; lean_object* v___x_371_; 
v_v_370_ = lean_array_uget_borrowed(v_bs_363_, v_i_362_);
lean_inc(v_v_370_);
lean_inc_ref(v_post_360_);
lean_inc_ref(v_pre_359_);
v___x_371_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_359_, v_post_360_, v_v_370_, v___y_364_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; lean_object* v_bs_x27_374_; size_t v___x_375_; size_t v___x_376_; lean_object* v___x_377_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = lean_unsigned_to_nat(0u);
v_bs_x27_374_ = lean_array_uset(v_bs_363_, v_i_362_, v___x_373_);
v___x_375_ = ((size_t)1ULL);
v___x_376_ = lean_usize_add(v_i_362_, v___x_375_);
v___x_377_ = lean_array_uset(v_bs_x27_374_, v_i_362_, v_a_372_);
v_i_362_ = v___x_376_;
v_bs_363_ = v___x_377_;
goto _start;
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_dec_ref(v_bs_363_);
lean_dec_ref(v_post_360_);
lean_dec_ref(v_pre_359_);
v_a_379_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_371_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_371_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(lean_object* v_pre_387_, lean_object* v_post_388_, lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
if (lean_obj_tag(v_x_389_) == 5)
{
lean_object* v_fn_396_; lean_object* v_arg_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_fn_396_ = lean_ctor_get(v_x_389_, 0);
lean_inc_ref(v_fn_396_);
v_arg_397_ = lean_ctor_get(v_x_389_, 1);
lean_inc_ref(v_arg_397_);
lean_dec_ref_known(v_x_389_, 2);
v___x_398_ = lean_array_set(v_x_390_, v_x_391_, v_arg_397_);
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = lean_nat_sub(v_x_391_, v___x_399_);
lean_dec(v_x_391_);
v_x_389_ = v_fn_396_;
v_x_390_ = v___x_398_;
v_x_391_ = v___x_400_;
goto _start;
}
else
{
lean_object* v___x_402_; 
lean_dec(v_x_391_);
lean_inc_ref(v_post_388_);
lean_inc_ref(v_pre_387_);
v___x_402_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_387_, v_post_388_, v_x_389_, v___y_392_, v___y_393_, v___y_394_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; size_t v_sz_404_; size_t v___x_405_; lean_object* v___x_406_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v_sz_404_ = lean_array_size(v_x_390_);
v___x_405_ = ((size_t)0ULL);
lean_inc_ref(v_post_388_);
lean_inc_ref(v_pre_387_);
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_387_, v_post_388_, v_sz_404_, v___x_405_, v_x_390_, v___y_392_, v___y_393_, v___y_394_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = l_Lean_mkAppN(v_a_403_, v_a_407_);
lean_dec(v_a_407_);
v___x_409_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_387_, v_post_388_, v___x_408_, v___y_392_, v___y_393_, v___y_394_);
return v___x_409_;
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_a_403_);
lean_dec_ref(v_post_388_);
lean_dec_ref(v_pre_387_);
v_a_410_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_406_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_dec_ref(v_x_390_);
lean_dec_ref(v_post_388_);
lean_dec_ref(v_pre_387_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(lean_object* v___x_418_, lean_object* v_pre_419_, lean_object* v_e_420_, lean_object* v_post_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Core_checkSystem(v___x_418_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v___x_427_; 
lean_dec_ref_known(v___x_426_, 1);
lean_inc_ref(v_pre_419_);
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
lean_inc_ref(v_e_420_);
v___x_427_ = lean_apply_4(v_pre_419_, v_e_420_, v___y_423_, v___y_424_, lean_box(0));
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_543_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_543_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_543_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_543_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___y_433_; 
switch(lean_obj_tag(v_a_428_))
{
case 0:
{
lean_object* v_e_533_; lean_object* v___x_535_; 
lean_dec_ref(v_post_421_);
lean_dec_ref(v_e_420_);
lean_dec_ref(v_pre_419_);
v_e_533_ = lean_ctor_get(v_a_428_, 0);
lean_inc_ref(v_e_533_);
lean_dec_ref_known(v_a_428_, 1);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v_e_533_);
v___x_535_ = v___x_430_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_e_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
case 1:
{
lean_object* v_e_537_; lean_object* v___x_538_; 
lean_del_object(v___x_430_);
lean_dec_ref(v_e_420_);
v_e_537_ = lean_ctor_get(v_a_428_, 0);
lean_inc_ref(v_e_537_);
lean_dec_ref_known(v_a_428_, 1);
lean_inc_ref(v_post_421_);
lean_inc_ref(v_pre_419_);
v___x_538_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_419_, v_post_421_, v_e_537_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v___x_540_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v_a_539_, v___y_422_, v___y_423_, v___y_424_);
return v___x_540_;
}
else
{
lean_dec_ref(v_post_421_);
lean_dec_ref(v_pre_419_);
return v___x_538_;
}
}
default: 
{
lean_object* v_e_x3f_541_; 
lean_del_object(v___x_430_);
v_e_x3f_541_ = lean_ctor_get(v_a_428_, 0);
lean_inc(v_e_x3f_541_);
lean_dec_ref_known(v_a_428_, 1);
if (lean_obj_tag(v_e_x3f_541_) == 0)
{
v___y_433_ = v_e_420_;
goto v___jp_432_;
}
else
{
lean_object* v_val_542_; 
lean_dec_ref(v_e_420_);
v_val_542_ = lean_ctor_get(v_e_x3f_541_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v_e_x3f_541_, 1);
v___y_433_ = v_val_542_;
goto v___jp_432_;
}
}
}
v___jp_432_:
{
switch(lean_obj_tag(v___y_433_))
{
case 7:
{
lean_object* v_binderName_434_; lean_object* v_binderType_435_; lean_object* v_body_436_; uint8_t v_binderInfo_437_; lean_object* v___x_438_; 
v_binderName_434_ = lean_ctor_get(v___y_433_, 0);
v_binderType_435_ = lean_ctor_get(v___y_433_, 1);
v_body_436_ = lean_ctor_get(v___y_433_, 2);
v_binderInfo_437_ = lean_ctor_get_uint8(v___y_433_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_435_);
lean_inc_ref(v_post_421_);
lean_inc_ref(v_pre_419_);
v___x_438_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_419_, v_post_421_, v_binderType_435_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
lean_inc_ref(v_body_436_);
lean_inc_ref(v_post_421_);
lean_inc_ref(v_pre_419_);
v___x_440_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_419_, v_post_421_, v_body_436_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; size_t v___x_442_; size_t v___x_443_; uint8_t v___x_444_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v___x_442_ = lean_ptr_addr(v_binderType_435_);
v___x_443_ = lean_ptr_addr(v_a_439_);
v___x_444_ = lean_usize_dec_eq(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_inc(v_binderName_434_);
lean_dec_ref_known(v___y_433_, 3);
v___x_445_ = l_Lean_Expr_forallE___override(v_binderName_434_, v_a_439_, v_a_441_, v_binderInfo_437_);
v___x_446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___x_445_, v___y_422_, v___y_423_, v___y_424_);
return v___x_446_;
}
else
{
size_t v___x_447_; size_t v___x_448_; uint8_t v___x_449_; 
v___x_447_ = lean_ptr_addr(v_body_436_);
v___x_448_ = lean_ptr_addr(v_a_441_);
v___x_449_ = lean_usize_dec_eq(v___x_447_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_inc(v_binderName_434_);
lean_dec_ref_known(v___y_433_, 3);
v___x_450_ = l_Lean_Expr_forallE___override(v_binderName_434_, v_a_439_, v_a_441_, v_binderInfo_437_);
v___x_451_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___x_450_, v___y_422_, v___y_423_, v___y_424_);
return v___x_451_;
}
else
{
uint8_t v___x_452_; 
v___x_452_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_437_, v_binderInfo_437_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc(v_binderName_434_);
lean_dec_ref_known(v___y_433_, 3);
v___x_453_ = l_Lean_Expr_forallE___override(v_binderName_434_, v_a_439_, v_a_441_, v_binderInfo_437_);
v___x_454_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___x_453_, v___y_422_, v___y_423_, v___y_424_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; 
lean_dec(v_a_441_);
lean_dec(v_a_439_);
v___x_455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___y_433_, v___y_422_, v___y_423_, v___y_424_);
return v___x_455_;
}
}
}
}
else
{
lean_dec(v_a_439_);
lean_dec_ref_known(v___y_433_, 3);
lean_dec_ref(v_post_421_);
lean_dec_ref(v_pre_419_);
return v___x_440_;
}
}
else
{
lean_dec_ref_known(v___y_433_, 3);
lean_dec_ref(v_post_421_);
lean_dec_ref(v_pre_419_);
return v___x_438_;
}
}
case 6:
{
lean_object* v_binderName_456_; lean_object* v_binderType_457_; lean_object* v_body_458_; uint8_t v_binderInfo_459_; lean_object* v___x_460_; 
v_binderName_456_ = lean_ctor_get(v___y_433_, 0);
v_binderType_457_ = lean_ctor_get(v___y_433_, 1);
v_body_458_ = lean_ctor_get(v___y_433_, 2);
v_binderInfo_459_ = lean_ctor_get_uint8(v___y_433_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_457_);
lean_inc_ref(v_post_421_);
lean_inc_ref(v_pre_419_);
v___x_460_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_419_, v_post_421_, v_binderType_457_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
lean_inc_ref(v_body_458_);
lean_inc_ref(v_post_421_);
lean_inc_ref(v_pre_419_);
v___x_462_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_419_, v_post_421_, v_body_458_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = lean_ptr_addr(v_binderType_457_);
v___x_465_ = lean_ptr_addr(v_a_461_);
v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_inc(v_binderName_456_);
lean_dec_ref_known(v___y_433_, 3);
v___x_467_ = l_Lean_Expr_lam___override(v_binderName_456_, v_a_461_, v_a_463_, v_binderInfo_459_);
v___x_468_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___x_467_, v___y_422_, v___y_423_, v___y_424_);
return v___x_468_;
}
else
{
size_t v___x_469_; size_t v___x_470_; uint8_t v___x_471_; 
v___x_469_ = lean_ptr_addr(v_body_458_);
v___x_470_ = lean_ptr_addr(v_a_463_);
v___x_471_ = lean_usize_dec_eq(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; 
lean_inc(v_binderName_456_);
lean_dec_ref_known(v___y_433_, 3);
v___x_472_ = l_Lean_Expr_lam___override(v_binderName_456_, v_a_461_, v_a_463_, v_binderInfo_459_);
v___x_473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___x_472_, v___y_422_, v___y_423_, v___y_424_);
return v___x_473_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_459_, v_binderInfo_459_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_inc(v_binderName_456_);
lean_dec_ref_known(v___y_433_, 3);
v___x_475_ = l_Lean_Expr_lam___override(v_binderName_456_, v_a_461_, v_a_463_, v_binderInfo_459_);
v___x_476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___x_475_, v___y_422_, v___y_423_, v___y_424_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; 
lean_dec(v_a_463_);
lean_dec(v_a_461_);
v___x_477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___y_433_, v___y_422_, v___y_423_, v___y_424_);
return v___x_477_;
}
}
}
}
else
{
lean_dec(v_a_461_);
lean_dec_ref_known(v___y_433_, 3);
lean_dec_ref(v_post_421_);
lean_dec_ref(v_pre_419_);
return v___x_462_;
}
}
else
{
lean_dec_ref_known(v___y_433_, 3);
lean_dec_ref(v_post_421_);
lean_dec_ref(v_pre_419_);
return v___x_460_;
}
}
case 8:
{
lean_object* v_declName_478_; lean_object* v_type_479_; lean_object* v_value_480_; lean_object* v_body_481_; uint8_t v_nondep_482_; lean_object* v___x_483_; 
v_declName_478_ = lean_ctor_get(v___y_433_, 0);
v_type_479_ = lean_ctor_get(v___y_433_, 1);
v_value_480_ = lean_ctor_get(v___y_433_, 2);
v_body_481_ = lean_ctor_get(v___y_433_, 3);
v_nondep_482_ = lean_ctor_get_uint8(v___y_433_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_479_);
lean_inc_ref(v_post_421_);
lean_inc_ref(v_pre_419_);
v___x_483_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_419_, v_post_421_, v_type_479_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_485_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
lean_inc_ref(v_value_480_);
lean_inc_ref(v_post_421_);
lean_inc_ref(v_pre_419_);
v___x_485_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_419_, v_post_421_, v_value_480_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_487_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
lean_inc_ref(v_body_481_);
lean_inc_ref(v_post_421_);
lean_inc_ref(v_pre_419_);
v___x_487_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_419_, v_post_421_, v_body_481_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; size_t v___x_489_; size_t v___x_490_; uint8_t v___x_491_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = lean_ptr_addr(v_type_479_);
v___x_490_ = lean_ptr_addr(v_a_484_);
v___x_491_ = lean_usize_dec_eq(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_inc(v_declName_478_);
lean_dec_ref_known(v___y_433_, 4);
v___x_492_ = l_Lean_Expr_letE___override(v_declName_478_, v_a_484_, v_a_486_, v_a_488_, v_nondep_482_);
v___x_493_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___x_492_, v___y_422_, v___y_423_, v___y_424_);
return v___x_493_;
}
else
{
size_t v___x_494_; size_t v___x_495_; uint8_t v___x_496_; 
v___x_494_ = lean_ptr_addr(v_value_480_);
v___x_495_ = lean_ptr_addr(v_a_486_);
v___x_496_ = lean_usize_dec_eq(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_inc(v_declName_478_);
lean_dec_ref_known(v___y_433_, 4);
v___x_497_ = l_Lean_Expr_letE___override(v_declName_478_, v_a_484_, v_a_486_, v_a_488_, v_nondep_482_);
v___x_498_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___x_497_, v___y_422_, v___y_423_, v___y_424_);
return v___x_498_;
}
else
{
size_t v___x_499_; size_t v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_ptr_addr(v_body_481_);
v___x_500_ = lean_ptr_addr(v_a_488_);
v___x_501_ = lean_usize_dec_eq(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_inc(v_declName_478_);
lean_dec_ref_known(v___y_433_, 4);
v___x_502_ = l_Lean_Expr_letE___override(v_declName_478_, v_a_484_, v_a_486_, v_a_488_, v_nondep_482_);
v___x_503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___x_502_, v___y_422_, v___y_423_, v___y_424_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; 
lean_dec(v_a_488_);
lean_dec(v_a_486_);
lean_dec(v_a_484_);
v___x_504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___y_433_, v___y_422_, v___y_423_, v___y_424_);
return v___x_504_;
}
}
}
}
else
{
lean_dec(v_a_486_);
lean_dec(v_a_484_);
lean_dec_ref_known(v___y_433_, 4);
lean_dec_ref(v_post_421_);
lean_dec_ref(v_pre_419_);
return v___x_487_;
}
}
else
{
lean_dec(v_a_484_);
lean_dec_ref_known(v___y_433_, 4);
lean_dec_ref(v_post_421_);
lean_dec_ref(v_pre_419_);
return v___x_485_;
}
}
else
{
lean_dec_ref_known(v___y_433_, 4);
lean_dec_ref(v_post_421_);
lean_dec_ref(v_pre_419_);
return v___x_483_;
}
}
case 5:
{
lean_object* v_dummy_505_; lean_object* v_nargs_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_dummy_505_ = lean_obj_once(&l_Lean_Elab_WF_floatRecApp___lam__1___closed__0, &l_Lean_Elab_WF_floatRecApp___lam__1___closed__0_once, _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__0);
v_nargs_506_ = l_Lean_Expr_getAppNumArgs(v___y_433_);
lean_inc(v_nargs_506_);
v___x_507_ = lean_mk_array(v_nargs_506_, v_dummy_505_);
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_sub(v_nargs_506_, v___x_508_);
lean_dec(v_nargs_506_);
v___x_510_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_419_, v_post_421_, v___y_433_, v___x_507_, v___x_509_, v___y_422_, v___y_423_, v___y_424_);
return v___x_510_;
}
case 10:
{
lean_object* v_data_511_; lean_object* v_expr_512_; lean_object* v___x_513_; 
v_data_511_ = lean_ctor_get(v___y_433_, 0);
v_expr_512_ = lean_ctor_get(v___y_433_, 1);
lean_inc_ref(v_expr_512_);
lean_inc_ref(v_post_421_);
lean_inc_ref(v_pre_419_);
v___x_513_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_419_, v_post_421_, v_expr_512_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; size_t v___x_515_; size_t v___x_516_; uint8_t v___x_517_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = lean_ptr_addr(v_expr_512_);
v___x_516_ = lean_ptr_addr(v_a_514_);
v___x_517_ = lean_usize_dec_eq(v___x_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_inc(v_data_511_);
lean_dec_ref_known(v___y_433_, 2);
v___x_518_ = l_Lean_Expr_mdata___override(v_data_511_, v_a_514_);
v___x_519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___x_518_, v___y_422_, v___y_423_, v___y_424_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; 
lean_dec(v_a_514_);
v___x_520_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___y_433_, v___y_422_, v___y_423_, v___y_424_);
return v___x_520_;
}
}
else
{
lean_dec_ref_known(v___y_433_, 2);
lean_dec_ref(v_post_421_);
lean_dec_ref(v_pre_419_);
return v___x_513_;
}
}
case 11:
{
lean_object* v_typeName_521_; lean_object* v_idx_522_; lean_object* v_struct_523_; lean_object* v___x_524_; 
v_typeName_521_ = lean_ctor_get(v___y_433_, 0);
v_idx_522_ = lean_ctor_get(v___y_433_, 1);
v_struct_523_ = lean_ctor_get(v___y_433_, 2);
lean_inc_ref(v_struct_523_);
lean_inc_ref(v_post_421_);
lean_inc_ref(v_pre_419_);
v___x_524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_419_, v_post_421_, v_struct_523_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; size_t v___x_526_; size_t v___x_527_; uint8_t v___x_528_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = lean_ptr_addr(v_struct_523_);
v___x_527_ = lean_ptr_addr(v_a_525_);
v___x_528_ = lean_usize_dec_eq(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_inc(v_idx_522_);
lean_inc(v_typeName_521_);
lean_dec_ref_known(v___y_433_, 3);
v___x_529_ = l_Lean_Expr_proj___override(v_typeName_521_, v_idx_522_, v_a_525_);
v___x_530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___x_529_, v___y_422_, v___y_423_, v___y_424_);
return v___x_530_;
}
else
{
lean_object* v___x_531_; 
lean_dec(v_a_525_);
v___x_531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___y_433_, v___y_422_, v___y_423_, v___y_424_);
return v___x_531_;
}
}
else
{
lean_dec_ref_known(v___y_433_, 3);
lean_dec_ref(v_post_421_);
lean_dec_ref(v_pre_419_);
return v___x_524_;
}
}
default: 
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_419_, v_post_421_, v___y_433_, v___y_422_, v___y_423_, v___y_424_);
return v___x_532_;
}
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v_post_421_);
lean_dec_ref(v_e_420_);
lean_dec_ref(v_pre_419_);
v_a_544_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_427_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_427_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec_ref(v_post_421_);
lean_dec_ref(v_e_420_);
lean_dec_ref(v_pre_419_);
v_a_552_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_426_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_426_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed(lean_object* v___x_560_, lean_object* v_pre_561_, lean_object* v_e_562_, lean_object* v_post_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(v___x_560_, v_pre_561_, v_e_562_, v_post_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(lean_object* v_pre_569_, lean_object* v_post_570_, lean_object* v_e_571_, lean_object* v_a_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_inc(v_a_572_);
v___x_576_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_576_, 0, lean_box(0));
lean_closure_set(v___x_576_, 1, lean_box(0));
lean_closure_set(v___x_576_, 2, v_a_572_);
v___x_577_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_box(0), v___x_576_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_609_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_609_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_609_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_609_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_a_578_, v_e_571_);
lean_dec(v_a_578_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___x_585_; 
lean_del_object(v___x_580_);
v___x_583_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___closed__0));
lean_inc_ref(v_e_571_);
v___f_584_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_584_, 0, v___x_583_);
lean_closure_set(v___f_584_, 1, v_pre_569_);
lean_closure_set(v___f_584_, 2, v_e_571_);
lean_closure_set(v___f_584_, 3, v_post_570_);
v___x_585_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v___f_584_, v_a_572_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___f_587_; lean_object* v___x_588_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_n(v_a_586_, 2);
lean_dec_ref_known(v___x_585_, 1);
lean_inc(v_a_572_);
v___f_587_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_587_, 0, v_a_572_);
lean_closure_set(v___f_587_, 1, v_e_571_);
lean_closure_set(v___f_587_, 2, v_a_586_);
v___x_588_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_box(0), v___f_587_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v___x_588_, 0);
lean_dec(v_unused_596_);
v___x_590_ = v___x_588_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_dec(v___x_588_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v_a_586_);
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_586_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec(v_a_586_);
v_a_597_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_588_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_588_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_dec_ref(v_e_571_);
return v___x_585_;
}
}
else
{
lean_object* v_val_605_; lean_object* v___x_607_; 
lean_dec_ref(v_e_571_);
lean_dec_ref(v_post_570_);
lean_dec_ref(v_pre_569_);
v_val_605_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v___x_582_, 1);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v_val_605_);
v___x_607_ = v___x_580_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_val_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v_e_571_);
lean_dec_ref(v_post_570_);
lean_dec_ref(v_pre_569_);
v_a_610_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_577_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_577_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(lean_object* v_pre_618_, lean_object* v_post_619_, lean_object* v_e_620_, lean_object* v_a_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; 
lean_inc_ref(v_post_619_);
lean_inc(v___y_623_);
lean_inc_ref(v___y_622_);
lean_inc_ref(v_e_620_);
v___x_625_ = lean_apply_4(v_post_619_, v_e_620_, v___y_622_, v___y_623_, lean_box(0));
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_644_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_644_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_644_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_644_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
switch(lean_obj_tag(v_a_626_))
{
case 0:
{
lean_object* v_e_630_; lean_object* v___x_632_; 
lean_dec_ref(v_e_620_);
lean_dec_ref(v_post_619_);
lean_dec_ref(v_pre_618_);
v_e_630_ = lean_ctor_get(v_a_626_, 0);
lean_inc_ref(v_e_630_);
lean_dec_ref_known(v_a_626_, 1);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v_e_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_e_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
case 1:
{
lean_object* v_e_634_; lean_object* v___x_635_; 
lean_del_object(v___x_628_);
lean_dec_ref(v_e_620_);
v_e_634_ = lean_ctor_get(v_a_626_, 0);
lean_inc_ref(v_e_634_);
lean_dec_ref_known(v_a_626_, 1);
v___x_635_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_618_, v_post_619_, v_e_634_, v_a_621_, v___y_622_, v___y_623_);
return v___x_635_;
}
default: 
{
lean_object* v_e_x3f_636_; 
lean_dec_ref(v_post_619_);
lean_dec_ref(v_pre_618_);
v_e_x3f_636_ = lean_ctor_get(v_a_626_, 0);
lean_inc(v_e_x3f_636_);
lean_dec_ref_known(v_a_626_, 1);
if (lean_obj_tag(v_e_x3f_636_) == 0)
{
lean_object* v___x_638_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v_e_620_);
v___x_638_ = v___x_628_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_e_620_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
else
{
lean_object* v_val_640_; lean_object* v___x_642_; 
lean_dec_ref(v_e_620_);
v_val_640_ = lean_ctor_get(v_e_x3f_636_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v_e_x3f_636_, 1);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v_val_640_);
v___x_642_ = v___x_628_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_val_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v_e_620_);
lean_dec_ref(v_post_619_);
lean_dec_ref(v_pre_618_);
v_a_645_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_625_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_625_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_653_, lean_object* v_post_654_, lean_object* v_e_655_, lean_object* v_a_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_653_, v_post_654_, v_e_655_, v_a_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v_a_656_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_661_, lean_object* v_post_662_, lean_object* v_sz_663_, lean_object* v_i_664_, lean_object* v_bs_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
size_t v_sz_boxed_670_; size_t v_i_boxed_671_; lean_object* v_res_672_; 
v_sz_boxed_670_ = lean_unbox_usize(v_sz_663_);
lean_dec(v_sz_663_);
v_i_boxed_671_ = lean_unbox_usize(v_i_664_);
lean_dec(v_i_664_);
v_res_672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_661_, v_post_662_, v_sz_boxed_670_, v_i_boxed_671_, v_bs_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_673_, lean_object* v_post_674_, lean_object* v_x_675_, lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_673_, v_post_674_, v_x_675_, v_x_676_, v_x_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___boxed(lean_object* v_pre_683_, lean_object* v_post_684_, lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_683_, v_post_684_, v_e_685_, v_a_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v_a_686_);
return v_res_690_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_box(0);
v___x_692_ = lean_unsigned_to_nat(16u);
v___x_693_ = lean_mk_array(v___x_692_, v___x_691_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1);
v___x_698_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_698_, 0, lean_box(0));
lean_closure_set(v___x_698_, 1, lean_box(0));
lean_closure_set(v___x_698_, 2, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(lean_object* v_input_699_, lean_object* v_pre_700_, lean_object* v_post_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_a_707_; lean_object* v___x_708_; 
v___x_705_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2);
v___x_706_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_box(0), v___x_705_, v___y_702_, v___y_703_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v___x_706_);
v___x_708_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_700_, v_post_701_, v_input_699_, v_a_707_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_710_, 0, lean_box(0));
lean_closure_set(v___x_710_, 1, lean_box(0));
lean_closure_set(v___x_710_, 2, v_a_707_);
v___x_711_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_box(0), v___x_710_, v___y_702_, v___y_703_);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v___x_711_, 0);
lean_dec(v_unused_719_);
v___x_713_ = v___x_711_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_dec(v___x_711_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v_a_709_);
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_709_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
lean_dec(v_a_707_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___boxed(lean_object* v_input_720_, lean_object* v_pre_721_, lean_object* v_post_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(v_input_720_, v_pre_721_, v_post_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp(lean_object* v_e_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___f_733_; lean_object* v___f_734_; lean_object* v___x_735_; 
v___f_733_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___closed__0));
v___f_734_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___closed__1));
v___x_735_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(v_e_729_, v___f_733_, v___f_734_, v_a_730_, v_a_731_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___boxed(lean_object* v_e_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Elab_WF_floatRecApp(v_e_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_741_, lean_object* v_m_742_, lean_object* v_a_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_m_742_, v_a_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_745_, lean_object* v_m_746_, lean_object* v_a_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(v_00_u03b2_745_, v_m_746_, v_a_747_);
lean_dec_ref(v_a_747_);
lean_dec_ref(v_m_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_749_, lean_object* v_ref_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_750_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_755_, lean_object* v_ref_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_755_, v_ref_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(lean_object* v_00_u03b1_771_, lean_object* v_x_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_772_, v___y_773_, v___y_774_, v___y_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b1_778_, lean_object* v_x_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(v_00_u03b1_778_, v_x_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_785_, lean_object* v_m_786_, lean_object* v_a_787_, lean_object* v_b_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v_m_786_, v_a_787_, v_b_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_790_, lean_object* v_a_791_, lean_object* v_x_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_a_791_, v_x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_00_u03b2_794_, lean_object* v_a_795_, lean_object* v_x_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_794_, v_a_795_, v_x_796_);
lean_dec(v_x_796_);
lean_dec_ref(v_a_795_);
return v_res_797_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_798_, lean_object* v_a_799_, lean_object* v_x_800_){
_start:
{
uint8_t v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_a_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_802_, lean_object* v_a_803_, lean_object* v_x_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_802_, v_a_803_, v_x_804_);
lean_dec(v_x_804_);
lean_dec_ref(v_a_803_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_807_, lean_object* v_data_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(v_data_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13(lean_object* v_00_u03b2_810_, lean_object* v_a_811_, lean_object* v_b_812_, lean_object* v_x_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(v_a_811_, v_b_812_, v_x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13(lean_object* v_00_u03b2_815_, lean_object* v_i_816_, lean_object* v_source_817_, lean_object* v_target_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v_i_816_, v_source_817_, v_target_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(lean_object* v_00_u03b2_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_x_821_, v_x_822_);
return v___x_823_;
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
