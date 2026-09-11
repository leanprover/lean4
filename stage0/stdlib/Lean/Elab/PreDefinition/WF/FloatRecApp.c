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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_nbuckets_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_166_ = lean_array_get_size(v_data_165_);
v___x_167_ = lean_unsigned_to_nat(2u);
v_nbuckets_168_ = lean_nat_mul(v___x_166_, v___x_167_);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_box(0);
v___x_171_ = lean_mk_array(v_nbuckets_168_, v___x_170_);
v___x_172_ = lean_array_propagate_mark(v_data_165_, v___x_171_);
v___x_173_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v___x_169_, v_data_165_, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
uint8_t v___x_176_; 
v___x_176_ = 0;
return v___x_176_;
}
else
{
lean_object* v_key_177_; lean_object* v_tail_178_; uint8_t v___x_179_; 
v_key_177_ = lean_ctor_get(v_x_175_, 0);
v_tail_178_ = lean_ctor_get(v_x_175_, 2);
v___x_179_ = l_Lean_ExprStructEq_beq(v_key_177_, v_a_174_);
if (v___x_179_ == 0)
{
v_x_175_ = v_tail_178_;
goto _start;
}
else
{
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_a_181_, lean_object* v_x_182_){
_start:
{
uint8_t v_res_183_; lean_object* v_r_184_; 
v_res_183_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_a_181_, v_x_182_);
lean_dec(v_x_182_);
lean_dec_ref(v_a_181_);
v_r_184_ = lean_box(v_res_183_);
return v_r_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(lean_object* v_a_185_, lean_object* v_b_186_, lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_dec(v_b_186_);
lean_dec_ref(v_a_185_);
return v_x_187_;
}
else
{
lean_object* v_key_188_; lean_object* v_value_189_; lean_object* v_tail_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_202_; 
v_key_188_ = lean_ctor_get(v_x_187_, 0);
v_value_189_ = lean_ctor_get(v_x_187_, 1);
v_tail_190_ = lean_ctor_get(v_x_187_, 2);
v_isSharedCheck_202_ = !lean_is_exclusive(v_x_187_);
if (v_isSharedCheck_202_ == 0)
{
v___x_192_ = v_x_187_;
v_isShared_193_ = v_isSharedCheck_202_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_tail_190_);
lean_inc(v_value_189_);
lean_inc(v_key_188_);
lean_dec(v_x_187_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_202_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
uint8_t v___x_194_; 
v___x_194_ = l_Lean_ExprStructEq_beq(v_key_188_, v_a_185_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(v_a_185_, v_b_186_, v_tail_190_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 2, v___x_195_);
v___x_197_ = v___x_192_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_key_188_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_value_189_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
else
{
lean_object* v___x_200_; 
lean_dec(v_value_189_);
lean_dec(v_key_188_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v_b_186_);
lean_ctor_set(v___x_192_, 0, v_a_185_);
v___x_200_ = v___x_192_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_185_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_b_186_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_tail_190_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(lean_object* v_m_203_, lean_object* v_a_204_, lean_object* v_b_205_){
_start:
{
lean_object* v_size_206_; lean_object* v_buckets_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_250_; 
v_size_206_ = lean_ctor_get(v_m_203_, 0);
v_buckets_207_ = lean_ctor_get(v_m_203_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_m_203_);
if (v_isSharedCheck_250_ == 0)
{
v___x_209_ = v_m_203_;
v_isShared_210_ = v_isSharedCheck_250_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_buckets_207_);
lean_inc(v_size_206_);
lean_dec(v_m_203_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_250_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v_fold_215_; uint64_t v___x_216_; uint64_t v___x_217_; uint64_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; lean_object* v_bkt_224_; uint8_t v___x_225_; 
v___x_211_ = lean_array_get_size(v_buckets_207_);
v___x_212_ = l_Lean_ExprStructEq_hash(v_a_204_);
v___x_213_ = 32ULL;
v___x_214_ = lean_uint64_shift_right(v___x_212_, v___x_213_);
v_fold_215_ = lean_uint64_xor(v___x_212_, v___x_214_);
v___x_216_ = 16ULL;
v___x_217_ = lean_uint64_shift_right(v_fold_215_, v___x_216_);
v___x_218_ = lean_uint64_xor(v_fold_215_, v___x_217_);
v___x_219_ = lean_uint64_to_usize(v___x_218_);
v___x_220_ = lean_usize_of_nat(v___x_211_);
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_sub(v___x_220_, v___x_221_);
v___x_223_ = lean_usize_land(v___x_219_, v___x_222_);
v_bkt_224_ = lean_array_uget_borrowed(v_buckets_207_, v___x_223_);
v___x_225_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_a_204_, v_bkt_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v_size_x27_227_; lean_object* v___x_228_; lean_object* v_buckets_x27_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_226_ = lean_unsigned_to_nat(1u);
v_size_x27_227_ = lean_nat_add(v_size_206_, v___x_226_);
lean_dec(v_size_206_);
lean_inc(v_bkt_224_);
v___x_228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_228_, 0, v_a_204_);
lean_ctor_set(v___x_228_, 1, v_b_205_);
lean_ctor_set(v___x_228_, 2, v_bkt_224_);
v_buckets_x27_229_ = lean_array_uset(v_buckets_207_, v___x_223_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(4u);
v___x_231_ = lean_nat_mul(v_size_x27_227_, v___x_230_);
v___x_232_ = lean_unsigned_to_nat(3u);
v___x_233_ = lean_nat_div(v___x_231_, v___x_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_array_get_size(v_buckets_x27_229_);
v___x_235_ = lean_nat_dec_le(v___x_233_, v___x_234_);
lean_dec(v___x_233_);
if (v___x_235_ == 0)
{
lean_object* v_val_236_; lean_object* v___x_238_; 
v_val_236_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(v_buckets_x27_229_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v_val_236_);
lean_ctor_set(v___x_209_, 0, v_size_x27_227_);
v___x_238_ = v___x_209_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_size_x27_227_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_val_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
else
{
lean_object* v___x_241_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v_buckets_x27_229_);
lean_ctor_set(v___x_209_, 0, v_size_x27_227_);
v___x_241_ = v___x_209_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_size_x27_227_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_buckets_x27_229_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
else
{
lean_object* v___x_243_; lean_object* v_buckets_x27_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
lean_inc(v_bkt_224_);
v___x_243_ = lean_box(0);
v_buckets_x27_244_ = lean_array_uset(v_buckets_207_, v___x_223_, v___x_243_);
v___x_245_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(v_a_204_, v_b_205_, v_bkt_224_);
v___x_246_ = lean_array_uset(v_buckets_x27_244_, v___x_223_, v___x_245_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___x_246_);
v___x_248_ = v___x_209_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_size_206_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2(lean_object* v_a_251_, lean_object* v_e_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_255_ = lean_st_ref_take(v_a_251_);
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v___x_255_, v_e_252_, v_a_253_);
v___x_257_ = lean_st_ref_put(v_a_251_, v___x_256_);
v___x_258_ = lean_box(0);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2___boxed(lean_object* v_a_259_, lean_object* v_e_260_, lean_object* v_a_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2(v_a_259_, v_e_260_, v_a_261_);
lean_dec(v_a_259_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_264_, lean_object* v_x_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_apply_1(v_x_265_, lean_box(0));
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_271_, lean_object* v_x_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(v_00_u03b1_271_, v_x_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_276_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = l_Lean_maxRecDepthErrorMessage;
v___x_283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__3);
v___x_285_ = l_Lean_MessageData_ofFormat(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__4);
v___x_287_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__2));
v___x_288_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(lean_object* v_ref_289_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___closed__5);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_ref_289_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg___boxed(lean_object* v_ref_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_294_);
return v_res_296_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_box(0);
v___x_298_ = l_Lean_interruptExceptionId;
v___x_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg(){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___closed__0);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg___boxed(lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(lean_object* v_x_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___y_311_; uint8_t v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; uint8_t v___y_324_; lean_object* v___y_325_; lean_object* v_toCold_330_; lean_object* v_currRecDepth_331_; lean_object* v_ref_332_; uint8_t v_diag_333_; uint8_t v_suppressElabErrors_334_; lean_object* v_maxRecDepth_335_; lean_object* v_cancelTk_x3f_336_; 
v_toCold_330_ = lean_ctor_get(v___y_307_, 0);
v_currRecDepth_331_ = lean_ctor_get(v___y_307_, 1);
v_ref_332_ = lean_ctor_get(v___y_307_, 2);
v_diag_333_ = lean_ctor_get_uint8(v___y_307_, sizeof(void*)*3);
v_suppressElabErrors_334_ = lean_ctor_get_uint8(v___y_307_, sizeof(void*)*3 + 1);
v_maxRecDepth_335_ = lean_ctor_get(v_toCold_330_, 3);
v_cancelTk_x3f_336_ = lean_ctor_get(v_toCold_330_, 10);
if (lean_obj_tag(v_cancelTk_x3f_336_) == 1)
{
lean_object* v_val_342_; uint8_t v___x_343_; 
v_val_342_ = lean_ctor_get(v_cancelTk_x3f_336_, 0);
v___x_343_ = l_IO_CancelToken_isSet(v_val_342_);
if (v___x_343_ == 0)
{
goto v___jp_337_;
}
else
{
lean_object* v___x_344_; lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec_ref(v_x_305_);
v___x_344_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
goto v___jp_337_;
}
v___jp_310_:
{
if (lean_obj_tag(v___y_311_) == 0)
{
return v___y_311_;
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_a_312_ = lean_ctor_get(v___y_311_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___y_311_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___y_311_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___y_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
v___jp_320_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = lean_nat_add(v___y_323_, v___x_326_);
lean_inc_ref(v___y_322_);
v___x_328_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_328_, 0, v___y_322_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
lean_ctor_set(v___x_328_, 2, v___y_325_);
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*3, v___y_321_);
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*3 + 1, v___y_324_);
lean_inc(v___y_308_);
lean_inc(v___y_306_);
v___x_329_ = lean_apply_4(v_x_305_, v___y_306_, v___x_328_, v___y_308_, lean_box(0));
v___y_311_ = v___x_329_;
goto v___jp_310_;
}
v___jp_337_:
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_nat_dec_eq(v_maxRecDepth_335_, v___x_338_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = lean_nat_dec_eq(v_currRecDepth_331_, v_maxRecDepth_335_);
if (v___x_340_ == 0)
{
lean_inc(v_ref_332_);
v___y_321_ = v_diag_333_;
v___y_322_ = v_toCold_330_;
v___y_323_ = v_currRecDepth_331_;
v___y_324_ = v_suppressElabErrors_334_;
v___y_325_ = v_ref_332_;
goto v___jp_320_;
}
else
{
lean_object* v___x_341_; 
lean_dec_ref(v_x_305_);
lean_inc(v_ref_332_);
v___x_341_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_332_);
v___y_311_ = v___x_341_;
goto v___jp_310_;
}
}
else
{
lean_inc(v_ref_332_);
v___y_321_ = v_diag_333_;
v___y_322_ = v_toCold_330_;
v___y_323_ = v_currRecDepth_331_;
v___y_324_ = v_suppressElabErrors_334_;
v___y_325_ = v_ref_332_;
goto v___jp_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_x_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(lean_object* v_pre_360_, lean_object* v_post_361_, size_t v_sz_362_, size_t v_i_363_, lean_object* v_bs_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = lean_usize_dec_lt(v_i_363_, v_sz_362_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
lean_dec_ref(v_post_361_);
lean_dec_ref(v_pre_360_);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v_bs_364_);
return v___x_370_;
}
else
{
lean_object* v_v_371_; lean_object* v___x_372_; 
v_v_371_ = lean_array_uget_borrowed(v_bs_364_, v_i_363_);
lean_inc(v_v_371_);
lean_inc_ref(v_post_361_);
lean_inc_ref(v_pre_360_);
v___x_372_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_360_, v_post_361_, v_v_371_, v___y_365_, v___y_366_, v___y_367_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_374_; lean_object* v_bs_x27_375_; size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_372_, 1);
v___x_374_ = lean_unsigned_to_nat(0u);
v_bs_x27_375_ = lean_array_uset(v_bs_364_, v_i_363_, v___x_374_);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_363_, v___x_376_);
v___x_378_ = lean_array_uset(v_bs_x27_375_, v_i_363_, v_a_373_);
v_i_363_ = v___x_377_;
v_bs_364_ = v___x_378_;
goto _start;
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v_bs_364_);
lean_dec_ref(v_post_361_);
lean_dec_ref(v_pre_360_);
v_a_380_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_372_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_372_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(lean_object* v_pre_388_, lean_object* v_post_389_, lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
if (lean_obj_tag(v_x_390_) == 5)
{
lean_object* v_fn_397_; lean_object* v_arg_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_fn_397_ = lean_ctor_get(v_x_390_, 0);
lean_inc_ref(v_fn_397_);
v_arg_398_ = lean_ctor_get(v_x_390_, 1);
lean_inc_ref(v_arg_398_);
lean_dec_ref_known(v_x_390_, 2);
v___x_399_ = lean_array_set(v_x_391_, v_x_392_, v_arg_398_);
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_sub(v_x_392_, v___x_400_);
lean_dec(v_x_392_);
v_x_390_ = v_fn_397_;
v_x_391_ = v___x_399_;
v_x_392_ = v___x_401_;
goto _start;
}
else
{
lean_object* v___x_403_; 
lean_dec(v_x_392_);
lean_inc_ref(v_post_389_);
lean_inc_ref(v_pre_388_);
v___x_403_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_388_, v_post_389_, v_x_390_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; size_t v_sz_405_; size_t v___x_406_; lean_object* v___x_407_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v_sz_405_ = lean_array_size(v_x_391_);
v___x_406_ = ((size_t)0ULL);
lean_inc_ref(v_post_389_);
lean_inc_ref(v_pre_388_);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_388_, v_post_389_, v_sz_405_, v___x_406_, v_x_391_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
v___x_409_ = l_Lean_mkAppN(v_a_404_, v_a_408_);
lean_dec(v_a_408_);
v___x_410_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_388_, v_post_389_, v___x_409_, v___y_393_, v___y_394_, v___y_395_);
return v___x_410_;
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_a_404_);
lean_dec_ref(v_post_389_);
lean_dec_ref(v_pre_388_);
v_a_411_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_407_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_407_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_dec_ref(v_x_391_);
lean_dec_ref(v_post_389_);
lean_dec_ref(v_pre_388_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(lean_object* v___x_419_, lean_object* v_pre_420_, lean_object* v_e_421_, lean_object* v_post_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Core_checkSystem(v___x_419_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v___x_428_; 
lean_dec_ref_known(v___x_427_, 1);
lean_inc_ref(v_pre_420_);
lean_inc(v___y_425_);
lean_inc_ref(v___y_424_);
lean_inc_ref(v_e_421_);
v___x_428_ = lean_apply_4(v_pre_420_, v_e_421_, v___y_424_, v___y_425_, lean_box(0));
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_544_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_544_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_544_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_544_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___y_434_; 
switch(lean_obj_tag(v_a_429_))
{
case 0:
{
lean_object* v_e_534_; lean_object* v___x_536_; 
lean_dec_ref(v_post_422_);
lean_dec_ref(v_e_421_);
lean_dec_ref(v_pre_420_);
v_e_534_ = lean_ctor_get(v_a_429_, 0);
lean_inc_ref(v_e_534_);
lean_dec_ref_known(v_a_429_, 1);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v_e_534_);
v___x_536_ = v___x_431_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_e_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
case 1:
{
lean_object* v_e_538_; lean_object* v___x_539_; 
lean_del_object(v___x_431_);
lean_dec_ref(v_e_421_);
v_e_538_ = lean_ctor_get(v_a_429_, 0);
lean_inc_ref(v_e_538_);
lean_dec_ref_known(v_a_429_, 1);
lean_inc_ref(v_post_422_);
lean_inc_ref(v_pre_420_);
v___x_539_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_420_, v_post_422_, v_e_538_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
v___x_541_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v_a_540_, v___y_423_, v___y_424_, v___y_425_);
return v___x_541_;
}
else
{
lean_dec_ref(v_post_422_);
lean_dec_ref(v_pre_420_);
return v___x_539_;
}
}
default: 
{
lean_object* v_e_x3f_542_; 
lean_del_object(v___x_431_);
v_e_x3f_542_ = lean_ctor_get(v_a_429_, 0);
lean_inc(v_e_x3f_542_);
lean_dec_ref_known(v_a_429_, 1);
if (lean_obj_tag(v_e_x3f_542_) == 0)
{
v___y_434_ = v_e_421_;
goto v___jp_433_;
}
else
{
lean_object* v_val_543_; 
lean_dec_ref(v_e_421_);
v_val_543_ = lean_ctor_get(v_e_x3f_542_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v_e_x3f_542_, 1);
v___y_434_ = v_val_543_;
goto v___jp_433_;
}
}
}
v___jp_433_:
{
switch(lean_obj_tag(v___y_434_))
{
case 7:
{
lean_object* v_binderName_435_; lean_object* v_binderType_436_; lean_object* v_body_437_; uint8_t v_binderInfo_438_; lean_object* v___x_439_; 
v_binderName_435_ = lean_ctor_get(v___y_434_, 0);
v_binderType_436_ = lean_ctor_get(v___y_434_, 1);
v_body_437_ = lean_ctor_get(v___y_434_, 2);
v_binderInfo_438_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_436_);
lean_inc_ref(v_post_422_);
lean_inc_ref(v_pre_420_);
v___x_439_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_420_, v_post_422_, v_binderType_436_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
lean_inc_ref(v_body_437_);
lean_inc_ref(v_post_422_);
lean_inc_ref(v_pre_420_);
v___x_441_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_420_, v_post_422_, v_body_437_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; size_t v___x_443_; size_t v___x_444_; uint8_t v___x_445_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v___x_443_ = lean_ptr_addr(v_binderType_436_);
v___x_444_ = lean_ptr_addr(v_a_440_);
v___x_445_ = lean_usize_dec_eq(v___x_443_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_inc(v_binderName_435_);
lean_dec_ref_known(v___y_434_, 3);
v___x_446_ = l_Lean_Expr_forallE___override(v_binderName_435_, v_a_440_, v_a_442_, v_binderInfo_438_);
v___x_447_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___x_446_, v___y_423_, v___y_424_, v___y_425_);
return v___x_447_;
}
else
{
size_t v___x_448_; size_t v___x_449_; uint8_t v___x_450_; 
v___x_448_ = lean_ptr_addr(v_body_437_);
v___x_449_ = lean_ptr_addr(v_a_442_);
v___x_450_ = lean_usize_dec_eq(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_inc(v_binderName_435_);
lean_dec_ref_known(v___y_434_, 3);
v___x_451_ = l_Lean_Expr_forallE___override(v_binderName_435_, v_a_440_, v_a_442_, v_binderInfo_438_);
v___x_452_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___x_451_, v___y_423_, v___y_424_, v___y_425_);
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
v___x_453_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_438_, v_binderInfo_438_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_inc(v_binderName_435_);
lean_dec_ref_known(v___y_434_, 3);
v___x_454_ = l_Lean_Expr_forallE___override(v_binderName_435_, v_a_440_, v_a_442_, v_binderInfo_438_);
v___x_455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___x_454_, v___y_423_, v___y_424_, v___y_425_);
return v___x_455_;
}
else
{
lean_object* v___x_456_; 
lean_dec(v_a_442_);
lean_dec(v_a_440_);
v___x_456_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___y_434_, v___y_423_, v___y_424_, v___y_425_);
return v___x_456_;
}
}
}
}
else
{
lean_dec(v_a_440_);
lean_dec_ref_known(v___y_434_, 3);
lean_dec_ref(v_post_422_);
lean_dec_ref(v_pre_420_);
return v___x_441_;
}
}
else
{
lean_dec_ref_known(v___y_434_, 3);
lean_dec_ref(v_post_422_);
lean_dec_ref(v_pre_420_);
return v___x_439_;
}
}
case 6:
{
lean_object* v_binderName_457_; lean_object* v_binderType_458_; lean_object* v_body_459_; uint8_t v_binderInfo_460_; lean_object* v___x_461_; 
v_binderName_457_ = lean_ctor_get(v___y_434_, 0);
v_binderType_458_ = lean_ctor_get(v___y_434_, 1);
v_body_459_ = lean_ctor_get(v___y_434_, 2);
v_binderInfo_460_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_458_);
lean_inc_ref(v_post_422_);
lean_inc_ref(v_pre_420_);
v___x_461_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_420_, v_post_422_, v_binderType_458_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
lean_inc_ref(v_body_459_);
lean_inc_ref(v_post_422_);
lean_inc_ref(v_pre_420_);
v___x_463_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_420_, v_post_422_, v_body_459_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; size_t v___x_465_; size_t v___x_466_; uint8_t v___x_467_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = lean_ptr_addr(v_binderType_458_);
v___x_466_ = lean_ptr_addr(v_a_462_);
v___x_467_ = lean_usize_dec_eq(v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_inc(v_binderName_457_);
lean_dec_ref_known(v___y_434_, 3);
v___x_468_ = l_Lean_Expr_lam___override(v_binderName_457_, v_a_462_, v_a_464_, v_binderInfo_460_);
v___x_469_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___x_468_, v___y_423_, v___y_424_, v___y_425_);
return v___x_469_;
}
else
{
size_t v___x_470_; size_t v___x_471_; uint8_t v___x_472_; 
v___x_470_ = lean_ptr_addr(v_body_459_);
v___x_471_ = lean_ptr_addr(v_a_464_);
v___x_472_ = lean_usize_dec_eq(v___x_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_inc(v_binderName_457_);
lean_dec_ref_known(v___y_434_, 3);
v___x_473_ = l_Lean_Expr_lam___override(v_binderName_457_, v_a_462_, v_a_464_, v_binderInfo_460_);
v___x_474_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___x_473_, v___y_423_, v___y_424_, v___y_425_);
return v___x_474_;
}
else
{
uint8_t v___x_475_; 
v___x_475_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_460_, v_binderInfo_460_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_inc(v_binderName_457_);
lean_dec_ref_known(v___y_434_, 3);
v___x_476_ = l_Lean_Expr_lam___override(v_binderName_457_, v_a_462_, v_a_464_, v_binderInfo_460_);
v___x_477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___x_476_, v___y_423_, v___y_424_, v___y_425_);
return v___x_477_;
}
else
{
lean_object* v___x_478_; 
lean_dec(v_a_464_);
lean_dec(v_a_462_);
v___x_478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___y_434_, v___y_423_, v___y_424_, v___y_425_);
return v___x_478_;
}
}
}
}
else
{
lean_dec(v_a_462_);
lean_dec_ref_known(v___y_434_, 3);
lean_dec_ref(v_post_422_);
lean_dec_ref(v_pre_420_);
return v___x_463_;
}
}
else
{
lean_dec_ref_known(v___y_434_, 3);
lean_dec_ref(v_post_422_);
lean_dec_ref(v_pre_420_);
return v___x_461_;
}
}
case 8:
{
lean_object* v_declName_479_; lean_object* v_type_480_; lean_object* v_value_481_; lean_object* v_body_482_; uint8_t v_nondep_483_; lean_object* v___x_484_; 
v_declName_479_ = lean_ctor_get(v___y_434_, 0);
v_type_480_ = lean_ctor_get(v___y_434_, 1);
v_value_481_ = lean_ctor_get(v___y_434_, 2);
v_body_482_ = lean_ctor_get(v___y_434_, 3);
v_nondep_483_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_480_);
lean_inc_ref(v_post_422_);
lean_inc_ref(v_pre_420_);
v___x_484_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_420_, v_post_422_, v_type_480_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
lean_inc_ref(v_value_481_);
lean_inc_ref(v_post_422_);
lean_inc_ref(v_pre_420_);
v___x_486_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_420_, v_post_422_, v_value_481_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 1);
lean_inc_ref(v_body_482_);
lean_inc_ref(v_post_422_);
lean_inc_ref(v_pre_420_);
v___x_488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_420_, v_post_422_, v_body_482_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; size_t v___x_490_; size_t v___x_491_; uint8_t v___x_492_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v___x_490_ = lean_ptr_addr(v_type_480_);
v___x_491_ = lean_ptr_addr(v_a_485_);
v___x_492_ = lean_usize_dec_eq(v___x_490_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_inc(v_declName_479_);
lean_dec_ref_known(v___y_434_, 4);
v___x_493_ = l_Lean_Expr_letE___override(v_declName_479_, v_a_485_, v_a_487_, v_a_489_, v_nondep_483_);
v___x_494_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___x_493_, v___y_423_, v___y_424_, v___y_425_);
return v___x_494_;
}
else
{
size_t v___x_495_; size_t v___x_496_; uint8_t v___x_497_; 
v___x_495_ = lean_ptr_addr(v_value_481_);
v___x_496_ = lean_ptr_addr(v_a_487_);
v___x_497_ = lean_usize_dec_eq(v___x_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_inc(v_declName_479_);
lean_dec_ref_known(v___y_434_, 4);
v___x_498_ = l_Lean_Expr_letE___override(v_declName_479_, v_a_485_, v_a_487_, v_a_489_, v_nondep_483_);
v___x_499_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___x_498_, v___y_423_, v___y_424_, v___y_425_);
return v___x_499_;
}
else
{
size_t v___x_500_; size_t v___x_501_; uint8_t v___x_502_; 
v___x_500_ = lean_ptr_addr(v_body_482_);
v___x_501_ = lean_ptr_addr(v_a_489_);
v___x_502_ = lean_usize_dec_eq(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_inc(v_declName_479_);
lean_dec_ref_known(v___y_434_, 4);
v___x_503_ = l_Lean_Expr_letE___override(v_declName_479_, v_a_485_, v_a_487_, v_a_489_, v_nondep_483_);
v___x_504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___x_503_, v___y_423_, v___y_424_, v___y_425_);
return v___x_504_;
}
else
{
lean_object* v___x_505_; 
lean_dec(v_a_489_);
lean_dec(v_a_487_);
lean_dec(v_a_485_);
v___x_505_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___y_434_, v___y_423_, v___y_424_, v___y_425_);
return v___x_505_;
}
}
}
}
else
{
lean_dec(v_a_487_);
lean_dec(v_a_485_);
lean_dec_ref_known(v___y_434_, 4);
lean_dec_ref(v_post_422_);
lean_dec_ref(v_pre_420_);
return v___x_488_;
}
}
else
{
lean_dec(v_a_485_);
lean_dec_ref_known(v___y_434_, 4);
lean_dec_ref(v_post_422_);
lean_dec_ref(v_pre_420_);
return v___x_486_;
}
}
else
{
lean_dec_ref_known(v___y_434_, 4);
lean_dec_ref(v_post_422_);
lean_dec_ref(v_pre_420_);
return v___x_484_;
}
}
case 5:
{
lean_object* v_dummy_506_; lean_object* v_nargs_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_dummy_506_ = lean_obj_once(&l_Lean_Elab_WF_floatRecApp___lam__1___closed__0, &l_Lean_Elab_WF_floatRecApp___lam__1___closed__0_once, _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__0);
v_nargs_507_ = l_Lean_Expr_getAppNumArgs(v___y_434_);
lean_inc(v_nargs_507_);
v___x_508_ = lean_mk_array(v_nargs_507_, v_dummy_506_);
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_nat_sub(v_nargs_507_, v___x_509_);
lean_dec(v_nargs_507_);
v___x_511_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_420_, v_post_422_, v___y_434_, v___x_508_, v___x_510_, v___y_423_, v___y_424_, v___y_425_);
return v___x_511_;
}
case 10:
{
lean_object* v_data_512_; lean_object* v_expr_513_; lean_object* v___x_514_; 
v_data_512_ = lean_ctor_get(v___y_434_, 0);
v_expr_513_ = lean_ctor_get(v___y_434_, 1);
lean_inc_ref(v_expr_513_);
lean_inc_ref(v_post_422_);
lean_inc_ref(v_pre_420_);
v___x_514_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_420_, v_post_422_, v_expr_513_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; size_t v___x_516_; size_t v___x_517_; uint8_t v___x_518_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_514_, 1);
v___x_516_ = lean_ptr_addr(v_expr_513_);
v___x_517_ = lean_ptr_addr(v_a_515_);
v___x_518_ = lean_usize_dec_eq(v___x_516_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_inc(v_data_512_);
lean_dec_ref_known(v___y_434_, 2);
v___x_519_ = l_Lean_Expr_mdata___override(v_data_512_, v_a_515_);
v___x_520_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___x_519_, v___y_423_, v___y_424_, v___y_425_);
return v___x_520_;
}
else
{
lean_object* v___x_521_; 
lean_dec(v_a_515_);
v___x_521_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___y_434_, v___y_423_, v___y_424_, v___y_425_);
return v___x_521_;
}
}
else
{
lean_dec_ref_known(v___y_434_, 2);
lean_dec_ref(v_post_422_);
lean_dec_ref(v_pre_420_);
return v___x_514_;
}
}
case 11:
{
lean_object* v_typeName_522_; lean_object* v_idx_523_; lean_object* v_struct_524_; lean_object* v___x_525_; 
v_typeName_522_ = lean_ctor_get(v___y_434_, 0);
v_idx_523_ = lean_ctor_get(v___y_434_, 1);
v_struct_524_ = lean_ctor_get(v___y_434_, 2);
lean_inc_ref(v_struct_524_);
lean_inc_ref(v_post_422_);
lean_inc_ref(v_pre_420_);
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_420_, v_post_422_, v_struct_524_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; size_t v___x_527_; size_t v___x_528_; uint8_t v___x_529_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = lean_ptr_addr(v_struct_524_);
v___x_528_ = lean_ptr_addr(v_a_526_);
v___x_529_ = lean_usize_dec_eq(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_inc(v_idx_523_);
lean_inc(v_typeName_522_);
lean_dec_ref_known(v___y_434_, 3);
v___x_530_ = l_Lean_Expr_proj___override(v_typeName_522_, v_idx_523_, v_a_526_);
v___x_531_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___x_530_, v___y_423_, v___y_424_, v___y_425_);
return v___x_531_;
}
else
{
lean_object* v___x_532_; 
lean_dec(v_a_526_);
v___x_532_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___y_434_, v___y_423_, v___y_424_, v___y_425_);
return v___x_532_;
}
}
else
{
lean_dec_ref_known(v___y_434_, 3);
lean_dec_ref(v_post_422_);
lean_dec_ref(v_pre_420_);
return v___x_525_;
}
}
default: 
{
lean_object* v___x_533_; 
v___x_533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_420_, v_post_422_, v___y_434_, v___y_423_, v___y_424_, v___y_425_);
return v___x_533_;
}
}
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_post_422_);
lean_dec_ref(v_e_421_);
lean_dec_ref(v_pre_420_);
v_a_545_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_428_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_428_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec_ref(v_post_422_);
lean_dec_ref(v_e_421_);
lean_dec_ref(v_pre_420_);
v_a_553_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_427_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_427_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed(lean_object* v___x_561_, lean_object* v_pre_562_, lean_object* v_e_563_, lean_object* v_post_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(v___x_561_, v_pre_562_, v_e_563_, v_post_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(lean_object* v_pre_570_, lean_object* v_post_571_, lean_object* v_e_572_, lean_object* v_a_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_inc(v_a_573_);
v___x_577_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_577_, 0, lean_box(0));
lean_closure_set(v___x_577_, 1, lean_box(0));
lean_closure_set(v___x_577_, 2, v_a_573_);
v___x_578_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_box(0), v___x_577_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_610_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_610_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_610_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_610_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_a_579_, v_e_572_);
lean_dec(v_a_579_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___x_586_; 
lean_del_object(v___x_581_);
v___x_584_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___closed__0));
lean_inc_ref(v_e_572_);
v___f_585_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_585_, 0, v___x_584_);
lean_closure_set(v___f_585_, 1, v_pre_570_);
lean_closure_set(v___f_585_, 2, v_e_572_);
lean_closure_set(v___f_585_, 3, v_post_571_);
v___x_586_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v___f_585_, v_a_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___f_588_; lean_object* v___x_589_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc_n(v_a_587_, 2);
lean_dec_ref_known(v___x_586_, 1);
lean_inc(v_a_573_);
v___f_588_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_588_, 0, v_a_573_);
lean_closure_set(v___f_588_, 1, v_e_572_);
lean_closure_set(v___f_588_, 2, v_a_587_);
v___x_589_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_box(0), v___f_588_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v___x_589_, 0);
lean_dec(v_unused_597_);
v___x_591_ = v___x_589_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_dec(v___x_589_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v_a_587_);
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_587_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_a_587_);
v_a_598_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_589_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_589_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_dec_ref(v_e_572_);
return v___x_586_;
}
}
else
{
lean_object* v_val_606_; lean_object* v___x_608_; 
lean_dec_ref(v_e_572_);
lean_dec_ref(v_post_571_);
lean_dec_ref(v_pre_570_);
v_val_606_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v___x_583_, 1);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_val_606_);
v___x_608_ = v___x_581_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_val_606_);
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
lean_dec_ref(v_e_572_);
lean_dec_ref(v_post_571_);
lean_dec_ref(v_pre_570_);
v_a_611_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_578_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_578_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(lean_object* v_pre_619_, lean_object* v_post_620_, lean_object* v_e_621_, lean_object* v_a_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___x_626_; 
lean_inc_ref(v_post_620_);
lean_inc(v___y_624_);
lean_inc_ref(v___y_623_);
lean_inc_ref(v_e_621_);
v___x_626_ = lean_apply_4(v_post_620_, v_e_621_, v___y_623_, v___y_624_, lean_box(0));
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_645_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_645_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_645_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_645_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
switch(lean_obj_tag(v_a_627_))
{
case 0:
{
lean_object* v_e_631_; lean_object* v___x_633_; 
lean_dec_ref(v_e_621_);
lean_dec_ref(v_post_620_);
lean_dec_ref(v_pre_619_);
v_e_631_ = lean_ctor_get(v_a_627_, 0);
lean_inc_ref(v_e_631_);
lean_dec_ref_known(v_a_627_, 1);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v_e_631_);
v___x_633_ = v___x_629_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_e_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
case 1:
{
lean_object* v_e_635_; lean_object* v___x_636_; 
lean_del_object(v___x_629_);
lean_dec_ref(v_e_621_);
v_e_635_ = lean_ctor_get(v_a_627_, 0);
lean_inc_ref(v_e_635_);
lean_dec_ref_known(v_a_627_, 1);
v___x_636_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_619_, v_post_620_, v_e_635_, v_a_622_, v___y_623_, v___y_624_);
return v___x_636_;
}
default: 
{
lean_object* v_e_x3f_637_; 
lean_dec_ref(v_post_620_);
lean_dec_ref(v_pre_619_);
v_e_x3f_637_ = lean_ctor_get(v_a_627_, 0);
lean_inc(v_e_x3f_637_);
lean_dec_ref_known(v_a_627_, 1);
if (lean_obj_tag(v_e_x3f_637_) == 0)
{
lean_object* v___x_639_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v_e_621_);
v___x_639_ = v___x_629_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_e_621_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
lean_object* v_val_641_; lean_object* v___x_643_; 
lean_dec_ref(v_e_621_);
v_val_641_ = lean_ctor_get(v_e_x3f_637_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v_e_x3f_637_, 1);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v_val_641_);
v___x_643_ = v___x_629_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_val_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref(v_e_621_);
lean_dec_ref(v_post_620_);
lean_dec_ref(v_pre_619_);
v_a_646_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_626_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_626_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_654_, lean_object* v_post_655_, lean_object* v_e_656_, lean_object* v_a_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_654_, v_post_655_, v_e_656_, v_a_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v_a_657_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_662_, lean_object* v_post_663_, lean_object* v_sz_664_, lean_object* v_i_665_, lean_object* v_bs_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
size_t v_sz_boxed_671_; size_t v_i_boxed_672_; lean_object* v_res_673_; 
v_sz_boxed_671_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v_i_boxed_672_ = lean_unbox_usize(v_i_665_);
lean_dec(v_i_665_);
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_662_, v_post_663_, v_sz_boxed_671_, v_i_boxed_672_, v_bs_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_674_, lean_object* v_post_675_, lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_674_, v_post_675_, v_x_676_, v_x_677_, v_x_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___boxed(lean_object* v_pre_684_, lean_object* v_post_685_, lean_object* v_e_686_, lean_object* v_a_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_684_, v_post_685_, v_e_686_, v_a_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v_a_687_);
return v_res_691_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = lean_box(0);
v___x_693_ = lean_unsigned_to_nat(16u);
v___x_694_ = lean_mk_array(v___x_693_, v___x_692_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0);
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___x_695_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1);
v___x_699_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_699_, 0, lean_box(0));
lean_closure_set(v___x_699_, 1, lean_box(0));
lean_closure_set(v___x_699_, 2, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(lean_object* v_input_700_, lean_object* v_pre_701_, lean_object* v_post_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v___x_709_; 
v___x_706_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2);
v___x_707_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_box(0), v___x_706_, v___y_703_, v___y_704_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
v___x_709_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_701_, v_post_702_, v_input_700_, v_a_708_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_711_, 0, lean_box(0));
lean_closure_set(v___x_711_, 1, lean_box(0));
lean_closure_set(v___x_711_, 2, v_a_708_);
v___x_712_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_box(0), v___x_711_, v___y_703_, v___y_704_);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v___x_712_, 0);
lean_dec(v_unused_720_);
v___x_714_ = v___x_712_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_dec(v___x_712_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v_a_710_);
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_710_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
lean_dec(v_a_708_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___boxed(lean_object* v_input_721_, lean_object* v_pre_722_, lean_object* v_post_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(v_input_721_, v_pre_722_, v_post_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp(lean_object* v_e_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___f_734_; lean_object* v___f_735_; lean_object* v___x_736_; 
v___f_734_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___closed__0));
v___f_735_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___closed__1));
v___x_736_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(v_e_730_, v___f_734_, v___f_735_, v_a_731_, v_a_732_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___boxed(lean_object* v_e_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Elab_WF_floatRecApp(v_e_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_742_, lean_object* v_m_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_m_743_, v_a_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_746_, lean_object* v_m_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(v_00_u03b2_746_, v_m_747_, v_a_748_);
lean_dec_ref(v_a_748_);
lean_dec_ref(v_m_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_750_, lean_object* v_ref_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_751_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_756_, lean_object* v_ref_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_756_, v_ref_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9(lean_object* v_00_u03b1_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___redArg();
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9___boxed(lean_object* v_00_u03b1_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__9(v_00_u03b1_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(lean_object* v_00_u03b1_772_, lean_object* v_x_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_773_, v___y_774_, v___y_775_, v___y_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b1_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(v_00_u03b1_779_, v_x_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_786_, lean_object* v_m_787_, lean_object* v_a_788_, lean_object* v_b_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v_m_787_, v_a_788_, v_b_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_791_, lean_object* v_a_792_, lean_object* v_x_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_a_792_, v_x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_00_u03b2_795_, lean_object* v_a_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_795_, v_a_796_, v_x_797_);
lean_dec(v_x_797_);
lean_dec_ref(v_a_796_);
return v_res_798_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_799_, lean_object* v_a_800_, lean_object* v_x_801_){
_start:
{
uint8_t v___x_802_; 
v___x_802_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_a_800_, v_x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_803_, lean_object* v_a_804_, lean_object* v_x_805_){
_start:
{
uint8_t v_res_806_; lean_object* v_r_807_; 
v_res_806_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_803_, v_a_804_, v_x_805_);
lean_dec(v_x_805_);
lean_dec_ref(v_a_804_);
v_r_807_ = lean_box(v_res_806_);
return v_r_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_808_, lean_object* v_data_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(v_data_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13(lean_object* v_00_u03b2_811_, lean_object* v_a_812_, lean_object* v_b_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__13___redArg(v_a_812_, v_b_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13(lean_object* v_00_u03b2_816_, lean_object* v_i_817_, lean_object* v_source_818_, lean_object* v_target_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13___redArg(v_i_817_, v_source_818_, v_target_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14(lean_object* v_00_u03b2_821_, lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12_spec__13_spec__14___redArg(v_x_822_, v_x_823_);
return v___x_824_;
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
