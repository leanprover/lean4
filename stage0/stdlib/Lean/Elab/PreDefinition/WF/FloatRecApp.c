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
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___f_6_; lean_object* v___x_585__overap_7_; lean_object* v___x_8_; 
v___f_6_ = ((lean_object*)(l_panic___at___00Lean_Elab_WF_floatRecApp_spec__0___closed__0));
v___x_585__overap_7_ = lean_panic_fn(v___f_6_, v_msg_2_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_8_ = lean_apply_3(v___x_585__overap_7_, v___y_3_, v___y_4_, lean_box(0));
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
lean_dec_ref(v___x_47_);
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
lean_dec_ref(v___x_62_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12_spec__13___redArg(lean_object* v_x_125_, lean_object* v_x_126_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12___redArg(lean_object* v_i_153_, lean_object* v_source_154_, lean_object* v_target_155_){
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
v_target_161_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12_spec__13___redArg(v_target_155_, v_es_158_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_data_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_nbuckets_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_166_ = lean_array_get_size(v_data_165_);
v___x_167_ = lean_unsigned_to_nat(2u);
v_nbuckets_168_ = lean_nat_mul(v___x_166_, v___x_167_);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_box(0);
v___x_171_ = lean_mk_array(v_nbuckets_168_, v___x_170_);
v___x_172_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12___redArg(v___x_169_, v_data_165_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10___redArg(lean_object* v_a_173_, lean_object* v_x_174_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10___redArg___boxed(lean_object* v_a_180_, lean_object* v_x_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10___redArg(v_a_180_, v_x_181_);
lean_dec(v_x_181_);
lean_dec_ref(v_a_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(lean_object* v_a_184_, lean_object* v_b_185_, lean_object* v_x_186_){
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
v___x_194_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(v_a_184_, v_b_185_, v_tail_189_);
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
v___x_224_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10___redArg(v_a_203_, v_bkt_223_);
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
v_val_235_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_buckets_x27_228_);
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
v___x_244_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(v_a_203_, v_b_204_, v_bkt_223_);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(lean_object* v_x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___y_302_; lean_object* v_fileName_311_; lean_object* v_fileMap_312_; lean_object* v_options_313_; lean_object* v_currRecDepth_314_; lean_object* v_maxRecDepth_315_; lean_object* v_ref_316_; lean_object* v_currNamespace_317_; lean_object* v_openDecls_318_; lean_object* v_initHeartbeats_319_; lean_object* v_maxHeartbeats_320_; lean_object* v_quotContext_321_; lean_object* v_currMacroScope_322_; uint8_t v_diag_323_; lean_object* v_cancelTk_x3f_324_; uint8_t v_suppressElabErrors_325_; lean_object* v_inheritedTraceOptions_326_; uint8_t v___x_327_; 
v_fileName_311_ = lean_ctor_get(v___y_298_, 0);
lean_inc_ref(v_fileName_311_);
v_fileMap_312_ = lean_ctor_get(v___y_298_, 1);
lean_inc_ref(v_fileMap_312_);
v_options_313_ = lean_ctor_get(v___y_298_, 2);
lean_inc_ref(v_options_313_);
v_currRecDepth_314_ = lean_ctor_get(v___y_298_, 3);
lean_inc(v_currRecDepth_314_);
v_maxRecDepth_315_ = lean_ctor_get(v___y_298_, 4);
lean_inc(v_maxRecDepth_315_);
v_ref_316_ = lean_ctor_get(v___y_298_, 5);
lean_inc(v_ref_316_);
v_currNamespace_317_ = lean_ctor_get(v___y_298_, 6);
lean_inc(v_currNamespace_317_);
v_openDecls_318_ = lean_ctor_get(v___y_298_, 7);
lean_inc(v_openDecls_318_);
v_initHeartbeats_319_ = lean_ctor_get(v___y_298_, 8);
lean_inc(v_initHeartbeats_319_);
v_maxHeartbeats_320_ = lean_ctor_get(v___y_298_, 9);
lean_inc(v_maxHeartbeats_320_);
v_quotContext_321_ = lean_ctor_get(v___y_298_, 10);
lean_inc(v_quotContext_321_);
v_currMacroScope_322_ = lean_ctor_get(v___y_298_, 11);
lean_inc(v_currMacroScope_322_);
v_diag_323_ = lean_ctor_get_uint8(v___y_298_, sizeof(void*)*14);
v_cancelTk_x3f_324_ = lean_ctor_get(v___y_298_, 12);
lean_inc(v_cancelTk_x3f_324_);
v_suppressElabErrors_325_ = lean_ctor_get_uint8(v___y_298_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_326_ = lean_ctor_get(v___y_298_, 13);
lean_inc_ref(v_inheritedTraceOptions_326_);
lean_dec_ref(v___y_298_);
v___x_327_ = lean_nat_dec_eq(v_currRecDepth_314_, v_maxRecDepth_315_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_add(v_currRecDepth_314_, v___x_328_);
lean_dec(v_currRecDepth_314_);
v___x_330_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_330_, 0, v_fileName_311_);
lean_ctor_set(v___x_330_, 1, v_fileMap_312_);
lean_ctor_set(v___x_330_, 2, v_options_313_);
lean_ctor_set(v___x_330_, 3, v___x_329_);
lean_ctor_set(v___x_330_, 4, v_maxRecDepth_315_);
lean_ctor_set(v___x_330_, 5, v_ref_316_);
lean_ctor_set(v___x_330_, 6, v_currNamespace_317_);
lean_ctor_set(v___x_330_, 7, v_openDecls_318_);
lean_ctor_set(v___x_330_, 8, v_initHeartbeats_319_);
lean_ctor_set(v___x_330_, 9, v_maxHeartbeats_320_);
lean_ctor_set(v___x_330_, 10, v_quotContext_321_);
lean_ctor_set(v___x_330_, 11, v_currMacroScope_322_);
lean_ctor_set(v___x_330_, 12, v_cancelTk_x3f_324_);
lean_ctor_set(v___x_330_, 13, v_inheritedTraceOptions_326_);
lean_ctor_set_uint8(v___x_330_, sizeof(void*)*14, v_diag_323_);
lean_ctor_set_uint8(v___x_330_, sizeof(void*)*14 + 1, v_suppressElabErrors_325_);
lean_inc(v___y_299_);
lean_inc(v___y_297_);
v___x_331_ = lean_apply_4(v_x_296_, v___y_297_, v___x_330_, v___y_299_, lean_box(0));
v___y_302_ = v___x_331_;
goto v___jp_301_;
}
else
{
lean_object* v___x_332_; 
lean_dec_ref(v_inheritedTraceOptions_326_);
lean_dec(v_cancelTk_x3f_324_);
lean_dec(v_currMacroScope_322_);
lean_dec(v_quotContext_321_);
lean_dec(v_maxHeartbeats_320_);
lean_dec(v_initHeartbeats_319_);
lean_dec(v_openDecls_318_);
lean_dec(v_currNamespace_317_);
lean_dec(v_maxRecDepth_315_);
lean_dec(v_currRecDepth_314_);
lean_dec_ref(v_options_313_);
lean_dec_ref(v_fileMap_312_);
lean_dec_ref(v_fileName_311_);
lean_dec_ref(v_x_296_);
v___x_332_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_316_);
v___y_302_ = v___x_332_;
goto v___jp_301_;
}
v___jp_301_:
{
if (lean_obj_tag(v___y_302_) == 0)
{
return v___y_302_;
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_303_ = lean_ctor_get(v___y_302_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___y_302_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___y_302_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___y_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_x_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec(v___y_334_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(lean_object* v_pre_339_, lean_object* v_post_340_, size_t v_sz_341_, size_t v_i_342_, lean_object* v_bs_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
uint8_t v___x_348_; 
v___x_348_ = lean_usize_dec_lt(v_i_342_, v_sz_341_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_dec_ref(v_post_340_);
lean_dec_ref(v_pre_339_);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v_bs_343_);
return v___x_349_;
}
else
{
lean_object* v_v_350_; lean_object* v___x_351_; 
v_v_350_ = lean_array_uget_borrowed(v_bs_343_, v_i_342_);
lean_inc(v_v_350_);
lean_inc_ref(v_post_340_);
lean_inc_ref(v_pre_339_);
v___x_351_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_339_, v_post_340_, v_v_350_, v___y_344_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; lean_object* v_bs_x27_354_; size_t v___x_355_; size_t v___x_356_; lean_object* v___x_357_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref(v___x_351_);
v___x_353_ = lean_unsigned_to_nat(0u);
v_bs_x27_354_ = lean_array_uset(v_bs_343_, v_i_342_, v___x_353_);
v___x_355_ = ((size_t)1ULL);
v___x_356_ = lean_usize_add(v_i_342_, v___x_355_);
v___x_357_ = lean_array_uset(v_bs_x27_354_, v_i_342_, v_a_352_);
v_i_342_ = v___x_356_;
v_bs_343_ = v___x_357_;
goto _start;
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v_bs_343_);
lean_dec_ref(v_post_340_);
lean_dec_ref(v_pre_339_);
v_a_359_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_351_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_351_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(lean_object* v_pre_367_, lean_object* v_post_368_, lean_object* v_x_369_, lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
if (lean_obj_tag(v_x_369_) == 5)
{
lean_object* v_fn_376_; lean_object* v_arg_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_fn_376_ = lean_ctor_get(v_x_369_, 0);
lean_inc_ref(v_fn_376_);
v_arg_377_ = lean_ctor_get(v_x_369_, 1);
lean_inc_ref(v_arg_377_);
lean_dec_ref(v_x_369_);
v___x_378_ = lean_array_set(v_x_370_, v_x_371_, v_arg_377_);
v___x_379_ = lean_unsigned_to_nat(1u);
v___x_380_ = lean_nat_sub(v_x_371_, v___x_379_);
lean_dec(v_x_371_);
v_x_369_ = v_fn_376_;
v_x_370_ = v___x_378_;
v_x_371_ = v___x_380_;
goto _start;
}
else
{
lean_object* v___x_382_; 
lean_dec(v_x_371_);
lean_inc_ref(v_post_368_);
lean_inc_ref(v_pre_367_);
v___x_382_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_367_, v_post_368_, v_x_369_, v___y_372_, v___y_373_, v___y_374_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; size_t v_sz_384_; size_t v___x_385_; lean_object* v___x_386_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref(v___x_382_);
v_sz_384_ = lean_array_size(v_x_370_);
v___x_385_ = ((size_t)0ULL);
lean_inc_ref(v_post_368_);
lean_inc_ref(v_pre_367_);
v___x_386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_367_, v_post_368_, v_sz_384_, v___x_385_, v_x_370_, v___y_372_, v___y_373_, v___y_374_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref(v___x_386_);
v___x_388_ = l_Lean_mkAppN(v_a_383_, v_a_387_);
lean_dec(v_a_387_);
v___x_389_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_367_, v_post_368_, v___x_388_, v___y_372_, v___y_373_, v___y_374_);
return v___x_389_;
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v_a_383_);
lean_dec_ref(v_post_368_);
lean_dec_ref(v_pre_367_);
v_a_390_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_386_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_386_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
else
{
lean_dec_ref(v_x_370_);
lean_dec_ref(v_post_368_);
lean_dec_ref(v_pre_367_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(lean_object* v_pre_398_, lean_object* v_e_399_, lean_object* v_post_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___y_406_; lean_object* v___y_407_; uint8_t v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; uint8_t v___y_413_; lean_object* v___y_423_; uint8_t v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; uint8_t v___y_428_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; uint8_t v___y_439_; lean_object* v___y_440_; uint8_t v___y_441_; lean_object* v___x_448_; 
lean_inc_ref(v_pre_398_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
lean_inc_ref(v_e_399_);
v___x_448_ = lean_apply_4(v_pre_398_, v_e_399_, v___y_402_, v___y_403_, lean_box(0));
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_538_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_538_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_538_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_538_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___y_454_; 
switch(lean_obj_tag(v_a_449_))
{
case 0:
{
lean_object* v_e_528_; lean_object* v___x_530_; 
lean_dec_ref(v_post_400_);
lean_dec_ref(v_e_399_);
lean_dec_ref(v_pre_398_);
v_e_528_ = lean_ctor_get(v_a_449_, 0);
lean_inc_ref(v_e_528_);
lean_dec_ref(v_a_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v_e_528_);
v___x_530_ = v___x_451_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_e_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
case 1:
{
lean_object* v_e_532_; lean_object* v___x_533_; 
lean_del_object(v___x_451_);
lean_dec_ref(v_e_399_);
v_e_532_ = lean_ctor_get(v_a_449_, 0);
lean_inc_ref(v_e_532_);
lean_dec_ref(v_a_449_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_398_);
v___x_533_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_398_, v_post_400_, v_e_532_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_535_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref(v___x_533_);
v___x_535_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v_a_534_, v___y_401_, v___y_402_, v___y_403_);
return v___x_535_;
}
else
{
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_398_);
return v___x_533_;
}
}
default: 
{
lean_object* v_e_x3f_536_; 
lean_del_object(v___x_451_);
v_e_x3f_536_ = lean_ctor_get(v_a_449_, 0);
lean_inc(v_e_x3f_536_);
lean_dec_ref(v_a_449_);
if (lean_obj_tag(v_e_x3f_536_) == 0)
{
v___y_454_ = v_e_399_;
goto v___jp_453_;
}
else
{
lean_object* v_val_537_; 
lean_dec_ref(v_e_399_);
v_val_537_ = lean_ctor_get(v_e_x3f_536_, 0);
lean_inc(v_val_537_);
lean_dec_ref(v_e_x3f_536_);
v___y_454_ = v_val_537_;
goto v___jp_453_;
}
}
}
v___jp_453_:
{
switch(lean_obj_tag(v___y_454_))
{
case 7:
{
lean_object* v_binderName_455_; lean_object* v_binderType_456_; lean_object* v_body_457_; uint8_t v_binderInfo_458_; lean_object* v___x_459_; 
v_binderName_455_ = lean_ctor_get(v___y_454_, 0);
lean_inc(v_binderName_455_);
v_binderType_456_ = lean_ctor_get(v___y_454_, 1);
v_body_457_ = lean_ctor_get(v___y_454_, 2);
v_binderInfo_458_ = lean_ctor_get_uint8(v___y_454_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_456_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_398_);
v___x_459_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_398_, v_post_400_, v_binderType_456_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_461_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref(v___x_459_);
lean_inc_ref(v_body_457_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_398_);
v___x_461_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_398_, v_post_400_, v_body_457_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; size_t v___x_463_; size_t v___x_464_; uint8_t v___x_465_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref(v___x_461_);
v___x_463_ = lean_ptr_addr(v_binderType_456_);
v___x_464_ = lean_ptr_addr(v_a_460_);
v___x_465_ = lean_usize_dec_eq(v___x_463_, v___x_464_);
if (v___x_465_ == 0)
{
v___y_436_ = v_a_462_;
v___y_437_ = v_binderName_455_;
v___y_438_ = v_a_460_;
v___y_439_ = v_binderInfo_458_;
v___y_440_ = v___y_454_;
v___y_441_ = v___x_465_;
goto v___jp_435_;
}
else
{
size_t v___x_466_; size_t v___x_467_; uint8_t v___x_468_; 
v___x_466_ = lean_ptr_addr(v_body_457_);
v___x_467_ = lean_ptr_addr(v_a_462_);
v___x_468_ = lean_usize_dec_eq(v___x_466_, v___x_467_);
v___y_436_ = v_a_462_;
v___y_437_ = v_binderName_455_;
v___y_438_ = v_a_460_;
v___y_439_ = v_binderInfo_458_;
v___y_440_ = v___y_454_;
v___y_441_ = v___x_468_;
goto v___jp_435_;
}
}
else
{
lean_dec(v_a_460_);
lean_dec(v_binderName_455_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_398_);
return v___x_461_;
}
}
else
{
lean_dec(v_binderName_455_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_398_);
return v___x_459_;
}
}
case 6:
{
lean_object* v_binderName_469_; lean_object* v_binderType_470_; lean_object* v_body_471_; uint8_t v_binderInfo_472_; lean_object* v___x_473_; 
v_binderName_469_ = lean_ctor_get(v___y_454_, 0);
lean_inc(v_binderName_469_);
v_binderType_470_ = lean_ctor_get(v___y_454_, 1);
v_body_471_ = lean_ctor_get(v___y_454_, 2);
v_binderInfo_472_ = lean_ctor_get_uint8(v___y_454_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_470_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_398_);
v___x_473_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_398_, v_post_400_, v_binderType_470_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_475_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref(v___x_473_);
lean_inc_ref(v_body_471_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_398_);
v___x_475_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_398_, v_post_400_, v_body_471_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; size_t v___x_477_; size_t v___x_478_; uint8_t v___x_479_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref(v___x_475_);
v___x_477_ = lean_ptr_addr(v_binderType_470_);
v___x_478_ = lean_ptr_addr(v_a_474_);
v___x_479_ = lean_usize_dec_eq(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
v___y_423_ = v_a_474_;
v___y_424_ = v_binderInfo_472_;
v___y_425_ = v_a_476_;
v___y_426_ = v___y_454_;
v___y_427_ = v_binderName_469_;
v___y_428_ = v___x_479_;
goto v___jp_422_;
}
else
{
size_t v___x_480_; size_t v___x_481_; uint8_t v___x_482_; 
v___x_480_ = lean_ptr_addr(v_body_471_);
v___x_481_ = lean_ptr_addr(v_a_476_);
v___x_482_ = lean_usize_dec_eq(v___x_480_, v___x_481_);
v___y_423_ = v_a_474_;
v___y_424_ = v_binderInfo_472_;
v___y_425_ = v_a_476_;
v___y_426_ = v___y_454_;
v___y_427_ = v_binderName_469_;
v___y_428_ = v___x_482_;
goto v___jp_422_;
}
}
else
{
lean_dec(v_a_474_);
lean_dec_ref(v___y_454_);
lean_dec(v_binderName_469_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_398_);
return v___x_475_;
}
}
else
{
lean_dec_ref(v___y_454_);
lean_dec(v_binderName_469_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_398_);
return v___x_473_;
}
}
case 8:
{
lean_object* v_declName_483_; lean_object* v_type_484_; lean_object* v_value_485_; lean_object* v_body_486_; uint8_t v_nondep_487_; lean_object* v___x_488_; 
v_declName_483_ = lean_ctor_get(v___y_454_, 0);
lean_inc(v_declName_483_);
v_type_484_ = lean_ctor_get(v___y_454_, 1);
v_value_485_ = lean_ctor_get(v___y_454_, 2);
v_body_486_ = lean_ctor_get(v___y_454_, 3);
lean_inc_ref(v_body_486_);
v_nondep_487_ = lean_ctor_get_uint8(v___y_454_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_484_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_398_);
v___x_488_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_398_, v_post_400_, v_type_484_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
lean_inc_ref(v_value_485_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_398_);
v___x_490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_398_, v_post_400_, v_value_485_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref(v___x_490_);
lean_inc_ref(v_body_486_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_398_);
v___x_492_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_398_, v_post_400_, v_body_486_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; size_t v___x_494_; size_t v___x_495_; uint8_t v___x_496_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref(v___x_492_);
v___x_494_ = lean_ptr_addr(v_type_484_);
v___x_495_ = lean_ptr_addr(v_a_489_);
v___x_496_ = lean_usize_dec_eq(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
v___y_406_ = v_a_493_;
v___y_407_ = v_a_489_;
v___y_408_ = v_nondep_487_;
v___y_409_ = v_body_486_;
v___y_410_ = v_declName_483_;
v___y_411_ = v___y_454_;
v___y_412_ = v_a_491_;
v___y_413_ = v___x_496_;
goto v___jp_405_;
}
else
{
size_t v___x_497_; size_t v___x_498_; uint8_t v___x_499_; 
v___x_497_ = lean_ptr_addr(v_value_485_);
v___x_498_ = lean_ptr_addr(v_a_491_);
v___x_499_ = lean_usize_dec_eq(v___x_497_, v___x_498_);
v___y_406_ = v_a_493_;
v___y_407_ = v_a_489_;
v___y_408_ = v_nondep_487_;
v___y_409_ = v_body_486_;
v___y_410_ = v_declName_483_;
v___y_411_ = v___y_454_;
v___y_412_ = v_a_491_;
v___y_413_ = v___x_499_;
goto v___jp_405_;
}
}
else
{
lean_dec(v_a_491_);
lean_dec(v_a_489_);
lean_dec_ref(v_body_486_);
lean_dec(v_declName_483_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_398_);
return v___x_492_;
}
}
else
{
lean_dec(v_a_489_);
lean_dec_ref(v_body_486_);
lean_dec(v_declName_483_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_398_);
return v___x_490_;
}
}
else
{
lean_dec_ref(v_body_486_);
lean_dec(v_declName_483_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_398_);
return v___x_488_;
}
}
case 5:
{
lean_object* v_dummy_500_; lean_object* v_nargs_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_dummy_500_ = lean_obj_once(&l_Lean_Elab_WF_floatRecApp___lam__1___closed__0, &l_Lean_Elab_WF_floatRecApp___lam__1___closed__0_once, _init_l_Lean_Elab_WF_floatRecApp___lam__1___closed__0);
v_nargs_501_ = l_Lean_Expr_getAppNumArgs(v___y_454_);
lean_inc(v_nargs_501_);
v___x_502_ = lean_mk_array(v_nargs_501_, v_dummy_500_);
v___x_503_ = lean_unsigned_to_nat(1u);
v___x_504_ = lean_nat_sub(v_nargs_501_, v___x_503_);
lean_dec(v_nargs_501_);
v___x_505_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_398_, v_post_400_, v___y_454_, v___x_502_, v___x_504_, v___y_401_, v___y_402_, v___y_403_);
return v___x_505_;
}
case 10:
{
lean_object* v_data_506_; lean_object* v_expr_507_; lean_object* v___x_508_; 
v_data_506_ = lean_ctor_get(v___y_454_, 0);
v_expr_507_ = lean_ctor_get(v___y_454_, 1);
lean_inc_ref(v_expr_507_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_398_);
v___x_508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_398_, v_post_400_, v_expr_507_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; size_t v___x_510_; size_t v___x_511_; uint8_t v___x_512_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
v___x_510_ = lean_ptr_addr(v_expr_507_);
v___x_511_ = lean_ptr_addr(v_a_509_);
v___x_512_ = lean_usize_dec_eq(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_inc(v_data_506_);
lean_dec_ref(v___y_454_);
v___x_513_ = l_Lean_Expr_mdata___override(v_data_506_, v_a_509_);
v___x_514_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___x_513_, v___y_401_, v___y_402_, v___y_403_);
return v___x_514_;
}
else
{
lean_object* v___x_515_; 
lean_dec(v_a_509_);
v___x_515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___y_454_, v___y_401_, v___y_402_, v___y_403_);
return v___x_515_;
}
}
else
{
lean_dec_ref(v___y_454_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_398_);
return v___x_508_;
}
}
case 11:
{
lean_object* v_typeName_516_; lean_object* v_idx_517_; lean_object* v_struct_518_; lean_object* v___x_519_; 
v_typeName_516_ = lean_ctor_get(v___y_454_, 0);
v_idx_517_ = lean_ctor_get(v___y_454_, 1);
v_struct_518_ = lean_ctor_get(v___y_454_, 2);
lean_inc_ref(v_struct_518_);
lean_inc_ref(v_post_400_);
lean_inc_ref(v_pre_398_);
v___x_519_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_398_, v_post_400_, v_struct_518_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; size_t v___x_521_; size_t v___x_522_; uint8_t v___x_523_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref(v___x_519_);
v___x_521_ = lean_ptr_addr(v_struct_518_);
v___x_522_ = lean_ptr_addr(v_a_520_);
v___x_523_ = lean_usize_dec_eq(v___x_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_inc(v_idx_517_);
lean_inc(v_typeName_516_);
lean_dec_ref(v___y_454_);
v___x_524_ = l_Lean_Expr_proj___override(v_typeName_516_, v_idx_517_, v_a_520_);
v___x_525_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___x_524_, v___y_401_, v___y_402_, v___y_403_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; 
lean_dec(v_a_520_);
v___x_526_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___y_454_, v___y_401_, v___y_402_, v___y_403_);
return v___x_526_;
}
}
else
{
lean_dec_ref(v___y_454_);
lean_dec_ref(v_post_400_);
lean_dec_ref(v_pre_398_);
return v___x_519_;
}
}
default: 
{
lean_object* v___x_527_; 
v___x_527_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___y_454_, v___y_401_, v___y_402_, v___y_403_);
return v___x_527_;
}
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec_ref(v_post_400_);
lean_dec_ref(v_e_399_);
lean_dec_ref(v_pre_398_);
v_a_539_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_448_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_448_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
v___jp_405_:
{
if (v___y_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v___y_411_);
lean_dec_ref(v___y_409_);
v___x_414_ = l_Lean_Expr_letE___override(v___y_410_, v___y_407_, v___y_412_, v___y_406_, v___y_408_);
v___x_415_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___x_414_, v___y_401_, v___y_402_, v___y_403_);
return v___x_415_;
}
else
{
size_t v___x_416_; size_t v___x_417_; uint8_t v___x_418_; 
v___x_416_ = lean_ptr_addr(v___y_409_);
lean_dec_ref(v___y_409_);
v___x_417_ = lean_ptr_addr(v___y_406_);
v___x_418_ = lean_usize_dec_eq(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec_ref(v___y_411_);
v___x_419_ = l_Lean_Expr_letE___override(v___y_410_, v___y_407_, v___y_412_, v___y_406_, v___y_408_);
v___x_420_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___x_419_, v___y_401_, v___y_402_, v___y_403_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; 
lean_dec_ref(v___y_412_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_407_);
lean_dec_ref(v___y_406_);
v___x_421_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___y_411_, v___y_401_, v___y_402_, v___y_403_);
return v___x_421_;
}
}
}
v___jp_422_:
{
if (v___y_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref(v___y_426_);
v___x_429_ = l_Lean_Expr_lam___override(v___y_427_, v___y_423_, v___y_425_, v___y_424_);
v___x_430_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___x_429_, v___y_401_, v___y_402_, v___y_403_);
return v___x_430_;
}
else
{
uint8_t v___x_431_; 
v___x_431_ = l_Lean_instBEqBinderInfo_beq(v___y_424_, v___y_424_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec_ref(v___y_426_);
v___x_432_ = l_Lean_Expr_lam___override(v___y_427_, v___y_423_, v___y_425_, v___y_424_);
v___x_433_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___x_432_, v___y_401_, v___y_402_, v___y_403_);
return v___x_433_;
}
else
{
lean_object* v___x_434_; 
lean_dec(v___y_427_);
lean_dec_ref(v___y_425_);
lean_dec_ref(v___y_423_);
v___x_434_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___y_426_, v___y_401_, v___y_402_, v___y_403_);
return v___x_434_;
}
}
}
v___jp_435_:
{
if (v___y_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec_ref(v___y_440_);
v___x_442_ = l_Lean_Expr_forallE___override(v___y_437_, v___y_438_, v___y_436_, v___y_439_);
v___x_443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___x_442_, v___y_401_, v___y_402_, v___y_403_);
return v___x_443_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = l_Lean_instBEqBinderInfo_beq(v___y_439_, v___y_439_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec_ref(v___y_440_);
v___x_445_ = l_Lean_Expr_forallE___override(v___y_437_, v___y_438_, v___y_436_, v___y_439_);
v___x_446_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___x_445_, v___y_401_, v___y_402_, v___y_403_);
return v___x_446_;
}
else
{
lean_object* v___x_447_; 
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
v___x_447_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_398_, v_post_400_, v___y_440_, v___y_401_, v___y_402_, v___y_403_);
return v___x_447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed(lean_object* v_pre_547_, lean_object* v_e_548_, lean_object* v_post_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1(v_pre_547_, v_e_548_, v_post_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(lean_object* v_pre_555_, lean_object* v_post_556_, lean_object* v_e_557_, lean_object* v_a_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_inc(v_a_558_);
v___x_562_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_562_, 0, lean_box(0));
lean_closure_set(v___x_562_, 1, lean_box(0));
lean_closure_set(v___x_562_, 2, v_a_558_);
v___x_563_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_box(0), v___x_562_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_594_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_594_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_594_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_594_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; 
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_a_564_, v_e_557_);
lean_dec(v_a_564_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___f_569_; lean_object* v___x_570_; 
lean_del_object(v___x_566_);
lean_inc_ref(v_e_557_);
v___f_569_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__1___boxed), 7, 3);
lean_closure_set(v___f_569_, 0, v_pre_555_);
lean_closure_set(v___f_569_, 1, v_e_557_);
lean_closure_set(v___f_569_, 2, v_post_556_);
lean_inc_ref(v___y_559_);
v___x_570_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v___f_569_, v_a_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___f_572_; lean_object* v___x_573_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref(v___x_570_);
lean_inc(v_a_571_);
lean_inc(v_a_558_);
v___f_572_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__2___boxed), 4, 3);
lean_closure_set(v___f_572_, 0, v_a_558_);
lean_closure_set(v___f_572_, 1, v_e_557_);
lean_closure_set(v___f_572_, 2, v_a_571_);
v___x_573_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___lam__0(lean_box(0), v___f_572_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v___x_573_, 0);
lean_dec(v_unused_581_);
v___x_575_ = v___x_573_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_dec(v___x_573_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_a_571_);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_571_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec(v_a_571_);
v_a_582_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_573_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_573_);
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
}
else
{
lean_dec_ref(v_e_557_);
return v___x_570_;
}
}
else
{
lean_object* v_val_590_; lean_object* v___x_592_; 
lean_dec_ref(v_e_557_);
lean_dec_ref(v_post_556_);
lean_dec_ref(v_pre_555_);
v_val_590_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_val_590_);
lean_dec_ref(v___x_568_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v_val_590_);
v___x_592_ = v___x_566_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_val_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v_e_557_);
lean_dec_ref(v_post_556_);
lean_dec_ref(v_pre_555_);
v_a_595_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_563_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_563_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(lean_object* v_pre_603_, lean_object* v_post_604_, lean_object* v_e_605_, lean_object* v_a_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; 
lean_inc_ref(v_post_604_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
lean_inc_ref(v_e_605_);
v___x_610_ = lean_apply_4(v_post_604_, v_e_605_, v___y_607_, v___y_608_, lean_box(0));
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_629_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_629_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_629_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_629_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
switch(lean_obj_tag(v_a_611_))
{
case 0:
{
lean_object* v_e_615_; lean_object* v___x_617_; 
lean_dec_ref(v_e_605_);
lean_dec_ref(v_post_604_);
lean_dec_ref(v_pre_603_);
v_e_615_ = lean_ctor_get(v_a_611_, 0);
lean_inc_ref(v_e_615_);
lean_dec_ref(v_a_611_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_e_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_e_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
case 1:
{
lean_object* v_e_619_; lean_object* v___x_620_; 
lean_del_object(v___x_613_);
lean_dec_ref(v_e_605_);
v_e_619_ = lean_ctor_get(v_a_611_, 0);
lean_inc_ref(v_e_619_);
lean_dec_ref(v_a_611_);
v___x_620_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_603_, v_post_604_, v_e_619_, v_a_606_, v___y_607_, v___y_608_);
return v___x_620_;
}
default: 
{
lean_object* v_e_x3f_621_; 
lean_dec_ref(v_post_604_);
lean_dec_ref(v_pre_603_);
v_e_x3f_621_ = lean_ctor_get(v_a_611_, 0);
lean_inc(v_e_x3f_621_);
lean_dec_ref(v_a_611_);
if (lean_obj_tag(v_e_x3f_621_) == 0)
{
lean_object* v___x_623_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_e_605_);
v___x_623_ = v___x_613_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_e_605_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v_val_625_; lean_object* v___x_627_; 
lean_dec_ref(v_e_605_);
v_val_625_ = lean_ctor_get(v_e_x3f_621_, 0);
lean_inc(v_val_625_);
lean_dec_ref(v_e_x3f_621_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_val_625_);
v___x_627_ = v___x_613_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_val_625_);
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
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v_e_605_);
lean_dec_ref(v_post_604_);
lean_dec_ref(v_pre_603_);
v_a_630_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_610_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_610_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_638_, lean_object* v_post_639_, lean_object* v_e_640_, lean_object* v_a_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__3(v_pre_638_, v_post_639_, v_e_640_, v_a_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v_a_641_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_646_, lean_object* v_post_647_, lean_object* v_sz_648_, lean_object* v_i_649_, lean_object* v_bs_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
size_t v_sz_boxed_655_; size_t v_i_boxed_656_; lean_object* v_res_657_; 
v_sz_boxed_655_ = lean_unbox_usize(v_sz_648_);
lean_dec(v_sz_648_);
v_i_boxed_656_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_res_657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__2(v_pre_646_, v_post_647_, v_sz_boxed_655_, v_i_boxed_656_, v_bs_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5___boxed(lean_object* v_pre_658_, lean_object* v_post_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__5(v_pre_658_, v_post_659_, v_x_660_, v_x_661_, v_x_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1___boxed(lean_object* v_pre_668_, lean_object* v_post_669_, lean_object* v_e_670_, lean_object* v_a_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_668_, v_post_669_, v_e_670_, v_a_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v_a_671_);
return v_res_675_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = lean_box(0);
v___x_677_ = lean_unsigned_to_nat(16u);
v___x_678_ = lean_mk_array(v___x_677_, v___x_676_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__0);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__1);
v___x_683_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_683_, 0, lean_box(0));
lean_closure_set(v___x_683_, 1, lean_box(0));
lean_closure_set(v___x_683_, 2, v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(lean_object* v_input_684_, lean_object* v_pre_685_, lean_object* v_post_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_a_692_; lean_object* v___x_693_; 
v___x_690_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2, &l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___closed__2);
v___x_691_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_box(0), v___x_690_, v___y_687_, v___y_688_);
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref(v___x_691_);
v___x_693_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1(v_pre_685_, v_post_686_, v_input_684_, v_a_692_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref(v___x_693_);
v___x_695_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_695_, 0, lean_box(0));
lean_closure_set(v___x_695_, 1, lean_box(0));
lean_closure_set(v___x_695_, 2, v_a_692_);
v___x_696_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___lam__0(lean_box(0), v___x_695_, v___y_687_, v___y_688_);
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
lean_dec(v_a_692_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1___boxed(lean_object* v_input_705_, lean_object* v_pre_706_, lean_object* v_post_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(v_input_705_, v_pre_706_, v_post_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp(lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___x_720_; 
v___f_718_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___closed__0));
v___f_719_ = ((lean_object*)(l_Lean_Elab_WF_floatRecApp___closed__1));
v___x_720_ = l_Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1(v_e_714_, v___f_718_, v___f_719_, v_a_715_, v_a_716_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_floatRecApp___boxed(lean_object* v_e_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Elab_WF_floatRecApp(v_e_721_, v_a_722_, v_a_723_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_726_, lean_object* v_m_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___redArg(v_m_727_, v_a_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_730_, lean_object* v_m_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4(v_00_u03b2_730_, v_m_731_, v_a_732_);
lean_dec_ref(v_a_732_);
lean_dec_ref(v_m_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(lean_object* v_00_u03b1_734_, lean_object* v_ref_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___redArg(v_ref_735_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8___boxed(lean_object* v_00_u03b1_740_, lean_object* v_ref_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_740_, v_ref_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(lean_object* v_00_u03b1_746_, lean_object* v_x_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; 
lean_inc_ref(v___y_749_);
v___x_752_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___redArg(v_x_747_, v___y_748_, v___y_749_, v___y_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b1_753_, lean_object* v_x_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__6(v_00_u03b1_753_, v_x_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7(lean_object* v_00_u03b2_760_, lean_object* v_m_761_, lean_object* v_a_762_, lean_object* v_b_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7___redArg(v_m_761_, v_a_762_, v_b_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_765_, lean_object* v_a_766_, lean_object* v_x_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___redArg(v_a_766_, v_x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_00_u03b2_769_, lean_object* v_a_770_, lean_object* v_x_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__4_spec__5(v_00_u03b2_769_, v_a_770_, v_x_771_);
lean_dec(v_x_771_);
lean_dec_ref(v_a_770_);
return v_res_772_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10(lean_object* v_00_u03b2_773_, lean_object* v_a_774_, lean_object* v_x_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10___redArg(v_a_774_, v_x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10___boxed(lean_object* v_00_u03b2_777_, lean_object* v_a_778_, lean_object* v_x_779_){
_start:
{
uint8_t v_res_780_; lean_object* v_r_781_; 
v_res_780_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__10(v_00_u03b2_777_, v_a_778_, v_x_779_);
lean_dec(v_x_779_);
lean_dec_ref(v_a_778_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_782_, lean_object* v_data_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11___redArg(v_data_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_785_, lean_object* v_a_786_, lean_object* v_b_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__12___redArg(v_a_786_, v_b_787_, v_x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12(lean_object* v_00_u03b2_790_, lean_object* v_i_791_, lean_object* v_source_792_, lean_object* v_target_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12___redArg(v_i_791_, v_source_792_, v_target_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_floatRecApp_spec__1_spec__1_spec__7_spec__11_spec__12_spec__13___redArg(v_x_796_, v_x_797_);
return v___x_798_;
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
