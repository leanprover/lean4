// Lean compiler output
// Module: Lean.Meta.Reduce
// Imports: public import Lean.Meta.FunInfo import Init.Data.Range.Polymorphic.Iterators
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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_reduce___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_reduce___closed__0;
static lean_once_cell_t l_Lean_Meta_reduce___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_reduce___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(lean_object* v_msg_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_panic_fn_borrowed(v___x_2_, v_msg_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(lean_object* v_k_4_, lean_object* v___y_5_, lean_object* v_b_6_, lean_object* v_c_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
lean_inc(v___y_11_);
lean_inc_ref(v___y_10_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_5_);
v___x_13_ = lean_apply_8(v_k_4_, v_b_6_, v_c_7_, v___y_5_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0___boxed(lean_object* v_k_14_, lean_object* v___y_15_, lean_object* v_b_16_, lean_object* v_c_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(v_k_14_, v___y_15_, v_b_16_, v_c_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_15_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(lean_object* v_e_24_, lean_object* v_k_25_, uint8_t v_cleanupAnnotations_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v___f_33_; uint8_t v___x_34_; uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_inc(v___y_27_);
v___f_33_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_33_, 0, v_k_25_);
lean_closure_set(v___f_33_, 1, v___y_27_);
v___x_34_ = 1;
v___x_35_ = 0;
v___x_36_ = lean_box(0);
v___x_37_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_24_, v___x_34_, v___x_35_, v___x_34_, v___x_35_, v___x_36_, v___f_33_, v_cleanupAnnotations_26_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
if (lean_obj_tag(v___x_37_) == 0)
{
return v___x_37_;
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_37_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_37_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___boxed(lean_object* v_e_46_, lean_object* v_k_47_, lean_object* v_cleanupAnnotations_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_55_; lean_object* v_res_56_; 
v_cleanupAnnotations_boxed_55_ = lean_unbox(v_cleanupAnnotations_48_);
v_res_56_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_e_46_, v_k_47_, v_cleanupAnnotations_boxed_55_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3(lean_object* v_00_u03b1_57_, lean_object* v_e_58_, lean_object* v_k_59_, uint8_t v_cleanupAnnotations_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_e_58_, v_k_59_, v_cleanupAnnotations_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___boxed(lean_object* v_00_u03b1_68_, lean_object* v_e_69_, lean_object* v_k_70_, lean_object* v_cleanupAnnotations_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_78_; lean_object* v_res_79_; 
v_cleanupAnnotations_boxed_78_ = lean_unbox(v_cleanupAnnotations_71_);
v_res_79_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3(v_00_u03b1_68_, v_e_69_, v_k_70_, v_cleanupAnnotations_boxed_78_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(lean_object* v_type_80_, lean_object* v_k_81_, uint8_t v_cleanupAnnotations_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___f_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
lean_inc(v___y_83_);
v___f_89_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_89_, 0, v_k_81_);
lean_closure_set(v___f_89_, 1, v___y_83_);
v___x_90_ = 0;
v___x_91_ = lean_box(0);
v___x_92_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_90_, v___x_91_, v_type_80_, v___f_89_, v_cleanupAnnotations_82_, v___x_90_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
if (lean_obj_tag(v___x_92_) == 0)
{
return v___x_92_;
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg___boxed(lean_object* v_type_101_, lean_object* v_k_102_, lean_object* v_cleanupAnnotations_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_110_; lean_object* v_res_111_; 
v_cleanupAnnotations_boxed_110_ = lean_unbox(v_cleanupAnnotations_103_);
v_res_111_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_type_101_, v_k_102_, v_cleanupAnnotations_boxed_110_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4(lean_object* v_00_u03b1_112_, lean_object* v_type_113_, lean_object* v_k_114_, uint8_t v_cleanupAnnotations_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_type_113_, v_k_114_, v_cleanupAnnotations_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___boxed(lean_object* v_00_u03b1_123_, lean_object* v_type_124_, lean_object* v_k_125_, lean_object* v_cleanupAnnotations_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_133_; lean_object* v_res_134_; 
v_cleanupAnnotations_boxed_133_ = lean_unbox(v_cleanupAnnotations_126_);
v_res_134_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4(v_00_u03b1_123_, v_type_124_, v_k_125_, v_cleanupAnnotations_boxed_133_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(lean_object* v_a_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_box(0);
return v___x_137_;
}
else
{
lean_object* v_key_138_; lean_object* v_value_139_; lean_object* v_tail_140_; uint8_t v___x_141_; 
v_key_138_ = lean_ctor_get(v_x_136_, 0);
v_value_139_ = lean_ctor_get(v_x_136_, 1);
v_tail_140_ = lean_ctor_get(v_x_136_, 2);
v___x_141_ = lean_expr_eqv(v_key_138_, v_a_135_);
if (v___x_141_ == 0)
{
v_x_136_ = v_tail_140_;
goto _start;
}
else
{
lean_object* v___x_143_; 
lean_inc(v_value_139_);
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v_value_139_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_a_144_, v_x_145_);
lean_dec(v_x_145_);
lean_dec_ref(v_a_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(lean_object* v_m_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_buckets_149_; lean_object* v___x_150_; uint64_t v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v_fold_154_; uint64_t v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; size_t v___x_158_; size_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_buckets_149_ = lean_ctor_get(v_m_147_, 1);
v___x_150_ = lean_array_get_size(v_buckets_149_);
v___x_151_ = l_Lean_Expr_hash(v_a_148_);
v___x_152_ = 32ULL;
v___x_153_ = lean_uint64_shift_right(v___x_151_, v___x_152_);
v_fold_154_ = lean_uint64_xor(v___x_151_, v___x_153_);
v___x_155_ = 16ULL;
v___x_156_ = lean_uint64_shift_right(v_fold_154_, v___x_155_);
v___x_157_ = lean_uint64_xor(v_fold_154_, v___x_156_);
v___x_158_ = lean_uint64_to_usize(v___x_157_);
v___x_159_ = lean_usize_of_nat(v___x_150_);
v___x_160_ = ((size_t)1ULL);
v___x_161_ = lean_usize_sub(v___x_159_, v___x_160_);
v___x_162_ = lean_usize_land(v___x_158_, v___x_161_);
v___x_163_ = lean_array_uget_borrowed(v_buckets_149_, v___x_162_);
v___x_164_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_a_148_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg___boxed(lean_object* v_m_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v_m_165_, v_a_166_);
lean_dec_ref(v_a_166_);
lean_dec_ref(v_m_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(lean_object* v_a_168_, lean_object* v_b_169_, lean_object* v_x_170_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_dec(v_b_169_);
lean_dec_ref(v_a_168_);
return v_x_170_;
}
else
{
lean_object* v_key_171_; lean_object* v_value_172_; lean_object* v_tail_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_185_; 
v_key_171_ = lean_ctor_get(v_x_170_, 0);
v_value_172_ = lean_ctor_get(v_x_170_, 1);
v_tail_173_ = lean_ctor_get(v_x_170_, 2);
v_isSharedCheck_185_ = !lean_is_exclusive(v_x_170_);
if (v_isSharedCheck_185_ == 0)
{
v___x_175_ = v_x_170_;
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_tail_173_);
lean_inc(v_value_172_);
lean_inc(v_key_171_);
lean_dec(v_x_170_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
uint8_t v___x_177_; 
v___x_177_ = lean_expr_eqv(v_key_171_, v_a_168_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(v_a_168_, v_b_169_, v_tail_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 2, v___x_178_);
v___x_180_ = v___x_175_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_key_171_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_value_172_);
lean_ctor_set(v_reuseFailAlloc_181_, 2, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
else
{
lean_object* v___x_183_; 
lean_dec(v_value_172_);
lean_dec(v_key_171_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v_b_169_);
lean_ctor_set(v___x_175_, 0, v_a_168_);
v___x_183_ = v___x_175_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_168_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_b_169_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_tail_173_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(lean_object* v_a_186_, lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
uint8_t v___x_188_; 
v___x_188_ = 0;
return v___x_188_;
}
else
{
lean_object* v_key_189_; lean_object* v_tail_190_; uint8_t v___x_191_; 
v_key_189_ = lean_ctor_get(v_x_187_, 0);
v_tail_190_ = lean_ctor_get(v_x_187_, 2);
v___x_191_ = lean_expr_eqv(v_key_189_, v_a_186_);
if (v___x_191_ == 0)
{
v_x_187_ = v_tail_190_;
goto _start;
}
else
{
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg___boxed(lean_object* v_a_193_, lean_object* v_x_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_a_193_, v_x_194_);
lean_dec(v_x_194_);
lean_dec_ref(v_a_193_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
return v_x_197_;
}
else
{
lean_object* v_key_199_; lean_object* v_value_200_; lean_object* v_tail_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_224_; 
v_key_199_ = lean_ctor_get(v_x_198_, 0);
v_value_200_ = lean_ctor_get(v_x_198_, 1);
v_tail_201_ = lean_ctor_get(v_x_198_, 2);
v_isSharedCheck_224_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_224_ == 0)
{
v___x_203_ = v_x_198_;
v_isShared_204_ = v_isSharedCheck_224_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_tail_201_);
lean_inc(v_value_200_);
lean_inc(v_key_199_);
lean_dec(v_x_198_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_224_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; uint64_t v___x_206_; uint64_t v___x_207_; uint64_t v___x_208_; uint64_t v_fold_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; size_t v___x_213_; size_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_205_ = lean_array_get_size(v_x_197_);
v___x_206_ = l_Lean_Expr_hash(v_key_199_);
v___x_207_ = 32ULL;
v___x_208_ = lean_uint64_shift_right(v___x_206_, v___x_207_);
v_fold_209_ = lean_uint64_xor(v___x_206_, v___x_208_);
v___x_210_ = 16ULL;
v___x_211_ = lean_uint64_shift_right(v_fold_209_, v___x_210_);
v___x_212_ = lean_uint64_xor(v_fold_209_, v___x_211_);
v___x_213_ = lean_uint64_to_usize(v___x_212_);
v___x_214_ = lean_usize_of_nat(v___x_205_);
v___x_215_ = ((size_t)1ULL);
v___x_216_ = lean_usize_sub(v___x_214_, v___x_215_);
v___x_217_ = lean_usize_land(v___x_213_, v___x_216_);
v___x_218_ = lean_array_uget_borrowed(v_x_197_, v___x_217_);
lean_inc(v___x_218_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 2, v___x_218_);
v___x_220_ = v___x_203_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_key_199_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_value_200_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v___x_218_);
v___x_220_ = v_reuseFailAlloc_223_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; 
v___x_221_ = lean_array_uset(v_x_197_, v___x_217_, v___x_220_);
v_x_197_ = v___x_221_;
v_x_198_ = v_tail_201_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11___redArg(lean_object* v_i_225_, lean_object* v_source_226_, lean_object* v_target_227_){
_start:
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_array_get_size(v_source_226_);
v___x_229_ = lean_nat_dec_lt(v_i_225_, v___x_228_);
if (v___x_229_ == 0)
{
lean_dec_ref(v_source_226_);
lean_dec(v_i_225_);
return v_target_227_;
}
else
{
lean_object* v_es_230_; lean_object* v___x_231_; lean_object* v_source_232_; lean_object* v_target_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_es_230_ = lean_array_fget(v_source_226_, v_i_225_);
v___x_231_ = lean_box(0);
v_source_232_ = lean_array_fset(v_source_226_, v_i_225_, v___x_231_);
v_target_233_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12___redArg(v_target_227_, v_es_230_);
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = lean_nat_add(v_i_225_, v___x_234_);
lean_dec(v_i_225_);
v_i_225_ = v___x_235_;
v_source_226_ = v_source_232_;
v_target_227_ = v_target_233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(lean_object* v_data_237_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v_nbuckets_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_238_ = lean_array_get_size(v_data_237_);
v___x_239_ = lean_unsigned_to_nat(2u);
v_nbuckets_240_ = lean_nat_mul(v___x_238_, v___x_239_);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_box(0);
v___x_243_ = lean_mk_array(v_nbuckets_240_, v___x_242_);
v___x_244_ = lean_array_propagate_mark(v_data_237_, v___x_243_);
v___x_245_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11___redArg(v___x_241_, v_data_237_, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(lean_object* v_m_246_, lean_object* v_a_247_, lean_object* v_b_248_){
_start:
{
lean_object* v_size_249_; lean_object* v_buckets_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_293_; 
v_size_249_ = lean_ctor_get(v_m_246_, 0);
v_buckets_250_ = lean_ctor_get(v_m_246_, 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v_m_246_);
if (v_isSharedCheck_293_ == 0)
{
v___x_252_ = v_m_246_;
v_isShared_253_ = v_isSharedCheck_293_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_buckets_250_);
lean_inc(v_size_249_);
lean_dec(v_m_246_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_293_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; uint64_t v___x_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v_fold_258_; uint64_t v___x_259_; uint64_t v___x_260_; uint64_t v___x_261_; size_t v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; lean_object* v_bkt_267_; uint8_t v___x_268_; 
v___x_254_ = lean_array_get_size(v_buckets_250_);
v___x_255_ = l_Lean_Expr_hash(v_a_247_);
v___x_256_ = 32ULL;
v___x_257_ = lean_uint64_shift_right(v___x_255_, v___x_256_);
v_fold_258_ = lean_uint64_xor(v___x_255_, v___x_257_);
v___x_259_ = 16ULL;
v___x_260_ = lean_uint64_shift_right(v_fold_258_, v___x_259_);
v___x_261_ = lean_uint64_xor(v_fold_258_, v___x_260_);
v___x_262_ = lean_uint64_to_usize(v___x_261_);
v___x_263_ = lean_usize_of_nat(v___x_254_);
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_sub(v___x_263_, v___x_264_);
v___x_266_ = lean_usize_land(v___x_262_, v___x_265_);
v_bkt_267_ = lean_array_uget_borrowed(v_buckets_250_, v___x_266_);
v___x_268_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_a_247_, v_bkt_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v_size_x27_270_; lean_object* v___x_271_; lean_object* v_buckets_x27_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v_size_x27_270_ = lean_nat_add(v_size_249_, v___x_269_);
lean_dec(v_size_249_);
lean_inc(v_bkt_267_);
v___x_271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_271_, 0, v_a_247_);
lean_ctor_set(v___x_271_, 1, v_b_248_);
lean_ctor_set(v___x_271_, 2, v_bkt_267_);
v_buckets_x27_272_ = lean_array_uset(v_buckets_250_, v___x_266_, v___x_271_);
v___x_273_ = lean_unsigned_to_nat(4u);
v___x_274_ = lean_nat_mul(v_size_x27_270_, v___x_273_);
v___x_275_ = lean_unsigned_to_nat(3u);
v___x_276_ = lean_nat_div(v___x_274_, v___x_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_array_get_size(v_buckets_x27_272_);
v___x_278_ = lean_nat_dec_le(v___x_276_, v___x_277_);
lean_dec(v___x_276_);
if (v___x_278_ == 0)
{
lean_object* v_val_279_; lean_object* v___x_281_; 
v_val_279_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(v_buckets_x27_272_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_val_279_);
lean_ctor_set(v___x_252_, 0, v_size_x27_270_);
v___x_281_ = v___x_252_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_size_x27_270_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_val_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
else
{
lean_object* v___x_284_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_buckets_x27_272_);
lean_ctor_set(v___x_252_, 0, v_size_x27_270_);
v___x_284_ = v___x_252_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_size_x27_270_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_buckets_x27_272_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v___x_286_; lean_object* v_buckets_x27_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
lean_inc(v_bkt_267_);
v___x_286_ = lean_box(0);
v_buckets_x27_287_ = lean_array_uset(v_buckets_250_, v___x_266_, v___x_286_);
v___x_288_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(v_a_247_, v_b_248_, v_bkt_267_);
v___x_289_ = lean_array_uset(v_buckets_x27_287_, v___x_266_, v___x_288_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v___x_289_);
v___x_291_ = v___x_252_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_size_249_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = l_Lean_maxRecDepthErrorMessage;
v___x_300_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3);
v___x_302_ = l_Lean_MessageData_ofFormat(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4);
v___x_304_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2));
v___x_305_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(lean_object* v_ref_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_ref_306_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___boxed(lean_object* v_ref_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_311_);
return v_res_313_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_box(0);
v___x_315_ = l_Lean_interruptExceptionId;
v___x_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg(){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___boxed(lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(lean_object* v_x_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___y_330_; lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; uint8_t v___y_343_; uint8_t v___y_344_; lean_object* v_toCold_349_; lean_object* v_currRecDepth_350_; lean_object* v_ref_351_; uint8_t v_diag_352_; uint8_t v_suppressElabErrors_353_; lean_object* v_maxRecDepth_354_; lean_object* v_cancelTk_x3f_355_; 
v_toCold_349_ = lean_ctor_get(v___y_326_, 0);
v_currRecDepth_350_ = lean_ctor_get(v___y_326_, 1);
v_ref_351_ = lean_ctor_get(v___y_326_, 2);
v_diag_352_ = lean_ctor_get_uint8(v___y_326_, sizeof(void*)*3);
v_suppressElabErrors_353_ = lean_ctor_get_uint8(v___y_326_, sizeof(void*)*3 + 1);
v_maxRecDepth_354_ = lean_ctor_get(v_toCold_349_, 3);
v_cancelTk_x3f_355_ = lean_ctor_get(v_toCold_349_, 10);
if (lean_obj_tag(v_cancelTk_x3f_355_) == 1)
{
lean_object* v_val_361_; uint8_t v___x_362_; 
v_val_361_ = lean_ctor_get(v_cancelTk_x3f_355_, 0);
v___x_362_ = l_IO_CancelToken_isSet(v_val_361_);
if (v___x_362_ == 0)
{
goto v___jp_356_;
}
else
{
lean_object* v___x_363_; lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v_x_322_);
v___x_363_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
goto v___jp_356_;
}
v___jp_329_:
{
if (lean_obj_tag(v___y_330_) == 0)
{
return v___y_330_;
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
v_a_331_ = lean_ctor_get(v___y_330_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___y_330_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___y_330_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___y_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
v___jp_339_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_add(v___y_340_, v___x_345_);
lean_inc_ref(v___y_341_);
v___x_347_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_347_, 0, v___y_341_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
lean_ctor_set(v___x_347_, 2, v___y_342_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*3, v___y_344_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*3 + 1, v___y_343_);
lean_inc(v___y_327_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
lean_inc(v___y_323_);
v___x_348_ = lean_apply_6(v_x_322_, v___y_323_, v___y_324_, v___y_325_, v___x_347_, v___y_327_, lean_box(0));
v___y_330_ = v___x_348_;
goto v___jp_329_;
}
v___jp_356_:
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_nat_dec_eq(v_maxRecDepth_354_, v___x_357_);
if (v___x_358_ == 0)
{
uint8_t v___x_359_; 
v___x_359_ = lean_nat_dec_eq(v_currRecDepth_350_, v_maxRecDepth_354_);
if (v___x_359_ == 0)
{
lean_inc(v_ref_351_);
v___y_340_ = v_currRecDepth_350_;
v___y_341_ = v_toCold_349_;
v___y_342_ = v_ref_351_;
v___y_343_ = v_suppressElabErrors_353_;
v___y_344_ = v_diag_352_;
goto v___jp_339_;
}
else
{
lean_object* v___x_360_; 
lean_dec_ref(v_x_322_);
lean_inc(v_ref_351_);
v___x_360_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_351_);
v___y_330_ = v___x_360_;
goto v___jp_329_;
}
}
else
{
lean_inc(v_ref_351_);
v___y_340_ = v_currRecDepth_350_;
v___y_341_ = v_toCold_349_;
v___y_342_ = v_ref_351_;
v___y_343_ = v_suppressElabErrors_353_;
v___y_344_ = v_diag_352_;
goto v___jp_339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg___boxed(lean_object* v_x_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
return v_res_379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2));
v___x_384_ = lean_unsigned_to_nat(14u);
v___x_385_ = lean_unsigned_to_nat(22u);
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1));
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0));
v___x_388_ = l_mkPanicMessageWithDecl(v___x_387_, v___x_386_, v___x_385_, v___x_384_, v___x_383_);
return v___x_388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4(void){
_start:
{
lean_object* v___x_389_; lean_object* v_dummy_390_; 
v___x_389_ = lean_box(0);
v_dummy_390_ = l_Lean_Expr_sort___override(v___x_389_);
return v_dummy_390_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(uint8_t v_explicitOnly_391_, uint8_t v_skipTypes_392_, uint8_t v_skipProofs_393_, lean_object* v_upperBound_394_, lean_object* v_a_395_, uint8_t v_a_396_, lean_object* v_a_397_, lean_object* v_b_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_a_406_; uint8_t v___x_427_; 
v___x_427_ = lean_nat_dec_lt(v_a_397_, v_upperBound_394_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec(v_a_397_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v_b_398_);
return v___x_428_;
}
else
{
lean_object* v_paramInfo_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_paramInfo_429_ = lean_ctor_get(v_a_395_, 0);
v___x_430_ = lean_array_get_size(v_paramInfo_429_);
v___x_431_ = lean_nat_dec_lt(v_a_397_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_array_get_size(v_b_398_);
v___x_433_ = lean_nat_dec_lt(v_a_397_, v___x_432_);
if (v___x_433_ == 0)
{
v_a_406_ = v_b_398_;
goto v___jp_405_;
}
else
{
lean_object* v_v_434_; lean_object* v___x_435_; 
v_v_434_ = lean_array_fget_borrowed(v_b_398_, v_a_397_);
lean_inc(v_v_434_);
v___x_435_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_391_, v_skipTypes_392_, v_skipProofs_393_, v_v_434_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v_xs_x27_438_; lean_object* v___x_439_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = lean_box(0);
v_xs_x27_438_ = lean_array_fset(v_b_398_, v_a_397_, v___x_437_);
v___x_439_ = lean_array_fset(v_xs_x27_438_, v_a_397_, v_a_436_);
v_a_406_ = v___x_439_;
goto v___jp_405_;
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec_ref(v_b_398_);
lean_dec(v_a_397_);
v_a_440_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_435_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_435_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
else
{
if (v_explicitOnly_391_ == 0)
{
goto v___jp_410_;
}
else
{
if (v_a_396_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_array_fget_borrowed(v_paramInfo_429_, v_a_397_);
v___x_449_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_448_);
if (v___x_449_ == 0)
{
v_a_406_ = v_b_398_;
goto v___jp_405_;
}
else
{
goto v___jp_410_;
}
}
else
{
goto v___jp_410_;
}
}
}
}
v___jp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_nat_add(v_a_397_, v___x_407_);
lean_dec(v_a_397_);
v_a_397_ = v___x_408_;
v_b_398_ = v_a_406_;
goto _start;
}
v___jp_410_:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = lean_array_get_size(v_b_398_);
v___x_412_ = lean_nat_dec_lt(v_a_397_, v___x_411_);
if (v___x_412_ == 0)
{
v_a_406_ = v_b_398_;
goto v___jp_405_;
}
else
{
lean_object* v_v_413_; lean_object* v___x_414_; 
v_v_413_ = lean_array_fget_borrowed(v_b_398_, v_a_397_);
lean_inc(v_v_413_);
v___x_414_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_391_, v_skipTypes_392_, v_skipProofs_393_, v_v_413_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_416_; lean_object* v_xs_x27_417_; lean_object* v___x_418_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = lean_box(0);
v_xs_x27_417_ = lean_array_fset(v_b_398_, v_a_397_, v___x_416_);
v___x_418_ = lean_array_fset(v_xs_x27_417_, v_a_397_, v_a_415_);
v_a_406_ = v___x_418_;
goto v___jp_405_;
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_b_398_);
lean_dec(v_a_397_);
v_a_419_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_414_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_414_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed(lean_object* v_explicitOnly_455_, lean_object* v_skipTypes_456_, lean_object* v_skipProofs_457_, lean_object* v_a_458_, lean_object* v___x_459_, lean_object* v_xs_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v_explicitOnly_boxed_468_; uint8_t v_skipTypes_boxed_469_; uint8_t v_skipProofs_boxed_470_; uint8_t v_a_14856__boxed_471_; uint8_t v___x_14857__boxed_472_; lean_object* v_res_473_; 
v_explicitOnly_boxed_468_ = lean_unbox(v_explicitOnly_455_);
v_skipTypes_boxed_469_ = lean_unbox(v_skipTypes_456_);
v_skipProofs_boxed_470_ = lean_unbox(v_skipProofs_457_);
v_a_14856__boxed_471_ = lean_unbox(v_a_458_);
v___x_14857__boxed_472_ = lean_unbox(v___x_459_);
v_res_473_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(v_explicitOnly_boxed_468_, v_skipTypes_boxed_469_, v_skipProofs_boxed_470_, v_a_14856__boxed_471_, v___x_14857__boxed_472_, v_xs_460_, v_b_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v_xs_460_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(uint8_t v_explicitOnly_474_, uint8_t v_skipTypes_475_, uint8_t v_skipProofs_476_, uint8_t v_a_477_, uint8_t v___x_478_, lean_object* v_xs_479_, lean_object* v_b_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_474_, v_skipTypes_475_, v_skipProofs_476_, v_b_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; uint8_t v___x_489_; lean_object* v___x_490_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = 1;
v___x_490_ = l_Lean_Meta_mkForallFVars(v_xs_479_, v_a_488_, v_a_477_, v___x_478_, v___x_478_, v___x_489_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
return v___x_490_;
}
else
{
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed(lean_object* v_explicitOnly_491_, lean_object* v_skipTypes_492_, lean_object* v_skipProofs_493_, lean_object* v_a_494_, lean_object* v___x_495_, lean_object* v_xs_496_, lean_object* v_b_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
uint8_t v_explicitOnly_boxed_504_; uint8_t v_skipTypes_boxed_505_; uint8_t v_skipProofs_boxed_506_; uint8_t v_a_14869__boxed_507_; uint8_t v___x_14870__boxed_508_; lean_object* v_res_509_; 
v_explicitOnly_boxed_504_ = lean_unbox(v_explicitOnly_491_);
v_skipTypes_boxed_505_ = lean_unbox(v_skipTypes_492_);
v_skipProofs_boxed_506_ = lean_unbox(v_skipProofs_493_);
v_a_14869__boxed_507_ = lean_unbox(v_a_494_);
v___x_14870__boxed_508_ = lean_unbox(v___x_495_);
v_res_509_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(v_explicitOnly_boxed_504_, v_skipTypes_boxed_505_, v_skipProofs_boxed_506_, v_a_14869__boxed_507_, v___x_14870__boxed_508_, v_xs_496_, v_b_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v_xs_496_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(lean_object* v___x_510_, lean_object* v_e_511_, uint8_t v_explicitOnly_512_, uint8_t v_skipTypes_513_, uint8_t v_skipProofs_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_527_; lean_object* v___y_533_; lean_object* v___y_534_; uint8_t v___y_535_; uint8_t v___y_544_; uint8_t v_a_545_; 
if (v_skipTypes_513_ == 0)
{
goto v___jp_610_;
}
else
{
lean_object* v___x_631_; 
lean_inc_ref(v_e_511_);
v___x_631_ = l_Lean_Meta_isType(v_e_511_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_640_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_640_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___x_636_; 
v___x_636_ = lean_unbox(v_a_632_);
lean_dec(v_a_632_);
if (v___x_636_ == 0)
{
lean_del_object(v___x_634_);
goto v___jp_610_;
}
else
{
lean_object* v___x_638_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v_e_511_);
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_e_511_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec_ref(v_e_511_);
v_a_641_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_631_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_631_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
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
v___jp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = l_Lean_mkAppN(v___y_523_, v___y_522_);
lean_dec_ref(v___y_522_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_add(v___y_527_, v___x_528_);
lean_dec(v___y_527_);
v___x_530_ = l_Lean_mkRawNatLit(v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
v___jp_532_:
{
if (v___y_535_ == 0)
{
v___y_522_ = v___y_533_;
v___y_523_ = v___y_534_;
goto v___jp_521_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_array_get_borrowed(v___x_510_, v___y_533_, v___x_536_);
v___x_538_ = l_Lean_Expr_isRawNatLit(v___x_537_);
if (v___x_538_ == 0)
{
v___y_522_ = v___y_533_;
v___y_523_ = v___y_534_;
goto v___jp_521_;
}
else
{
lean_object* v___x_539_; 
lean_inc(v___x_537_);
lean_dec_ref(v___y_534_);
lean_dec_ref(v___y_533_);
v___x_539_ = l_Lean_Expr_rawNatLit_x3f(v___x_537_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_obj_once(&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3, &l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3);
v___x_541_ = l_panic___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(v___x_540_);
v___y_527_ = v___x_541_;
goto v___jp_526_;
}
else
{
lean_object* v_val_542_; 
v_val_542_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v___x_539_, 1);
v___y_527_ = v_val_542_;
goto v___jp_526_;
}
}
}
}
v___jp_543_:
{
lean_object* v___x_546_; 
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
v___x_546_ = lean_whnf(v_e_511_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
switch(lean_obj_tag(v_a_547_))
{
case 5:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = l_Lean_Expr_getAppFn(v_a_547_);
v___x_549_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_512_, v_skipTypes_513_, v_skipProofs_514_, v___x_548_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc_n(v_a_550_, 2);
lean_dec_ref_known(v___x_549_, 1);
v___x_551_ = l_Lean_Expr_getAppNumArgs(v_a_547_);
lean_inc(v___x_551_);
v___x_552_ = l_Lean_Meta_getFunInfoNArgs(v_a_550_, v___x_551_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v_dummy_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v_dummy_554_ = lean_obj_once(&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4, &l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4_once, _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4);
lean_inc(v___x_551_);
v___x_555_ = lean_mk_array(v___x_551_, v_dummy_554_);
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_sub(v___x_551_, v___x_556_);
lean_dec(v___x_551_);
v___x_558_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_547_, v___x_555_, v___x_557_);
v___x_559_ = lean_array_get_size(v___x_558_);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_512_, v_skipTypes_513_, v_skipProofs_514_, v___x_559_, v_a_553_, v_a_545_, v___x_560_, v___x_558_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v_a_553_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref_known(v___x_561_, 1);
v___x_563_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7));
v___x_564_ = l_Lean_Expr_isConstOf(v_a_550_, v___x_563_);
if (v___x_564_ == 0)
{
v___y_533_ = v_a_562_;
v___y_534_ = v_a_550_;
v___y_535_ = v_a_545_;
goto v___jp_532_;
}
else
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_array_get_size(v_a_562_);
v___x_566_ = lean_nat_dec_eq(v___x_565_, v___x_556_);
v___y_533_ = v_a_562_;
v___y_534_ = v_a_550_;
v___y_535_ = v___x_566_;
goto v___jp_532_;
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v_a_550_);
v_a_567_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_561_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_561_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec(v___x_551_);
lean_dec(v_a_550_);
lean_dec_ref_known(v_a_547_, 2);
v_a_575_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_552_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_552_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_547_, 2);
return v___x_549_;
}
}
case 6:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___f_588_; lean_object* v___x_589_; 
lean_dec_ref_known(v___x_546_, 1);
v___x_583_ = lean_box(v_explicitOnly_512_);
v___x_584_ = lean_box(v_skipTypes_513_);
v___x_585_ = lean_box(v_skipProofs_514_);
v___x_586_ = lean_box(v_a_545_);
v___x_587_ = lean_box(v___y_544_);
v___f_588_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed), 13, 5);
lean_closure_set(v___f_588_, 0, v___x_583_);
lean_closure_set(v___f_588_, 1, v___x_584_);
lean_closure_set(v___f_588_, 2, v___x_585_);
lean_closure_set(v___f_588_, 3, v___x_586_);
lean_closure_set(v___f_588_, 4, v___x_587_);
v___x_589_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_a_547_, v___f_588_, v_a_545_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
return v___x_589_;
}
case 7:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___f_595_; lean_object* v___x_596_; 
lean_dec_ref_known(v___x_546_, 1);
v___x_590_ = lean_box(v_explicitOnly_512_);
v___x_591_ = lean_box(v_skipTypes_513_);
v___x_592_ = lean_box(v_skipProofs_514_);
v___x_593_ = lean_box(v_a_545_);
v___x_594_ = lean_box(v___y_544_);
v___f_595_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed), 13, 5);
lean_closure_set(v___f_595_, 0, v___x_590_);
lean_closure_set(v___f_595_, 1, v___x_591_);
lean_closure_set(v___f_595_, 2, v___x_592_);
lean_closure_set(v___f_595_, 3, v___x_593_);
lean_closure_set(v___f_595_, 4, v___x_594_);
v___x_596_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_a_547_, v___f_595_, v_a_545_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
return v___x_596_;
}
case 11:
{
lean_object* v_typeName_597_; lean_object* v_idx_598_; lean_object* v_struct_599_; lean_object* v___x_600_; 
lean_dec_ref_known(v___x_546_, 1);
v_typeName_597_ = lean_ctor_get(v_a_547_, 0);
lean_inc(v_typeName_597_);
v_idx_598_ = lean_ctor_get(v_a_547_, 1);
lean_inc(v_idx_598_);
v_struct_599_ = lean_ctor_get(v_a_547_, 2);
lean_inc_ref(v_struct_599_);
lean_dec_ref_known(v_a_547_, 3);
v___x_600_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_512_, v_skipTypes_513_, v_skipProofs_514_, v_struct_599_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_609_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = l_Lean_mkProj(v_typeName_597_, v_idx_598_, v_a_601_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
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
lean_dec(v_idx_598_);
lean_dec(v_typeName_597_);
return v___x_600_;
}
}
default: 
{
lean_dec(v_a_547_);
return v___x_546_;
}
}
}
else
{
return v___x_546_;
}
}
v___jp_610_:
{
uint8_t v___x_611_; 
v___x_611_ = 1;
if (v_skipProofs_514_ == 0)
{
v___y_544_ = v___x_611_;
v_a_545_ = v_skipProofs_514_;
goto v___jp_543_;
}
else
{
lean_object* v___x_612_; 
lean_inc_ref(v_e_511_);
v___x_612_ = l_Lean_Meta_isProof(v_e_511_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_622_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_622_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint8_t v___x_617_; 
v___x_617_ = lean_unbox(v_a_613_);
if (v___x_617_ == 0)
{
uint8_t v___x_618_; 
lean_del_object(v___x_615_);
v___x_618_ = lean_unbox(v_a_613_);
lean_dec(v_a_613_);
v___y_544_ = v___x_611_;
v_a_545_ = v___x_618_;
goto v___jp_543_;
}
else
{
lean_object* v___x_620_; 
lean_dec(v_a_613_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v_e_511_);
v___x_620_ = v___x_615_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_e_511_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_e_511_);
v_a_623_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_612_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_612_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed(lean_object* v___x_649_, lean_object* v_e_650_, lean_object* v_explicitOnly_651_, lean_object* v_skipTypes_652_, lean_object* v_skipProofs_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
uint8_t v_explicitOnly_boxed_660_; uint8_t v_skipTypes_boxed_661_; uint8_t v_skipProofs_boxed_662_; lean_object* v_res_663_; 
v_explicitOnly_boxed_660_ = lean_unbox(v_explicitOnly_651_);
v_skipTypes_boxed_661_ = lean_unbox(v_skipTypes_652_);
v_skipProofs_boxed_662_ = lean_unbox(v_skipProofs_653_);
v_res_663_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(v___x_649_, v_e_650_, v_explicitOnly_boxed_660_, v_skipTypes_boxed_661_, v_skipProofs_boxed_662_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___x_649_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(uint8_t v_explicitOnly_664_, uint8_t v_skipTypes_665_, uint8_t v_skipProofs_666_, lean_object* v_e_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_st_ref_get(v_a_668_);
v___x_675_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v___x_674_, v_e_667_);
lean_dec(v___x_674_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___f_680_; lean_object* v___x_681_; 
v___x_676_ = l_Lean_instInhabitedExpr;
v___x_677_ = lean_box(v_explicitOnly_664_);
v___x_678_ = lean_box(v_skipTypes_665_);
v___x_679_ = lean_box(v_skipProofs_666_);
lean_inc_ref(v_e_667_);
v___f_680_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed), 11, 5);
lean_closure_set(v___f_680_, 0, v___x_676_);
lean_closure_set(v___f_680_, 1, v_e_667_);
lean_closure_set(v___f_680_, 2, v___x_677_);
lean_closure_set(v___f_680_, 3, v___x_678_);
lean_closure_set(v___f_680_, 4, v___x_679_);
v___x_681_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v___f_680_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_692_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_692_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_686_ = lean_st_ref_take(v_a_668_);
lean_inc(v_a_682_);
v___x_687_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v___x_686_, v_e_667_, v_a_682_);
v___x_688_ = lean_st_ref_put(v_a_668_, v___x_687_);
if (v_isShared_685_ == 0)
{
v___x_690_ = v___x_684_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_682_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_dec_ref(v_e_667_);
return v___x_681_;
}
}
else
{
lean_object* v_val_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_e_667_);
v_val_693_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_675_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_val_693_);
lean_dec(v___x_675_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set_tag(v___x_695_, 0);
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_val_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(uint8_t v_explicitOnly_701_, uint8_t v_skipTypes_702_, uint8_t v_skipProofs_703_, uint8_t v_a_704_, uint8_t v___x_705_, lean_object* v_xs_706_, lean_object* v_b_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_701_, v_skipTypes_702_, v_skipProofs_703_, v_b_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; uint8_t v___x_716_; lean_object* v___x_717_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = 1;
v___x_717_ = l_Lean_Meta_mkLambdaFVars(v_xs_706_, v_a_715_, v_a_704_, v___x_705_, v_a_704_, v___x_705_, v___x_716_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
return v___x_717_;
}
else
{
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___boxed(lean_object* v_explicitOnly_718_, lean_object* v_skipTypes_719_, lean_object* v_skipProofs_720_, lean_object* v_e_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
uint8_t v_explicitOnly_boxed_728_; uint8_t v_skipTypes_boxed_729_; uint8_t v_skipProofs_boxed_730_; lean_object* v_res_731_; 
v_explicitOnly_boxed_728_ = lean_unbox(v_explicitOnly_718_);
v_skipTypes_boxed_729_ = lean_unbox(v_skipTypes_719_);
v_skipProofs_boxed_730_ = lean_unbox(v_skipProofs_720_);
v_res_731_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_boxed_728_, v_skipTypes_boxed_729_, v_skipProofs_boxed_730_, v_e_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg___boxed(lean_object* v_explicitOnly_732_, lean_object* v_skipTypes_733_, lean_object* v_skipProofs_734_, lean_object* v_upperBound_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
uint8_t v_explicitOnly_boxed_746_; uint8_t v_skipTypes_boxed_747_; uint8_t v_skipProofs_boxed_748_; uint8_t v_a_14898__boxed_749_; lean_object* v_res_750_; 
v_explicitOnly_boxed_746_ = lean_unbox(v_explicitOnly_732_);
v_skipTypes_boxed_747_ = lean_unbox(v_skipTypes_733_);
v_skipProofs_boxed_748_ = lean_unbox(v_skipProofs_734_);
v_a_14898__boxed_749_ = lean_unbox(v_a_737_);
v_res_750_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_boxed_746_, v_skipTypes_boxed_747_, v_skipProofs_boxed_748_, v_upperBound_735_, v_a_736_, v_a_14898__boxed_749_, v_a_738_, v_b_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v_a_736_);
lean_dec(v_upperBound_735_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(lean_object* v_00_u03b2_751_, lean_object* v_m_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v_m_752_, v_a_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___boxed(lean_object* v_00_u03b2_755_, lean_object* v_m_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(v_00_u03b2_755_, v_m_756_, v_a_757_);
lean_dec_ref(v_a_757_);
lean_dec_ref(v_m_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(uint8_t v_explicitOnly_759_, uint8_t v_skipTypes_760_, uint8_t v_skipProofs_761_, lean_object* v_upperBound_762_, lean_object* v_a_763_, uint8_t v_a_764_, lean_object* v_inst_765_, lean_object* v_R_766_, lean_object* v_a_767_, lean_object* v_b_768_, lean_object* v_c_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_759_, v_skipTypes_760_, v_skipProofs_761_, v_upperBound_762_, v_a_763_, v_a_764_, v_a_767_, v_b_768_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___boxed(lean_object** _args){
lean_object* v_explicitOnly_777_ = _args[0];
lean_object* v_skipTypes_778_ = _args[1];
lean_object* v_skipProofs_779_ = _args[2];
lean_object* v_upperBound_780_ = _args[3];
lean_object* v_a_781_ = _args[4];
lean_object* v_a_782_ = _args[5];
lean_object* v_inst_783_ = _args[6];
lean_object* v_R_784_ = _args[7];
lean_object* v_a_785_ = _args[8];
lean_object* v_b_786_ = _args[9];
lean_object* v_c_787_ = _args[10];
lean_object* v___y_788_ = _args[11];
lean_object* v___y_789_ = _args[12];
lean_object* v___y_790_ = _args[13];
lean_object* v___y_791_ = _args[14];
lean_object* v___y_792_ = _args[15];
lean_object* v___y_793_ = _args[16];
_start:
{
uint8_t v_explicitOnly_boxed_794_; uint8_t v_skipTypes_boxed_795_; uint8_t v_skipProofs_boxed_796_; uint8_t v_a_15409__boxed_797_; lean_object* v_res_798_; 
v_explicitOnly_boxed_794_ = lean_unbox(v_explicitOnly_777_);
v_skipTypes_boxed_795_ = lean_unbox(v_skipTypes_778_);
v_skipProofs_boxed_796_ = lean_unbox(v_skipProofs_779_);
v_a_15409__boxed_797_ = lean_unbox(v_a_782_);
v_res_798_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(v_explicitOnly_boxed_794_, v_skipTypes_boxed_795_, v_skipProofs_boxed_796_, v_upperBound_780_, v_a_781_, v_a_15409__boxed_797_, v_inst_783_, v_R_784_, v_a_785_, v_b_786_, v_c_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v_a_781_);
lean_dec(v_upperBound_780_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(lean_object* v_00_u03b1_799_, lean_object* v_ref_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_800_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___boxed(lean_object* v_00_u03b1_805_, lean_object* v_ref_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(v_00_u03b1_805_, v_ref_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7(lean_object* v_00_u03b1_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___boxed(lean_object* v_00_u03b1_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7(v_00_u03b1_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(lean_object* v_00_u03b1_821_, lean_object* v_x_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___boxed(lean_object* v_00_u03b1_830_, lean_object* v_x_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(v_00_u03b1_830_, v_x_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6(lean_object* v_00_u03b2_839_, lean_object* v_m_840_, lean_object* v_a_841_, lean_object* v_b_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v_m_840_, v_a_841_, v_b_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(lean_object* v_00_u03b2_844_, lean_object* v_a_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_a_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_848_, lean_object* v_a_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(v_00_u03b2_848_, v_a_849_, v_x_850_);
lean_dec(v_x_850_);
lean_dec_ref(v_a_849_);
return v_res_851_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(lean_object* v_00_u03b2_852_, lean_object* v_a_853_, lean_object* v_x_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_a_853_, v_x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___boxed(lean_object* v_00_u03b2_856_, lean_object* v_a_857_, lean_object* v_x_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(v_00_u03b2_856_, v_a_857_, v_x_858_);
lean_dec(v_x_858_);
lean_dec_ref(v_a_857_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10(lean_object* v_00_u03b2_861_, lean_object* v_data_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(v_data_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11(lean_object* v_00_u03b2_864_, lean_object* v_a_865_, lean_object* v_b_866_, lean_object* v_x_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(v_a_865_, v_b_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_869_, lean_object* v_i_870_, lean_object* v_source_871_, lean_object* v_target_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11___redArg(v_i_870_, v_source_871_, v_target_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12___redArg(v_x_875_, v_x_876_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__0(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = lean_box(0);
v___x_879_ = lean_unsigned_to_nat(16u);
v___x_880_ = lean_mk_array(v___x_879_, v___x_878_);
return v___x_880_;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__1(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_obj_once(&l_Lean_Meta_reduce___closed__0, &l_Lean_Meta_reduce___closed__0_once, _init_l_Lean_Meta_reduce___closed__0);
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___x_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce(lean_object* v_e_884_, uint8_t v_explicitOnly_885_, uint8_t v_skipTypes_886_, uint8_t v_skipProofs_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_obj_once(&l_Lean_Meta_reduce___closed__1, &l_Lean_Meta_reduce___closed__1_once, _init_l_Lean_Meta_reduce___closed__1);
v___x_894_ = lean_st_mk_ref(v___x_893_);
v___x_895_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_885_, v_skipTypes_886_, v_skipProofs_887_, v_e_884_, v___x_894_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_904_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_904_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_900_ = lean_st_ref_get(v___x_894_);
lean_dec(v___x_894_);
lean_dec(v___x_900_);
if (v_isShared_899_ == 0)
{
v___x_902_ = v___x_898_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_896_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
else
{
lean_dec(v___x_894_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object* v_e_905_, lean_object* v_explicitOnly_906_, lean_object* v_skipTypes_907_, lean_object* v_skipProofs_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
uint8_t v_explicitOnly_boxed_914_; uint8_t v_skipTypes_boxed_915_; uint8_t v_skipProofs_boxed_916_; lean_object* v_res_917_; 
v_explicitOnly_boxed_914_ = lean_unbox(v_explicitOnly_906_);
v_skipTypes_boxed_915_ = lean_unbox(v_skipTypes_907_);
v_skipProofs_boxed_916_ = lean_unbox(v_skipProofs_908_);
v_res_917_ = l_Lean_Meta_reduce(v_e_905_, v_explicitOnly_boxed_914_, v_skipTypes_boxed_915_, v_skipProofs_boxed_916_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll(lean_object* v_e_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
uint8_t v___x_924_; lean_object* v___x_925_; 
v___x_924_ = 0;
v___x_925_ = l_Lean_Meta_reduce(v_e_918_, v___x_924_, v___x_924_, v___x_924_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll___boxed(lean_object* v_e_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Meta_reduceAll(v_e_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
return v_res_932_;
}
}
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_FunInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Reduce(builtin);
}
#ifdef __cplusplus
}
#endif
