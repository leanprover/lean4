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
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_reduce___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_reduce___closed__0;
static lean_once_cell_t l_Lean_Meta_reduce___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_reduce___closed__1;
static lean_once_cell_t l_Lean_Meta_reduce___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_reduce___closed__2;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(lean_object* v_m_135_, lean_object* v_query_136_, lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_zero_140_; uint8_t v_isZero_141_; 
v_zero_140_ = lean_unsigned_to_nat(0u);
v_isZero_141_ = lean_nat_dec_eq(v_x_138_, v_zero_140_);
if (v_isZero_141_ == 1)
{
lean_dec(v_x_139_);
lean_dec(v_x_138_);
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_box(2);
return v___x_142_;
}
else
{
lean_object* v_val_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_val_143_ = lean_ctor_get(v_x_137_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v_x_137_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_val_143_);
lean_dec(v_x_137_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_val_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
lean_object* v_keyArray_151_; lean_object* v_valueArray_152_; lean_object* v___x_153_; uint8_t v_isSome_154_; 
v_keyArray_151_ = lean_ctor_get(v_m_135_, 1);
v_valueArray_152_ = lean_ctor_get(v_m_135_, 2);
v___x_153_ = lean_array_fget_borrowed(v_keyArray_151_, v_x_139_);
v_isSome_154_ = lean_noption_is_some(v___x_153_);
if (v_isSome_154_ == 0)
{
lean_dec(v_x_138_);
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v_x_139_);
return v___x_155_;
}
else
{
lean_object* v_val_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_x_139_);
v_val_156_ = lean_ctor_get(v_x_137_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v_x_137_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_val_156_);
lean_dec(v_x_137_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_val_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_object* v_one_164_; lean_object* v_n_165_; lean_object* v___y_167_; 
v_one_164_ = lean_unsigned_to_nat(1u);
v_n_165_ = lean_nat_sub(v_x_138_, v_one_164_);
lean_dec(v_x_138_);
if (v_isSome_154_ == 0)
{
goto v___jp_173_;
}
else
{
lean_object* v___x_175_; uint8_t v_isSome_176_; 
v___x_175_ = lean_array_fget_borrowed(v_valueArray_152_, v_x_139_);
v_isSome_176_ = lean_noption_is_some(v___x_175_);
if (v_isSome_176_ == 0)
{
goto v___jp_173_;
}
else
{
lean_object* v_val_177_; uint8_t v___x_178_; 
lean_inc(v___x_153_);
v_val_177_ = lean_noption_get(v___x_153_);
v___x_178_ = lean_expr_eqv(v_val_177_, v_query_136_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
lean_dec(v_val_177_);
v___x_179_ = lean_array_get_size(v_keyArray_151_);
v___x_180_ = lean_nat_add(v_x_139_, v_one_164_);
lean_dec(v_x_139_);
v___x_181_ = lean_nat_dec_lt(v___x_180_, v___x_179_);
if (v___x_181_ == 0)
{
lean_dec(v___x_180_);
v_x_138_ = v_n_165_;
v_x_139_ = v_zero_140_;
goto _start;
}
else
{
v_x_138_ = v_n_165_;
v_x_139_ = v___x_180_;
goto _start;
}
}
else
{
lean_object* v_val_184_; lean_object* v___x_185_; 
lean_dec(v_n_165_);
lean_dec(v_x_137_);
lean_inc(v___x_175_);
v_val_184_ = lean_noption_get(v___x_175_);
v___x_185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_185_, 0, v_x_139_);
lean_ctor_set(v___x_185_, 1, v_val_177_);
lean_ctor_set(v___x_185_, 2, v_val_184_);
return v___x_185_;
}
}
}
v___jp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_168_ = lean_array_get_size(v_keyArray_151_);
v___x_169_ = lean_nat_add(v_x_139_, v_one_164_);
lean_dec(v_x_139_);
v___x_170_ = lean_nat_dec_lt(v___x_169_, v___x_168_);
if (v___x_170_ == 0)
{
lean_dec(v___x_169_);
v_x_137_ = v___y_167_;
v_x_138_ = v_n_165_;
v_x_139_ = v_zero_140_;
goto _start;
}
else
{
v_x_137_ = v___y_167_;
v_x_138_ = v_n_165_;
v_x_139_ = v___x_169_;
goto _start;
}
}
v___jp_173_:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v___x_174_; 
lean_inc(v_x_139_);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v_x_139_);
v___y_167_ = v___x_174_;
goto v___jp_166_;
}
else
{
v___y_167_ = v_x_137_;
goto v___jp_166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg___boxed(lean_object* v_m_186_, lean_object* v_query_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_m_186_, v_query_187_, v_x_188_, v_x_189_, v_x_190_);
lean_dec_ref(v_query_187_);
lean_dec_ref(v_m_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(lean_object* v_m_192_, lean_object* v_query_193_){
_start:
{
lean_object* v_keyArray_194_; lean_object* v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v_fold_199_; uint64_t v___x_200_; uint64_t v___x_201_; uint64_t v___x_202_; size_t v___x_203_; size_t v___x_204_; size_t v___x_205_; size_t v___x_206_; size_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_keyArray_194_ = lean_ctor_get(v_m_192_, 1);
v___x_195_ = lean_array_get_size(v_keyArray_194_);
v___x_196_ = l_Lean_Expr_hash(v_query_193_);
v___x_197_ = 32ULL;
v___x_198_ = lean_uint64_shift_right(v___x_196_, v___x_197_);
v_fold_199_ = lean_uint64_xor(v___x_196_, v___x_198_);
v___x_200_ = 16ULL;
v___x_201_ = lean_uint64_shift_right(v_fold_199_, v___x_200_);
v___x_202_ = lean_uint64_xor(v_fold_199_, v___x_201_);
v___x_203_ = lean_uint64_to_usize(v___x_202_);
v___x_204_ = lean_usize_of_nat(v___x_195_);
v___x_205_ = ((size_t)1ULL);
v___x_206_ = lean_usize_sub(v___x_204_, v___x_205_);
v___x_207_ = lean_usize_land(v___x_203_, v___x_206_);
v___x_208_ = lean_usize_to_nat(v___x_207_);
v___x_209_ = lean_box(0);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_m_192_, v_query_193_, v___x_209_, v___x_195_, v___x_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg___boxed(lean_object* v_m_211_, lean_object* v_query_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v_m_211_, v_query_212_);
lean_dec_ref(v_query_212_);
lean_dec_ref(v_m_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(lean_object* v_m_214_, lean_object* v_query_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v_m_214_, v_query_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_index_217_; lean_object* v_key_218_; lean_object* v_value_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
v_index_217_ = lean_ctor_get(v___x_216_, 0);
v_key_218_ = lean_ctor_get(v___x_216_, 1);
v_value_219_ = lean_ctor_get(v___x_216_, 2);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_216_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_value_219_);
lean_inc(v_key_218_);
lean_inc(v_index_217_);
lean_dec(v___x_216_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_index_217_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_key_218_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_value_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
else
{
lean_object* v___x_227_; 
lean_dec(v___x_216_);
v___x_227_ = lean_box(1);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg___boxed(lean_object* v_m_228_, lean_object* v_query_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_m_228_, v_query_229_);
lean_dec_ref(v_query_229_);
lean_dec_ref(v_m_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(lean_object* v_m_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_m_231_, v_a_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_value_234_; lean_object* v___x_235_; 
v_value_234_ = lean_ctor_get(v___x_233_, 2);
lean_inc(v_value_234_);
lean_dec_ref_known(v___x_233_, 3);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v_value_234_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; 
v___x_236_ = lean_box(0);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg___boxed(lean_object* v_m_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v_m_237_, v_a_238_);
lean_dec_ref(v_a_238_);
lean_dec_ref(v_m_237_);
return v_res_239_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = l_Lean_maxRecDepthErrorMessage;
v___x_246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3);
v___x_248_ = l_Lean_MessageData_ofFormat(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4);
v___x_250_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2));
v___x_251_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(lean_object* v_ref_252_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_ref_252_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___boxed(lean_object* v_ref_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_257_);
return v_res_259_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_box(0);
v___x_261_ = l_Lean_interruptExceptionId;
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg(){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___boxed(lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(lean_object* v_x_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___y_276_; lean_object* v___y_286_; uint8_t v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; uint8_t v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v_fileName_306_; lean_object* v_fileMap_307_; lean_object* v_options_308_; lean_object* v_currRecDepth_309_; lean_object* v_maxRecDepth_310_; lean_object* v_ref_311_; lean_object* v_currNamespace_312_; lean_object* v_openDecls_313_; lean_object* v_initHeartbeats_314_; lean_object* v_maxHeartbeats_315_; lean_object* v_quotContext_316_; lean_object* v_currMacroScope_317_; uint8_t v_diag_318_; lean_object* v_cancelTk_x3f_319_; uint8_t v_suppressElabErrors_320_; lean_object* v_inheritedTraceOptions_321_; 
v_fileName_306_ = lean_ctor_get(v___y_272_, 0);
v_fileMap_307_ = lean_ctor_get(v___y_272_, 1);
v_options_308_ = lean_ctor_get(v___y_272_, 2);
v_currRecDepth_309_ = lean_ctor_get(v___y_272_, 3);
v_maxRecDepth_310_ = lean_ctor_get(v___y_272_, 4);
v_ref_311_ = lean_ctor_get(v___y_272_, 5);
v_currNamespace_312_ = lean_ctor_get(v___y_272_, 6);
v_openDecls_313_ = lean_ctor_get(v___y_272_, 7);
v_initHeartbeats_314_ = lean_ctor_get(v___y_272_, 8);
v_maxHeartbeats_315_ = lean_ctor_get(v___y_272_, 9);
v_quotContext_316_ = lean_ctor_get(v___y_272_, 10);
v_currMacroScope_317_ = lean_ctor_get(v___y_272_, 11);
v_diag_318_ = lean_ctor_get_uint8(v___y_272_, sizeof(void*)*14);
v_cancelTk_x3f_319_ = lean_ctor_get(v___y_272_, 12);
v_suppressElabErrors_320_ = lean_ctor_get_uint8(v___y_272_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_321_ = lean_ctor_get(v___y_272_, 13);
if (lean_obj_tag(v_cancelTk_x3f_319_) == 1)
{
lean_object* v_val_327_; uint8_t v___x_328_; 
v_val_327_ = lean_ctor_get(v_cancelTk_x3f_319_, 0);
v___x_328_ = l_IO_CancelToken_isSet(v_val_327_);
if (v___x_328_ == 0)
{
goto v___jp_322_;
}
else
{
lean_object* v___x_329_; lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v_x_268_);
v___x_329_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
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
else
{
goto v___jp_322_;
}
v___jp_275_:
{
if (lean_obj_tag(v___y_276_) == 0)
{
return v___y_276_;
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
v_a_277_ = lean_ctor_get(v___y_276_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___y_276_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___y_276_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___y_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
v___jp_285_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v___y_297_, v___x_302_);
lean_inc_ref(v___y_295_);
lean_inc(v___y_289_);
lean_inc(v___y_286_);
lean_inc(v___y_292_);
lean_inc(v___y_291_);
lean_inc(v___y_288_);
lean_inc(v___y_298_);
lean_inc(v___y_293_);
lean_inc(v___y_299_);
lean_inc_ref(v___y_290_);
lean_inc_ref(v___y_300_);
lean_inc_ref(v___y_294_);
v___x_304_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_304_, 0, v___y_294_);
lean_ctor_set(v___x_304_, 1, v___y_300_);
lean_ctor_set(v___x_304_, 2, v___y_290_);
lean_ctor_set(v___x_304_, 3, v___x_303_);
lean_ctor_set(v___x_304_, 4, v___y_299_);
lean_ctor_set(v___x_304_, 5, v___y_301_);
lean_ctor_set(v___x_304_, 6, v___y_293_);
lean_ctor_set(v___x_304_, 7, v___y_298_);
lean_ctor_set(v___x_304_, 8, v___y_288_);
lean_ctor_set(v___x_304_, 9, v___y_291_);
lean_ctor_set(v___x_304_, 10, v___y_292_);
lean_ctor_set(v___x_304_, 11, v___y_286_);
lean_ctor_set(v___x_304_, 12, v___y_289_);
lean_ctor_set(v___x_304_, 13, v___y_295_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*14, v___y_296_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*14 + 1, v___y_287_);
lean_inc(v___y_273_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
lean_inc(v___y_269_);
v___x_305_ = lean_apply_6(v_x_268_, v___y_269_, v___y_270_, v___y_271_, v___x_304_, v___y_273_, lean_box(0));
v___y_276_ = v___x_305_;
goto v___jp_275_;
}
v___jp_322_:
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_nat_dec_eq(v_maxRecDepth_310_, v___x_323_);
if (v___x_324_ == 0)
{
uint8_t v___x_325_; 
v___x_325_ = lean_nat_dec_eq(v_currRecDepth_309_, v_maxRecDepth_310_);
if (v___x_325_ == 0)
{
lean_inc(v_ref_311_);
v___y_286_ = v_currMacroScope_317_;
v___y_287_ = v_suppressElabErrors_320_;
v___y_288_ = v_initHeartbeats_314_;
v___y_289_ = v_cancelTk_x3f_319_;
v___y_290_ = v_options_308_;
v___y_291_ = v_maxHeartbeats_315_;
v___y_292_ = v_quotContext_316_;
v___y_293_ = v_currNamespace_312_;
v___y_294_ = v_fileName_306_;
v___y_295_ = v_inheritedTraceOptions_321_;
v___y_296_ = v_diag_318_;
v___y_297_ = v_currRecDepth_309_;
v___y_298_ = v_openDecls_313_;
v___y_299_ = v_maxRecDepth_310_;
v___y_300_ = v_fileMap_307_;
v___y_301_ = v_ref_311_;
goto v___jp_285_;
}
else
{
lean_object* v___x_326_; 
lean_dec_ref(v_x_268_);
lean_inc(v_ref_311_);
v___x_326_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_311_);
v___y_276_ = v___x_326_;
goto v___jp_275_;
}
}
else
{
lean_inc(v_ref_311_);
v___y_286_ = v_currMacroScope_317_;
v___y_287_ = v_suppressElabErrors_320_;
v___y_288_ = v_initHeartbeats_314_;
v___y_289_ = v_cancelTk_x3f_319_;
v___y_290_ = v_options_308_;
v___y_291_ = v_maxHeartbeats_315_;
v___y_292_ = v_quotContext_316_;
v___y_293_ = v_currNamespace_312_;
v___y_294_ = v_fileName_306_;
v___y_295_ = v_inheritedTraceOptions_321_;
v___y_296_ = v_diag_318_;
v___y_297_ = v_currRecDepth_309_;
v___y_298_ = v_openDecls_313_;
v___y_299_ = v_maxRecDepth_310_;
v___y_300_ = v_fileMap_307_;
v___y_301_ = v_ref_311_;
goto v___jp_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg___boxed(lean_object* v_x_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12___redArg(lean_object* v_b_346_, lean_object* v_acc_347_, lean_object* v_i_348_){
_start:
{
lean_object* v___y_350_; lean_object* v_keyArray_358_; lean_object* v_valueArray_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_keyArray_358_ = lean_ctor_get(v_b_346_, 1);
v_valueArray_359_ = lean_ctor_get(v_b_346_, 2);
v___x_360_ = lean_array_get_size(v_keyArray_358_);
v___x_361_ = lean_nat_dec_lt(v_i_348_, v___x_360_);
if (v___x_361_ == 0)
{
lean_dec(v_i_348_);
return v_acc_347_;
}
else
{
lean_object* v___x_362_; uint8_t v_isSome_363_; 
v___x_362_ = lean_array_fget_borrowed(v_keyArray_358_, v_i_348_);
v_isSome_363_ = lean_noption_is_some(v___x_362_);
if (v_isSome_363_ == 0)
{
goto v___jp_354_;
}
else
{
lean_object* v___x_364_; uint8_t v_isSome_365_; 
v___x_364_ = lean_array_fget_borrowed(v_valueArray_359_, v_i_348_);
v_isSome_365_ = lean_noption_is_some(v___x_364_);
if (v_isSome_365_ == 0)
{
goto v___jp_354_;
}
else
{
lean_object* v_val_366_; lean_object* v_val_367_; lean_object* v_i_369_; lean_object* v___x_374_; 
lean_inc(v___x_362_);
v_val_366_ = lean_noption_get(v___x_362_);
lean_inc(v___x_364_);
v_val_367_ = lean_noption_get(v___x_364_);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v_acc_347_, v_val_366_);
switch(lean_obj_tag(v___x_374_))
{
case 0:
{
lean_object* v_index_375_; lean_object* v_size_376_; lean_object* v___x_377_; 
v_index_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_index_375_);
lean_dec_ref_known(v___x_374_, 3);
v_size_376_ = lean_ctor_get(v_acc_347_, 0);
lean_inc(v_size_376_);
v___x_377_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_347_, v_size_376_, v_index_375_, v_val_366_, v_val_367_);
lean_dec(v_index_375_);
v___y_350_ = v___x_377_;
goto v___jp_349_;
}
case 1:
{
lean_object* v_index_378_; 
v_index_378_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_index_378_);
lean_dec_ref_known(v___x_374_, 1);
v_i_369_ = v_index_378_;
goto v___jp_368_;
}
default: 
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_347_, v___x_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_index_381_; 
v_index_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_index_381_);
lean_dec_ref_known(v___x_380_, 1);
v_i_369_ = v_index_381_;
goto v___jp_368_;
}
else
{
lean_dec(v_val_367_);
lean_dec(v_val_366_);
v___y_350_ = v_acc_347_;
goto v___jp_349_;
}
}
}
v___jp_368_:
{
lean_object* v_size_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_size_370_ = lean_ctor_get(v_acc_347_, 0);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_size_370_, v___x_371_);
v___x_373_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_347_, v___x_372_, v_i_369_, v_val_366_, v_val_367_);
lean_dec(v_i_369_);
v___y_350_ = v___x_373_;
goto v___jp_349_;
}
}
}
}
v___jp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_add(v_i_348_, v___x_351_);
lean_dec(v_i_348_);
v_acc_347_ = v___y_350_;
v_i_348_ = v___x_352_;
goto _start;
}
v___jp_354_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_i_348_, v___x_355_);
lean_dec(v_i_348_);
v_i_348_ = v___x_356_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12___redArg___boxed(lean_object* v_b_382_, lean_object* v_acc_383_, lean_object* v_i_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12___redArg(v_b_382_, v_acc_383_, v_i_384_);
lean_dec_ref(v_b_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11___redArg(lean_object* v_init_386_, lean_object* v_b_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12___redArg(v_b_387_, v_init_386_, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11___redArg___boxed(lean_object* v_init_390_, lean_object* v_b_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11___redArg(v_init_390_, v_b_391_);
lean_dec_ref(v_b_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(lean_object* v_m_393_){
_start:
{
lean_object* v_keyArray_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v_cellCount_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_target_401_; lean_object* v___x_402_; 
v_keyArray_394_ = lean_ctor_get(v_m_393_, 1);
v___x_395_ = lean_array_get_size(v_keyArray_394_);
v___x_396_ = lean_unsigned_to_nat(2u);
v_cellCount_397_ = lean_nat_mul(v___x_395_, v___x_396_);
v___x_398_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_397_);
v___x_399_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_397_);
v___x_400_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_397_);
v_target_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_401_, 0, v___x_398_);
lean_ctor_set(v_target_401_, 1, v___x_399_);
lean_ctor_set(v_target_401_, 2, v___x_400_);
v___x_402_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11___redArg(v_target_401_, v_m_393_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg___boxed(lean_object* v_m_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(v_m_403_);
lean_dec_ref(v_m_403_);
return v_res_404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_408_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2));
v___x_409_ = lean_unsigned_to_nat(14u);
v___x_410_ = lean_unsigned_to_nat(22u);
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1));
v___x_412_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0));
v___x_413_ = l_mkPanicMessageWithDecl(v___x_412_, v___x_411_, v___x_410_, v___x_409_, v___x_408_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4(void){
_start:
{
lean_object* v___x_414_; lean_object* v_dummy_415_; 
v___x_414_ = lean_box(0);
v_dummy_415_ = l_Lean_Expr_sort___override(v___x_414_);
return v_dummy_415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(uint8_t v_explicitOnly_416_, uint8_t v_skipTypes_417_, uint8_t v_skipProofs_418_, lean_object* v_upperBound_419_, lean_object* v_a_420_, uint8_t v_a_421_, lean_object* v_a_422_, lean_object* v_b_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_a_431_; uint8_t v___x_452_; 
v___x_452_ = lean_nat_dec_lt(v_a_422_, v_upperBound_419_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
lean_dec(v_a_422_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v_b_423_);
return v___x_453_;
}
else
{
lean_object* v_paramInfo_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_paramInfo_454_ = lean_ctor_get(v_a_420_, 0);
v___x_455_ = lean_array_get_size(v_paramInfo_454_);
v___x_456_ = lean_nat_dec_lt(v_a_422_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_array_get_size(v_b_423_);
v___x_458_ = lean_nat_dec_lt(v_a_422_, v___x_457_);
if (v___x_458_ == 0)
{
v_a_431_ = v_b_423_;
goto v___jp_430_;
}
else
{
lean_object* v_v_459_; lean_object* v___x_460_; 
v_v_459_ = lean_array_fget_borrowed(v_b_423_, v_a_422_);
lean_inc(v_v_459_);
v___x_460_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_416_, v_skipTypes_417_, v_skipProofs_418_, v_v_459_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; lean_object* v_xs_x27_463_; lean_object* v___x_464_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = lean_box(0);
v_xs_x27_463_ = lean_array_fset(v_b_423_, v_a_422_, v___x_462_);
v___x_464_ = lean_array_fset(v_xs_x27_463_, v_a_422_, v_a_461_);
v_a_431_ = v___x_464_;
goto v___jp_430_;
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v_b_423_);
lean_dec(v_a_422_);
v_a_465_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_460_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_460_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
else
{
if (v_explicitOnly_416_ == 0)
{
goto v___jp_435_;
}
else
{
if (v_a_421_ == 0)
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_array_fget_borrowed(v_paramInfo_454_, v_a_422_);
v___x_474_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_473_);
if (v___x_474_ == 0)
{
v_a_431_ = v_b_423_;
goto v___jp_430_;
}
else
{
goto v___jp_435_;
}
}
else
{
goto v___jp_435_;
}
}
}
}
v___jp_430_:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_add(v_a_422_, v___x_432_);
lean_dec(v_a_422_);
v_a_422_ = v___x_433_;
v_b_423_ = v_a_431_;
goto _start;
}
v___jp_435_:
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_array_get_size(v_b_423_);
v___x_437_ = lean_nat_dec_lt(v_a_422_, v___x_436_);
if (v___x_437_ == 0)
{
v_a_431_ = v_b_423_;
goto v___jp_430_;
}
else
{
lean_object* v_v_438_; lean_object* v___x_439_; 
v_v_438_ = lean_array_fget_borrowed(v_b_423_, v_a_422_);
lean_inc(v_v_438_);
v___x_439_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_416_, v_skipTypes_417_, v_skipProofs_418_, v_v_438_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v_xs_x27_442_; lean_object* v___x_443_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v___x_441_ = lean_box(0);
v_xs_x27_442_ = lean_array_fset(v_b_423_, v_a_422_, v___x_441_);
v___x_443_ = lean_array_fset(v_xs_x27_442_, v_a_422_, v_a_440_);
v_a_431_ = v___x_443_;
goto v___jp_430_;
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec_ref(v_b_423_);
lean_dec(v_a_422_);
v_a_444_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_439_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_439_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed(lean_object* v_explicitOnly_480_, lean_object* v_skipTypes_481_, lean_object* v_skipProofs_482_, lean_object* v_a_483_, lean_object* v___x_484_, lean_object* v_xs_485_, lean_object* v_b_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
uint8_t v_explicitOnly_boxed_493_; uint8_t v_skipTypes_boxed_494_; uint8_t v_skipProofs_boxed_495_; uint8_t v_a_18380__boxed_496_; uint8_t v___x_18381__boxed_497_; lean_object* v_res_498_; 
v_explicitOnly_boxed_493_ = lean_unbox(v_explicitOnly_480_);
v_skipTypes_boxed_494_ = lean_unbox(v_skipTypes_481_);
v_skipProofs_boxed_495_ = lean_unbox(v_skipProofs_482_);
v_a_18380__boxed_496_ = lean_unbox(v_a_483_);
v___x_18381__boxed_497_ = lean_unbox(v___x_484_);
v_res_498_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(v_explicitOnly_boxed_493_, v_skipTypes_boxed_494_, v_skipProofs_boxed_495_, v_a_18380__boxed_496_, v___x_18381__boxed_497_, v_xs_485_, v_b_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v_xs_485_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(uint8_t v_explicitOnly_499_, uint8_t v_skipTypes_500_, uint8_t v_skipProofs_501_, uint8_t v_a_502_, uint8_t v___x_503_, lean_object* v_xs_504_, lean_object* v_b_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_499_, v_skipTypes_500_, v_skipProofs_501_, v_b_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; uint8_t v___x_514_; lean_object* v___x_515_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_512_, 1);
v___x_514_ = 1;
v___x_515_ = l_Lean_Meta_mkForallFVars(v_xs_504_, v_a_513_, v_a_502_, v___x_503_, v___x_503_, v___x_514_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
return v___x_515_;
}
else
{
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed(lean_object* v_explicitOnly_516_, lean_object* v_skipTypes_517_, lean_object* v_skipProofs_518_, lean_object* v_a_519_, lean_object* v___x_520_, lean_object* v_xs_521_, lean_object* v_b_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
uint8_t v_explicitOnly_boxed_529_; uint8_t v_skipTypes_boxed_530_; uint8_t v_skipProofs_boxed_531_; uint8_t v_a_18393__boxed_532_; uint8_t v___x_18394__boxed_533_; lean_object* v_res_534_; 
v_explicitOnly_boxed_529_ = lean_unbox(v_explicitOnly_516_);
v_skipTypes_boxed_530_ = lean_unbox(v_skipTypes_517_);
v_skipProofs_boxed_531_ = lean_unbox(v_skipProofs_518_);
v_a_18393__boxed_532_ = lean_unbox(v_a_519_);
v___x_18394__boxed_533_ = lean_unbox(v___x_520_);
v_res_534_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(v_explicitOnly_boxed_529_, v_skipTypes_boxed_530_, v_skipProofs_boxed_531_, v_a_18393__boxed_532_, v___x_18394__boxed_533_, v_xs_521_, v_b_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v_xs_521_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(lean_object* v_e_535_, uint8_t v_explicitOnly_536_, uint8_t v_skipTypes_537_, uint8_t v_skipProofs_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_551_; lean_object* v___y_557_; lean_object* v___y_558_; uint8_t v___y_559_; uint8_t v___y_569_; uint8_t v_a_570_; 
if (v_skipTypes_537_ == 0)
{
goto v___jp_635_;
}
else
{
lean_object* v___x_656_; 
lean_inc_ref(v_e_535_);
v___x_656_ = l_Lean_Meta_isType(v_e_535_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_665_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
uint8_t v___x_661_; 
v___x_661_ = lean_unbox(v_a_657_);
lean_dec(v_a_657_);
if (v___x_661_ == 0)
{
lean_del_object(v___x_659_);
goto v___jp_635_;
}
else
{
lean_object* v___x_663_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_e_535_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_e_535_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_e_535_);
v_a_666_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_656_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_656_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
v___jp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = l_Lean_mkAppN(v___y_547_, v___y_546_);
lean_dec_ref(v___y_546_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
v___jp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = lean_nat_add(v___y_551_, v___x_552_);
lean_dec(v___y_551_);
v___x_554_ = l_Lean_mkRawNatLit(v___x_553_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
v___jp_556_:
{
if (v___y_559_ == 0)
{
v___y_546_ = v___y_557_;
v___y_547_ = v___y_558_;
goto v___jp_545_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_560_ = l_Lean_instInhabitedExpr;
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_array_get_borrowed(v___x_560_, v___y_557_, v___x_561_);
v___x_563_ = l_Lean_Expr_isRawNatLit(v___x_562_);
if (v___x_563_ == 0)
{
v___y_546_ = v___y_557_;
v___y_547_ = v___y_558_;
goto v___jp_545_;
}
else
{
lean_object* v___x_564_; 
lean_inc(v___x_562_);
lean_dec_ref(v___y_558_);
lean_dec_ref(v___y_557_);
v___x_564_ = l_Lean_Expr_rawNatLit_x3f(v___x_562_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3, &l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3);
v___x_566_ = l_panic___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(v___x_565_);
v___y_551_ = v___x_566_;
goto v___jp_550_;
}
else
{
lean_object* v_val_567_; 
v_val_567_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v___x_564_, 1);
v___y_551_ = v_val_567_;
goto v___jp_550_;
}
}
}
}
v___jp_568_:
{
lean_object* v___x_571_; 
lean_inc(v___y_543_);
lean_inc_ref(v___y_542_);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
v___x_571_ = lean_whnf(v_e_535_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
switch(lean_obj_tag(v_a_572_))
{
case 5:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref_known(v___x_571_, 1);
v___x_573_ = l_Lean_Expr_getAppFn(v_a_572_);
v___x_574_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_536_, v_skipTypes_537_, v_skipProofs_538_, v___x_573_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc_n(v_a_575_, 2);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = l_Lean_Expr_getAppNumArgs(v_a_572_);
lean_inc(v___x_576_);
v___x_577_ = l_Lean_Meta_getFunInfoNArgs(v_a_575_, v___x_576_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v_dummy_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_577_, 1);
v_dummy_579_ = lean_obj_once(&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4, &l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4_once, _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4);
lean_inc(v___x_576_);
v___x_580_ = lean_mk_array(v___x_576_, v_dummy_579_);
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_nat_sub(v___x_576_, v___x_581_);
lean_dec(v___x_576_);
v___x_583_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_572_, v___x_580_, v___x_582_);
v___x_584_ = lean_array_get_size(v___x_583_);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_536_, v_skipTypes_537_, v_skipProofs_538_, v___x_584_, v_a_578_, v_a_570_, v___x_585_, v___x_583_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v_a_578_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v___x_586_, 1);
v___x_588_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7));
v___x_589_ = l_Lean_Expr_isConstOf(v_a_575_, v___x_588_);
if (v___x_589_ == 0)
{
v___y_557_ = v_a_587_;
v___y_558_ = v_a_575_;
v___y_559_ = v___x_589_;
goto v___jp_556_;
}
else
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_array_get_size(v_a_587_);
v___x_591_ = lean_nat_dec_eq(v___x_590_, v___x_581_);
v___y_557_ = v_a_587_;
v___y_558_ = v_a_575_;
v___y_559_ = v___x_591_;
goto v___jp_556_;
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_a_575_);
v_a_592_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_586_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_586_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v___x_576_);
lean_dec(v_a_575_);
lean_dec_ref_known(v_a_572_, 2);
v_a_600_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_577_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_577_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_572_, 2);
return v___x_574_;
}
}
case 6:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___x_614_; 
lean_dec_ref_known(v___x_571_, 1);
v___x_608_ = lean_box(v_explicitOnly_536_);
v___x_609_ = lean_box(v_skipTypes_537_);
v___x_610_ = lean_box(v_skipProofs_538_);
v___x_611_ = lean_box(v_a_570_);
v___x_612_ = lean_box(v___y_569_);
v___f_613_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed), 13, 5);
lean_closure_set(v___f_613_, 0, v___x_608_);
lean_closure_set(v___f_613_, 1, v___x_609_);
lean_closure_set(v___f_613_, 2, v___x_610_);
lean_closure_set(v___f_613_, 3, v___x_611_);
lean_closure_set(v___f_613_, 4, v___x_612_);
v___x_614_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_a_572_, v___f_613_, v_a_570_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_614_;
}
case 7:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___f_620_; lean_object* v___x_621_; 
lean_dec_ref_known(v___x_571_, 1);
v___x_615_ = lean_box(v_explicitOnly_536_);
v___x_616_ = lean_box(v_skipTypes_537_);
v___x_617_ = lean_box(v_skipProofs_538_);
v___x_618_ = lean_box(v_a_570_);
v___x_619_ = lean_box(v___y_569_);
v___f_620_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed), 13, 5);
lean_closure_set(v___f_620_, 0, v___x_615_);
lean_closure_set(v___f_620_, 1, v___x_616_);
lean_closure_set(v___f_620_, 2, v___x_617_);
lean_closure_set(v___f_620_, 3, v___x_618_);
lean_closure_set(v___f_620_, 4, v___x_619_);
v___x_621_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_a_572_, v___f_620_, v_a_570_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_621_;
}
case 11:
{
lean_object* v_typeName_622_; lean_object* v_idx_623_; lean_object* v_struct_624_; lean_object* v___x_625_; 
lean_dec_ref_known(v___x_571_, 1);
v_typeName_622_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_typeName_622_);
v_idx_623_ = lean_ctor_get(v_a_572_, 1);
lean_inc(v_idx_623_);
v_struct_624_ = lean_ctor_get(v_a_572_, 2);
lean_inc_ref(v_struct_624_);
lean_dec_ref_known(v_a_572_, 3);
v___x_625_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_536_, v_skipTypes_537_, v_skipProofs_538_, v_struct_624_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_634_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_634_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = l_Lean_mkProj(v_typeName_622_, v_idx_623_, v_a_626_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
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
lean_dec(v_idx_623_);
lean_dec(v_typeName_622_);
return v___x_625_;
}
}
default: 
{
lean_dec(v_a_572_);
return v___x_571_;
}
}
}
else
{
return v___x_571_;
}
}
v___jp_635_:
{
uint8_t v___x_636_; 
v___x_636_ = 1;
if (v_skipProofs_538_ == 0)
{
v___y_569_ = v___x_636_;
v_a_570_ = v_skipProofs_538_;
goto v___jp_568_;
}
else
{
lean_object* v___x_637_; 
lean_inc_ref(v_e_535_);
v___x_637_ = l_Lean_Meta_isProof(v_e_535_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_647_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_647_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_647_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_647_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
uint8_t v___x_642_; 
v___x_642_ = lean_unbox(v_a_638_);
if (v___x_642_ == 0)
{
uint8_t v___x_643_; 
lean_del_object(v___x_640_);
v___x_643_ = lean_unbox(v_a_638_);
lean_dec(v_a_638_);
v___y_569_ = v___x_636_;
v_a_570_ = v___x_643_;
goto v___jp_568_;
}
else
{
lean_object* v___x_645_; 
lean_dec(v_a_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v_e_535_);
v___x_645_ = v___x_640_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_e_535_);
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
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v_e_535_);
v_a_648_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_637_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_637_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed(lean_object* v_e_674_, lean_object* v_explicitOnly_675_, lean_object* v_skipTypes_676_, lean_object* v_skipProofs_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
uint8_t v_explicitOnly_boxed_684_; uint8_t v_skipTypes_boxed_685_; uint8_t v_skipProofs_boxed_686_; lean_object* v_res_687_; 
v_explicitOnly_boxed_684_ = lean_unbox(v_explicitOnly_675_);
v_skipTypes_boxed_685_ = lean_unbox(v_skipTypes_676_);
v_skipProofs_boxed_686_ = lean_unbox(v_skipProofs_677_);
v_res_687_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(v_e_674_, v_explicitOnly_boxed_684_, v_skipTypes_boxed_685_, v_skipProofs_boxed_686_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(uint8_t v_explicitOnly_688_, uint8_t v_skipTypes_689_, uint8_t v_skipProofs_690_, lean_object* v_e_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_st_ref_get(v_a_692_);
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v___x_698_, v_e_691_);
lean_dec(v___x_698_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___f_703_; lean_object* v___x_704_; 
v___x_700_ = lean_box(v_explicitOnly_688_);
v___x_701_ = lean_box(v_skipTypes_689_);
v___x_702_ = lean_box(v_skipProofs_690_);
lean_inc_ref(v_e_691_);
v___f_703_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed), 10, 4);
lean_closure_set(v___f_703_, 0, v_e_691_);
lean_closure_set(v___f_703_, 1, v___x_700_);
lean_closure_set(v___f_703_, 2, v___x_701_);
lean_closure_set(v___f_703_, 3, v___x_702_);
v___x_704_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v___f_703_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_780_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_780_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_780_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_780_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___y_711_; lean_object* v___y_717_; lean_object* v_i_718_; lean_object* v___y_724_; lean_object* v___y_734_; lean_object* v_i_735_; lean_object* v___x_750_; 
v___x_709_ = lean_st_ref_take(v_a_692_);
v___x_750_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v___x_709_, v_e_691_);
switch(lean_obj_tag(v___x_750_))
{
case 0:
{
lean_object* v_index_751_; lean_object* v_size_752_; lean_object* v___x_753_; 
v_index_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_index_751_);
lean_dec_ref_known(v___x_750_, 3);
v_size_752_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_size_752_);
lean_inc(v_a_705_);
v___x_753_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_709_, v_size_752_, v_index_751_, v_e_691_, v_a_705_);
lean_dec(v_index_751_);
v___y_711_ = v___x_753_;
goto v___jp_710_;
}
case 1:
{
lean_object* v_index_754_; lean_object* v_size_755_; lean_object* v_keyArray_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_index_754_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_index_754_);
lean_dec_ref_known(v___x_750_, 1);
v_size_755_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_size_755_);
v_keyArray_756_ = lean_ctor_get(v___x_709_, 1);
lean_inc_ref(v_keyArray_756_);
v___x_757_ = lean_unsigned_to_nat(1u);
v___x_758_ = lean_nat_add(v_size_755_, v___x_757_);
lean_dec(v_size_755_);
v___x_759_ = lean_array_get_size(v_keyArray_756_);
lean_dec_ref(v_keyArray_756_);
v___x_760_ = lean_nat_dec_lt(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v___x_758_);
lean_dec(v_index_754_);
goto v___jp_740_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_761_ = lean_unsigned_to_nat(4u);
v___x_762_ = lean_nat_mul(v___x_758_, v___x_761_);
v___x_763_ = lean_unsigned_to_nat(3u);
v___x_764_ = lean_nat_mul(v___x_759_, v___x_763_);
v___x_765_ = lean_nat_dec_le(v___x_762_, v___x_764_);
lean_dec(v___x_764_);
lean_dec(v___x_762_);
if (v___x_765_ == 0)
{
lean_dec(v___x_758_);
lean_dec(v_index_754_);
goto v___jp_740_;
}
else
{
lean_object* v___x_766_; 
lean_inc(v_a_705_);
v___x_766_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_709_, v___x_758_, v_index_754_, v_e_691_, v_a_705_);
lean_dec(v_index_754_);
v___y_711_ = v___x_766_;
goto v___jp_710_;
}
}
}
default: 
{
lean_object* v_size_767_; lean_object* v_keyArray_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v_size_767_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_size_767_);
v_keyArray_768_ = lean_ctor_get(v___x_709_, 1);
lean_inc_ref(v_keyArray_768_);
v___x_769_ = lean_unsigned_to_nat(1u);
v___x_770_ = lean_nat_add(v_size_767_, v___x_769_);
lean_dec(v_size_767_);
v___x_771_ = lean_array_get_size(v_keyArray_768_);
lean_dec_ref(v_keyArray_768_);
v___x_772_ = lean_nat_dec_lt(v___x_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
lean_dec(v___x_770_);
v___x_773_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(v___x_709_);
lean_dec(v___x_709_);
v___y_724_ = v___x_773_;
goto v___jp_723_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_774_ = lean_unsigned_to_nat(4u);
v___x_775_ = lean_nat_mul(v___x_770_, v___x_774_);
lean_dec(v___x_770_);
v___x_776_ = lean_unsigned_to_nat(3u);
v___x_777_ = lean_nat_mul(v___x_771_, v___x_776_);
v___x_778_ = lean_nat_dec_le(v___x_775_, v___x_777_);
lean_dec(v___x_777_);
lean_dec(v___x_775_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(v___x_709_);
lean_dec(v___x_709_);
v___y_724_ = v___x_779_;
goto v___jp_723_;
}
else
{
v___y_724_ = v___x_709_;
goto v___jp_723_;
}
}
}
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_st_ref_put(v_a_692_, v___y_711_);
if (v_isShared_708_ == 0)
{
v___x_714_ = v___x_707_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_705_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
v___jp_716_:
{
lean_object* v_size_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_size_719_ = lean_ctor_get(v___y_717_, 0);
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = lean_nat_add(v_size_719_, v___x_720_);
lean_inc(v_a_705_);
v___x_722_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_717_, v___x_721_, v_i_718_, v_e_691_, v_a_705_);
lean_dec(v_i_718_);
v___y_711_ = v___x_722_;
goto v___jp_710_;
}
v___jp_723_:
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v___y_724_, v_e_691_);
switch(lean_obj_tag(v___x_725_))
{
case 0:
{
lean_object* v_index_726_; lean_object* v_size_727_; lean_object* v___x_728_; 
v_index_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_index_726_);
lean_dec_ref_known(v___x_725_, 3);
v_size_727_ = lean_ctor_get(v___y_724_, 0);
lean_inc(v_size_727_);
lean_inc(v_a_705_);
v___x_728_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_724_, v_size_727_, v_index_726_, v_e_691_, v_a_705_);
lean_dec(v_index_726_);
v___y_711_ = v___x_728_;
goto v___jp_710_;
}
case 1:
{
lean_object* v_index_729_; 
v_index_729_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_index_729_);
lean_dec_ref_known(v___x_725_, 1);
v___y_717_ = v___y_724_;
v_i_718_ = v_index_729_;
goto v___jp_716_;
}
default: 
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(0u);
v___x_731_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_724_, v___x_730_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_index_732_; 
v_index_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_index_732_);
lean_dec_ref_known(v___x_731_, 1);
v___y_717_ = v___y_724_;
v_i_718_ = v_index_732_;
goto v___jp_716_;
}
else
{
lean_dec_ref(v_e_691_);
v___y_711_ = v___y_724_;
goto v___jp_710_;
}
}
}
}
v___jp_733_:
{
lean_object* v_size_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_size_736_ = lean_ctor_get(v___y_734_, 0);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v_size_736_, v___x_737_);
lean_inc(v_a_705_);
v___x_739_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_734_, v___x_738_, v_i_735_, v_e_691_, v_a_705_);
lean_dec(v_i_735_);
v___y_711_ = v___x_739_;
goto v___jp_710_;
}
v___jp_740_:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(v___x_709_);
lean_dec(v___x_709_);
v___x_742_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v___x_741_, v_e_691_);
switch(lean_obj_tag(v___x_742_))
{
case 0:
{
lean_object* v_index_743_; lean_object* v_size_744_; lean_object* v___x_745_; 
v_index_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_index_743_);
lean_dec_ref_known(v___x_742_, 3);
v_size_744_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_size_744_);
lean_inc(v_a_705_);
v___x_745_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_741_, v_size_744_, v_index_743_, v_e_691_, v_a_705_);
lean_dec(v_index_743_);
v___y_711_ = v___x_745_;
goto v___jp_710_;
}
case 1:
{
lean_object* v_index_746_; 
v_index_746_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_index_746_);
lean_dec_ref_known(v___x_742_, 1);
v___y_734_ = v___x_741_;
v_i_735_ = v_index_746_;
goto v___jp_733_;
}
default: 
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_741_, v___x_747_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_index_749_; 
v_index_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_index_749_);
lean_dec_ref_known(v___x_748_, 1);
v___y_734_ = v___x_741_;
v_i_735_ = v_index_749_;
goto v___jp_733_;
}
else
{
lean_dec_ref(v_e_691_);
v___y_711_ = v___x_741_;
goto v___jp_710_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_691_);
return v___x_704_;
}
}
else
{
lean_object* v_val_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v_e_691_);
v_val_781_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_699_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_val_781_);
lean_dec(v___x_699_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set_tag(v___x_783_, 0);
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_val_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(uint8_t v_explicitOnly_789_, uint8_t v_skipTypes_790_, uint8_t v_skipProofs_791_, uint8_t v_a_792_, uint8_t v___x_793_, lean_object* v_xs_794_, lean_object* v_b_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_789_, v_skipTypes_790_, v_skipProofs_791_, v_b_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; uint8_t v___x_804_; lean_object* v___x_805_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v___x_804_ = 1;
v___x_805_ = l_Lean_Meta_mkLambdaFVars(v_xs_794_, v_a_803_, v_a_792_, v___x_793_, v_a_792_, v___x_793_, v___x_804_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
return v___x_805_;
}
else
{
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg___boxed(lean_object* v_explicitOnly_806_, lean_object* v_skipTypes_807_, lean_object* v_skipProofs_808_, lean_object* v_upperBound_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
uint8_t v_explicitOnly_boxed_820_; uint8_t v_skipTypes_boxed_821_; uint8_t v_skipProofs_boxed_822_; uint8_t v_a_18408__boxed_823_; lean_object* v_res_824_; 
v_explicitOnly_boxed_820_ = lean_unbox(v_explicitOnly_806_);
v_skipTypes_boxed_821_ = lean_unbox(v_skipTypes_807_);
v_skipProofs_boxed_822_ = lean_unbox(v_skipProofs_808_);
v_a_18408__boxed_823_ = lean_unbox(v_a_811_);
v_res_824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_boxed_820_, v_skipTypes_boxed_821_, v_skipProofs_boxed_822_, v_upperBound_809_, v_a_810_, v_a_18408__boxed_823_, v_a_812_, v_b_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v_a_810_);
lean_dec(v_upperBound_809_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___boxed(lean_object* v_explicitOnly_825_, lean_object* v_skipTypes_826_, lean_object* v_skipProofs_827_, lean_object* v_e_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
uint8_t v_explicitOnly_boxed_835_; uint8_t v_skipTypes_boxed_836_; uint8_t v_skipProofs_boxed_837_; lean_object* v_res_838_; 
v_explicitOnly_boxed_835_ = lean_unbox(v_explicitOnly_825_);
v_skipTypes_boxed_836_ = lean_unbox(v_skipTypes_826_);
v_skipProofs_boxed_837_ = lean_unbox(v_skipProofs_827_);
v_res_838_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_boxed_835_, v_skipTypes_boxed_836_, v_skipProofs_boxed_837_, v_e_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(lean_object* v_00_u03b2_839_, lean_object* v_m_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v_m_840_, v_a_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___boxed(lean_object* v_00_u03b2_843_, lean_object* v_m_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(v_00_u03b2_843_, v_m_844_, v_a_845_);
lean_dec_ref(v_a_845_);
lean_dec_ref(v_m_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(uint8_t v_explicitOnly_847_, uint8_t v_skipTypes_848_, uint8_t v_skipProofs_849_, lean_object* v_upperBound_850_, lean_object* v_a_851_, uint8_t v_a_852_, lean_object* v_inst_853_, lean_object* v_R_854_, lean_object* v_a_855_, lean_object* v_b_856_, lean_object* v_c_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_847_, v_skipTypes_848_, v_skipProofs_849_, v_upperBound_850_, v_a_851_, v_a_852_, v_a_855_, v_b_856_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___boxed(lean_object** _args){
lean_object* v_explicitOnly_865_ = _args[0];
lean_object* v_skipTypes_866_ = _args[1];
lean_object* v_skipProofs_867_ = _args[2];
lean_object* v_upperBound_868_ = _args[3];
lean_object* v_a_869_ = _args[4];
lean_object* v_a_870_ = _args[5];
lean_object* v_inst_871_ = _args[6];
lean_object* v_R_872_ = _args[7];
lean_object* v_a_873_ = _args[8];
lean_object* v_b_874_ = _args[9];
lean_object* v_c_875_ = _args[10];
lean_object* v___y_876_ = _args[11];
lean_object* v___y_877_ = _args[12];
lean_object* v___y_878_ = _args[13];
lean_object* v___y_879_ = _args[14];
lean_object* v___y_880_ = _args[15];
lean_object* v___y_881_ = _args[16];
_start:
{
uint8_t v_explicitOnly_boxed_882_; uint8_t v_skipTypes_boxed_883_; uint8_t v_skipProofs_boxed_884_; uint8_t v_a_19038__boxed_885_; lean_object* v_res_886_; 
v_explicitOnly_boxed_882_ = lean_unbox(v_explicitOnly_865_);
v_skipTypes_boxed_883_ = lean_unbox(v_skipTypes_866_);
v_skipProofs_boxed_884_ = lean_unbox(v_skipProofs_867_);
v_a_19038__boxed_885_ = lean_unbox(v_a_870_);
v_res_886_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(v_explicitOnly_boxed_882_, v_skipTypes_boxed_883_, v_skipProofs_boxed_884_, v_upperBound_868_, v_a_869_, v_a_19038__boxed_885_, v_inst_871_, v_R_872_, v_a_873_, v_b_874_, v_c_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v_a_869_);
lean_dec(v_upperBound_868_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(lean_object* v_00_u03b1_887_, lean_object* v_ref_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_888_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___boxed(lean_object* v_00_u03b1_893_, lean_object* v_ref_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(v_00_u03b1_893_, v_ref_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7(lean_object* v_00_u03b1_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___boxed(lean_object* v_00_u03b1_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7(v_00_u03b1_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(lean_object* v_00_u03b1_909_, lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___boxed(lean_object* v_00_u03b1_918_, lean_object* v_x_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(v_00_u03b1_918_, v_x_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6(lean_object* v_00_u03b2_927_, lean_object* v_m_928_, lean_object* v_query_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v_m_928_, v_query_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___boxed(lean_object* v_00_u03b2_931_, lean_object* v_m_932_, lean_object* v_query_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6(v_00_u03b2_931_, v_m_932_, v_query_933_);
lean_dec_ref(v_query_933_);
lean_dec_ref(v_m_932_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7(lean_object* v_00_u03b2_935_, lean_object* v_m_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___redArg(v_m_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7___boxed(lean_object* v_00_u03b2_938_, lean_object* v_m_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7(v_00_u03b2_938_, v_m_939_);
lean_dec_ref(v_m_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(lean_object* v_00_u03b2_941_, lean_object* v_m_942_, lean_object* v_query_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_m_942_, v_query_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_945_, lean_object* v_m_946_, lean_object* v_query_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(v_00_u03b2_945_, v_m_946_, v_query_947_);
lean_dec_ref(v_query_947_);
lean_dec_ref(v_m_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(lean_object* v_00_u03b2_949_, lean_object* v_m_950_, lean_object* v_query_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_m_950_, v_query_951_, v_x_952_, v_x_953_, v_x_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___boxed(lean_object* v_00_u03b2_957_, lean_object* v_m_958_, lean_object* v_query_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(v_00_u03b2_957_, v_m_958_, v_query_959_, v_x_960_, v_x_961_, v_x_962_, v_x_963_);
lean_dec_ref(v_query_959_);
lean_dec_ref(v_m_958_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11(lean_object* v_00_u03b2_965_, lean_object* v_init_966_, lean_object* v_b_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11___redArg(v_init_966_, v_b_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11___boxed(lean_object* v_00_u03b2_969_, lean_object* v_init_970_, lean_object* v_b_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11(v_00_u03b2_969_, v_init_970_, v_b_971_);
lean_dec_ref(v_b_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12(lean_object* v_00_u03b2_973_, lean_object* v_b_974_, lean_object* v_acc_975_, lean_object* v_i_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12___redArg(v_b_974_, v_acc_975_, v_i_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12___boxed(lean_object* v_00_u03b2_978_, lean_object* v_b_979_, lean_object* v_acc_980_, lean_object* v_i_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__7_spec__11_spec__12(v_00_u03b2_978_, v_b_979_, v_acc_980_, v_i_981_);
lean_dec_ref(v_b_979_);
return v_res_982_;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__0(void){
_start:
{
lean_object* v_cellCount_983_; lean_object* v___x_984_; 
v_cellCount_983_ = lean_unsigned_to_nat(16u);
v___x_984_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__1(void){
_start:
{
lean_object* v_cellCount_985_; lean_object* v___x_986_; 
v_cellCount_985_ = lean_unsigned_to_nat(16u);
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_985_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__2(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_987_ = lean_obj_once(&l_Lean_Meta_reduce___closed__1, &l_Lean_Meta_reduce___closed__1_once, _init_l_Lean_Meta_reduce___closed__1);
v___x_988_ = lean_obj_once(&l_Lean_Meta_reduce___closed__0, &l_Lean_Meta_reduce___closed__0_once, _init_l_Lean_Meta_reduce___closed__0);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_988_);
lean_ctor_set(v___x_990_, 2, v___x_987_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce(lean_object* v_e_991_, uint8_t v_explicitOnly_992_, uint8_t v_skipTypes_993_, uint8_t v_skipProofs_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_obj_once(&l_Lean_Meta_reduce___closed__2, &l_Lean_Meta_reduce___closed__2_once, _init_l_Lean_Meta_reduce___closed__2);
v___x_1001_ = lean_st_mk_ref(v___x_1000_);
v___x_1002_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_992_, v_skipTypes_993_, v_skipProofs_994_, v_e_991_, v___x_1001_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1011_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1007_ = lean_st_ref_get(v___x_1001_);
lean_dec(v___x_1001_);
lean_dec(v___x_1007_);
if (v_isShared_1006_ == 0)
{
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1003_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_dec(v___x_1001_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object* v_e_1012_, lean_object* v_explicitOnly_1013_, lean_object* v_skipTypes_1014_, lean_object* v_skipProofs_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
uint8_t v_explicitOnly_boxed_1021_; uint8_t v_skipTypes_boxed_1022_; uint8_t v_skipProofs_boxed_1023_; lean_object* v_res_1024_; 
v_explicitOnly_boxed_1021_ = lean_unbox(v_explicitOnly_1013_);
v_skipTypes_boxed_1022_ = lean_unbox(v_skipTypes_1014_);
v_skipProofs_boxed_1023_ = lean_unbox(v_skipProofs_1015_);
v_res_1024_ = l_Lean_Meta_reduce(v_e_1012_, v_explicitOnly_boxed_1021_, v_skipTypes_boxed_1022_, v_skipProofs_boxed_1023_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll(lean_object* v_e_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
uint8_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = 0;
v___x_1032_ = l_Lean_Meta_reduce(v_e_1025_, v___x_1031_, v___x_1031_, v___x_1031_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll___boxed(lean_object* v_e_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Meta_reduceAll(v_e_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
return v_res_1039_;
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
