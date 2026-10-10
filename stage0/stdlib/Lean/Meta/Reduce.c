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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(lean_object* v_k_4_, lean_object* v___y_5_, lean_object* v_b_6_, lean_object* v_c_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
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
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4_ = stack[0].m_obj;
lean_object* v___y_5_ = stack[1].m_obj;
lean_object* v_b_6_ = stack[2].m_obj;
lean_object* v_c_7_ = stack[3].m_obj;
lean_object* v___y_8_ = stack[4].m_obj;
lean_object* v___y_9_ = stack[5].m_obj;
lean_object* v___y_10_ = stack[6].m_obj;
lean_object* v___y_11_ = stack[7].m_obj;
lean_object* v_res_14_;
v_res_14_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(v_k_4_, v___y_5_, v_b_6_, v_c_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0___boxed(lean_object* v_k_15_, lean_object* v___y_16_, lean_object* v_b_17_, lean_object* v_c_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(v_k_15_, v___y_16_, v_b_17_, v_c_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_16_);
return v_res_24_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(lean_object* v_e_25_, lean_object* v_k_26_, uint8_t v_cleanupAnnotations_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___f_34_; uint8_t v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
lean_inc(v___y_28_);
v___f_34_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_34_, 0, v_k_26_);
lean_closure_set(v___f_34_, 1, v___y_28_);
v___x_35_ = 1;
v___x_36_ = 0;
v___x_37_ = lean_box(0);
v___x_38_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_25_, v___x_35_, v___x_36_, v___x_35_, v___x_36_, v___x_37_, v___f_34_, v_cleanupAnnotations_27_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_38_) == 0)
{
return v___x_38_;
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_38_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_38_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
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
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_25_ = stack[0].m_obj;
lean_object* v_k_26_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_27_ = stack[2].m_num;
lean_object* v___y_28_ = stack[3].m_obj;
lean_object* v___y_29_ = stack[4].m_obj;
lean_object* v___y_30_ = stack[5].m_obj;
lean_object* v___y_31_ = stack[6].m_obj;
lean_object* v___y_32_ = stack[7].m_obj;
lean_object* v_res_47_;
v_res_47_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_e_25_, v_k_26_, v_cleanupAnnotations_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___boxed(lean_object* v_e_48_, lean_object* v_k_49_, lean_object* v_cleanupAnnotations_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_57_; lean_object* v_res_58_; 
v_cleanupAnnotations_boxed_57_ = lean_unbox(v_cleanupAnnotations_50_);
v_res_58_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_e_48_, v_k_49_, v_cleanupAnnotations_boxed_57_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
return v_res_58_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3(lean_object* v_00_u03b1_59_, lean_object* v_e_60_, lean_object* v_k_61_, uint8_t v_cleanupAnnotations_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_e_60_, v_k_61_, v_cleanupAnnotations_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
return v___x_69_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_60_ = stack[1].m_obj;
lean_object* v_k_61_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_62_ = stack[3].m_num;
lean_object* v___y_63_ = stack[4].m_obj;
lean_object* v___y_64_ = stack[5].m_obj;
lean_object* v___y_65_ = stack[6].m_obj;
lean_object* v___y_66_ = stack[7].m_obj;
lean_object* v___y_67_ = stack[8].m_obj;
lean_object* v_res_70_;
v_res_70_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3(lean_box(0), v_e_60_, v_k_61_, v_cleanupAnnotations_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___boxed(lean_object* v_00_u03b1_71_, lean_object* v_e_72_, lean_object* v_k_73_, lean_object* v_cleanupAnnotations_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_81_; lean_object* v_res_82_; 
v_cleanupAnnotations_boxed_81_ = lean_unbox(v_cleanupAnnotations_74_);
v_res_82_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3(v_00_u03b1_71_, v_e_72_, v_k_73_, v_cleanupAnnotations_boxed_81_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
return v_res_82_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(lean_object* v_type_83_, lean_object* v_k_84_, uint8_t v_cleanupAnnotations_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___f_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
lean_inc(v___y_86_);
v___f_92_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_92_, 0, v_k_84_);
lean_closure_set(v___f_92_, 1, v___y_86_);
v___x_93_ = 0;
v___x_94_ = lean_box(0);
v___x_95_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_93_, v___x_94_, v_type_83_, v___f_92_, v_cleanupAnnotations_85_, v___x_93_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_95_) == 0)
{
return v___x_95_;
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_83_ = stack[0].m_obj;
lean_object* v_k_84_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_85_ = stack[2].m_num;
lean_object* v___y_86_ = stack[3].m_obj;
lean_object* v___y_87_ = stack[4].m_obj;
lean_object* v___y_88_ = stack[5].m_obj;
lean_object* v___y_89_ = stack[6].m_obj;
lean_object* v___y_90_ = stack[7].m_obj;
lean_object* v_res_104_;
v_res_104_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_type_83_, v_k_84_, v_cleanupAnnotations_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg___boxed(lean_object* v_type_105_, lean_object* v_k_106_, lean_object* v_cleanupAnnotations_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_114_; lean_object* v_res_115_; 
v_cleanupAnnotations_boxed_114_ = lean_unbox(v_cleanupAnnotations_107_);
v_res_115_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_type_105_, v_k_106_, v_cleanupAnnotations_boxed_114_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
return v_res_115_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4(lean_object* v_00_u03b1_116_, lean_object* v_type_117_, lean_object* v_k_118_, uint8_t v_cleanupAnnotations_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_type_117_, v_k_118_, v_cleanupAnnotations_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
return v___x_126_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_117_ = stack[1].m_obj;
lean_object* v_k_118_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_119_ = stack[3].m_num;
lean_object* v___y_120_ = stack[4].m_obj;
lean_object* v___y_121_ = stack[5].m_obj;
lean_object* v___y_122_ = stack[6].m_obj;
lean_object* v___y_123_ = stack[7].m_obj;
lean_object* v___y_124_ = stack[8].m_obj;
lean_object* v_res_127_;
v_res_127_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4(lean_box(0), v_type_117_, v_k_118_, v_cleanupAnnotations_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___boxed(lean_object* v_00_u03b1_128_, lean_object* v_type_129_, lean_object* v_k_130_, lean_object* v_cleanupAnnotations_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_138_; lean_object* v_res_139_; 
v_cleanupAnnotations_boxed_138_ = lean_unbox(v_cleanupAnnotations_131_);
v_res_139_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4(v_00_u03b1_128_, v_type_129_, v_k_130_, v_cleanupAnnotations_boxed_138_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(lean_object* v_a_140_, lean_object* v_x_141_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_box(0);
return v___x_142_;
}
else
{
lean_object* v_key_143_; lean_object* v_value_144_; lean_object* v_tail_145_; uint8_t v___x_146_; 
v_key_143_ = lean_ctor_get(v_x_141_, 0);
v_value_144_ = lean_ctor_get(v_x_141_, 1);
v_tail_145_ = lean_ctor_get(v_x_141_, 2);
v___x_146_ = lean_expr_eqv(v_key_143_, v_a_140_);
if (v___x_146_ == 0)
{
v_x_141_ = v_tail_145_;
goto _start;
}
else
{
lean_object* v___x_148_; 
lean_inc(v_value_144_);
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v_value_144_);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_a_149_, v_x_150_);
lean_dec(v_x_150_);
lean_dec_ref(v_a_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(lean_object* v_m_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_buckets_154_; lean_object* v___x_155_; uint64_t v___x_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v_fold_159_; uint64_t v___x_160_; uint64_t v___x_161_; uint64_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_buckets_154_ = lean_ctor_get(v_m_152_, 1);
v___x_155_ = lean_array_get_size(v_buckets_154_);
v___x_156_ = l_Lean_Expr_hash(v_a_153_);
v___x_157_ = 32ULL;
v___x_158_ = lean_uint64_shift_right(v___x_156_, v___x_157_);
v_fold_159_ = lean_uint64_xor(v___x_156_, v___x_158_);
v___x_160_ = 16ULL;
v___x_161_ = lean_uint64_shift_right(v_fold_159_, v___x_160_);
v___x_162_ = lean_uint64_xor(v_fold_159_, v___x_161_);
v___x_163_ = lean_uint64_to_usize(v___x_162_);
v___x_164_ = lean_usize_of_nat(v___x_155_);
v___x_165_ = ((size_t)1ULL);
v___x_166_ = lean_usize_sub(v___x_164_, v___x_165_);
v___x_167_ = lean_usize_land(v___x_163_, v___x_166_);
v___x_168_ = lean_array_uget_borrowed(v_buckets_154_, v___x_167_);
v___x_169_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_a_153_, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg___boxed(lean_object* v_m_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v_m_170_, v_a_171_);
lean_dec_ref(v_a_171_);
lean_dec_ref(v_m_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(lean_object* v_a_173_, lean_object* v_b_174_, lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_dec(v_b_174_);
lean_dec_ref(v_a_173_);
return v_x_175_;
}
else
{
lean_object* v_key_176_; lean_object* v_value_177_; lean_object* v_tail_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_190_; 
v_key_176_ = lean_ctor_get(v_x_175_, 0);
v_value_177_ = lean_ctor_get(v_x_175_, 1);
v_tail_178_ = lean_ctor_get(v_x_175_, 2);
v_isSharedCheck_190_ = !lean_is_exclusive(v_x_175_);
if (v_isSharedCheck_190_ == 0)
{
v___x_180_ = v_x_175_;
v_isShared_181_ = v_isSharedCheck_190_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_tail_178_);
lean_inc(v_value_177_);
lean_inc(v_key_176_);
lean_dec(v_x_175_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_190_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
uint8_t v___x_182_; 
v___x_182_ = lean_expr_eqv(v_key_176_, v_a_173_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(v_a_173_, v_b_174_, v_tail_178_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 2, v___x_183_);
v___x_185_ = v___x_180_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_key_176_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_value_177_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
else
{
lean_object* v___x_188_; 
lean_dec(v_value_177_);
lean_dec(v_key_176_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v_b_174_);
lean_ctor_set(v___x_180_, 0, v_a_173_);
v___x_188_ = v___x_180_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_173_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_b_174_);
lean_ctor_set(v_reuseFailAlloc_189_, 2, v_tail_178_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(lean_object* v_a_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
uint8_t v___x_193_; 
v___x_193_ = 0;
return v___x_193_;
}
else
{
lean_object* v_key_194_; lean_object* v_tail_195_; uint8_t v___x_196_; 
v_key_194_ = lean_ctor_get(v_x_192_, 0);
v_tail_195_ = lean_ctor_get(v_x_192_, 2);
v___x_196_ = lean_expr_eqv(v_key_194_, v_a_191_);
if (v___x_196_ == 0)
{
v_x_192_ = v_tail_195_;
goto _start;
}
else
{
return v___x_196_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_191_ = stack[0].m_obj;
lean_object* v_x_192_ = stack[1].m_obj;
uint8_t v_res_198_;
v_res_198_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_a_191_, v_x_192_);
stack->m_num = v_res_198_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg___boxed(lean_object* v_a_199_, lean_object* v_x_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_a_199_, v_x_200_);
lean_dec(v_x_200_);
lean_dec_ref(v_a_199_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
return v_x_203_;
}
else
{
lean_object* v_key_205_; lean_object* v_value_206_; lean_object* v_tail_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_230_; 
v_key_205_ = lean_ctor_get(v_x_204_, 0);
v_value_206_ = lean_ctor_get(v_x_204_, 1);
v_tail_207_ = lean_ctor_get(v_x_204_, 2);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_204_);
if (v_isSharedCheck_230_ == 0)
{
v___x_209_ = v_x_204_;
v_isShared_210_ = v_isSharedCheck_230_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_tail_207_);
lean_inc(v_value_206_);
lean_inc(v_key_205_);
lean_dec(v_x_204_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_230_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; uint64_t v_fold_215_; uint64_t v___x_216_; uint64_t v___x_217_; uint64_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_211_ = lean_array_get_size(v_x_203_);
v___x_212_ = l_Lean_Expr_hash(v_key_205_);
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
v___x_224_ = lean_array_uget_borrowed(v_x_203_, v___x_223_);
lean_inc(v___x_224_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 2, v___x_224_);
v___x_226_ = v___x_209_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_key_205_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_value_206_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v___x_224_);
v___x_226_ = v_reuseFailAlloc_229_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; 
v___x_227_ = lean_array_uset(v_x_203_, v___x_223_, v___x_226_);
v_x_203_ = v___x_227_;
v_x_204_ = v_tail_207_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11___redArg(lean_object* v_i_231_, lean_object* v_source_232_, lean_object* v_target_233_){
_start:
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = lean_array_get_size(v_source_232_);
v___x_235_ = lean_nat_dec_lt(v_i_231_, v___x_234_);
if (v___x_235_ == 0)
{
lean_dec_ref(v_source_232_);
lean_dec(v_i_231_);
return v_target_233_;
}
else
{
lean_object* v_es_236_; lean_object* v___x_237_; lean_object* v_source_238_; lean_object* v_target_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_es_236_ = lean_array_fget(v_source_232_, v_i_231_);
v___x_237_ = lean_box(0);
v_source_238_ = lean_array_fset(v_source_232_, v_i_231_, v___x_237_);
v_target_239_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12___redArg(v_target_233_, v_es_236_);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_i_231_, v___x_240_);
lean_dec(v_i_231_);
v_i_231_ = v___x_241_;
v_source_232_ = v_source_238_;
v_target_233_ = v_target_239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(lean_object* v_data_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_nbuckets_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_244_ = lean_array_get_size(v_data_243_);
v___x_245_ = lean_unsigned_to_nat(2u);
v_nbuckets_246_ = lean_nat_mul(v___x_244_, v___x_245_);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_box(0);
v___x_249_ = lean_mk_array(v_nbuckets_246_, v___x_248_);
v___x_250_ = lean_array_propagate_mark(v_data_243_, v___x_249_);
v___x_251_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11___redArg(v___x_247_, v_data_243_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(lean_object* v_m_252_, lean_object* v_a_253_, lean_object* v_b_254_){
_start:
{
lean_object* v_size_255_; lean_object* v_buckets_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_299_; 
v_size_255_ = lean_ctor_get(v_m_252_, 0);
v_buckets_256_ = lean_ctor_get(v_m_252_, 1);
v_isSharedCheck_299_ = !lean_is_exclusive(v_m_252_);
if (v_isSharedCheck_299_ == 0)
{
v___x_258_ = v_m_252_;
v_isShared_259_ = v_isSharedCheck_299_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_buckets_256_);
lean_inc(v_size_255_);
lean_dec(v_m_252_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_299_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; uint64_t v___x_261_; uint64_t v___x_262_; uint64_t v___x_263_; uint64_t v_fold_264_; uint64_t v___x_265_; uint64_t v___x_266_; uint64_t v___x_267_; size_t v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v_bkt_273_; uint8_t v___x_274_; 
v___x_260_ = lean_array_get_size(v_buckets_256_);
v___x_261_ = l_Lean_Expr_hash(v_a_253_);
v___x_262_ = 32ULL;
v___x_263_ = lean_uint64_shift_right(v___x_261_, v___x_262_);
v_fold_264_ = lean_uint64_xor(v___x_261_, v___x_263_);
v___x_265_ = 16ULL;
v___x_266_ = lean_uint64_shift_right(v_fold_264_, v___x_265_);
v___x_267_ = lean_uint64_xor(v_fold_264_, v___x_266_);
v___x_268_ = lean_uint64_to_usize(v___x_267_);
v___x_269_ = lean_usize_of_nat(v___x_260_);
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_sub(v___x_269_, v___x_270_);
v___x_272_ = lean_usize_land(v___x_268_, v___x_271_);
v_bkt_273_ = lean_array_uget_borrowed(v_buckets_256_, v___x_272_);
v___x_274_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_a_253_, v_bkt_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v_size_x27_276_; lean_object* v___x_277_; lean_object* v_buckets_x27_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_275_ = lean_unsigned_to_nat(1u);
v_size_x27_276_ = lean_nat_add(v_size_255_, v___x_275_);
lean_dec(v_size_255_);
lean_inc(v_bkt_273_);
v___x_277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_277_, 0, v_a_253_);
lean_ctor_set(v___x_277_, 1, v_b_254_);
lean_ctor_set(v___x_277_, 2, v_bkt_273_);
v_buckets_x27_278_ = lean_array_uset(v_buckets_256_, v___x_272_, v___x_277_);
v___x_279_ = lean_unsigned_to_nat(4u);
v___x_280_ = lean_nat_mul(v_size_x27_276_, v___x_279_);
v___x_281_ = lean_unsigned_to_nat(3u);
v___x_282_ = lean_nat_div(v___x_280_, v___x_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_array_get_size(v_buckets_x27_278_);
v___x_284_ = lean_nat_dec_le(v___x_282_, v___x_283_);
lean_dec(v___x_282_);
if (v___x_284_ == 0)
{
lean_object* v_val_285_; lean_object* v___x_287_; 
v_val_285_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(v_buckets_x27_278_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v_val_285_);
lean_ctor_set(v___x_258_, 0, v_size_x27_276_);
v___x_287_ = v___x_258_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_size_x27_276_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_val_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
else
{
lean_object* v___x_290_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v_buckets_x27_278_);
lean_ctor_set(v___x_258_, 0, v_size_x27_276_);
v___x_290_ = v___x_258_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_size_x27_276_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_buckets_x27_278_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v___x_292_; lean_object* v_buckets_x27_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
lean_inc(v_bkt_273_);
v___x_292_ = lean_box(0);
v_buckets_x27_293_ = lean_array_uset(v_buckets_256_, v___x_272_, v___x_292_);
v___x_294_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(v_a_253_, v_b_254_, v_bkt_273_);
v___x_295_ = lean_array_uset(v_buckets_x27_293_, v___x_272_, v___x_294_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___x_295_);
v___x_297_ = v___x_258_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_size_255_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = l_Lean_maxRecDepthErrorMessage;
v___x_306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3);
v___x_308_ = l_Lean_MessageData_ofFormat(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4);
v___x_310_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2));
v___x_311_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_309_);
return v___x_311_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(lean_object* v_ref_312_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v_ref_312_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_312_ = stack[0].m_obj;
lean_object* v_res_317_;
v_res_317_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_312_);
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___boxed(lean_object* v_ref_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_318_);
return v_res_320_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_box(0);
v___x_322_ = l_Lean_interruptExceptionId;
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
return v___x_323_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg(){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___closed__0);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_327_;
v_res_327_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg___boxed(lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
return v_res_329_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(lean_object* v_x_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___y_338_; uint8_t v___y_348_; uint16_t v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; uint8_t v___y_353_; lean_object* v_toCold_358_; lean_object* v_currRecDepth_359_; lean_object* v_ref_360_; uint16_t v_optionFlags_361_; uint8_t v_suppressElabErrors_362_; uint8_t v_isRecordingDeps_363_; lean_object* v_maxRecDepth_364_; lean_object* v_cancelTk_x3f_365_; 
v_toCold_358_ = lean_ctor_get(v___y_334_, 0);
v_currRecDepth_359_ = lean_ctor_get(v___y_334_, 1);
v_ref_360_ = lean_ctor_get(v___y_334_, 2);
v_optionFlags_361_ = lean_ctor_get_uint16(v___y_334_, sizeof(void*)*3);
v_suppressElabErrors_362_ = lean_ctor_get_uint8(v___y_334_, sizeof(void*)*3 + 2);
v_isRecordingDeps_363_ = lean_ctor_get_uint8(v___y_334_, sizeof(void*)*3 + 3);
v_maxRecDepth_364_ = lean_ctor_get(v_toCold_358_, 3);
v_cancelTk_x3f_365_ = lean_ctor_get(v_toCold_358_, 10);
if (lean_obj_tag(v_cancelTk_x3f_365_) == 1)
{
lean_object* v_val_371_; uint8_t v___x_372_; 
v_val_371_ = lean_ctor_get(v_cancelTk_x3f_365_, 0);
v___x_372_ = l_IO_CancelToken_isSet(v_val_371_);
if (v___x_372_ == 0)
{
goto v___jp_366_;
}
else
{
lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v_x_330_);
v___x_373_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
goto v___jp_366_;
}
v___jp_337_:
{
if (lean_obj_tag(v___y_338_) == 0)
{
return v___y_338_;
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
v_a_339_ = lean_ctor_get(v___y_338_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___y_338_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___y_338_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___y_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
v___jp_347_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_add(v___y_352_, v___x_354_);
lean_inc_ref(v___y_350_);
v___x_356_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_356_, 0, v___y_350_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
lean_ctor_set(v___x_356_, 2, v___y_351_);
lean_ctor_set_uint16(v___x_356_, sizeof(void*)*3, v___y_349_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*3 + 2, v___y_348_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*3 + 3, v___y_353_);
lean_inc(v___y_335_);
lean_inc(v___y_333_);
lean_inc_ref(v___y_332_);
lean_inc(v___y_331_);
v___x_357_ = lean_apply_6(v_x_330_, v___y_331_, v___y_332_, v___y_333_, v___x_356_, v___y_335_, lean_box(0));
v___y_338_ = v___x_357_;
goto v___jp_337_;
}
v___jp_366_:
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_nat_dec_eq(v_maxRecDepth_364_, v___x_367_);
if (v___x_368_ == 0)
{
uint8_t v___x_369_; 
v___x_369_ = lean_nat_dec_eq(v_currRecDepth_359_, v_maxRecDepth_364_);
if (v___x_369_ == 0)
{
lean_inc(v_ref_360_);
v___y_348_ = v_suppressElabErrors_362_;
v___y_349_ = v_optionFlags_361_;
v___y_350_ = v_toCold_358_;
v___y_351_ = v_ref_360_;
v___y_352_ = v_currRecDepth_359_;
v___y_353_ = v_isRecordingDeps_363_;
goto v___jp_347_;
}
else
{
lean_object* v___x_370_; 
lean_dec_ref(v_x_330_);
lean_inc(v_ref_360_);
v___x_370_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_360_);
v___y_338_ = v___x_370_;
goto v___jp_337_;
}
}
else
{
lean_inc(v_ref_360_);
v___y_348_ = v_suppressElabErrors_362_;
v___y_349_ = v_optionFlags_361_;
v___y_350_ = v_toCold_358_;
v___y_351_ = v_ref_360_;
v___y_352_ = v_currRecDepth_359_;
v___y_353_ = v_isRecordingDeps_363_;
goto v___jp_347_;
}
}
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_330_ = stack[0].m_obj;
lean_object* v___y_331_ = stack[1].m_obj;
lean_object* v___y_332_ = stack[2].m_obj;
lean_object* v___y_333_ = stack[3].m_obj;
lean_object* v___y_334_ = stack[4].m_obj;
lean_object* v___y_335_ = stack[5].m_obj;
lean_object* v_res_382_;
v_res_382_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg___boxed(lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
return v_res_390_;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_394_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2));
v___x_395_ = lean_unsigned_to_nat(14u);
v___x_396_ = lean_unsigned_to_nat(22u);
v___x_397_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1));
v___x_398_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0));
v___x_399_ = l_mkPanicMessageWithDecl(v___x_398_, v___x_397_, v___x_396_, v___x_395_, v___x_394_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed(lean_object* v_explicitOnly_400_, lean_object* v_skipTypes_401_, lean_object* v_skipProofs_402_, lean_object* v_a_403_, lean_object* v___x_404_, lean_object* v_xs_405_, lean_object* v_b_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
uint8_t v_explicitOnly_boxed_413_; uint8_t v_skipTypes_boxed_414_; uint8_t v_skipProofs_boxed_415_; uint8_t v_a_15173__boxed_416_; uint8_t v___x_15174__boxed_417_; lean_object* v_res_418_; 
v_explicitOnly_boxed_413_ = lean_unbox(v_explicitOnly_400_);
v_skipTypes_boxed_414_ = lean_unbox(v_skipTypes_401_);
v_skipProofs_boxed_415_ = lean_unbox(v_skipProofs_402_);
v_a_15173__boxed_416_ = lean_unbox(v_a_403_);
v___x_15174__boxed_417_ = lean_unbox(v___x_404_);
v_res_418_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(v_explicitOnly_boxed_413_, v_skipTypes_boxed_414_, v_skipProofs_boxed_415_, v_a_15173__boxed_416_, v___x_15174__boxed_417_, v_xs_405_, v_b_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v_xs_405_);
return v_res_418_;
}
}
lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(uint8_t v_explicitOnly_419_, uint8_t v_skipTypes_420_, uint8_t v_skipProofs_421_, uint8_t v_a_422_, uint8_t v___x_423_, lean_object* v_xs_424_, lean_object* v_b_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_419_, v_skipTypes_420_, v_skipProofs_421_, v_b_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; uint8_t v___x_434_; lean_object* v___x_435_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_432_, 1);
v___x_434_ = 1;
v___x_435_ = l_Lean_Meta_mkForallFVars(v_xs_424_, v_a_433_, v_a_422_, v___x_423_, v___x_423_, v___x_434_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_435_;
}
else
{
return v___x_432_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_explicitOnly_419_ = stack[0].m_num;
uint8_t v_skipTypes_420_ = stack[1].m_num;
uint8_t v_skipProofs_421_ = stack[2].m_num;
uint8_t v_a_422_ = stack[3].m_num;
uint8_t v___x_423_ = stack[4].m_num;
lean_object* v_xs_424_ = stack[5].m_obj;
lean_object* v_b_425_ = stack[6].m_obj;
lean_object* v___y_426_ = stack[7].m_obj;
lean_object* v___y_427_ = stack[8].m_obj;
lean_object* v___y_428_ = stack[9].m_obj;
lean_object* v___y_429_ = stack[10].m_obj;
lean_object* v___y_430_ = stack[11].m_obj;
lean_object* v_res_436_;
v_res_436_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(v_explicitOnly_419_, v_skipTypes_420_, v_skipProofs_421_, v_a_422_, v___x_423_, v_xs_424_, v_b_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed(lean_object* v_explicitOnly_437_, lean_object* v_skipTypes_438_, lean_object* v_skipProofs_439_, lean_object* v_a_440_, lean_object* v___x_441_, lean_object* v_xs_442_, lean_object* v_b_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
uint8_t v_explicitOnly_boxed_450_; uint8_t v_skipTypes_boxed_451_; uint8_t v_skipProofs_boxed_452_; uint8_t v_a_15186__boxed_453_; uint8_t v___x_15187__boxed_454_; lean_object* v_res_455_; 
v_explicitOnly_boxed_450_ = lean_unbox(v_explicitOnly_437_);
v_skipTypes_boxed_451_ = lean_unbox(v_skipTypes_438_);
v_skipProofs_boxed_452_ = lean_unbox(v_skipProofs_439_);
v_a_15186__boxed_453_ = lean_unbox(v_a_440_);
v___x_15187__boxed_454_ = lean_unbox(v___x_441_);
v_res_455_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(v_explicitOnly_boxed_450_, v_skipTypes_boxed_451_, v_skipProofs_boxed_452_, v_a_15186__boxed_453_, v___x_15187__boxed_454_, v_xs_442_, v_b_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v_xs_442_);
return v_res_455_;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4(void){
_start:
{
lean_object* v___x_456_; lean_object* v_dummy_457_; 
v___x_456_ = lean_box(0);
v_dummy_457_ = l_Lean_Expr_sort___override(v___x_456_);
return v_dummy_457_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(uint8_t v_explicitOnly_458_, uint8_t v_skipTypes_459_, uint8_t v_skipProofs_460_, lean_object* v_upperBound_461_, lean_object* v_a_462_, uint8_t v_a_463_, lean_object* v_a_464_, lean_object* v_b_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_a_473_; uint8_t v___x_494_; 
v___x_494_ = lean_nat_dec_lt(v_a_464_, v_upperBound_461_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
lean_dec(v_a_464_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v_b_465_);
return v___x_495_;
}
else
{
lean_object* v_paramInfo_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_paramInfo_496_ = lean_ctor_get(v_a_462_, 0);
v___x_497_ = lean_array_get_size(v_paramInfo_496_);
v___x_498_ = lean_nat_dec_lt(v_a_464_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_array_get_size(v_b_465_);
v___x_500_ = lean_nat_dec_lt(v_a_464_, v___x_499_);
if (v___x_500_ == 0)
{
v_a_473_ = v_b_465_;
goto v___jp_472_;
}
else
{
lean_object* v_v_501_; lean_object* v___x_502_; lean_object* v_xs_x27_503_; lean_object* v___x_504_; 
v_v_501_ = lean_array_fget(v_b_465_, v_a_464_);
v___x_502_ = lean_box(0);
v_xs_x27_503_ = lean_array_fset(v_b_465_, v_a_464_, v___x_502_);
v___x_504_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_458_, v_skipTypes_459_, v_skipProofs_460_, v_v_501_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_506_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = lean_array_fset(v_xs_x27_503_, v_a_464_, v_a_505_);
v_a_473_ = v___x_506_;
goto v___jp_472_;
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec_ref(v_xs_x27_503_);
lean_dec(v_a_464_);
v_a_507_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_504_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_504_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
else
{
if (v_explicitOnly_458_ == 0)
{
goto v___jp_477_;
}
else
{
if (v_a_463_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_array_fget_borrowed(v_paramInfo_496_, v_a_464_);
v___x_516_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_515_);
if (v___x_516_ == 0)
{
v_a_473_ = v_b_465_;
goto v___jp_472_;
}
else
{
goto v___jp_477_;
}
}
else
{
goto v___jp_477_;
}
}
}
}
v___jp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_add(v_a_464_, v___x_474_);
lean_dec(v_a_464_);
v_a_464_ = v___x_475_;
v_b_465_ = v_a_473_;
goto _start;
}
v___jp_477_:
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_array_get_size(v_b_465_);
v___x_479_ = lean_nat_dec_lt(v_a_464_, v___x_478_);
if (v___x_479_ == 0)
{
v_a_473_ = v_b_465_;
goto v___jp_472_;
}
else
{
lean_object* v_v_480_; lean_object* v___x_481_; lean_object* v_xs_x27_482_; lean_object* v___x_483_; 
v_v_480_ = lean_array_fget(v_b_465_, v_a_464_);
v___x_481_ = lean_box(0);
v_xs_x27_482_ = lean_array_fset(v_b_465_, v_a_464_, v___x_481_);
v___x_483_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_458_, v_skipTypes_459_, v_skipProofs_460_, v_v_480_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_485_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
v___x_485_ = lean_array_fset(v_xs_x27_482_, v_a_464_, v_a_484_);
v_a_473_ = v___x_485_;
goto v___jp_472_;
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref(v_xs_x27_482_);
lean_dec(v_a_464_);
v_a_486_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_483_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_483_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_explicitOnly_458_ = stack[0].m_num;
uint8_t v_skipTypes_459_ = stack[1].m_num;
uint8_t v_skipProofs_460_ = stack[2].m_num;
lean_object* v_upperBound_461_ = stack[3].m_obj;
lean_object* v_a_462_ = stack[4].m_obj;
uint8_t v_a_463_ = stack[5].m_num;
lean_object* v_a_464_ = stack[6].m_obj;
lean_object* v_b_465_ = stack[7].m_obj;
lean_object* v___y_466_ = stack[8].m_obj;
lean_object* v___y_467_ = stack[9].m_obj;
lean_object* v___y_468_ = stack[10].m_obj;
lean_object* v___y_469_ = stack[11].m_obj;
lean_object* v___y_470_ = stack[12].m_obj;
lean_object* v_res_517_;
v_res_517_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_458_, v_skipTypes_459_, v_skipProofs_460_, v_upperBound_461_, v_a_462_, v_a_463_, v_a_464_, v_b_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
stack->m_obj
 = v_res_517_;
}
lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(lean_object* v___x_523_, uint8_t v_explicitOnly_524_, uint8_t v_skipTypes_525_, uint8_t v_skipProofs_526_, lean_object* v_e_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_540_; lean_object* v___y_546_; lean_object* v___y_547_; uint8_t v___y_548_; uint8_t v___y_557_; uint8_t v_a_558_; 
if (v_skipTypes_525_ == 0)
{
goto v___jp_623_;
}
else
{
lean_object* v___x_644_; 
lean_inc_ref(v_e_527_);
v___x_644_ = l_Lean_Meta_isType(v_e_527_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_653_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
uint8_t v___x_649_; 
v___x_649_ = lean_unbox(v_a_645_);
lean_dec(v_a_645_);
if (v___x_649_ == 0)
{
lean_del_object(v___x_647_);
goto v___jp_623_;
}
else
{
lean_object* v___x_651_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v_e_527_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_e_527_);
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
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_e_527_);
v_a_654_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_644_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_644_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
v___jp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = l_Lean_mkAppN(v___y_536_, v___y_535_);
lean_dec_ref(v___y_535_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_add(v___y_540_, v___x_541_);
lean_dec(v___y_540_);
v___x_543_ = l_Lean_mkRawNatLit(v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
v___jp_545_:
{
if (v___y_548_ == 0)
{
v___y_535_ = v___y_546_;
v___y_536_ = v___y_547_;
goto v___jp_534_;
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_array_get_borrowed(v___x_523_, v___y_546_, v___x_549_);
v___x_551_ = l_Lean_Expr_isRawNatLit(v___x_550_);
if (v___x_551_ == 0)
{
v___y_535_ = v___y_546_;
v___y_536_ = v___y_547_;
goto v___jp_534_;
}
else
{
lean_object* v___x_552_; 
lean_inc(v___x_550_);
lean_dec_ref(v___y_547_);
lean_dec_ref(v___y_546_);
v___x_552_ = l_Lean_Expr_rawNatLit_x3f(v___x_550_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_obj_once(&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3, &l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3);
v___x_554_ = l_panic___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(v___x_553_);
v___y_540_ = v___x_554_;
goto v___jp_539_;
}
else
{
lean_object* v_val_555_; 
v_val_555_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v___x_552_, 1);
v___y_540_ = v_val_555_;
goto v___jp_539_;
}
}
}
}
v___jp_556_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___f_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___f_570_; lean_object* v___x_571_; 
v___x_559_ = lean_box(v_explicitOnly_524_);
v___x_560_ = lean_box(v_skipTypes_525_);
v___x_561_ = lean_box(v_skipProofs_526_);
v___x_562_ = lean_box(v_a_558_);
v___x_563_ = lean_box(v___y_557_);
v___f_564_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed), 13, 5);
lean_closure_set(v___f_564_, 0, v___x_559_);
lean_closure_set(v___f_564_, 1, v___x_560_);
lean_closure_set(v___f_564_, 2, v___x_561_);
lean_closure_set(v___f_564_, 3, v___x_562_);
lean_closure_set(v___f_564_, 4, v___x_563_);
v___x_565_ = lean_box(v_explicitOnly_524_);
v___x_566_ = lean_box(v_skipTypes_525_);
v___x_567_ = lean_box(v_skipProofs_526_);
v___x_568_ = lean_box(v_a_558_);
v___x_569_ = lean_box(v___y_557_);
v___f_570_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed), 13, 5);
lean_closure_set(v___f_570_, 0, v___x_565_);
lean_closure_set(v___f_570_, 1, v___x_566_);
lean_closure_set(v___f_570_, 2, v___x_567_);
lean_closure_set(v___f_570_, 3, v___x_568_);
lean_closure_set(v___f_570_, 4, v___x_569_);
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
v___x_571_ = lean_whnf(v_e_527_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
switch(lean_obj_tag(v_a_572_))
{
case 5:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_inc_ref(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
lean_dec_ref(v___f_570_);
lean_dec_ref(v___f_564_);
v___x_573_ = l_Lean_Expr_getAppFn(v_a_572_);
v___x_574_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_524_, v_skipTypes_525_, v_skipProofs_526_, v___x_573_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc_n(v_a_575_, 2);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = l_Lean_Expr_getAppNumArgs(v_a_572_);
lean_inc(v___x_576_);
v___x_577_ = l_Lean_Meta_getFunInfoNArgs(v_a_575_, v___x_576_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
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
v___x_586_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_524_, v_skipTypes_525_, v_skipProofs_526_, v___x_584_, v_a_578_, v_a_558_, v___x_585_, v___x_583_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
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
v___y_546_ = v_a_587_;
v___y_547_ = v_a_575_;
v___y_548_ = v_a_558_;
goto v___jp_545_;
}
else
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_array_get_size(v_a_587_);
v___x_591_ = lean_nat_dec_eq(v___x_590_, v___x_581_);
v___y_546_ = v_a_587_;
v___y_547_ = v_a_575_;
v___y_548_ = v___x_591_;
goto v___jp_545_;
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
lean_object* v___x_608_; 
lean_inc_ref(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
lean_dec_ref(v___f_570_);
v___x_608_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_a_572_, v___f_564_, v_a_558_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
return v___x_608_;
}
case 7:
{
lean_object* v___x_609_; 
lean_inc_ref(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
lean_dec_ref(v___f_564_);
v___x_609_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_a_572_, v___f_570_, v_a_558_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
return v___x_609_;
}
case 11:
{
lean_object* v_typeName_610_; lean_object* v_idx_611_; lean_object* v_struct_612_; lean_object* v___x_613_; 
lean_inc_ref(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
lean_dec_ref(v___f_570_);
lean_dec_ref(v___f_564_);
v_typeName_610_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_typeName_610_);
v_idx_611_ = lean_ctor_get(v_a_572_, 1);
lean_inc(v_idx_611_);
v_struct_612_ = lean_ctor_get(v_a_572_, 2);
lean_inc_ref(v_struct_612_);
lean_dec_ref_known(v_a_572_, 3);
v___x_613_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_524_, v_skipTypes_525_, v_skipProofs_526_, v_struct_612_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_622_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_622_ == 0)
{
v___x_616_ = v___x_613_;
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = l_Lean_mkProj(v_typeName_610_, v_idx_611_, v_a_614_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_618_);
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_dec(v_idx_611_);
lean_dec(v_typeName_610_);
return v___x_613_;
}
}
default: 
{
lean_dec_ref(v___f_570_);
lean_dec_ref(v___f_564_);
return v___x_571_;
}
}
}
else
{
lean_dec_ref(v___f_570_);
lean_dec_ref(v___f_564_);
return v___x_571_;
}
}
v___jp_623_:
{
uint8_t v___x_624_; 
v___x_624_ = 1;
if (v_skipProofs_526_ == 0)
{
v___y_557_ = v___x_624_;
v_a_558_ = v_skipProofs_526_;
goto v___jp_556_;
}
else
{
lean_object* v___x_625_; 
lean_inc_ref(v_e_527_);
v___x_625_ = l_Lean_Meta_isProof(v_e_527_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_635_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_635_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_635_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_635_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
uint8_t v___x_630_; 
v___x_630_ = lean_unbox(v_a_626_);
if (v___x_630_ == 0)
{
uint8_t v___x_631_; 
lean_del_object(v___x_628_);
v___x_631_ = lean_unbox(v_a_626_);
lean_dec(v_a_626_);
v___y_557_ = v___x_624_;
v_a_558_ = v___x_631_;
goto v___jp_556_;
}
else
{
lean_object* v___x_633_; 
lean_dec(v_a_626_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v_e_527_);
v___x_633_ = v___x_628_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_e_527_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v_e_527_);
v_a_636_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_625_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_625_);
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
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_523_ = stack[0].m_obj;
uint8_t v_explicitOnly_524_ = stack[1].m_num;
uint8_t v_skipTypes_525_ = stack[2].m_num;
uint8_t v_skipProofs_526_ = stack[3].m_num;
lean_object* v_e_527_ = stack[4].m_obj;
lean_object* v___y_528_ = stack[5].m_obj;
lean_object* v___y_529_ = stack[6].m_obj;
lean_object* v___y_530_ = stack[7].m_obj;
lean_object* v___y_531_ = stack[8].m_obj;
lean_object* v___y_532_ = stack[9].m_obj;
lean_object* v_res_662_;
v_res_662_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(v___x_523_, v_explicitOnly_524_, v_skipTypes_525_, v_skipProofs_526_, v_e_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed(lean_object* v___x_663_, lean_object* v_explicitOnly_664_, lean_object* v_skipTypes_665_, lean_object* v_skipProofs_666_, lean_object* v_e_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
uint8_t v_explicitOnly_boxed_674_; uint8_t v_skipTypes_boxed_675_; uint8_t v_skipProofs_boxed_676_; lean_object* v_res_677_; 
v_explicitOnly_boxed_674_ = lean_unbox(v_explicitOnly_664_);
v_skipTypes_boxed_675_ = lean_unbox(v_skipTypes_665_);
v_skipProofs_boxed_676_ = lean_unbox(v_skipProofs_666_);
v_res_677_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(v___x_663_, v_explicitOnly_boxed_674_, v_skipTypes_boxed_675_, v_skipProofs_boxed_676_, v_e_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___x_663_);
return v_res_677_;
}
}
lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(uint8_t v_explicitOnly_678_, uint8_t v_skipTypes_679_, uint8_t v_skipProofs_680_, lean_object* v_e_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___f_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_688_ = l_Lean_instInhabitedExpr;
v___x_689_ = lean_box(v_explicitOnly_678_);
v___x_690_ = lean_box(v_skipTypes_679_);
v___x_691_ = lean_box(v_skipProofs_680_);
lean_inc_ref(v_e_681_);
v___f_692_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed), 11, 5);
lean_closure_set(v___f_692_, 0, v___x_688_);
lean_closure_set(v___f_692_, 1, v___x_689_);
lean_closure_set(v___f_692_, 2, v___x_690_);
lean_closure_set(v___f_692_, 3, v___x_691_);
lean_closure_set(v___f_692_, 4, v_e_681_);
v___x_693_ = lean_st_ref_get(v_a_682_);
v___x_694_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v___x_693_, v_e_681_);
lean_dec(v___x_693_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v___f_692_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_706_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_706_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_700_ = lean_st_ref_take(v_a_682_);
lean_inc(v_a_696_);
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v___x_700_, v_e_681_, v_a_696_);
v___x_702_ = lean_st_ref_put(v_a_682_, v___x_701_);
if (v_isShared_699_ == 0)
{
v___x_704_ = v___x_698_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_696_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
lean_dec_ref(v_e_681_);
return v___x_695_;
}
}
else
{
lean_object* v_val_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v___f_692_);
lean_dec_ref(v_e_681_);
v_val_707_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_694_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_val_707_);
lean_dec(v___x_694_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 0);
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_val_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_0interp(lean_interpreter_value* stack)
{
uint8_t v_explicitOnly_678_ = stack[0].m_num;
uint8_t v_skipTypes_679_ = stack[1].m_num;
uint8_t v_skipProofs_680_ = stack[2].m_num;
lean_object* v_e_681_ = stack[3].m_obj;
lean_object* v_a_682_ = stack[4].m_obj;
lean_object* v_a_683_ = stack[5].m_obj;
lean_object* v_a_684_ = stack[6].m_obj;
lean_object* v_a_685_ = stack[7].m_obj;
lean_object* v_a_686_ = stack[8].m_obj;
lean_object* v_res_715_;
v_res_715_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_678_, v_skipTypes_679_, v_skipProofs_680_, v_e_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
stack->m_obj
 = v_res_715_;
}
lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(uint8_t v_explicitOnly_716_, uint8_t v_skipTypes_717_, uint8_t v_skipProofs_718_, uint8_t v_a_719_, uint8_t v___x_720_, lean_object* v_xs_721_, lean_object* v_b_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_716_, v_skipTypes_717_, v_skipProofs_718_, v_b_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; uint8_t v___x_731_; lean_object* v___x_732_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = 1;
v___x_732_ = l_Lean_Meta_mkLambdaFVars(v_xs_721_, v_a_730_, v_a_719_, v___x_720_, v_a_719_, v___x_720_, v___x_731_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
return v___x_732_;
}
else
{
return v___x_729_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_explicitOnly_716_ = stack[0].m_num;
uint8_t v_skipTypes_717_ = stack[1].m_num;
uint8_t v_skipProofs_718_ = stack[2].m_num;
uint8_t v_a_719_ = stack[3].m_num;
uint8_t v___x_720_ = stack[4].m_num;
lean_object* v_xs_721_ = stack[5].m_obj;
lean_object* v_b_722_ = stack[6].m_obj;
lean_object* v___y_723_ = stack[7].m_obj;
lean_object* v___y_724_ = stack[8].m_obj;
lean_object* v___y_725_ = stack[9].m_obj;
lean_object* v___y_726_ = stack[10].m_obj;
lean_object* v___y_727_ = stack[11].m_obj;
lean_object* v_res_733_;
v_res_733_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(v_explicitOnly_716_, v_skipTypes_717_, v_skipProofs_718_, v_a_719_, v___x_720_, v_xs_721_, v_b_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
stack->m_obj
 = v_res_733_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___boxed(lean_object* v_explicitOnly_734_, lean_object* v_skipTypes_735_, lean_object* v_skipProofs_736_, lean_object* v_e_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
uint8_t v_explicitOnly_boxed_744_; uint8_t v_skipTypes_boxed_745_; uint8_t v_skipProofs_boxed_746_; lean_object* v_res_747_; 
v_explicitOnly_boxed_744_ = lean_unbox(v_explicitOnly_734_);
v_skipTypes_boxed_745_ = lean_unbox(v_skipTypes_735_);
v_skipProofs_boxed_746_ = lean_unbox(v_skipProofs_736_);
v_res_747_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_boxed_744_, v_skipTypes_boxed_745_, v_skipProofs_boxed_746_, v_e_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg___boxed(lean_object* v_explicitOnly_748_, lean_object* v_skipTypes_749_, lean_object* v_skipProofs_750_, lean_object* v_upperBound_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_b_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
uint8_t v_explicitOnly_boxed_762_; uint8_t v_skipTypes_boxed_763_; uint8_t v_skipProofs_boxed_764_; uint8_t v_a_15215__boxed_765_; lean_object* v_res_766_; 
v_explicitOnly_boxed_762_ = lean_unbox(v_explicitOnly_748_);
v_skipTypes_boxed_763_ = lean_unbox(v_skipTypes_749_);
v_skipProofs_boxed_764_ = lean_unbox(v_skipProofs_750_);
v_a_15215__boxed_765_ = lean_unbox(v_a_753_);
v_res_766_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_boxed_762_, v_skipTypes_boxed_763_, v_skipProofs_boxed_764_, v_upperBound_751_, v_a_752_, v_a_15215__boxed_765_, v_a_754_, v_b_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v_a_752_);
lean_dec(v_upperBound_751_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(lean_object* v_00_u03b2_767_, lean_object* v_m_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v_m_768_, v_a_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___boxed(lean_object* v_00_u03b2_771_, lean_object* v_m_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(v_00_u03b2_771_, v_m_772_, v_a_773_);
lean_dec_ref(v_a_773_);
lean_dec_ref(v_m_772_);
return v_res_774_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(uint8_t v_explicitOnly_775_, uint8_t v_skipTypes_776_, uint8_t v_skipProofs_777_, lean_object* v_upperBound_778_, lean_object* v_a_779_, uint8_t v_a_780_, lean_object* v_inst_781_, lean_object* v_R_782_, lean_object* v_a_783_, lean_object* v_b_784_, lean_object* v_c_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_775_, v_skipTypes_776_, v_skipProofs_777_, v_upperBound_778_, v_a_779_, v_a_780_, v_a_783_, v_b_784_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
return v___x_792_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_explicitOnly_775_ = stack[0].m_num;
uint8_t v_skipTypes_776_ = stack[1].m_num;
uint8_t v_skipProofs_777_ = stack[2].m_num;
lean_object* v_upperBound_778_ = stack[3].m_obj;
lean_object* v_a_779_ = stack[4].m_obj;
uint8_t v_a_780_ = stack[5].m_num;
lean_object* v_a_783_ = stack[8].m_obj;
lean_object* v_b_784_ = stack[9].m_obj;
lean_object* v___y_786_ = stack[11].m_obj;
lean_object* v___y_787_ = stack[12].m_obj;
lean_object* v___y_788_ = stack[13].m_obj;
lean_object* v___y_789_ = stack[14].m_obj;
lean_object* v___y_790_ = stack[15].m_obj;
lean_object* v_res_793_;
v_res_793_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(v_explicitOnly_775_, v_skipTypes_776_, v_skipProofs_777_, v_upperBound_778_, v_a_779_, v_a_780_, lean_box(0), lean_box(0), v_a_783_, v_b_784_, lean_box(0), v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
stack->m_obj
 = v_res_793_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___boxed(lean_object** _args){
lean_object* v_explicitOnly_794_ = _args[0];
lean_object* v_skipTypes_795_ = _args[1];
lean_object* v_skipProofs_796_ = _args[2];
lean_object* v_upperBound_797_ = _args[3];
lean_object* v_a_798_ = _args[4];
lean_object* v_a_799_ = _args[5];
lean_object* v_inst_800_ = _args[6];
lean_object* v_R_801_ = _args[7];
lean_object* v_a_802_ = _args[8];
lean_object* v_b_803_ = _args[9];
lean_object* v_c_804_ = _args[10];
lean_object* v___y_805_ = _args[11];
lean_object* v___y_806_ = _args[12];
lean_object* v___y_807_ = _args[13];
lean_object* v___y_808_ = _args[14];
lean_object* v___y_809_ = _args[15];
lean_object* v___y_810_ = _args[16];
_start:
{
uint8_t v_explicitOnly_boxed_811_; uint8_t v_skipTypes_boxed_812_; uint8_t v_skipProofs_boxed_813_; uint8_t v_a_16010__boxed_814_; lean_object* v_res_815_; 
v_explicitOnly_boxed_811_ = lean_unbox(v_explicitOnly_794_);
v_skipTypes_boxed_812_ = lean_unbox(v_skipTypes_795_);
v_skipProofs_boxed_813_ = lean_unbox(v_skipProofs_796_);
v_a_16010__boxed_814_ = lean_unbox(v_a_799_);
v_res_815_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(v_explicitOnly_boxed_811_, v_skipTypes_boxed_812_, v_skipProofs_boxed_813_, v_upperBound_797_, v_a_798_, v_a_16010__boxed_814_, v_inst_800_, v_R_801_, v_a_802_, v_b_803_, v_c_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v_a_798_);
lean_dec(v_upperBound_797_);
return v_res_815_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(lean_object* v_00_u03b1_816_, lean_object* v_ref_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_817_);
return v___x_821_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_817_ = stack[1].m_obj;
lean_object* v___y_818_ = stack[2].m_obj;
lean_object* v___y_819_ = stack[3].m_obj;
lean_object* v_res_822_;
v_res_822_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(lean_box(0), v_ref_817_, v___y_818_, v___y_819_);
stack->m_obj
 = v_res_822_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___boxed(lean_object* v_00_u03b1_823_, lean_object* v_ref_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(v_00_u03b1_823_, v_ref_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
return v_res_828_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7(lean_object* v_00_u03b1_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___redArg();
return v___x_833_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_830_ = stack[1].m_obj;
lean_object* v___y_831_ = stack[2].m_obj;
lean_object* v_res_834_;
v_res_834_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7(lean_box(0), v___y_830_, v___y_831_);
stack->m_obj
 = v_res_834_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7___boxed(lean_object* v_00_u03b1_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__7(v_00_u03b1_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
return v_res_839_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(lean_object* v_00_u03b1_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
return v___x_848_;
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_841_ = stack[1].m_obj;
lean_object* v___y_842_ = stack[2].m_obj;
lean_object* v___y_843_ = stack[3].m_obj;
lean_object* v___y_844_ = stack[4].m_obj;
lean_object* v___y_845_ = stack[5].m_obj;
lean_object* v___y_846_ = stack[6].m_obj;
lean_object* v_res_849_;
v_res_849_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(lean_box(0), v_x_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
stack->m_obj
 = v_res_849_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___boxed(lean_object* v_00_u03b1_850_, lean_object* v_x_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(v_00_u03b1_850_, v_x_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6(lean_object* v_00_u03b2_859_, lean_object* v_m_860_, lean_object* v_a_861_, lean_object* v_b_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v_m_860_, v_a_861_, v_b_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(lean_object* v_00_u03b2_864_, lean_object* v_a_865_, lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_a_865_, v_x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_868_, lean_object* v_a_869_, lean_object* v_x_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(v_00_u03b2_868_, v_a_869_, v_x_870_);
lean_dec(v_x_870_);
lean_dec_ref(v_a_869_);
return v_res_871_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(lean_object* v_00_u03b2_872_, lean_object* v_a_873_, lean_object* v_x_874_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_a_873_, v_x_874_);
return v___x_875_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_873_ = stack[1].m_obj;
lean_object* v_x_874_ = stack[2].m_obj;
uint8_t v_res_876_;
v_res_876_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(lean_box(0), v_a_873_, v_x_874_);
stack->m_num = v_res_876_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___boxed(lean_object* v_00_u03b2_877_, lean_object* v_a_878_, lean_object* v_x_879_){
_start:
{
uint8_t v_res_880_; lean_object* v_r_881_; 
v_res_880_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(v_00_u03b2_877_, v_a_878_, v_x_879_);
lean_dec(v_x_879_);
lean_dec_ref(v_a_878_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10(lean_object* v_00_u03b2_882_, lean_object* v_data_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(v_data_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11(lean_object* v_00_u03b2_885_, lean_object* v_a_886_, lean_object* v_b_887_, lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__11___redArg(v_a_886_, v_b_887_, v_x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_890_, lean_object* v_i_891_, lean_object* v_source_892_, lean_object* v_target_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11___redArg(v_i_891_, v_source_892_, v_target_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10_spec__11_spec__12___redArg(v_x_896_, v_x_897_);
return v___x_898_;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__0(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_box(0);
v___x_900_ = lean_unsigned_to_nat(16u);
v___x_901_ = lean_mk_array(v___x_900_, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__1(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_obj_once(&l_Lean_Meta_reduce___closed__0, &l_Lean_Meta_reduce___closed__0_once, _init_l_Lean_Meta_reduce___closed__0);
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_902_);
return v___x_904_;
}
}
lean_object* l_Lean_Meta_reduce(lean_object* v_e_905_, uint8_t v_explicitOnly_906_, uint8_t v_skipTypes_907_, uint8_t v_skipProofs_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = lean_obj_once(&l_Lean_Meta_reduce___closed__1, &l_Lean_Meta_reduce___closed__1_once, _init_l_Lean_Meta_reduce___closed__1);
v___x_915_ = lean_st_mk_ref(v___x_914_);
v___x_916_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_906_, v_skipTypes_907_, v_skipProofs_908_, v_e_905_, v___x_915_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_925_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_925_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_921_ = lean_st_ref_get(v___x_915_);
lean_dec(v___x_915_);
lean_dec(v___x_921_);
if (v_isShared_920_ == 0)
{
v___x_923_ = v___x_919_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_917_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
else
{
lean_dec(v___x_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_reduce_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_905_ = stack[0].m_obj;
uint8_t v_explicitOnly_906_ = stack[1].m_num;
uint8_t v_skipTypes_907_ = stack[2].m_num;
uint8_t v_skipProofs_908_ = stack[3].m_num;
lean_object* v_a_909_ = stack[4].m_obj;
lean_object* v_a_910_ = stack[5].m_obj;
lean_object* v_a_911_ = stack[6].m_obj;
lean_object* v_a_912_ = stack[7].m_obj;
lean_object* v_res_926_;
v_res_926_ = l_Lean_Meta_reduce(v_e_905_, v_explicitOnly_906_, v_skipTypes_907_, v_skipProofs_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
stack->m_obj
 = v_res_926_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object* v_e_927_, lean_object* v_explicitOnly_928_, lean_object* v_skipTypes_929_, lean_object* v_skipProofs_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
uint8_t v_explicitOnly_boxed_936_; uint8_t v_skipTypes_boxed_937_; uint8_t v_skipProofs_boxed_938_; lean_object* v_res_939_; 
v_explicitOnly_boxed_936_ = lean_unbox(v_explicitOnly_928_);
v_skipTypes_boxed_937_ = lean_unbox(v_skipTypes_929_);
v_skipProofs_boxed_938_ = lean_unbox(v_skipProofs_930_);
v_res_939_ = l_Lean_Meta_reduce(v_e_927_, v_explicitOnly_boxed_936_, v_skipTypes_boxed_937_, v_skipProofs_boxed_938_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
return v_res_939_;
}
}
lean_object* l_Lean_Meta_reduceAll(lean_object* v_e_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
uint8_t v___x_946_; lean_object* v___x_947_; 
v___x_946_ = 0;
v___x_947_ = l_Lean_Meta_reduce(v_e_940_, v___x_946_, v___x_946_, v___x_946_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
return v___x_947_;
}
}
LEAN_EXPORT void l_Lean_Meta_reduceAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_940_ = stack[0].m_obj;
lean_object* v_a_941_ = stack[1].m_obj;
lean_object* v_a_942_ = stack[2].m_obj;
lean_object* v_a_943_ = stack[3].m_obj;
lean_object* v_a_944_ = stack[4].m_obj;
lean_object* v_res_948_;
v_res_948_ = l_Lean_Meta_reduceAll(v_e_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll___boxed(lean_object* v_e_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Meta_reduceAll(v_e_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
return v_res_955_;
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
