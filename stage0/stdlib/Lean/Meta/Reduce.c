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
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10_spec__11(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(lean_object* v_a_168_, lean_object* v_b_169_, lean_object* v_x_170_){
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
v___x_178_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(v_a_168_, v_b_169_, v_tail_173_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8___redArg(lean_object* v_a_186_, lean_object* v_x_187_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8___redArg___boxed(lean_object* v_a_193_, lean_object* v_x_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8___redArg(v_a_193_, v_x_194_);
lean_dec(v_x_194_);
lean_dec_ref(v_a_193_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10_spec__11___redArg(lean_object* v_x_197_, lean_object* v_x_198_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10___redArg(lean_object* v_i_225_, lean_object* v_source_226_, lean_object* v_target_227_){
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
v_target_233_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10_spec__11___redArg(v_target_227_, v_es_230_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(lean_object* v_data_237_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v_nbuckets_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_238_ = lean_array_get_size(v_data_237_);
v___x_239_ = lean_unsigned_to_nat(2u);
v_nbuckets_240_ = lean_nat_mul(v___x_238_, v___x_239_);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_box(0);
v___x_243_ = lean_mk_array(v_nbuckets_240_, v___x_242_);
v___x_244_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10___redArg(v___x_241_, v_data_237_, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(lean_object* v_m_245_, lean_object* v_a_246_, lean_object* v_b_247_){
_start:
{
lean_object* v_size_248_; lean_object* v_buckets_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_292_; 
v_size_248_ = lean_ctor_get(v_m_245_, 0);
v_buckets_249_ = lean_ctor_get(v_m_245_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_m_245_);
if (v_isSharedCheck_292_ == 0)
{
v___x_251_ = v_m_245_;
v_isShared_252_ = v_isSharedCheck_292_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_buckets_249_);
lean_inc(v_size_248_);
lean_dec(v_m_245_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_292_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; uint64_t v___x_254_; uint64_t v___x_255_; uint64_t v___x_256_; uint64_t v_fold_257_; uint64_t v___x_258_; uint64_t v___x_259_; uint64_t v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; lean_object* v_bkt_266_; uint8_t v___x_267_; 
v___x_253_ = lean_array_get_size(v_buckets_249_);
v___x_254_ = l_Lean_Expr_hash(v_a_246_);
v___x_255_ = 32ULL;
v___x_256_ = lean_uint64_shift_right(v___x_254_, v___x_255_);
v_fold_257_ = lean_uint64_xor(v___x_254_, v___x_256_);
v___x_258_ = 16ULL;
v___x_259_ = lean_uint64_shift_right(v_fold_257_, v___x_258_);
v___x_260_ = lean_uint64_xor(v_fold_257_, v___x_259_);
v___x_261_ = lean_uint64_to_usize(v___x_260_);
v___x_262_ = lean_usize_of_nat(v___x_253_);
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_sub(v___x_262_, v___x_263_);
v___x_265_ = lean_usize_land(v___x_261_, v___x_264_);
v_bkt_266_ = lean_array_uget_borrowed(v_buckets_249_, v___x_265_);
v___x_267_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8___redArg(v_a_246_, v_bkt_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v_size_x27_269_; lean_object* v___x_270_; lean_object* v_buckets_x27_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v_size_x27_269_ = lean_nat_add(v_size_248_, v___x_268_);
lean_dec(v_size_248_);
lean_inc(v_bkt_266_);
v___x_270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_270_, 0, v_a_246_);
lean_ctor_set(v___x_270_, 1, v_b_247_);
lean_ctor_set(v___x_270_, 2, v_bkt_266_);
v_buckets_x27_271_ = lean_array_uset(v_buckets_249_, v___x_265_, v___x_270_);
v___x_272_ = lean_unsigned_to_nat(4u);
v___x_273_ = lean_nat_mul(v_size_x27_269_, v___x_272_);
v___x_274_ = lean_unsigned_to_nat(3u);
v___x_275_ = lean_nat_div(v___x_273_, v___x_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_array_get_size(v_buckets_x27_271_);
v___x_277_ = lean_nat_dec_le(v___x_275_, v___x_276_);
lean_dec(v___x_275_);
if (v___x_277_ == 0)
{
lean_object* v_val_278_; lean_object* v___x_280_; 
v_val_278_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_buckets_x27_271_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_val_278_);
lean_ctor_set(v___x_251_, 0, v_size_x27_269_);
v___x_280_ = v___x_251_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_size_x27_269_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_val_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
else
{
lean_object* v___x_283_; 
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_buckets_x27_271_);
lean_ctor_set(v___x_251_, 0, v_size_x27_269_);
v___x_283_ = v___x_251_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_size_x27_269_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_buckets_x27_271_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_object* v___x_285_; lean_object* v_buckets_x27_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
lean_inc(v_bkt_266_);
v___x_285_ = lean_box(0);
v_buckets_x27_286_ = lean_array_uset(v_buckets_249_, v___x_265_, v___x_285_);
v___x_287_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(v_a_246_, v_b_247_, v_bkt_266_);
v___x_288_ = lean_array_uset(v_buckets_x27_286_, v___x_265_, v___x_287_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v___x_288_);
v___x_290_ = v___x_251_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_size_248_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = l_Lean_maxRecDepthErrorMessage;
v___x_299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__3);
v___x_301_ = l_Lean_MessageData_ofFormat(v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__4);
v___x_303_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__2));
v___x_304_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(lean_object* v_ref_305_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___closed__5);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_ref_305_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg___boxed(lean_object* v_ref_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(lean_object* v_x_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___y_321_; lean_object* v_fileName_330_; lean_object* v_fileMap_331_; lean_object* v_options_332_; lean_object* v_currRecDepth_333_; lean_object* v_maxRecDepth_334_; lean_object* v_ref_335_; lean_object* v_currNamespace_336_; lean_object* v_openDecls_337_; lean_object* v_initHeartbeats_338_; lean_object* v_maxHeartbeats_339_; lean_object* v_quotContext_340_; lean_object* v_currMacroScope_341_; uint8_t v_diag_342_; lean_object* v_cancelTk_x3f_343_; uint8_t v_suppressElabErrors_344_; lean_object* v_inheritedTraceOptions_345_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_fileName_330_ = lean_ctor_get(v___y_317_, 0);
v_fileMap_331_ = lean_ctor_get(v___y_317_, 1);
v_options_332_ = lean_ctor_get(v___y_317_, 2);
v_currRecDepth_333_ = lean_ctor_get(v___y_317_, 3);
v_maxRecDepth_334_ = lean_ctor_get(v___y_317_, 4);
v_ref_335_ = lean_ctor_get(v___y_317_, 5);
v_currNamespace_336_ = lean_ctor_get(v___y_317_, 6);
v_openDecls_337_ = lean_ctor_get(v___y_317_, 7);
v_initHeartbeats_338_ = lean_ctor_get(v___y_317_, 8);
v_maxHeartbeats_339_ = lean_ctor_get(v___y_317_, 9);
v_quotContext_340_ = lean_ctor_get(v___y_317_, 10);
v_currMacroScope_341_ = lean_ctor_get(v___y_317_, 11);
v_diag_342_ = lean_ctor_get_uint8(v___y_317_, sizeof(void*)*14);
v_cancelTk_x3f_343_ = lean_ctor_get(v___y_317_, 12);
v_suppressElabErrors_344_ = lean_ctor_get_uint8(v___y_317_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_345_ = lean_ctor_get(v___y_317_, 13);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_nat_dec_eq(v_maxRecDepth_334_, v___x_351_);
if (v___x_352_ == 0)
{
uint8_t v___x_353_; 
v___x_353_ = lean_nat_dec_eq(v_currRecDepth_333_, v_maxRecDepth_334_);
if (v___x_353_ == 0)
{
goto v___jp_346_;
}
else
{
lean_object* v___x_354_; 
lean_dec_ref(v_x_313_);
lean_inc(v_ref_335_);
v___x_354_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_335_);
v___y_321_ = v___x_354_;
goto v___jp_320_;
}
}
else
{
goto v___jp_346_;
}
v___jp_320_:
{
if (lean_obj_tag(v___y_321_) == 0)
{
return v___y_321_;
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_a_322_ = lean_ctor_get(v___y_321_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___y_321_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___y_321_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___y_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
v___jp_346_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_currRecDepth_333_, v___x_347_);
lean_inc_ref(v_inheritedTraceOptions_345_);
lean_inc(v_cancelTk_x3f_343_);
lean_inc(v_currMacroScope_341_);
lean_inc(v_quotContext_340_);
lean_inc(v_maxHeartbeats_339_);
lean_inc(v_initHeartbeats_338_);
lean_inc(v_openDecls_337_);
lean_inc(v_currNamespace_336_);
lean_inc(v_ref_335_);
lean_inc(v_maxRecDepth_334_);
lean_inc_ref(v_options_332_);
lean_inc_ref(v_fileMap_331_);
lean_inc_ref(v_fileName_330_);
v___x_349_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_349_, 0, v_fileName_330_);
lean_ctor_set(v___x_349_, 1, v_fileMap_331_);
lean_ctor_set(v___x_349_, 2, v_options_332_);
lean_ctor_set(v___x_349_, 3, v___x_348_);
lean_ctor_set(v___x_349_, 4, v_maxRecDepth_334_);
lean_ctor_set(v___x_349_, 5, v_ref_335_);
lean_ctor_set(v___x_349_, 6, v_currNamespace_336_);
lean_ctor_set(v___x_349_, 7, v_openDecls_337_);
lean_ctor_set(v___x_349_, 8, v_initHeartbeats_338_);
lean_ctor_set(v___x_349_, 9, v_maxHeartbeats_339_);
lean_ctor_set(v___x_349_, 10, v_quotContext_340_);
lean_ctor_set(v___x_349_, 11, v_currMacroScope_341_);
lean_ctor_set(v___x_349_, 12, v_cancelTk_x3f_343_);
lean_ctor_set(v___x_349_, 13, v_inheritedTraceOptions_345_);
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*14, v_diag_342_);
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*14 + 1, v_suppressElabErrors_344_);
lean_inc(v___y_318_);
lean_inc(v___y_316_);
lean_inc_ref(v___y_315_);
lean_inc(v___y_314_);
v___x_350_ = lean_apply_6(v_x_313_, v___y_314_, v___y_315_, v___y_316_, v___x_349_, v___y_318_, lean_box(0));
v___y_321_ = v___x_350_;
goto v___jp_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg___boxed(lean_object* v_x_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
return v_res_362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2));
v___x_367_ = lean_unsigned_to_nat(14u);
v___x_368_ = lean_unsigned_to_nat(22u);
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1));
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0));
v___x_371_ = l_mkPanicMessageWithDecl(v___x_370_, v___x_369_, v___x_368_, v___x_367_, v___x_366_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4(void){
_start:
{
lean_object* v___x_372_; lean_object* v_dummy_373_; 
v___x_372_ = lean_box(0);
v_dummy_373_ = l_Lean_Expr_sort___override(v___x_372_);
return v_dummy_373_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(uint8_t v_explicitOnly_374_, uint8_t v_skipTypes_375_, uint8_t v_skipProofs_376_, lean_object* v_upperBound_377_, lean_object* v_a_378_, uint8_t v_a_379_, lean_object* v_a_380_, lean_object* v_b_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_a_389_; uint8_t v___x_410_; 
v___x_410_ = lean_nat_dec_lt(v_a_380_, v_upperBound_377_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec(v_a_380_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v_b_381_);
return v___x_411_;
}
else
{
lean_object* v_paramInfo_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v_paramInfo_412_ = lean_ctor_get(v_a_378_, 0);
v___x_413_ = lean_array_get_size(v_paramInfo_412_);
v___x_414_ = lean_nat_dec_lt(v_a_380_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_array_get_size(v_b_381_);
v___x_416_ = lean_nat_dec_lt(v_a_380_, v___x_415_);
if (v___x_416_ == 0)
{
v_a_389_ = v_b_381_;
goto v___jp_388_;
}
else
{
lean_object* v_v_417_; lean_object* v___x_418_; 
v_v_417_ = lean_array_fget_borrowed(v_b_381_, v_a_380_);
lean_inc(v_v_417_);
v___x_418_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_374_, v_skipTypes_375_, v_skipProofs_376_, v_v_417_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; lean_object* v_xs_x27_421_; lean_object* v___x_422_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref(v___x_418_);
v___x_420_ = lean_box(0);
v_xs_x27_421_ = lean_array_fset(v_b_381_, v_a_380_, v___x_420_);
v___x_422_ = lean_array_fset(v_xs_x27_421_, v_a_380_, v_a_419_);
v_a_389_ = v___x_422_;
goto v___jp_388_;
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_b_381_);
lean_dec(v_a_380_);
v_a_423_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_418_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_418_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
else
{
if (v_explicitOnly_374_ == 0)
{
goto v___jp_393_;
}
else
{
if (v_a_379_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = lean_array_fget_borrowed(v_paramInfo_412_, v_a_380_);
v___x_432_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_431_);
if (v___x_432_ == 0)
{
v_a_389_ = v_b_381_;
goto v___jp_388_;
}
else
{
goto v___jp_393_;
}
}
else
{
goto v___jp_393_;
}
}
}
}
v___jp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_add(v_a_380_, v___x_390_);
lean_dec(v_a_380_);
v_a_380_ = v___x_391_;
v_b_381_ = v_a_389_;
goto _start;
}
v___jp_393_:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_array_get_size(v_b_381_);
v___x_395_ = lean_nat_dec_lt(v_a_380_, v___x_394_);
if (v___x_395_ == 0)
{
v_a_389_ = v_b_381_;
goto v___jp_388_;
}
else
{
lean_object* v_v_396_; lean_object* v___x_397_; 
v_v_396_ = lean_array_fget_borrowed(v_b_381_, v_a_380_);
lean_inc(v_v_396_);
v___x_397_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_374_, v_skipTypes_375_, v_skipProofs_376_, v_v_396_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_399_; lean_object* v_xs_x27_400_; lean_object* v___x_401_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref(v___x_397_);
v___x_399_ = lean_box(0);
v_xs_x27_400_ = lean_array_fset(v_b_381_, v_a_380_, v___x_399_);
v___x_401_ = lean_array_fset(v_xs_x27_400_, v_a_380_, v_a_398_);
v_a_389_ = v___x_401_;
goto v___jp_388_;
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec_ref(v_b_381_);
lean_dec(v_a_380_);
v_a_402_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_397_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_397_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed(lean_object* v_explicitOnly_438_, lean_object* v_skipTypes_439_, lean_object* v_skipProofs_440_, lean_object* v_a_441_, lean_object* v___x_442_, lean_object* v_xs_443_, lean_object* v_b_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
uint8_t v_explicitOnly_boxed_451_; uint8_t v_skipTypes_boxed_452_; uint8_t v_skipProofs_boxed_453_; uint8_t v_a_16255__boxed_454_; uint8_t v___x_16256__boxed_455_; lean_object* v_res_456_; 
v_explicitOnly_boxed_451_ = lean_unbox(v_explicitOnly_438_);
v_skipTypes_boxed_452_ = lean_unbox(v_skipTypes_439_);
v_skipProofs_boxed_453_ = lean_unbox(v_skipProofs_440_);
v_a_16255__boxed_454_ = lean_unbox(v_a_441_);
v___x_16256__boxed_455_ = lean_unbox(v___x_442_);
v_res_456_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(v_explicitOnly_boxed_451_, v_skipTypes_boxed_452_, v_skipProofs_boxed_453_, v_a_16255__boxed_454_, v___x_16256__boxed_455_, v_xs_443_, v_b_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v_xs_443_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(uint8_t v_explicitOnly_457_, uint8_t v_skipTypes_458_, uint8_t v_skipProofs_459_, uint8_t v_a_460_, uint8_t v___x_461_, lean_object* v_xs_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_457_, v_skipTypes_458_, v_skipProofs_459_, v_b_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; uint8_t v___x_472_; lean_object* v___x_473_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref(v___x_470_);
v___x_472_ = 1;
v___x_473_ = l_Lean_Meta_mkForallFVars(v_xs_462_, v_a_471_, v_a_460_, v___x_461_, v___x_461_, v___x_472_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_473_;
}
else
{
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed(lean_object* v_explicitOnly_474_, lean_object* v_skipTypes_475_, lean_object* v_skipProofs_476_, lean_object* v_a_477_, lean_object* v___x_478_, lean_object* v_xs_479_, lean_object* v_b_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
uint8_t v_explicitOnly_boxed_487_; uint8_t v_skipTypes_boxed_488_; uint8_t v_skipProofs_boxed_489_; uint8_t v_a_16268__boxed_490_; uint8_t v___x_16269__boxed_491_; lean_object* v_res_492_; 
v_explicitOnly_boxed_487_ = lean_unbox(v_explicitOnly_474_);
v_skipTypes_boxed_488_ = lean_unbox(v_skipTypes_475_);
v_skipProofs_boxed_489_ = lean_unbox(v_skipProofs_476_);
v_a_16268__boxed_490_ = lean_unbox(v_a_477_);
v___x_16269__boxed_491_ = lean_unbox(v___x_478_);
v_res_492_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(v_explicitOnly_boxed_487_, v_skipTypes_boxed_488_, v_skipProofs_boxed_489_, v_a_16268__boxed_490_, v___x_16269__boxed_491_, v_xs_479_, v_b_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v_xs_479_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(lean_object* v_e_493_, uint8_t v_explicitOnly_494_, uint8_t v_skipTypes_495_, uint8_t v_skipProofs_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_509_; lean_object* v___y_515_; lean_object* v___y_516_; uint8_t v___y_517_; uint8_t v___y_527_; uint8_t v_a_528_; 
if (v_skipTypes_495_ == 0)
{
goto v___jp_593_;
}
else
{
lean_object* v___x_614_; 
lean_inc_ref(v_e_493_);
v___x_614_ = l_Lean_Meta_isType(v_e_493_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_623_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_623_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint8_t v___x_619_; 
v___x_619_ = lean_unbox(v_a_615_);
lean_dec(v_a_615_);
if (v___x_619_ == 0)
{
lean_del_object(v___x_617_);
goto v___jp_593_;
}
else
{
lean_object* v___x_621_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v_e_493_);
v___x_621_ = v___x_617_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_e_493_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v_e_493_);
v_a_624_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_614_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_614_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
v___jp_503_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = l_Lean_mkAppN(v___y_505_, v___y_504_);
lean_dec_ref(v___y_504_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
v___jp_508_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_add(v___y_509_, v___x_510_);
lean_dec(v___y_509_);
v___x_512_ = l_Lean_mkRawNatLit(v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
v___jp_514_:
{
if (v___y_517_ == 0)
{
v___y_504_ = v___y_515_;
v___y_505_ = v___y_516_;
goto v___jp_503_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_518_ = l_Lean_instInhabitedExpr;
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_array_get_borrowed(v___x_518_, v___y_515_, v___x_519_);
v___x_521_ = l_Lean_Expr_isRawNatLit(v___x_520_);
if (v___x_521_ == 0)
{
v___y_504_ = v___y_515_;
v___y_505_ = v___y_516_;
goto v___jp_503_;
}
else
{
lean_object* v___x_522_; 
lean_inc(v___x_520_);
lean_dec_ref(v___y_516_);
lean_dec_ref(v___y_515_);
v___x_522_ = l_Lean_Expr_rawNatLit_x3f(v___x_520_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3, &l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3);
v___x_524_ = l_panic___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(v___x_523_);
v___y_509_ = v___x_524_;
goto v___jp_508_;
}
else
{
lean_object* v_val_525_; 
v_val_525_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_val_525_);
lean_dec_ref(v___x_522_);
v___y_509_ = v_val_525_;
goto v___jp_508_;
}
}
}
}
v___jp_526_:
{
lean_object* v___x_529_; 
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
v___x_529_ = lean_whnf(v_e_493_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
switch(lean_obj_tag(v_a_530_))
{
case 5:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec_ref(v___x_529_);
v___x_531_ = l_Lean_Expr_getAppFn(v_a_530_);
v___x_532_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_494_, v_skipTypes_495_, v_skipProofs_496_, v___x_531_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc_n(v_a_533_, 2);
lean_dec_ref(v___x_532_);
v___x_534_ = l_Lean_Expr_getAppNumArgs(v_a_530_);
lean_inc(v___x_534_);
v___x_535_ = l_Lean_Meta_getFunInfoNArgs(v_a_533_, v___x_534_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v_dummy_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref(v___x_535_);
v_dummy_537_ = lean_obj_once(&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4, &l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4_once, _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4);
lean_inc(v___x_534_);
v___x_538_ = lean_mk_array(v___x_534_, v_dummy_537_);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_sub(v___x_534_, v___x_539_);
lean_dec(v___x_534_);
v___x_541_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_530_, v___x_538_, v___x_540_);
v___x_542_ = lean_array_get_size(v___x_541_);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_494_, v_skipTypes_495_, v_skipProofs_496_, v___x_542_, v_a_536_, v_a_528_, v___x_543_, v___x_541_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v_a_536_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref(v___x_544_);
v___x_546_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7));
v___x_547_ = l_Lean_Expr_isConstOf(v_a_533_, v___x_546_);
if (v___x_547_ == 0)
{
v___y_515_ = v_a_545_;
v___y_516_ = v_a_533_;
v___y_517_ = v___x_547_;
goto v___jp_514_;
}
else
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = lean_array_get_size(v_a_545_);
v___x_549_ = lean_nat_dec_eq(v___x_548_, v___x_539_);
v___y_515_ = v_a_545_;
v___y_516_ = v_a_533_;
v___y_517_ = v___x_549_;
goto v___jp_514_;
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec(v_a_533_);
v_a_550_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_544_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_544_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec(v___x_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_530_);
v_a_558_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_535_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_535_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_dec_ref(v_a_530_);
return v___x_532_;
}
}
case 6:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___f_571_; lean_object* v___x_572_; 
lean_dec_ref(v___x_529_);
v___x_566_ = lean_box(v_explicitOnly_494_);
v___x_567_ = lean_box(v_skipTypes_495_);
v___x_568_ = lean_box(v_skipProofs_496_);
v___x_569_ = lean_box(v_a_528_);
v___x_570_ = lean_box(v___y_527_);
v___f_571_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed), 13, 5);
lean_closure_set(v___f_571_, 0, v___x_566_);
lean_closure_set(v___f_571_, 1, v___x_567_);
lean_closure_set(v___f_571_, 2, v___x_568_);
lean_closure_set(v___f_571_, 3, v___x_569_);
lean_closure_set(v___f_571_, 4, v___x_570_);
v___x_572_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_a_530_, v___f_571_, v_a_528_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
return v___x_572_;
}
case 7:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___f_578_; lean_object* v___x_579_; 
lean_dec_ref(v___x_529_);
v___x_573_ = lean_box(v_explicitOnly_494_);
v___x_574_ = lean_box(v_skipTypes_495_);
v___x_575_ = lean_box(v_skipProofs_496_);
v___x_576_ = lean_box(v_a_528_);
v___x_577_ = lean_box(v___y_527_);
v___f_578_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed), 13, 5);
lean_closure_set(v___f_578_, 0, v___x_573_);
lean_closure_set(v___f_578_, 1, v___x_574_);
lean_closure_set(v___f_578_, 2, v___x_575_);
lean_closure_set(v___f_578_, 3, v___x_576_);
lean_closure_set(v___f_578_, 4, v___x_577_);
v___x_579_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_a_530_, v___f_578_, v_a_528_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
return v___x_579_;
}
case 11:
{
lean_object* v_typeName_580_; lean_object* v_idx_581_; lean_object* v_struct_582_; lean_object* v___x_583_; 
lean_dec_ref(v___x_529_);
v_typeName_580_ = lean_ctor_get(v_a_530_, 0);
lean_inc(v_typeName_580_);
v_idx_581_ = lean_ctor_get(v_a_530_, 1);
lean_inc(v_idx_581_);
v_struct_582_ = lean_ctor_get(v_a_530_, 2);
lean_inc_ref(v_struct_582_);
lean_dec_ref(v_a_530_);
v___x_583_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_494_, v_skipTypes_495_, v_skipProofs_496_, v_struct_582_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_592_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_592_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_592_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = l_Lean_mkProj(v_typeName_580_, v_idx_581_, v_a_584_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
else
{
lean_dec(v_idx_581_);
lean_dec(v_typeName_580_);
return v___x_583_;
}
}
default: 
{
lean_dec(v_a_530_);
return v___x_529_;
}
}
}
else
{
return v___x_529_;
}
}
v___jp_593_:
{
uint8_t v___x_594_; 
v___x_594_ = 1;
if (v_skipProofs_496_ == 0)
{
v___y_527_ = v___x_594_;
v_a_528_ = v_skipProofs_496_;
goto v___jp_526_;
}
else
{
lean_object* v___x_595_; 
lean_inc_ref(v_e_493_);
v___x_595_ = l_Lean_Meta_isProof(v_e_493_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_605_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_605_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
uint8_t v___x_600_; 
v___x_600_ = lean_unbox(v_a_596_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; 
lean_del_object(v___x_598_);
v___x_601_ = lean_unbox(v_a_596_);
lean_dec(v_a_596_);
v___y_527_ = v___x_594_;
v_a_528_ = v___x_601_;
goto v___jp_526_;
}
else
{
lean_object* v___x_603_; 
lean_dec(v_a_596_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v_e_493_);
v___x_603_ = v___x_598_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_e_493_);
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
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_e_493_);
v_a_606_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_595_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_595_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed(lean_object* v_e_632_, lean_object* v_explicitOnly_633_, lean_object* v_skipTypes_634_, lean_object* v_skipProofs_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
uint8_t v_explicitOnly_boxed_642_; uint8_t v_skipTypes_boxed_643_; uint8_t v_skipProofs_boxed_644_; lean_object* v_res_645_; 
v_explicitOnly_boxed_642_ = lean_unbox(v_explicitOnly_633_);
v_skipTypes_boxed_643_ = lean_unbox(v_skipTypes_634_);
v_skipProofs_boxed_644_ = lean_unbox(v_skipProofs_635_);
v_res_645_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(v_e_632_, v_explicitOnly_boxed_642_, v_skipTypes_boxed_643_, v_skipProofs_boxed_644_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(uint8_t v_explicitOnly_646_, uint8_t v_skipTypes_647_, uint8_t v_skipProofs_648_, lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_st_ref_get(v_a_650_);
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v___x_656_, v_e_649_);
lean_dec(v___x_656_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___f_661_; lean_object* v___x_662_; 
v___x_658_ = lean_box(v_explicitOnly_646_);
v___x_659_ = lean_box(v_skipTypes_647_);
v___x_660_ = lean_box(v_skipProofs_648_);
lean_inc_ref(v_e_649_);
v___f_661_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed), 10, 4);
lean_closure_set(v___f_661_, 0, v_e_649_);
lean_closure_set(v___f_661_, 1, v___x_658_);
lean_closure_set(v___f_661_, 2, v___x_659_);
lean_closure_set(v___f_661_, 3, v___x_660_);
v___x_662_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v___f_661_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_673_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_673_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_673_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_673_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_667_ = lean_st_ref_take(v_a_650_);
lean_inc(v_a_663_);
v___x_668_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v___x_667_, v_e_649_, v_a_663_);
v___x_669_ = lean_st_ref_set(v_a_650_, v___x_668_);
if (v_isShared_666_ == 0)
{
v___x_671_ = v___x_665_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_663_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_dec_ref(v_e_649_);
return v___x_662_;
}
}
else
{
lean_object* v_val_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v_e_649_);
v_val_674_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_657_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_val_674_);
lean_dec(v___x_657_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 0);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_val_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(uint8_t v_explicitOnly_682_, uint8_t v_skipTypes_683_, uint8_t v_skipProofs_684_, uint8_t v_a_685_, uint8_t v___x_686_, lean_object* v_xs_687_, lean_object* v_b_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_682_, v_skipTypes_683_, v_skipProofs_684_, v_b_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; uint8_t v___x_697_; lean_object* v___x_698_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref(v___x_695_);
v___x_697_ = 1;
v___x_698_ = l_Lean_Meta_mkLambdaFVars(v_xs_687_, v_a_696_, v_a_685_, v___x_686_, v_a_685_, v___x_686_, v___x_697_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
return v___x_698_;
}
else
{
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___boxed(lean_object* v_explicitOnly_699_, lean_object* v_skipTypes_700_, lean_object* v_skipProofs_701_, lean_object* v_e_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
uint8_t v_explicitOnly_boxed_709_; uint8_t v_skipTypes_boxed_710_; uint8_t v_skipProofs_boxed_711_; lean_object* v_res_712_; 
v_explicitOnly_boxed_709_ = lean_unbox(v_explicitOnly_699_);
v_skipTypes_boxed_710_ = lean_unbox(v_skipTypes_700_);
v_skipProofs_boxed_711_ = lean_unbox(v_skipProofs_701_);
v_res_712_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_boxed_709_, v_skipTypes_boxed_710_, v_skipProofs_boxed_711_, v_e_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg___boxed(lean_object* v_explicitOnly_713_, lean_object* v_skipTypes_714_, lean_object* v_skipProofs_715_, lean_object* v_upperBound_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_b_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
uint8_t v_explicitOnly_boxed_727_; uint8_t v_skipTypes_boxed_728_; uint8_t v_skipProofs_boxed_729_; uint8_t v_a_16296__boxed_730_; lean_object* v_res_731_; 
v_explicitOnly_boxed_727_ = lean_unbox(v_explicitOnly_713_);
v_skipTypes_boxed_728_ = lean_unbox(v_skipTypes_714_);
v_skipProofs_boxed_729_ = lean_unbox(v_skipProofs_715_);
v_a_16296__boxed_730_ = lean_unbox(v_a_718_);
v_res_731_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_boxed_727_, v_skipTypes_boxed_728_, v_skipProofs_boxed_729_, v_upperBound_716_, v_a_717_, v_a_16296__boxed_730_, v_a_719_, v_b_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v_a_717_);
lean_dec(v_upperBound_716_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(lean_object* v_00_u03b2_732_, lean_object* v_m_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v_m_733_, v_a_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___boxed(lean_object* v_00_u03b2_736_, lean_object* v_m_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(v_00_u03b2_736_, v_m_737_, v_a_738_);
lean_dec_ref(v_a_738_);
lean_dec_ref(v_m_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(uint8_t v_explicitOnly_740_, uint8_t v_skipTypes_741_, uint8_t v_skipProofs_742_, lean_object* v_upperBound_743_, lean_object* v_a_744_, uint8_t v_a_745_, lean_object* v_inst_746_, lean_object* v_R_747_, lean_object* v_a_748_, lean_object* v_b_749_, lean_object* v_c_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_740_, v_skipTypes_741_, v_skipProofs_742_, v_upperBound_743_, v_a_744_, v_a_745_, v_a_748_, v_b_749_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___boxed(lean_object** _args){
lean_object* v_explicitOnly_758_ = _args[0];
lean_object* v_skipTypes_759_ = _args[1];
lean_object* v_skipProofs_760_ = _args[2];
lean_object* v_upperBound_761_ = _args[3];
lean_object* v_a_762_ = _args[4];
lean_object* v_a_763_ = _args[5];
lean_object* v_inst_764_ = _args[6];
lean_object* v_R_765_ = _args[7];
lean_object* v_a_766_ = _args[8];
lean_object* v_b_767_ = _args[9];
lean_object* v_c_768_ = _args[10];
lean_object* v___y_769_ = _args[11];
lean_object* v___y_770_ = _args[12];
lean_object* v___y_771_ = _args[13];
lean_object* v___y_772_ = _args[14];
lean_object* v___y_773_ = _args[15];
lean_object* v___y_774_ = _args[16];
_start:
{
uint8_t v_explicitOnly_boxed_775_; uint8_t v_skipTypes_boxed_776_; uint8_t v_skipProofs_boxed_777_; uint8_t v_a_16805__boxed_778_; lean_object* v_res_779_; 
v_explicitOnly_boxed_775_ = lean_unbox(v_explicitOnly_758_);
v_skipTypes_boxed_776_ = lean_unbox(v_skipTypes_759_);
v_skipProofs_boxed_777_ = lean_unbox(v_skipProofs_760_);
v_a_16805__boxed_778_ = lean_unbox(v_a_763_);
v_res_779_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(v_explicitOnly_boxed_775_, v_skipTypes_boxed_776_, v_skipProofs_boxed_777_, v_upperBound_761_, v_a_762_, v_a_16805__boxed_778_, v_inst_764_, v_R_765_, v_a_766_, v_b_767_, v_c_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v_a_762_);
lean_dec(v_upperBound_761_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(lean_object* v_00_u03b1_780_, lean_object* v_ref_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_781_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___boxed(lean_object* v_00_u03b1_786_, lean_object* v_ref_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(v_00_u03b1_786_, v_ref_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(lean_object* v_00_u03b1_792_, lean_object* v_x_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___boxed(lean_object* v_00_u03b1_801_, lean_object* v_x_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(v_00_u03b1_801_, v_x_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6(lean_object* v_00_u03b2_810_, lean_object* v_m_811_, lean_object* v_a_812_, lean_object* v_b_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v_m_811_, v_a_812_, v_b_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(lean_object* v_00_u03b2_815_, lean_object* v_a_816_, lean_object* v_x_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_a_816_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_819_, lean_object* v_a_820_, lean_object* v_x_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(v_00_u03b2_819_, v_a_820_, v_x_821_);
lean_dec(v_x_821_);
lean_dec_ref(v_a_820_);
return v_res_822_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8(lean_object* v_00_u03b2_823_, lean_object* v_a_824_, lean_object* v_x_825_){
_start:
{
uint8_t v___x_826_; 
v___x_826_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8___redArg(v_a_824_, v_x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8___boxed(lean_object* v_00_u03b2_827_, lean_object* v_a_828_, lean_object* v_x_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8(v_00_u03b2_827_, v_a_828_, v_x_829_);
lean_dec(v_x_829_);
lean_dec_ref(v_a_828_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(lean_object* v_00_u03b2_832_, lean_object* v_data_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_data_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10(lean_object* v_00_u03b2_835_, lean_object* v_a_836_, lean_object* v_b_837_, lean_object* v_x_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(v_a_836_, v_b_837_, v_x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10(lean_object* v_00_u03b2_840_, lean_object* v_i_841_, lean_object* v_source_842_, lean_object* v_target_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10___redArg(v_i_841_, v_source_842_, v_target_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10_spec__11(lean_object* v_00_u03b2_845_, lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10_spec__11___redArg(v_x_846_, v_x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__0(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_box(0);
v___x_850_ = lean_unsigned_to_nat(16u);
v___x_851_ = lean_mk_array(v___x_850_, v___x_849_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__1(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_obj_once(&l_Lean_Meta_reduce___closed__0, &l_Lean_Meta_reduce___closed__0_once, _init_l_Lean_Meta_reduce___closed__0);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce(lean_object* v_e_855_, uint8_t v_explicitOnly_856_, uint8_t v_skipTypes_857_, uint8_t v_skipProofs_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_obj_once(&l_Lean_Meta_reduce___closed__1, &l_Lean_Meta_reduce___closed__1_once, _init_l_Lean_Meta_reduce___closed__1);
v___x_865_ = lean_st_mk_ref(v___x_864_);
v___x_866_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_856_, v_skipTypes_857_, v_skipProofs_858_, v_e_855_, v___x_865_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_875_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_875_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = lean_st_ref_get(v___x_865_);
lean_dec(v___x_865_);
lean_dec(v___x_871_);
if (v_isShared_870_ == 0)
{
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_867_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_dec(v___x_865_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object* v_e_876_, lean_object* v_explicitOnly_877_, lean_object* v_skipTypes_878_, lean_object* v_skipProofs_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
uint8_t v_explicitOnly_boxed_885_; uint8_t v_skipTypes_boxed_886_; uint8_t v_skipProofs_boxed_887_; lean_object* v_res_888_; 
v_explicitOnly_boxed_885_ = lean_unbox(v_explicitOnly_877_);
v_skipTypes_boxed_886_ = lean_unbox(v_skipTypes_878_);
v_skipProofs_boxed_887_ = lean_unbox(v_skipProofs_879_);
v_res_888_ = l_Lean_Meta_reduce(v_e_876_, v_explicitOnly_boxed_885_, v_skipTypes_boxed_886_, v_skipProofs_boxed_887_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll(lean_object* v_e_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
uint8_t v___x_895_; lean_object* v___x_896_; 
v___x_895_ = 0;
v___x_896_ = l_Lean_Meta_reduce(v_e_889_, v___x_895_, v___x_895_, v___x_895_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll___boxed(lean_object* v_e_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Meta_reduceAll(v_e_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
return v_res_903_;
}
}
lean_object* runtime_initialize_Lean_Meta_FunInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
