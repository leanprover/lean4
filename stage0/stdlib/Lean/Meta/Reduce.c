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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
v___x_3_ = lean_panic_fn(v___x_2_, v_msg_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(lean_object* v_k_4_, lean_object* v___y_5_, lean_object* v_b_6_, lean_object* v_c_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_apply_8(v_k_4_, v_b_6_, v_c_7_, v___y_5_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0___boxed(lean_object* v_k_14_, lean_object* v___y_15_, lean_object* v_b_16_, lean_object* v_c_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg___lam__0(v_k_14_, v___y_15_, v_b_16_, v_c_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(lean_object* v_e_24_, lean_object* v_k_25_, uint8_t v_cleanupAnnotations_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v___f_33_; uint8_t v___x_34_; uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
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
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(lean_object* v_type_80_, lean_object* v_k_81_, uint8_t v_cleanupAnnotations_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___f_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
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
lean_object* v___y_321_; lean_object* v_fileName_330_; lean_object* v_fileMap_331_; lean_object* v_options_332_; lean_object* v_currRecDepth_333_; lean_object* v_maxRecDepth_334_; lean_object* v_ref_335_; lean_object* v_currNamespace_336_; lean_object* v_openDecls_337_; lean_object* v_initHeartbeats_338_; lean_object* v_maxHeartbeats_339_; lean_object* v_quotContext_340_; lean_object* v_currMacroScope_341_; uint8_t v_diag_342_; lean_object* v_cancelTk_x3f_343_; uint8_t v_suppressElabErrors_344_; lean_object* v_inheritedTraceOptions_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_357_; 
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
v_isSharedCheck_357_ = !lean_is_exclusive(v___y_317_);
if (v_isSharedCheck_357_ == 0)
{
v___x_347_ = v___y_317_;
v_isShared_348_ = v_isSharedCheck_357_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_inheritedTraceOptions_345_);
lean_inc(v_cancelTk_x3f_343_);
lean_inc(v_currMacroScope_341_);
lean_inc(v_quotContext_340_);
lean_inc(v_maxHeartbeats_339_);
lean_inc(v_initHeartbeats_338_);
lean_inc(v_openDecls_337_);
lean_inc(v_currNamespace_336_);
lean_inc(v_ref_335_);
lean_inc(v_maxRecDepth_334_);
lean_inc(v_currRecDepth_333_);
lean_inc(v_options_332_);
lean_inc(v_fileMap_331_);
lean_inc(v_fileName_330_);
lean_dec(v___y_317_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_357_;
goto v_resetjp_346_;
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
v_resetjp_346_:
{
uint8_t v___x_349_; 
v___x_349_ = lean_nat_dec_eq(v_currRecDepth_333_, v_maxRecDepth_334_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_add(v_currRecDepth_333_, v___x_350_);
lean_dec(v_currRecDepth_333_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 3, v___x_351_);
v___x_353_ = v___x_347_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_fileName_330_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_fileMap_331_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_options_332_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_maxRecDepth_334_);
lean_ctor_set(v_reuseFailAlloc_355_, 5, v_ref_335_);
lean_ctor_set(v_reuseFailAlloc_355_, 6, v_currNamespace_336_);
lean_ctor_set(v_reuseFailAlloc_355_, 7, v_openDecls_337_);
lean_ctor_set(v_reuseFailAlloc_355_, 8, v_initHeartbeats_338_);
lean_ctor_set(v_reuseFailAlloc_355_, 9, v_maxHeartbeats_339_);
lean_ctor_set(v_reuseFailAlloc_355_, 10, v_quotContext_340_);
lean_ctor_set(v_reuseFailAlloc_355_, 11, v_currMacroScope_341_);
lean_ctor_set(v_reuseFailAlloc_355_, 12, v_cancelTk_x3f_343_);
lean_ctor_set(v_reuseFailAlloc_355_, 13, v_inheritedTraceOptions_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*14, v_diag_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*14 + 1, v_suppressElabErrors_344_);
v___x_353_ = v_reuseFailAlloc_355_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; 
v___x_354_ = lean_apply_6(v_x_313_, v___y_314_, v___y_315_, v___y_316_, v___x_353_, v___y_318_, lean_box(0));
v___y_321_ = v___x_354_;
goto v___jp_320_;
}
}
else
{
lean_object* v___x_356_; 
lean_del_object(v___x_347_);
lean_dec_ref(v_inheritedTraceOptions_345_);
lean_dec(v_cancelTk_x3f_343_);
lean_dec(v_currMacroScope_341_);
lean_dec(v_quotContext_340_);
lean_dec(v_maxHeartbeats_339_);
lean_dec(v_initHeartbeats_338_);
lean_dec(v_openDecls_337_);
lean_dec(v_currNamespace_336_);
lean_dec(v_maxRecDepth_334_);
lean_dec(v_currRecDepth_333_);
lean_dec_ref(v_options_332_);
lean_dec_ref(v_fileMap_331_);
lean_dec_ref(v_fileName_330_);
lean_dec(v___y_318_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v_x_313_);
v___x_356_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_335_);
v___y_321_ = v___x_356_;
goto v___jp_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg___boxed(lean_object* v_x_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
return v_res_365_;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__2));
v___x_370_ = lean_unsigned_to_nat(14u);
v___x_371_ = lean_unsigned_to_nat(22u);
v___x_372_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__1));
v___x_373_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__0));
v___x_374_ = l_mkPanicMessageWithDecl(v___x_373_, v___x_372_, v___x_371_, v___x_370_, v___x_369_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4(void){
_start:
{
lean_object* v___x_375_; lean_object* v_dummy_376_; 
v___x_375_ = lean_box(0);
v_dummy_376_ = l_Lean_Expr_sort___override(v___x_375_);
return v_dummy_376_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(uint8_t v_explicitOnly_377_, uint8_t v_skipTypes_378_, uint8_t v_skipProofs_379_, lean_object* v_upperBound_380_, lean_object* v_a_381_, uint8_t v_a_382_, lean_object* v_a_383_, lean_object* v_b_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_a_392_; uint8_t v___x_413_; 
v___x_413_ = lean_nat_dec_lt(v_a_383_, v_upperBound_380_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec(v_a_383_);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v_b_384_);
return v___x_414_;
}
else
{
lean_object* v_paramInfo_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_paramInfo_415_ = lean_ctor_get(v_a_381_, 0);
v___x_416_ = lean_array_get_size(v_paramInfo_415_);
v___x_417_ = lean_nat_dec_lt(v_a_383_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_array_get_size(v_b_384_);
v___x_419_ = lean_nat_dec_lt(v_a_383_, v___x_418_);
if (v___x_419_ == 0)
{
v_a_392_ = v_b_384_;
goto v___jp_391_;
}
else
{
lean_object* v_v_420_; lean_object* v___x_421_; 
v_v_420_ = lean_array_fget_borrowed(v_b_384_, v_a_383_);
lean_inc(v___y_389_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
lean_inc(v___y_385_);
lean_inc(v_v_420_);
v___x_421_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_377_, v_skipTypes_378_, v_skipProofs_379_, v_v_420_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_423_; lean_object* v_xs_x27_424_; lean_object* v___x_425_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
lean_dec_ref(v___x_421_);
v___x_423_ = lean_box(0);
v_xs_x27_424_ = lean_array_fset(v_b_384_, v_a_383_, v___x_423_);
v___x_425_ = lean_array_fset(v_xs_x27_424_, v_a_383_, v_a_422_);
v_a_392_ = v___x_425_;
goto v___jp_391_;
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v_b_384_);
lean_dec(v_a_383_);
v_a_426_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_421_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_421_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
else
{
if (v_explicitOnly_377_ == 0)
{
goto v___jp_396_;
}
else
{
if (v_a_382_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_array_fget_borrowed(v_paramInfo_415_, v_a_383_);
v___x_435_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_434_);
if (v___x_435_ == 0)
{
v_a_392_ = v_b_384_;
goto v___jp_391_;
}
else
{
goto v___jp_396_;
}
}
else
{
goto v___jp_396_;
}
}
}
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_a_383_, v___x_393_);
lean_dec(v_a_383_);
v_a_383_ = v___x_394_;
v_b_384_ = v_a_392_;
goto _start;
}
v___jp_396_:
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = lean_array_get_size(v_b_384_);
v___x_398_ = lean_nat_dec_lt(v_a_383_, v___x_397_);
if (v___x_398_ == 0)
{
v_a_392_ = v_b_384_;
goto v___jp_391_;
}
else
{
lean_object* v_v_399_; lean_object* v___x_400_; 
v_v_399_ = lean_array_fget_borrowed(v_b_384_, v_a_383_);
lean_inc(v___y_389_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
lean_inc(v___y_385_);
lean_inc(v_v_399_);
v___x_400_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_377_, v_skipTypes_378_, v_skipProofs_379_, v_v_399_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_402_; lean_object* v_xs_x27_403_; lean_object* v___x_404_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref(v___x_400_);
v___x_402_ = lean_box(0);
v_xs_x27_403_ = lean_array_fset(v_b_384_, v_a_383_, v___x_402_);
v___x_404_ = lean_array_fset(v_xs_x27_403_, v_a_383_, v_a_401_);
v_a_392_ = v___x_404_;
goto v___jp_391_;
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v_b_384_);
lean_dec(v_a_383_);
v_a_405_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_400_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_400_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed(lean_object* v_explicitOnly_441_, lean_object* v_skipTypes_442_, lean_object* v_skipProofs_443_, lean_object* v_a_444_, lean_object* v___x_445_, lean_object* v_xs_446_, lean_object* v_b_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
uint8_t v_explicitOnly_boxed_454_; uint8_t v_skipTypes_boxed_455_; uint8_t v_skipProofs_boxed_456_; uint8_t v_a_16929__boxed_457_; uint8_t v___x_16930__boxed_458_; lean_object* v_res_459_; 
v_explicitOnly_boxed_454_ = lean_unbox(v_explicitOnly_441_);
v_skipTypes_boxed_455_ = lean_unbox(v_skipTypes_442_);
v_skipProofs_boxed_456_ = lean_unbox(v_skipProofs_443_);
v_a_16929__boxed_457_ = lean_unbox(v_a_444_);
v___x_16930__boxed_458_ = lean_unbox(v___x_445_);
v_res_459_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(v_explicitOnly_boxed_454_, v_skipTypes_boxed_455_, v_skipProofs_boxed_456_, v_a_16929__boxed_457_, v___x_16930__boxed_458_, v_xs_446_, v_b_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec_ref(v_xs_446_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(uint8_t v_explicitOnly_460_, uint8_t v_skipTypes_461_, uint8_t v_skipProofs_462_, uint8_t v_a_463_, uint8_t v___x_464_, lean_object* v_xs_465_, lean_object* v_b_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; 
lean_inc(v___y_471_);
lean_inc_ref(v___y_470_);
lean_inc(v___y_469_);
lean_inc_ref(v___y_468_);
v___x_473_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_460_, v_skipTypes_461_, v_skipProofs_462_, v_b_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; uint8_t v___x_475_; lean_object* v___x_476_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref(v___x_473_);
v___x_475_ = 1;
v___x_476_ = l_Lean_Meta_mkForallFVars(v_xs_465_, v_a_474_, v_a_463_, v___x_464_, v___x_464_, v___x_475_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
return v___x_476_;
}
else
{
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed(lean_object* v_explicitOnly_477_, lean_object* v_skipTypes_478_, lean_object* v_skipProofs_479_, lean_object* v_a_480_, lean_object* v___x_481_, lean_object* v_xs_482_, lean_object* v_b_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
uint8_t v_explicitOnly_boxed_490_; uint8_t v_skipTypes_boxed_491_; uint8_t v_skipProofs_boxed_492_; uint8_t v_a_16942__boxed_493_; uint8_t v___x_16943__boxed_494_; lean_object* v_res_495_; 
v_explicitOnly_boxed_490_ = lean_unbox(v_explicitOnly_477_);
v_skipTypes_boxed_491_ = lean_unbox(v_skipTypes_478_);
v_skipProofs_boxed_492_ = lean_unbox(v_skipProofs_479_);
v_a_16942__boxed_493_ = lean_unbox(v_a_480_);
v___x_16943__boxed_494_ = lean_unbox(v___x_481_);
v_res_495_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1(v_explicitOnly_boxed_490_, v_skipTypes_boxed_491_, v_skipProofs_boxed_492_, v_a_16942__boxed_493_, v___x_16943__boxed_494_, v_xs_482_, v_b_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec_ref(v_xs_482_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(lean_object* v_e_496_, uint8_t v_explicitOnly_497_, uint8_t v_skipTypes_498_, uint8_t v_skipProofs_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_512_; lean_object* v___y_518_; lean_object* v___y_519_; uint8_t v___y_520_; uint8_t v___y_530_; uint8_t v_a_531_; 
if (v_skipTypes_498_ == 0)
{
goto v___jp_596_;
}
else
{
lean_object* v___x_617_; 
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc_ref(v_e_496_);
v___x_617_ = l_Lean_Meta_isType(v_e_496_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_626_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_626_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint8_t v___x_622_; 
v___x_622_ = lean_unbox(v_a_618_);
lean_dec(v_a_618_);
if (v___x_622_ == 0)
{
lean_del_object(v___x_620_);
goto v___jp_596_;
}
else
{
lean_object* v___x_624_; 
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v_e_496_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_e_496_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v_e_496_);
v_a_627_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_617_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_617_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
v___jp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = l_Lean_mkAppN(v___y_507_, v___y_508_);
lean_dec_ref(v___y_508_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_add(v___y_512_, v___x_513_);
lean_dec(v___y_512_);
v___x_515_ = l_Lean_mkRawNatLit(v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
v___jp_517_:
{
if (v___y_520_ == 0)
{
v___y_507_ = v___y_518_;
v___y_508_ = v___y_519_;
goto v___jp_506_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_521_ = l_Lean_instInhabitedExpr;
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_array_get_borrowed(v___x_521_, v___y_519_, v___x_522_);
v___x_524_ = l_Lean_Expr_isRawNatLit(v___x_523_);
if (v___x_524_ == 0)
{
v___y_507_ = v___y_518_;
v___y_508_ = v___y_519_;
goto v___jp_506_;
}
else
{
lean_object* v___x_525_; 
lean_inc(v___x_523_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v___y_518_);
v___x_525_ = l_Lean_Expr_rawNatLit_x3f(v___x_523_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3, &l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__3);
v___x_527_ = l_panic___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__1(v___x_526_);
v___y_512_ = v___x_527_;
goto v___jp_511_;
}
else
{
lean_object* v_val_528_; 
v_val_528_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_val_528_);
lean_dec_ref(v___x_525_);
v___y_512_ = v_val_528_;
goto v___jp_511_;
}
}
}
}
v___jp_529_:
{
lean_object* v___x_532_; 
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
v___x_532_ = lean_whnf(v_e_496_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
switch(lean_obj_tag(v_a_533_))
{
case 5:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec_ref(v___x_532_);
v___x_534_ = l_Lean_Expr_getAppFn(v_a_533_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
v___x_535_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_497_, v_skipTypes_498_, v_skipProofs_499_, v___x_534_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_dec_ref(v___x_535_);
v___x_537_ = l_Lean_Expr_getAppNumArgs(v_a_533_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___x_537_);
lean_inc(v_a_536_);
v___x_538_ = l_Lean_Meta_getFunInfoNArgs(v_a_536_, v___x_537_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v_dummy_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref(v___x_538_);
v_dummy_540_ = lean_obj_once(&l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4, &l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4_once, _init_l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__4);
lean_inc(v___x_537_);
v___x_541_ = lean_mk_array(v___x_537_, v_dummy_540_);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_sub(v___x_537_, v___x_542_);
lean_dec(v___x_537_);
v___x_544_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_533_, v___x_541_, v___x_543_);
v___x_545_ = lean_array_get_size(v___x_544_);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_497_, v_skipTypes_498_, v_skipProofs_499_, v___x_545_, v_a_539_, v_a_531_, v___x_546_, v___x_544_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v_a_539_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref(v___x_547_);
v___x_549_ = ((lean_object*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___closed__7));
v___x_550_ = l_Lean_Expr_isConstOf(v_a_536_, v___x_549_);
if (v___x_550_ == 0)
{
v___y_518_ = v_a_536_;
v___y_519_ = v_a_548_;
v___y_520_ = v___x_550_;
goto v___jp_517_;
}
else
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = lean_array_get_size(v_a_548_);
v___x_552_ = lean_nat_dec_eq(v___x_551_, v___x_542_);
v___y_518_ = v_a_536_;
v___y_519_ = v_a_548_;
v___y_520_ = v___x_552_;
goto v___jp_517_;
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec(v_a_536_);
v_a_553_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_547_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_547_);
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
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v___x_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_533_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
v_a_561_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_538_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_538_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_dec_ref(v_a_533_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
return v___x_535_;
}
}
case 6:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___f_574_; lean_object* v___x_575_; 
lean_dec_ref(v___x_532_);
v___x_569_ = lean_box(v_explicitOnly_497_);
v___x_570_ = lean_box(v_skipTypes_498_);
v___x_571_ = lean_box(v_skipProofs_499_);
v___x_572_ = lean_box(v_a_531_);
v___x_573_ = lean_box(v___y_530_);
v___f_574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0___boxed), 13, 5);
lean_closure_set(v___f_574_, 0, v___x_569_);
lean_closure_set(v___f_574_, 1, v___x_570_);
lean_closure_set(v___f_574_, 2, v___x_571_);
lean_closure_set(v___f_574_, 3, v___x_572_);
lean_closure_set(v___f_574_, 4, v___x_573_);
v___x_575_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__3___redArg(v_a_533_, v___f_574_, v_a_531_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_575_;
}
case 7:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___f_581_; lean_object* v___x_582_; 
lean_dec_ref(v___x_532_);
v___x_576_ = lean_box(v_explicitOnly_497_);
v___x_577_ = lean_box(v_skipTypes_498_);
v___x_578_ = lean_box(v_skipProofs_499_);
v___x_579_ = lean_box(v_a_531_);
v___x_580_ = lean_box(v___y_530_);
v___f_581_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__1___boxed), 13, 5);
lean_closure_set(v___f_581_, 0, v___x_576_);
lean_closure_set(v___f_581_, 1, v___x_577_);
lean_closure_set(v___f_581_, 2, v___x_578_);
lean_closure_set(v___f_581_, 3, v___x_579_);
lean_closure_set(v___f_581_, 4, v___x_580_);
v___x_582_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__4___redArg(v_a_533_, v___f_581_, v_a_531_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_582_;
}
case 11:
{
lean_object* v_typeName_583_; lean_object* v_idx_584_; lean_object* v_struct_585_; lean_object* v___x_586_; 
lean_dec_ref(v___x_532_);
v_typeName_583_ = lean_ctor_get(v_a_533_, 0);
lean_inc(v_typeName_583_);
v_idx_584_ = lean_ctor_get(v_a_533_, 1);
lean_inc(v_idx_584_);
v_struct_585_ = lean_ctor_get(v_a_533_, 2);
lean_inc_ref(v_struct_585_);
lean_dec_ref(v_a_533_);
v___x_586_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_497_, v_skipTypes_498_, v_skipProofs_499_, v_struct_585_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_595_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_595_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = l_Lean_mkProj(v_typeName_583_, v_idx_584_, v_a_587_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
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
lean_dec(v_idx_584_);
lean_dec(v_typeName_583_);
return v___x_586_;
}
}
default: 
{
lean_dec(v_a_533_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
return v___x_532_;
}
}
}
else
{
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
return v___x_532_;
}
}
v___jp_596_:
{
uint8_t v___x_597_; 
v___x_597_ = 1;
if (v_skipProofs_499_ == 0)
{
v___y_530_ = v___x_597_;
v_a_531_ = v_skipProofs_499_;
goto v___jp_529_;
}
else
{
lean_object* v___x_598_; 
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc_ref(v_e_496_);
v___x_598_ = l_Lean_Meta_isProof(v_e_496_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_608_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_608_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint8_t v___x_603_; 
v___x_603_ = lean_unbox(v_a_599_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; 
lean_del_object(v___x_601_);
v___x_604_ = lean_unbox(v_a_599_);
lean_dec(v_a_599_);
v___y_530_ = v___x_597_;
v_a_531_ = v___x_604_;
goto v___jp_529_;
}
else
{
lean_object* v___x_606_; 
lean_dec(v_a_599_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v_e_496_);
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_e_496_);
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
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v_e_496_);
v_a_609_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_598_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_598_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed(lean_object* v_e_635_, lean_object* v_explicitOnly_636_, lean_object* v_skipTypes_637_, lean_object* v_skipProofs_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
uint8_t v_explicitOnly_boxed_645_; uint8_t v_skipTypes_boxed_646_; uint8_t v_skipProofs_boxed_647_; lean_object* v_res_648_; 
v_explicitOnly_boxed_645_ = lean_unbox(v_explicitOnly_636_);
v_skipTypes_boxed_646_ = lean_unbox(v_skipTypes_637_);
v_skipProofs_boxed_647_ = lean_unbox(v_skipProofs_638_);
v_res_648_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2(v_e_635_, v_explicitOnly_boxed_645_, v_skipTypes_boxed_646_, v_skipProofs_boxed_647_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(uint8_t v_explicitOnly_649_, uint8_t v_skipTypes_650_, uint8_t v_skipProofs_651_, lean_object* v_e_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_st_ref_get(v_a_653_);
v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v___x_659_, v_e_652_);
lean_dec(v___x_659_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___f_664_; lean_object* v___x_665_; 
v___x_661_ = lean_box(v_explicitOnly_649_);
v___x_662_ = lean_box(v_skipTypes_650_);
v___x_663_ = lean_box(v_skipProofs_651_);
lean_inc_ref(v_e_652_);
v___f_664_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__2___boxed), 10, 4);
lean_closure_set(v___f_664_, 0, v_e_652_);
lean_closure_set(v___f_664_, 1, v___x_661_);
lean_closure_set(v___f_664_, 2, v___x_662_);
lean_closure_set(v___f_664_, 3, v___x_663_);
lean_inc(v_a_653_);
v___x_665_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v___f_664_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_676_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_676_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_670_ = lean_st_ref_take(v_a_653_);
lean_inc(v_a_666_);
v___x_671_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v___x_670_, v_e_652_, v_a_666_);
v___x_672_ = lean_st_ref_set(v_a_653_, v___x_671_);
lean_dec(v_a_653_);
if (v_isShared_669_ == 0)
{
v___x_674_ = v___x_668_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_666_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
lean_dec(v_a_653_);
lean_dec_ref(v_e_652_);
return v___x_665_;
}
}
else
{
lean_object* v_val_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_e_652_);
v_val_677_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_660_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_val_677_);
lean_dec(v___x_660_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set_tag(v___x_679_, 0);
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_val_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___lam__0(uint8_t v_explicitOnly_685_, uint8_t v_skipTypes_686_, uint8_t v_skipProofs_687_, uint8_t v_a_688_, uint8_t v___x_689_, lean_object* v_xs_690_, lean_object* v_b_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; 
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
v___x_698_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_685_, v_skipTypes_686_, v_skipProofs_687_, v_b_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; uint8_t v___x_700_; lean_object* v___x_701_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_698_);
v___x_700_ = 1;
v___x_701_ = l_Lean_Meta_mkLambdaFVars(v_xs_690_, v_a_699_, v_a_688_, v___x_689_, v_a_688_, v___x_689_, v___x_700_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v___x_701_;
}
else
{
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit___boxed(lean_object* v_explicitOnly_702_, lean_object* v_skipTypes_703_, lean_object* v_skipProofs_704_, lean_object* v_e_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
uint8_t v_explicitOnly_boxed_712_; uint8_t v_skipTypes_boxed_713_; uint8_t v_skipProofs_boxed_714_; lean_object* v_res_715_; 
v_explicitOnly_boxed_712_ = lean_unbox(v_explicitOnly_702_);
v_skipTypes_boxed_713_ = lean_unbox(v_skipTypes_703_);
v_skipProofs_boxed_714_ = lean_unbox(v_skipProofs_704_);
v_res_715_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_boxed_712_, v_skipTypes_boxed_713_, v_skipProofs_boxed_714_, v_e_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg___boxed(lean_object* v_explicitOnly_716_, lean_object* v_skipTypes_717_, lean_object* v_skipProofs_718_, lean_object* v_upperBound_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_b_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
uint8_t v_explicitOnly_boxed_730_; uint8_t v_skipTypes_boxed_731_; uint8_t v_skipProofs_boxed_732_; uint8_t v_a_16975__boxed_733_; lean_object* v_res_734_; 
v_explicitOnly_boxed_730_ = lean_unbox(v_explicitOnly_716_);
v_skipTypes_boxed_731_ = lean_unbox(v_skipTypes_717_);
v_skipProofs_boxed_732_ = lean_unbox(v_skipProofs_718_);
v_a_16975__boxed_733_ = lean_unbox(v_a_721_);
v_res_734_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_boxed_730_, v_skipTypes_boxed_731_, v_skipProofs_boxed_732_, v_upperBound_719_, v_a_720_, v_a_16975__boxed_733_, v_a_722_, v_b_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec_ref(v_a_720_);
lean_dec(v_upperBound_719_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(lean_object* v_00_u03b2_735_, lean_object* v_m_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___redArg(v_m_736_, v_a_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0___boxed(lean_object* v_00_u03b2_739_, lean_object* v_m_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0(v_00_u03b2_739_, v_m_740_, v_a_741_);
lean_dec_ref(v_a_741_);
lean_dec_ref(v_m_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(uint8_t v_explicitOnly_743_, uint8_t v_skipTypes_744_, uint8_t v_skipProofs_745_, lean_object* v_upperBound_746_, lean_object* v_a_747_, uint8_t v_a_748_, lean_object* v_inst_749_, lean_object* v_R_750_, lean_object* v_a_751_, lean_object* v_b_752_, lean_object* v_c_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___redArg(v_explicitOnly_743_, v_skipTypes_744_, v_skipProofs_745_, v_upperBound_746_, v_a_747_, v_a_748_, v_a_751_, v_b_752_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2___boxed(lean_object** _args){
lean_object* v_explicitOnly_761_ = _args[0];
lean_object* v_skipTypes_762_ = _args[1];
lean_object* v_skipProofs_763_ = _args[2];
lean_object* v_upperBound_764_ = _args[3];
lean_object* v_a_765_ = _args[4];
lean_object* v_a_766_ = _args[5];
lean_object* v_inst_767_ = _args[6];
lean_object* v_R_768_ = _args[7];
lean_object* v_a_769_ = _args[8];
lean_object* v_b_770_ = _args[9];
lean_object* v_c_771_ = _args[10];
lean_object* v___y_772_ = _args[11];
lean_object* v___y_773_ = _args[12];
lean_object* v___y_774_ = _args[13];
lean_object* v___y_775_ = _args[14];
lean_object* v___y_776_ = _args[15];
lean_object* v___y_777_ = _args[16];
_start:
{
uint8_t v_explicitOnly_boxed_778_; uint8_t v_skipTypes_boxed_779_; uint8_t v_skipProofs_boxed_780_; uint8_t v_a_17494__boxed_781_; lean_object* v_res_782_; 
v_explicitOnly_boxed_778_ = lean_unbox(v_explicitOnly_761_);
v_skipTypes_boxed_779_ = lean_unbox(v_skipTypes_762_);
v_skipProofs_boxed_780_ = lean_unbox(v_skipProofs_763_);
v_a_17494__boxed_781_ = lean_unbox(v_a_766_);
v_res_782_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__2(v_explicitOnly_boxed_778_, v_skipTypes_boxed_779_, v_skipProofs_boxed_780_, v_upperBound_764_, v_a_765_, v_a_17494__boxed_781_, v_inst_767_, v_R_768_, v_a_769_, v_b_770_, v_c_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec_ref(v_a_765_);
lean_dec(v_upperBound_764_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(lean_object* v_00_u03b1_783_, lean_object* v_ref_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___redArg(v_ref_784_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6___boxed(lean_object* v_00_u03b1_789_, lean_object* v_ref_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5_spec__6(v_00_u03b1_789_, v_ref_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(lean_object* v_00_u03b1_795_, lean_object* v_x_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___redArg(v_x_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5___boxed(lean_object* v_00_u03b1_804_, lean_object* v_x_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__5(v_00_u03b1_804_, v_x_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6(lean_object* v_00_u03b2_813_, lean_object* v_m_814_, lean_object* v_a_815_, lean_object* v_b_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6___redArg(v_m_814_, v_a_815_, v_b_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(lean_object* v_00_u03b2_818_, lean_object* v_a_819_, lean_object* v_x_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___redArg(v_a_819_, v_x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_822_, lean_object* v_a_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__0_spec__0(v_00_u03b2_822_, v_a_823_, v_x_824_);
lean_dec(v_x_824_);
lean_dec_ref(v_a_823_);
return v_res_825_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8(lean_object* v_00_u03b2_826_, lean_object* v_a_827_, lean_object* v_x_828_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8___redArg(v_a_827_, v_x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8___boxed(lean_object* v_00_u03b2_830_, lean_object* v_a_831_, lean_object* v_x_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__8(v_00_u03b2_830_, v_a_831_, v_x_832_);
lean_dec(v_x_832_);
lean_dec_ref(v_a_831_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9(lean_object* v_00_u03b2_835_, lean_object* v_data_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9___redArg(v_data_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10(lean_object* v_00_u03b2_838_, lean_object* v_a_839_, lean_object* v_b_840_, lean_object* v_x_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__10___redArg(v_a_839_, v_b_840_, v_x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10(lean_object* v_00_u03b2_843_, lean_object* v_i_844_, lean_object* v_source_845_, lean_object* v_target_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10___redArg(v_i_844_, v_source_845_, v_target_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10_spec__11(lean_object* v_00_u03b2_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit_spec__6_spec__9_spec__10_spec__11___redArg(v_x_849_, v_x_850_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__0(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_box(0);
v___x_853_ = lean_unsigned_to_nat(16u);
v___x_854_ = lean_mk_array(v___x_853_, v___x_852_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Meta_reduce___closed__1(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_obj_once(&l_Lean_Meta_reduce___closed__0, &l_Lean_Meta_reduce___closed__0_once, _init_l_Lean_Meta_reduce___closed__0);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___x_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce(lean_object* v_e_858_, uint8_t v_explicitOnly_859_, uint8_t v_skipTypes_860_, uint8_t v_skipProofs_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = lean_obj_once(&l_Lean_Meta_reduce___closed__1, &l_Lean_Meta_reduce___closed__1_once, _init_l_Lean_Meta_reduce___closed__1);
v___x_868_ = lean_st_mk_ref(v___x_867_);
lean_inc(v___x_868_);
v___x_869_ = l___private_Lean_Meta_Reduce_0__Lean_Meta_reduce_visit(v_explicitOnly_859_, v_skipTypes_860_, v_skipProofs_861_, v_e_858_, v___x_868_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_878_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_878_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_878_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = lean_st_ref_get(v___x_868_);
lean_dec(v___x_868_);
lean_dec(v___x_874_);
if (v_isShared_873_ == 0)
{
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_870_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_dec(v___x_868_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object* v_e_879_, lean_object* v_explicitOnly_880_, lean_object* v_skipTypes_881_, lean_object* v_skipProofs_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
uint8_t v_explicitOnly_boxed_888_; uint8_t v_skipTypes_boxed_889_; uint8_t v_skipProofs_boxed_890_; lean_object* v_res_891_; 
v_explicitOnly_boxed_888_ = lean_unbox(v_explicitOnly_880_);
v_skipTypes_boxed_889_ = lean_unbox(v_skipTypes_881_);
v_skipProofs_boxed_890_ = lean_unbox(v_skipProofs_882_);
v_res_891_ = l_Lean_Meta_reduce(v_e_879_, v_explicitOnly_boxed_888_, v_skipTypes_boxed_889_, v_skipProofs_boxed_890_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll(lean_object* v_e_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
uint8_t v___x_898_; lean_object* v___x_899_; 
v___x_898_ = 0;
v___x_899_ = l_Lean_Meta_reduce(v_e_892_, v___x_898_, v___x_898_, v___x_898_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll___boxed(lean_object* v_e_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Meta_reduceAll(v_e_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
return v_res_906_;
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
