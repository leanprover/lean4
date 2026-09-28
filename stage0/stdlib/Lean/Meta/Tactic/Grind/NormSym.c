// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.NormSym
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.Simp.Theorems import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.SimpUtil import Lean.Meta.Sym.Simp.Main import Lean.Meta.Sym.Simp.Simproc import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.EvalGround import Lean.Meta.Sym.Simp.Arith import Lean.Meta.Sym.Simp.Discharger import Lean.Meta.Tactic.Grind.NormSymProcs import Lean.Meta.Sym.Simp.Reduce import Lean.Meta.Sym.Util import Lean.Meta.DiscrTree
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
lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpNatRel___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpArith(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_pushNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_reduceProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_reduceMatcher___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_simpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "norm"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 82, 242, 154, 5, 26, 236, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 98, 249, 2, 230, 183, 10, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NormSym"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 72, 244, 41, 173, 163, 38, 111)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(91, 151, 249, 251, 61, 22, 245, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 142, 119, 132, 202, 140, 88, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 173, 88, 87, 165, 240, 57, 38)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 116, 171, 33, 214, 249, 3, 177)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 40, 131, 37, 223, 140, 233, 156)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(80, 14, 51, 186, 93, 225, 179, 117)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 155, 24, 227, 140, 86, 177, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(121, 19, 117, 45, 106, 253, 56, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(208, 240, 80, 117, 35, 134, 153, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 187, 158, 200, 39, 234, 175, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 145, 68, 235, 61, 196, 216, 66)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(448808965) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(12, 155, 41, 39, 188, 96, 232, 50)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 146, 66, 68, 231, 69, 175, 2)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(35, 59, 192, 107, 253, 50, 81, 198)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(38, 125, 76, 15, 154, 46, 129, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "skipping `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`, not a global declaration"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "skipping unfold `"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymTheorems___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkNormSymTheorems___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_mkNormSymTheorems___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_mkNormSymTheorems___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__3;
static const lean_array_object l_Lean_Meta_Grind_mkNormSymTheorems___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_mkNormSymTheorems___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_mkNormSymTheorems___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_le_eq"};
static const lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymTheorems___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__5_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymTheorems___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__6_value),LEAN_SCALAR_PTR_LITERAL(235, 23, 140, 144, 182, 73, 3, 60)}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_mkNormSymTheorems___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymTheorems___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__8_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymTheorems___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__6_value),LEAN_SCALAR_PTR_LITERAL(77, 74, 162, 108, 148, 71, 165, 71)}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymTheorems___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymTheorems___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__10_value)}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymTheorems___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymMethods___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___lam__8___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__0_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__2___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__3___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__2_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__4___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__3_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__4_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__5_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__6_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__7___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__6_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__7_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__8___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__7_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__8_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__9_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__1_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__10_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__1_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_normSym___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_normSym___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_normSym___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_normSym___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normSym___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_normSym___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normSym___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_83_ = 0;
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_85_ = l_Lean_registerTraceClass(v___x_82_, v___x_83_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2____boxed(lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_();
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(lean_object* v_thms_88_, lean_object* v_____r_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v_thms_88_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0___boxed(lean_object* v_thms_97_, lean_object* v_____r_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(v_thms_97_, v_____r_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0(lean_object* v_msgData_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; lean_object* v_env_112_; lean_object* v___x_113_; lean_object* v_toCold_114_; lean_object* v_mctx_115_; lean_object* v_lctx_116_; lean_object* v_options_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_111_ = lean_st_ref_get(v___y_109_);
v_env_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref(v_env_112_);
lean_dec(v___x_111_);
v___x_113_ = lean_st_ref_get(v___y_107_);
v_toCold_114_ = lean_ctor_get(v___y_108_, 0);
v_mctx_115_ = lean_ctor_get(v___x_113_, 0);
lean_inc_ref(v_mctx_115_);
lean_dec(v___x_113_);
v_lctx_116_ = lean_ctor_get(v___y_106_, 2);
v_options_117_ = lean_ctor_get(v_toCold_114_, 2);
lean_inc_ref(v_options_117_);
lean_inc_ref(v_lctx_116_);
v___x_118_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_118_, 0, v_env_112_);
lean_ctor_set(v___x_118_, 1, v_mctx_115_);
lean_ctor_set(v___x_118_, 2, v_lctx_116_);
lean_ctor_set(v___x_118_, 3, v_options_117_);
v___x_119_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_msgData_105_);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0___boxed(lean_object* v_msgData_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0(v_msgData_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0(void){
_start:
{
lean_object* v___x_128_; double v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_float_of_nat(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(lean_object* v_cls_133_, lean_object* v_msg_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_ref_140_; lean_object* v___x_141_; lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_187_; 
v_ref_140_ = lean_ctor_get(v___y_137_, 2);
v___x_141_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0(v_msg_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
v_a_142_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_187_ == 0)
{
v___x_144_ = v___x_141_;
v_isShared_145_ = v_isSharedCheck_187_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_187_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v_traceState_147_; lean_object* v_env_148_; lean_object* v_nextMacroScope_149_; lean_object* v_ngen_150_; lean_object* v_auxDeclNGen_151_; lean_object* v_cache_152_; lean_object* v_recordedDeps_153_; lean_object* v_messages_154_; lean_object* v_infoState_155_; lean_object* v_snapshotTasks_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_186_; 
v___x_146_ = lean_st_ref_take(v___y_138_);
v_traceState_147_ = lean_ctor_get(v___x_146_, 4);
v_env_148_ = lean_ctor_get(v___x_146_, 0);
v_nextMacroScope_149_ = lean_ctor_get(v___x_146_, 1);
v_ngen_150_ = lean_ctor_get(v___x_146_, 2);
v_auxDeclNGen_151_ = lean_ctor_get(v___x_146_, 3);
v_cache_152_ = lean_ctor_get(v___x_146_, 5);
v_recordedDeps_153_ = lean_ctor_get(v___x_146_, 6);
v_messages_154_ = lean_ctor_get(v___x_146_, 7);
v_infoState_155_ = lean_ctor_get(v___x_146_, 8);
v_snapshotTasks_156_ = lean_ctor_get(v___x_146_, 9);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_186_ == 0)
{
v___x_158_ = v___x_146_;
v_isShared_159_ = v_isSharedCheck_186_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_snapshotTasks_156_);
lean_inc(v_infoState_155_);
lean_inc(v_messages_154_);
lean_inc(v_recordedDeps_153_);
lean_inc(v_cache_152_);
lean_inc(v_traceState_147_);
lean_inc(v_auxDeclNGen_151_);
lean_inc(v_ngen_150_);
lean_inc(v_nextMacroScope_149_);
lean_inc(v_env_148_);
lean_dec(v___x_146_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_186_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
uint64_t v_tid_160_; lean_object* v_traces_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_185_; 
v_tid_160_ = lean_ctor_get_uint64(v_traceState_147_, sizeof(void*)*1);
v_traces_161_ = lean_ctor_get(v_traceState_147_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_traceState_147_);
if (v_isSharedCheck_185_ == 0)
{
v___x_163_ = v_traceState_147_;
v_isShared_164_ = v_isSharedCheck_185_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_traces_161_);
lean_dec(v_traceState_147_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_185_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_166_; double v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_165_ = lean_box(0);
v___x_166_ = lean_box(0);
v___x_167_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0);
v___x_168_ = 0;
v___x_169_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__1));
v___x_170_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_170_, 0, v_cls_133_);
lean_ctor_set(v___x_170_, 1, v___x_166_);
lean_ctor_set(v___x_170_, 2, v___x_169_);
lean_ctor_set_float(v___x_170_, sizeof(void*)*3, v___x_167_);
lean_ctor_set_float(v___x_170_, sizeof(void*)*3 + 8, v___x_167_);
lean_ctor_set_uint8(v___x_170_, sizeof(void*)*3 + 16, v___x_168_);
v___x_171_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__2));
v___x_172_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v_a_142_);
lean_ctor_set(v___x_172_, 2, v___x_171_);
lean_inc(v_ref_140_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v_ref_140_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = l_Lean_PersistentArray_push___redArg(v_traces_161_, v___x_173_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_174_);
v___x_176_ = v___x_163_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_174_);
lean_ctor_set_uint64(v_reuseFailAlloc_184_, sizeof(void*)*1, v_tid_160_);
v___x_176_ = v_reuseFailAlloc_184_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_178_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 4, v___x_176_);
v___x_178_ = v___x_158_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_env_148_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_nextMacroScope_149_);
lean_ctor_set(v_reuseFailAlloc_183_, 2, v_ngen_150_);
lean_ctor_set(v_reuseFailAlloc_183_, 3, v_auxDeclNGen_151_);
lean_ctor_set(v_reuseFailAlloc_183_, 4, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_183_, 5, v_cache_152_);
lean_ctor_set(v_reuseFailAlloc_183_, 6, v_recordedDeps_153_);
lean_ctor_set(v_reuseFailAlloc_183_, 7, v_messages_154_);
lean_ctor_set(v_reuseFailAlloc_183_, 8, v_infoState_155_);
lean_ctor_set(v_reuseFailAlloc_183_, 9, v_snapshotTasks_156_);
v___x_178_ = v_reuseFailAlloc_183_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_st_ref_put(v___y_138_, v___x_178_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_165_);
v___x_181_ = v___x_144_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_165_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___boxed(lean_object* v_cls_188_, lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v_cls_188_, v_msg_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_195_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__1));
v___x_201_ = l_Lean_Name_append(v___x_200_, v___x_199_);
return v___x_201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__3));
v___x_204_ = l_Lean_stringToMessageData(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__5));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__7));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(lean_object* v_thms_211_, lean_object* v_thm_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___y_219_; lean_object* v_proof_229_; 
v_proof_229_ = lean_ctor_get(v_thm_212_, 2);
if (lean_obj_tag(v_proof_229_) == 4)
{
lean_object* v_declName_230_; lean_object* v___x_234_; 
lean_inc_ref(v_proof_229_);
lean_dec_ref(v_thm_212_);
v_declName_230_ = lean_ctor_get(v_proof_229_, 0);
lean_inc_n(v_declName_230_, 2);
lean_dec_ref_known(v_proof_229_, 2);
v___x_234_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_230_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_declName_230_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_thms_211_, v_a_235_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
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
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_280_; 
v_a_244_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_280_ == 0)
{
v___x_246_ = v___x_234_;
v_isShared_247_ = v_isSharedCheck_280_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_234_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_280_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v___y_249_; uint8_t v___x_278_; 
v___x_278_ = l_Lean_Exception_isInterrupt(v_a_244_);
if (v___x_278_ == 0)
{
uint8_t v___x_279_; 
lean_inc(v_a_244_);
v___x_279_ = l_Lean_Exception_isRuntime(v_a_244_);
v___y_249_ = v___x_279_;
goto v___jp_248_;
}
else
{
v___y_249_ = v___x_278_;
goto v___jp_248_;
}
v___jp_248_:
{
if (v___y_249_ == 0)
{
lean_object* v_toCold_250_; lean_object* v_options_251_; uint8_t v_hasTrace_252_; 
lean_del_object(v___x_246_);
v_toCold_250_ = lean_ctor_get(v_a_215_, 0);
v_options_251_ = lean_ctor_get(v_toCold_250_, 2);
v_hasTrace_252_ = lean_ctor_get_uint8(v_options_251_, sizeof(void*)*1);
if (v_hasTrace_252_ == 0)
{
lean_dec(v_a_244_);
lean_dec(v_declName_230_);
goto v___jp_231_;
}
else
{
lean_object* v_inheritedTraceOptions_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_inheritedTraceOptions_253_ = lean_ctor_get(v_toCold_250_, 11);
v___x_254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_255_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2);
v___x_256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_253_, v_options_251_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec(v_a_244_);
lean_dec(v_declName_230_);
goto v___jp_231_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4);
v___x_258_ = l_Lean_MessageData_ofConstName(v_declName_230_, v___y_249_);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = l_Lean_Exception_toMessageData(v_a_244_);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v___x_254_, v___x_263_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
v___x_266_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(v_thms_211_, v_a_265_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
v___y_219_ = v___x_266_;
goto v___jp_218_;
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec_ref(v_thms_211_);
v_a_267_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_264_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_264_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
}
else
{
lean_object* v___x_276_; 
lean_dec(v_declName_230_);
lean_dec_ref(v_thms_211_);
if (v_isShared_247_ == 0)
{
v___x_276_ = v___x_246_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_244_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
v___jp_231_:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_box(0);
v___x_233_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(v_thms_211_, v___x_232_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
v___y_219_ = v___x_233_;
goto v___jp_218_;
}
}
else
{
lean_object* v_toCold_281_; lean_object* v_options_282_; uint8_t v_hasTrace_283_; 
v_toCold_281_ = lean_ctor_get(v_a_215_, 0);
v_options_282_ = lean_ctor_get(v_toCold_281_, 2);
v_hasTrace_283_ = lean_ctor_get_uint8(v_options_282_, sizeof(void*)*1);
if (v_hasTrace_283_ == 0)
{
lean_object* v___x_284_; 
lean_dec_ref(v_thm_212_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v_thms_211_);
return v___x_284_;
}
else
{
lean_object* v_origin_285_; lean_object* v_inheritedTraceOptions_286_; lean_object* v_cls_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_origin_285_ = lean_ctor_get(v_thm_212_, 4);
lean_inc_ref(v_origin_285_);
lean_dec_ref(v_thm_212_);
v_inheritedTraceOptions_286_ = lean_ctor_get(v_toCold_281_, 11);
v_cls_287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_288_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2);
v___x_289_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_286_, v_options_282_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
lean_dec_ref(v_origin_285_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v_thms_211_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_291_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4);
v___x_292_ = l_Lean_Meta_Origin_key(v_origin_285_);
lean_dec_ref(v_origin_285_);
v___x_293_ = l_Lean_MessageData_ofName(v___x_292_);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_291_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v_cls_287_, v___x_296_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v___x_297_, 0);
lean_dec(v_unused_305_);
v___x_299_ = v___x_297_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_dec(v___x_297_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v_thms_211_);
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_thms_211_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec_ref(v_thms_211_);
v_a_306_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_297_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_297_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
}
v___jp_218_:
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_a_220_ = lean_ctor_get(v___y_219_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___y_219_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v___y_219_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___y_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_a_224_; lean_object* v___x_226_; 
v_a_224_ = lean_ctor_get(v_a_220_, 0);
lean_inc(v_a_224_);
lean_dec(v_a_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v_a_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___boxed(lean_object* v_thms_314_, lean_object* v_thm_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_thms_314_, v_thm_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(lean_object* v_as_322_, size_t v_i_323_, size_t v_stop_324_, lean_object* v_b_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_eq(v_i_323_, v_stop_324_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; size_t v___x_329_; size_t v___x_330_; 
v___x_327_ = lean_array_uget_borrowed(v_as_322_, v_i_323_);
lean_inc(v___x_327_);
v___x_328_ = lean_array_push(v_b_325_, v___x_327_);
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_add(v_i_323_, v___x_329_);
v_i_323_ = v___x_330_;
v_b_325_ = v___x_328_;
goto _start;
}
else
{
return v_b_325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4___boxed(lean_object* v_as_332_, lean_object* v_i_333_, lean_object* v_stop_334_, lean_object* v_b_335_){
_start:
{
size_t v_i_boxed_336_; size_t v_stop_boxed_337_; lean_object* v_res_338_; 
v_i_boxed_336_ = lean_unbox_usize(v_i_333_);
lean_dec(v_i_333_);
v_stop_boxed_337_ = lean_unbox_usize(v_stop_334_);
lean_dec(v_stop_334_);
v_res_338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(v_as_332_, v_i_boxed_336_, v_stop_boxed_337_, v_b_335_);
lean_dec_ref(v_as_332_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_object* v_child_341_; 
v_child_341_ = lean_ctor_get(v_x_340_, 1);
v_x_340_ = v_child_341_;
goto _start;
}
else
{
lean_object* v_vs_343_; lean_object* v_children_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_vs_343_ = lean_ctor_get(v_x_340_, 0);
v_children_344_ = lean_ctor_get(v_x_340_, 1);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_array_get_size(v_vs_343_);
v___x_347_ = lean_nat_dec_lt(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_array_get_size(v_children_344_);
v___x_349_ = lean_nat_dec_lt(v___x_345_, v___x_348_);
if (v___x_349_ == 0)
{
return v_x_339_;
}
else
{
size_t v___x_350_; size_t v___x_351_; lean_object* v___x_352_; 
v___x_350_ = ((size_t)0ULL);
v___x_351_ = lean_usize_of_nat(v___x_348_);
v___x_352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_children_344_, v___x_350_, v___x_351_, v_x_339_);
return v___x_352_;
}
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_353_ = ((size_t)0ULL);
v___x_354_ = lean_usize_of_nat(v___x_346_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(v_vs_343_, v___x_353_, v___x_354_, v_x_339_);
v___x_356_ = lean_array_get_size(v_children_344_);
v___x_357_ = lean_nat_dec_lt(v___x_345_, v___x_356_);
if (v___x_357_ == 0)
{
return v___x_355_;
}
else
{
size_t v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_usize_of_nat(v___x_356_);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_children_344_, v___x_353_, v___x_358_, v___x_355_);
return v___x_359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(lean_object* v_as_360_, size_t v_i_361_, size_t v_stop_362_, lean_object* v_b_363_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = lean_usize_dec_eq(v_i_361_, v_stop_362_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v_snd_366_; lean_object* v___x_367_; size_t v___x_368_; size_t v___x_369_; 
v___x_365_ = lean_array_uget_borrowed(v_as_360_, v_i_361_);
v_snd_366_ = lean_ctor_get(v___x_365_, 1);
v___x_367_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_b_363_, v_snd_366_);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_add(v_i_361_, v___x_368_);
v_i_361_ = v___x_369_;
v_b_363_ = v___x_367_;
goto _start;
}
else
{
return v_b_363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3___boxed(lean_object* v_as_371_, lean_object* v_i_372_, lean_object* v_stop_373_, lean_object* v_b_374_){
_start:
{
size_t v_i_boxed_375_; size_t v_stop_boxed_376_; lean_object* v_res_377_; 
v_i_boxed_375_ = lean_unbox_usize(v_i_372_);
lean_dec(v_i_372_);
v_stop_boxed_376_ = lean_unbox_usize(v_stop_373_);
lean_dec(v_stop_373_);
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_as_371_, v_i_boxed_375_, v_stop_boxed_376_, v_b_374_);
lean_dec_ref(v_as_371_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2___boxed(lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_x_378_, v_x_379_);
lean_dec_ref(v_x_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___lam__0(lean_object* v_s_381_, lean_object* v_x_382_, lean_object* v_t_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_s_381_, v_t_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___lam__0___boxed(lean_object* v_s_385_, lean_object* v_x_386_, lean_object* v_t_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Meta_Grind_mkNormSymTheorems___lam__0(v_s_385_, v_x_386_, v_t_387_);
lean_dec_ref(v_t_387_);
lean_dec(v_x_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(lean_object* v_as_389_, size_t v_sz_390_, size_t v_i_391_, lean_object* v_b_392_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = lean_usize_dec_lt(v_i_391_, v_sz_390_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v_b_392_);
return v___x_395_;
}
else
{
lean_object* v_a_396_; lean_object* v___x_397_; size_t v___x_398_; size_t v___x_399_; 
v_a_396_ = lean_array_uget_borrowed(v_as_389_, v_i_391_);
lean_inc(v_a_396_);
v___x_397_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_392_, v_a_396_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_391_, v___x_398_);
v_i_391_ = v___x_399_;
v_b_392_ = v___x_397_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg___boxed(lean_object* v_as_401_, lean_object* v_sz_402_, lean_object* v_i_403_, lean_object* v_b_404_, lean_object* v___y_405_){
_start:
{
size_t v_sz_boxed_406_; size_t v_i_boxed_407_; lean_object* v_res_408_; 
v_sz_boxed_406_ = lean_unbox_usize(v_sz_402_);
lean_dec(v_sz_402_);
v_i_boxed_407_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_as_401_, v_sz_boxed_406_, v_i_boxed_407_, v_b_404_);
lean_dec_ref(v_as_401_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(lean_object* v_declName_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; lean_object* v_env_413_; uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_412_ = lean_st_ref_get(v___y_410_);
v_env_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc_ref(v_env_413_);
lean_dec(v___x_412_);
v___x_414_ = l_Lean_getReducibilityStatusCore(v_env_413_, v_declName_409_);
v___x_415_ = lean_box(v___x_414_);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg___boxed(lean_object* v_declName_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_417_, v___y_418_);
lean_dec(v___y_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(lean_object* v_declName_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_443_; 
v___x_427_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_421_, v___y_425_);
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_443_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_443_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_443_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
uint8_t v___x_432_; 
v___x_432_ = lean_unbox(v_a_428_);
lean_dec(v_a_428_);
if (v___x_432_ == 0)
{
uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_433_ = 1;
v___x_434_ = lean_box(v___x_433_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_434_);
v___x_436_ = v___x_430_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
else
{
uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_438_ = 0;
v___x_439_ = lean_box(v___x_438_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_439_);
v___x_441_ = v___x_430_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0___boxed(lean_object* v_declName_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(v_declName_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_450_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___closed__0));
v___x_453_ = l_Lean_stringToMessageData(v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg(lean_object* v_as_x27_454_, lean_object* v_b_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
if (lean_obj_tag(v_as_x27_454_) == 0)
{
lean_object* v___x_461_; 
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v_b_455_);
return v___x_461_;
}
else
{
lean_object* v_head_462_; lean_object* v_tail_463_; lean_object* v___x_464_; 
v_head_462_ = lean_ctor_get(v_as_x27_454_, 0);
v_tail_463_ = lean_ctor_get(v_as_x27_454_, 1);
lean_inc(v_head_462_);
v___x_464_ = l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(v_head_462_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_517_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_517_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_517_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_517_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___y_470_; uint8_t v___y_471_; lean_object* v_a_503_; uint8_t v___x_506_; 
v___x_506_ = lean_unbox(v_a_465_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
lean_inc(v_head_462_);
v___x_507_ = l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(v_head_462_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; size_t v_sz_509_; size_t v___x_510_; lean_object* v___x_511_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v_sz_509_ = lean_array_size(v_a_508_);
v___x_510_ = ((size_t)0ULL);
lean_inc_ref(v_b_455_);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_a_508_, v_sz_509_, v___x_510_, v_b_455_);
lean_dec(v_a_508_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; 
lean_del_object(v___x_467_);
lean_dec(v_a_465_);
lean_dec_ref(v_b_455_);
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v_as_x27_454_ = v_tail_463_;
v_b_455_ = v_a_512_;
goto _start;
}
else
{
lean_object* v_a_514_; 
v_a_514_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_511_, 1);
v_a_503_ = v_a_514_;
goto v___jp_502_;
}
}
else
{
lean_object* v_a_515_; 
v_a_515_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_507_, 1);
v_a_503_ = v_a_515_;
goto v___jp_502_;
}
}
else
{
lean_del_object(v___x_467_);
lean_dec(v_a_465_);
v_as_x27_454_ = v_tail_463_;
goto _start;
}
v___jp_469_:
{
if (v___y_471_ == 0)
{
lean_object* v_toCold_472_; lean_object* v_options_473_; uint8_t v_hasTrace_474_; 
lean_del_object(v___x_467_);
v_toCold_472_ = lean_ctor_get(v___y_458_, 0);
v_options_473_ = lean_ctor_get(v_toCold_472_, 2);
v_hasTrace_474_ = lean_ctor_get_uint8(v_options_473_, sizeof(void*)*1);
if (v_hasTrace_474_ == 0)
{
lean_dec_ref(v___y_470_);
lean_dec(v_a_465_);
v_as_x27_454_ = v_tail_463_;
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_inheritedTraceOptions_476_ = lean_ctor_get(v_toCold_472_, 11);
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_478_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2);
v___x_479_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_476_, v_options_473_, v___x_478_);
if (v___x_479_ == 0)
{
lean_dec_ref(v___y_470_);
lean_dec(v_a_465_);
v_as_x27_454_ = v_tail_463_;
goto _start;
}
else
{
lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_481_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___closed__1);
v___x_482_ = lean_unbox(v_a_465_);
lean_dec(v_a_465_);
lean_inc(v_head_462_);
v___x_483_ = l_Lean_MessageData_ofConstName(v_head_462_, v___x_482_);
v___x_484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_481_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = l_Lean_Exception_toMessageData(v___y_470_);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v___x_477_, v___x_488_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_dec_ref_known(v___x_489_, 1);
v_as_x27_454_ = v_tail_463_;
goto _start;
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec_ref(v_b_455_);
v_a_491_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_489_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_489_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
else
{
lean_object* v___x_500_; 
lean_dec(v_a_465_);
lean_dec_ref(v_b_455_);
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 1);
lean_ctor_set(v___x_467_, 0, v___y_470_);
v___x_500_ = v___x_467_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___y_470_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
v___jp_502_:
{
uint8_t v___x_504_; 
v___x_504_ = l_Lean_Exception_isInterrupt(v_a_503_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
lean_inc_ref(v_a_503_);
v___x_505_ = l_Lean_Exception_isRuntime(v_a_503_);
v___y_470_ = v_a_503_;
v___y_471_ = v___x_505_;
goto v___jp_469_;
}
else
{
v___y_470_ = v_a_503_;
v___y_471_ = v___x_504_;
goto v___jp_469_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_b_455_);
v_a_518_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_464_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_464_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg___boxed(lean_object* v_as_x27_526_, lean_object* v_b_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg(v_as_x27_526_, v_b_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v_as_x27_526_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(lean_object* v_as_534_, size_t v_sz_535_, size_t v_i_536_, lean_object* v_b_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = lean_usize_dec_lt(v_i_536_, v_sz_535_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v_b_537_);
return v___x_544_;
}
else
{
lean_object* v_a_545_; lean_object* v___x_546_; 
v_a_545_ = lean_array_uget_borrowed(v_as_534_, v_i_536_);
lean_inc(v_a_545_);
v___x_546_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_b_537_, v_a_545_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; size_t v___x_548_; size_t v___x_549_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = ((size_t)1ULL);
v___x_549_ = lean_usize_add(v_i_536_, v___x_548_);
v_i_536_ = v___x_549_;
v_b_537_ = v_a_547_;
goto _start;
}
else
{
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4___boxed(lean_object* v_as_551_, lean_object* v_sz_552_, lean_object* v_i_553_, lean_object* v_b_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
size_t v_sz_boxed_560_; size_t v_i_boxed_561_; lean_object* v_res_562_; 
v_sz_boxed_560_ = lean_unbox_usize(v_sz_552_);
lean_dec(v_sz_552_);
v_i_boxed_561_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(v_as_551_, v_sz_boxed_560_, v_i_boxed_561_, v_b_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec_ref(v_as_551_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(lean_object* v_f_563_, lean_object* v_keys_564_, lean_object* v_vals_565_, lean_object* v_i_566_, lean_object* v_acc_567_){
_start:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_array_get_size(v_keys_564_);
v___x_569_ = lean_nat_dec_lt(v_i_566_, v___x_568_);
if (v___x_569_ == 0)
{
lean_dec(v_i_566_);
lean_dec(v_f_563_);
return v_acc_567_;
}
else
{
lean_object* v_k_570_; lean_object* v_v_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_k_570_ = lean_array_fget_borrowed(v_keys_564_, v_i_566_);
v_v_571_ = lean_array_fget_borrowed(v_vals_565_, v_i_566_);
lean_inc(v_f_563_);
lean_inc(v_v_571_);
lean_inc(v_k_570_);
v___x_572_ = lean_apply_3(v_f_563_, v_acc_567_, v_k_570_, v_v_571_);
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = lean_nat_add(v_i_566_, v___x_573_);
lean_dec(v_i_566_);
v_i_566_ = v___x_574_;
v_acc_567_ = v___x_572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_f_576_, lean_object* v_keys_577_, lean_object* v_vals_578_, lean_object* v_i_579_, lean_object* v_acc_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_576_, v_keys_577_, v_vals_578_, v_i_579_, v_acc_580_);
lean_dec_ref(v_vals_578_);
lean_dec_ref(v_keys_577_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(lean_object* v_f_582_, lean_object* v_as_583_, size_t v_i_584_, size_t v_stop_585_, lean_object* v_b_586_){
_start:
{
lean_object* v___y_588_; uint8_t v___x_592_; 
v___x_592_ = lean_usize_dec_eq(v_i_584_, v_stop_585_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_array_uget_borrowed(v_as_583_, v_i_584_);
switch(lean_obj_tag(v___x_593_))
{
case 0:
{
lean_object* v_key_594_; lean_object* v_val_595_; lean_object* v___x_596_; 
v_key_594_ = lean_ctor_get(v___x_593_, 0);
v_val_595_ = lean_ctor_get(v___x_593_, 1);
lean_inc(v_f_582_);
lean_inc(v_val_595_);
lean_inc(v_key_594_);
v___x_596_ = lean_apply_3(v_f_582_, v_b_586_, v_key_594_, v_val_595_);
v___y_588_ = v___x_596_;
goto v___jp_587_;
}
case 1:
{
lean_object* v_node_597_; lean_object* v___x_598_; 
v_node_597_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_f_582_);
v___x_598_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_582_, v_node_597_, v_b_586_);
v___y_588_ = v___x_598_;
goto v___jp_587_;
}
default: 
{
v___y_588_ = v_b_586_;
goto v___jp_587_;
}
}
}
else
{
lean_dec(v_f_582_);
return v_b_586_;
}
v___jp_587_:
{
size_t v___x_589_; size_t v___x_590_; 
v___x_589_ = ((size_t)1ULL);
v___x_590_ = lean_usize_add(v_i_584_, v___x_589_);
v_i_584_ = v___x_590_;
v_b_586_ = v___y_588_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(lean_object* v_f_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v_es_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_es_602_ = lean_ctor_get(v_x_600_, 0);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_array_get_size(v_es_602_);
v___x_605_ = lean_nat_dec_lt(v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_dec(v_f_599_);
return v_x_601_;
}
else
{
size_t v___x_606_; size_t v___x_607_; lean_object* v___x_608_; 
v___x_606_ = ((size_t)0ULL);
v___x_607_ = lean_usize_of_nat(v___x_604_);
v___x_608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_599_, v_es_602_, v___x_606_, v___x_607_, v_x_601_);
return v___x_608_;
}
}
else
{
lean_object* v_ks_609_; lean_object* v_vs_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_ks_609_ = lean_ctor_get(v_x_600_, 0);
v_vs_610_ = lean_ctor_get(v_x_600_, 1);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_599_, v_ks_609_, v_vs_610_, v___x_611_, v_x_601_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg___boxed(lean_object* v_f_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_613_, v_x_614_, v_x_615_);
lean_dec_ref(v_x_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v_f_617_, lean_object* v_as_618_, lean_object* v_i_619_, lean_object* v_stop_620_, lean_object* v_b_621_){
_start:
{
size_t v_i_boxed_622_; size_t v_stop_boxed_623_; lean_object* v_res_624_; 
v_i_boxed_622_ = lean_unbox_usize(v_i_619_);
lean_dec(v_i_619_);
v_stop_boxed_623_ = lean_unbox_usize(v_stop_620_);
lean_dec(v_stop_620_);
v_res_624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_617_, v_as_618_, v_i_boxed_622_, v_stop_boxed_623_, v_b_621_);
lean_dec_ref(v_as_618_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(lean_object* v_as_x27_625_, lean_object* v_b_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
if (lean_obj_tag(v_as_x27_625_) == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_b_626_);
return v___x_632_;
}
else
{
lean_object* v_head_633_; lean_object* v_tail_634_; lean_object* v___x_635_; 
v_head_633_ = lean_ctor_get(v_as_x27_625_, 0);
v_tail_634_ = lean_ctor_get(v_as_x27_625_, 1);
lean_inc(v_head_633_);
v___x_635_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_head_633_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_626_, v_a_636_);
v_as_x27_625_ = v_tail_634_;
v_b_626_ = v___x_637_;
goto _start;
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v_b_626_);
v_a_639_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_635_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_635_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg___boxed(lean_object* v_as_x27_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v_as_x27_647_, v_b_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v_as_x27_647_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg___lam__0(lean_object* v_ps_655_, lean_object* v_k_656_, lean_object* v_v_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v_k_656_);
lean_ctor_set(v___x_658_, 1, v_v_657_);
v___x_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v_ps_655_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___redArg___lam__0(lean_object* v_f_660_, lean_object* v_x1_661_, lean_object* v_x2_662_, lean_object* v_x3_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = lean_apply_3(v_f_660_, v_x1_661_, v_x2_662_, v_x3_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___redArg(lean_object* v_map_665_, lean_object* v_f_666_, lean_object* v_init_667_){
_start:
{
lean_object* v___f_668_; lean_object* v___x_669_; 
v___f_668_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___redArg___lam__0), 4, 1);
lean_closure_set(v___f_668_, 0, v_f_666_);
v___x_669_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_668_, v_map_665_, v_init_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___redArg___boxed(lean_object* v_map_670_, lean_object* v_f_671_, lean_object* v_init_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___redArg(v_map_670_, v_f_671_, v_init_672_);
lean_dec_ref(v_map_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg(lean_object* v_m_675_){
_start:
{
lean_object* v___f_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___f_676_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg___closed__0));
v___x_677_ = lean_box(0);
v___x_678_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___redArg(v_m_675_, v___f_676_, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg___boxed(lean_object* v_m_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg(v_m_679_);
lean_dec_ref(v_m_679_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__11(lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
if (lean_obj_tag(v_a_681_) == 0)
{
lean_object* v___x_683_; 
v___x_683_ = l_List_reverse___redArg(v_a_682_);
return v___x_683_;
}
else
{
lean_object* v_head_684_; lean_object* v_tail_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_694_; 
v_head_684_ = lean_ctor_get(v_a_681_, 0);
v_tail_685_ = lean_ctor_get(v_a_681_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_a_681_);
if (v_isSharedCheck_694_ == 0)
{
v___x_687_ = v_a_681_;
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_tail_685_);
lean_inc(v_head_684_);
lean_dec(v_a_681_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_694_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_fst_689_; lean_object* v___x_691_; 
v_fst_689_ = lean_ctor_get(v_head_684_, 0);
lean_inc(v_fst_689_);
lean_dec(v_head_684_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v_a_682_);
lean_ctor_set(v___x_687_, 0, v_fst_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_fst_689_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_a_682_);
v___x_691_ = v_reuseFailAlloc_693_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v_a_681_ = v_tail_685_;
v_a_682_ = v___x_691_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(lean_object* v_s_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg(v_s_695_);
v___x_697_ = lean_box(0);
v___x_698_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__11(v___x_696_, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6___boxed(lean_object* v_s_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(v_s_699_);
lean_dec_ref(v_s_699_);
return v_res_700_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1(void){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__2(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__1, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__1_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__2, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__2_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__2);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems(lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___f_729_; lean_object* v___x_730_; 
v___f_729_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__0));
v___x_730_ = l_Lean_Meta_Grind_getNormTheorems(v_a_724_, v_a_725_, v_a_726_, v_a_727_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; lean_object* v_pre_733_; lean_object* v_post_734_; lean_object* v_toUnfold_735_; lean_object* v___x_736_; lean_object* v___x_737_; size_t v_sz_738_; size_t v___x_739_; lean_object* v___x_740_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__3, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__3_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3);
v_pre_733_ = lean_ctor_get(v_a_731_, 0);
lean_inc_ref(v_pre_733_);
v_post_734_ = lean_ctor_get(v_a_731_, 1);
lean_inc_ref(v_post_734_);
v_toUnfold_735_ = lean_ctor_get(v_a_731_, 3);
lean_inc_ref(v_toUnfold_735_);
lean_dec(v_a_731_);
v___x_736_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__4));
v___x_737_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_729_, v_pre_733_, v___x_736_);
lean_dec_ref(v_pre_733_);
v_sz_738_ = lean_array_size(v___x_737_);
v___x_739_ = ((size_t)0ULL);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(v___x_737_, v_sz_738_, v___x_739_, v___x_732_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec(v___x_737_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__11));
v___x_743_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v___x_742_, v_a_741_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; size_t v_sz_746_; lean_object* v___x_747_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_729_, v_post_734_, v___x_736_);
lean_dec_ref(v_post_734_);
v_sz_746_ = lean_array_size(v___x_745_);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(v___x_745_, v_sz_746_, v___x_739_, v___x_732_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec(v___x_745_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v___x_749_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(v_toUnfold_735_);
lean_dec_ref(v_toUnfold_735_);
v___x_750_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg(v___x_749_, v_a_748_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec(v___x_749_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_759_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_759_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_759_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_759_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_a_744_);
lean_ctor_set(v___x_755_, 1, v_a_751_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_755_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_a_744_);
v_a_760_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_750_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_750_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v_a_744_);
lean_dec_ref(v_toUnfold_735_);
v_a_768_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_747_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_747_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_toUnfold_735_);
lean_dec_ref(v_post_734_);
v_a_776_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_743_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_743_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v_toUnfold_735_);
lean_dec_ref(v_post_734_);
v_a_784_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_740_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_740_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
v_a_792_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_730_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_730_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___boxed(lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Meta_Grind_mkNormSymTheorems(v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0(lean_object* v_declName_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_806_, v___y_810_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___boxed(lean_object* v_declName_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0(v_declName_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1(lean_object* v_as_820_, size_t v_sz_821_, size_t v_i_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_as_820_, v_sz_821_, v_i_822_, v_b_823_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___boxed(lean_object* v_as_830_, lean_object* v_sz_831_, lean_object* v_i_832_, lean_object* v_b_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
size_t v_sz_boxed_839_; size_t v_i_boxed_840_; lean_object* v_res_841_; 
v_sz_boxed_839_ = lean_unbox_usize(v_sz_831_);
lean_dec(v_sz_831_);
v_i_boxed_840_ = lean_unbox_usize(v_i_832_);
lean_dec(v_i_832_);
v_res_841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1(v_as_830_, v_sz_boxed_839_, v_i_boxed_840_, v_b_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v_as_830_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg(lean_object* v_map_842_, lean_object* v_f_843_, lean_object* v_init_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_843_, v_map_842_, v_init_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg___boxed(lean_object* v_map_846_, lean_object* v_f_847_, lean_object* v_init_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg(v_map_846_, v_f_847_, v_init_848_);
lean_dec_ref(v_map_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3(lean_object* v_00_u03c3_850_, lean_object* v_00_u03b2_851_, lean_object* v_map_852_, lean_object* v_f_853_, lean_object* v_init_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_853_, v_map_852_, v_init_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___boxed(lean_object* v_00_u03c3_856_, lean_object* v_00_u03b2_857_, lean_object* v_map_858_, lean_object* v_f_859_, lean_object* v_init_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3(v_00_u03c3_856_, v_00_u03b2_857_, v_map_858_, v_f_859_, v_init_860_);
lean_dec_ref(v_map_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5(lean_object* v_as_862_, lean_object* v_as_x27_863_, lean_object* v_b_864_, lean_object* v_a_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v_as_x27_863_, v_b_864_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___boxed(lean_object* v_as_872_, lean_object* v_as_x27_873_, lean_object* v_b_874_, lean_object* v_a_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5(v_as_872_, v_as_x27_873_, v_b_874_, v_a_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v_as_x27_873_);
lean_dec(v_as_872_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(lean_object* v_as_882_, lean_object* v_as_x27_883_, lean_object* v_b_884_, lean_object* v_a_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___redArg(v_as_x27_883_, v_b_884_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___boxed(lean_object* v_as_892_, lean_object* v_as_x27_893_, lean_object* v_b_894_, lean_object* v_a_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(v_as_892_, v_as_x27_893_, v_b_894_, v_a_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v_as_x27_893_);
lean_dec(v_as_892_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6(lean_object* v_00_u03c3_902_, lean_object* v_00_u03b1_903_, lean_object* v_00_u03b2_904_, lean_object* v_f_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_905_, v_x_906_, v_x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___boxed(lean_object* v_00_u03c3_909_, lean_object* v_00_u03b1_910_, lean_object* v_00_u03b2_911_, lean_object* v_f_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6(v_00_u03c3_909_, v_00_u03b1_910_, v_00_u03b2_911_, v_f_912_, v_x_913_, v_x_914_);
lean_dec_ref(v_x_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10(lean_object* v_00_u03b2_916_, lean_object* v_m_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___redArg(v_m_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10___boxed(lean_object* v_00_u03b2_919_, lean_object* v_m_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10(v_00_u03b2_919_, v_m_920_);
lean_dec_ref(v_m_920_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7(lean_object* v_00_u03b1_922_, lean_object* v_00_u03b2_923_, lean_object* v_00_u03c3_924_, lean_object* v_f_925_, lean_object* v_as_926_, size_t v_i_927_, size_t v_stop_928_, lean_object* v_b_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_925_, v_as_926_, v_i_927_, v_stop_928_, v_b_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___boxed(lean_object* v_00_u03b1_931_, lean_object* v_00_u03b2_932_, lean_object* v_00_u03c3_933_, lean_object* v_f_934_, lean_object* v_as_935_, lean_object* v_i_936_, lean_object* v_stop_937_, lean_object* v_b_938_){
_start:
{
size_t v_i_boxed_939_; size_t v_stop_boxed_940_; lean_object* v_res_941_; 
v_i_boxed_939_ = lean_unbox_usize(v_i_936_);
lean_dec(v_i_936_);
v_stop_boxed_940_ = lean_unbox_usize(v_stop_937_);
lean_dec(v_stop_937_);
v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7(v_00_u03b1_931_, v_00_u03b2_932_, v_00_u03c3_933_, v_f_934_, v_as_935_, v_i_boxed_939_, v_stop_boxed_940_, v_b_938_);
lean_dec_ref(v_as_935_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8(lean_object* v_00_u03c3_942_, lean_object* v_00_u03b1_943_, lean_object* v_00_u03b2_944_, lean_object* v_f_945_, lean_object* v_keys_946_, lean_object* v_vals_947_, lean_object* v_heq_948_, lean_object* v_i_949_, lean_object* v_acc_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_945_, v_keys_946_, v_vals_947_, v_i_949_, v_acc_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03c3_952_, lean_object* v_00_u03b1_953_, lean_object* v_00_u03b2_954_, lean_object* v_f_955_, lean_object* v_keys_956_, lean_object* v_vals_957_, lean_object* v_heq_958_, lean_object* v_i_959_, lean_object* v_acc_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8(v_00_u03c3_952_, v_00_u03b1_953_, v_00_u03b2_954_, v_f_955_, v_keys_956_, v_vals_957_, v_heq_958_, v_i_959_, v_acc_960_);
lean_dec_ref(v_vals_957_);
lean_dec_ref(v_keys_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13(lean_object* v_00_u03c3_962_, lean_object* v_00_u03b2_963_, lean_object* v_map_964_, lean_object* v_f_965_, lean_object* v_init_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___redArg(v_map_964_, v_f_965_, v_init_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13___boxed(lean_object* v_00_u03c3_968_, lean_object* v_00_u03b2_969_, lean_object* v_map_970_, lean_object* v_f_971_, lean_object* v_init_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13(v_00_u03c3_968_, v_00_u03b2_969_, v_map_970_, v_f_971_, v_init_972_);
lean_dec_ref(v_map_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13_spec__15___redArg(lean_object* v_map_974_, lean_object* v_f_975_, lean_object* v_init_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_975_, v_map_974_, v_init_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13_spec__15___redArg___boxed(lean_object* v_map_978_, lean_object* v_f_979_, lean_object* v_init_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13_spec__15___redArg(v_map_978_, v_f_979_, v_init_980_);
lean_dec_ref(v_map_978_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13_spec__15(lean_object* v_00_u03c3_982_, lean_object* v_00_u03b2_983_, lean_object* v_map_984_, lean_object* v_f_985_, lean_object* v_init_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_985_, v_map_984_, v_init_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13_spec__15___boxed(lean_object* v_00_u03c3_988_, lean_object* v_00_u03b2_989_, lean_object* v_map_990_, lean_object* v_f_991_, lean_object* v_init_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_spec__10_spec__13_spec__15(v_00_u03c3_988_, v_00_u03b2_989_, v_map_990_, v_f_991_, v_init_992_);
lean_dec_ref(v_map_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0(lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
lean_inc_ref(v___y_995_);
v___x_1006_ = l_Lean_Meta_Sym_Simp_reduceProj___redArg(v___y_995_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
if (lean_obj_tag(v_a_1007_) == 0)
{
uint8_t v_done_1008_; 
v_done_1008_ = lean_ctor_get_uint8(v_a_1007_, 0);
if (v_done_1008_ == 0)
{
uint8_t v_contextDependent_1009_; lean_object* v___x_1010_; 
lean_dec_ref_known(v___x_1006_, 1);
v_contextDependent_1009_ = lean_ctor_get_uint8(v_a_1007_, 1);
lean_dec_ref_known(v_a_1007_, 0);
v___x_1010_ = l_Lean_Meta_Sym_Simp_reduceMatcher___redArg(v___y_995_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec_ref(v___y_995_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; uint8_t v___y_1013_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
if (v_contextDependent_1009_ == 0)
{
return v___x_1010_;
}
else
{
if (lean_obj_tag(v_a_1011_) == 0)
{
uint8_t v_contextDependent_1023_; 
v_contextDependent_1023_ = lean_ctor_get_uint8(v_a_1011_, 1);
v___y_1013_ = v_contextDependent_1023_;
goto v___jp_1012_;
}
else
{
uint8_t v_contextDependent_1024_; 
v_contextDependent_1024_ = lean_ctor_get_uint8(v_a_1011_, sizeof(void*)*2 + 1);
v___y_1013_ = v_contextDependent_1024_;
goto v___jp_1012_;
}
}
v___jp_1012_:
{
if (v___y_1013_ == 0)
{
lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1021_; 
lean_inc(v_a_1011_);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v___x_1010_, 0);
lean_dec(v_unused_1022_);
v___x_1015_ = v___x_1010_;
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
else
{
lean_dec(v___x_1010_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1017_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1011_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1017_);
v___x_1019_ = v___x_1015_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
return v___x_1010_;
}
}
}
else
{
return v___x_1010_;
}
}
else
{
lean_dec_ref_known(v_a_1007_, 0);
lean_dec_ref(v___y_995_);
return v___x_1006_;
}
}
else
{
uint8_t v_done_1025_; 
v_done_1025_ = lean_ctor_get_uint8(v_a_1007_, sizeof(void*)*2);
if (v_done_1025_ == 0)
{
lean_object* v_e_x27_1026_; lean_object* v_proof_1027_; uint8_t v_contextDependent_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1078_; 
lean_dec_ref_known(v___x_1006_, 1);
v_e_x27_1026_ = lean_ctor_get(v_a_1007_, 0);
v_proof_1027_ = lean_ctor_get(v_a_1007_, 1);
v_contextDependent_1028_ = lean_ctor_get_uint8(v_a_1007_, sizeof(void*)*2 + 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_a_1007_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1030_ = v_a_1007_;
v_isShared_1031_ = v_isSharedCheck_1078_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_proof_1027_);
lean_inc(v_e_x27_1026_);
lean_dec(v_a_1007_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1078_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Meta_Sym_Simp_reduceMatcher___redArg(v_e_x27_1026_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1077_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1077_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1077_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
if (lean_obj_tag(v_a_1033_) == 0)
{
uint8_t v_done_1037_; uint8_t v_contextDependent_1038_; uint8_t v___y_1040_; 
lean_dec_ref(v___y_995_);
v_done_1037_ = lean_ctor_get_uint8(v_a_1033_, 0);
v_contextDependent_1038_ = lean_ctor_get_uint8(v_a_1033_, 1);
lean_dec_ref_known(v_a_1033_, 0);
if (v_contextDependent_1028_ == 0)
{
v___y_1040_ = v_contextDependent_1038_;
goto v___jp_1039_;
}
else
{
v___y_1040_ = v_contextDependent_1028_;
goto v___jp_1039_;
}
v___jp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_1031_ == 0)
{
v___x_1042_ = v___x_1030_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_e_x27_1026_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_proof_1027_);
v___x_1042_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1044_; 
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*2, v_done_1037_);
lean_ctor_set_uint8(v___x_1042_, sizeof(void*)*2 + 1, v___y_1040_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1042_);
v___x_1044_ = v___x_1035_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_e_x27_1047_; lean_object* v_proof_1048_; uint8_t v_done_1049_; uint8_t v_contextDependent_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1076_; 
lean_del_object(v___x_1035_);
lean_del_object(v___x_1030_);
v_e_x27_1047_ = lean_ctor_get(v_a_1033_, 0);
v_proof_1048_ = lean_ctor_get(v_a_1033_, 1);
v_done_1049_ = lean_ctor_get_uint8(v_a_1033_, sizeof(void*)*2);
v_contextDependent_1050_ = lean_ctor_get_uint8(v_a_1033_, sizeof(void*)*2 + 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_a_1033_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1052_ = v_a_1033_;
v_isShared_1053_ = v_isSharedCheck_1076_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_proof_1048_);
lean_inc(v_e_x27_1047_);
lean_dec(v_a_1033_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1076_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; 
lean_inc_ref(v_e_x27_1047_);
v___x_1054_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_995_, v_e_x27_1026_, v_proof_1027_, v_e_x27_1047_, v_proof_1048_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1067_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1067_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1067_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
uint8_t v___y_1060_; 
if (v_contextDependent_1028_ == 0)
{
v___y_1060_ = v_contextDependent_1050_;
goto v___jp_1059_;
}
else
{
v___y_1060_ = v_contextDependent_1028_;
goto v___jp_1059_;
}
v___jp_1059_:
{
lean_object* v___x_1062_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v_a_1055_);
v___x_1062_ = v___x_1052_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_e_x27_1047_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_a_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*2, v_done_1049_);
v___x_1062_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1064_; 
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*2 + 1, v___y_1060_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1062_);
v___x_1064_ = v___x_1057_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_del_object(v___x_1052_);
lean_dec_ref(v_e_x27_1047_);
v_a_1068_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1054_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1054_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1030_);
lean_dec_ref(v_proof_1027_);
lean_dec_ref(v_e_x27_1026_);
lean_dec_ref(v___y_995_);
return v___x_1032_;
}
}
}
else
{
lean_dec_ref_known(v_a_1007_, 2);
lean_dec_ref(v___y_995_);
return v___x_1006_;
}
}
}
else
{
lean_dec_ref(v___y_995_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0___boxed(lean_object* v_x_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__0(v_x_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1(lean_object* v___f_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_box(0);
lean_inc_ref(v___y_1094_);
v___x_1106_ = l_Lean_Meta_Sym_Simp_beta___redArg(v___y_1094_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
if (lean_obj_tag(v_a_1107_) == 0)
{
uint8_t v_done_1108_; 
v_done_1108_ = lean_ctor_get_uint8(v_a_1107_, 0);
if (v_done_1108_ == 0)
{
uint8_t v_contextDependent_1109_; lean_object* v___x_1110_; 
lean_dec_ref_known(v___x_1106_, 1);
v_contextDependent_1109_ = lean_ctor_get_uint8(v_a_1107_, 1);
lean_dec_ref_known(v_a_1107_, 0);
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
v___x_1110_ = lean_apply_12(v___f_1092_, v___x_1105_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, lean_box(0));
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; uint8_t v___y_1113_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
if (v_contextDependent_1109_ == 0)
{
lean_dec(v_a_1111_);
return v___x_1110_;
}
else
{
if (lean_obj_tag(v_a_1111_) == 0)
{
uint8_t v_contextDependent_1123_; 
v_contextDependent_1123_ = lean_ctor_get_uint8(v_a_1111_, 1);
v___y_1113_ = v_contextDependent_1123_;
goto v___jp_1112_;
}
else
{
uint8_t v_contextDependent_1124_; 
v_contextDependent_1124_ = lean_ctor_get_uint8(v_a_1111_, sizeof(void*)*2 + 1);
v___y_1113_ = v_contextDependent_1124_;
goto v___jp_1112_;
}
}
v___jp_1112_:
{
if (v___y_1113_ == 0)
{
lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v___x_1110_, 0);
lean_dec(v_unused_1122_);
v___x_1115_ = v___x_1110_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_dec(v___x_1110_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1111_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1117_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
else
{
lean_dec(v_a_1111_);
return v___x_1110_;
}
}
}
else
{
return v___x_1110_;
}
}
else
{
lean_dec_ref_known(v_a_1107_, 0);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v___f_1092_);
return v___x_1106_;
}
}
else
{
uint8_t v_done_1125_; 
v_done_1125_ = lean_ctor_get_uint8(v_a_1107_, sizeof(void*)*2);
if (v_done_1125_ == 0)
{
lean_object* v_e_x27_1126_; lean_object* v_proof_1127_; uint8_t v_contextDependent_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref_known(v___x_1106_, 1);
v_e_x27_1126_ = lean_ctor_get(v_a_1107_, 0);
v_proof_1127_ = lean_ctor_get(v_a_1107_, 1);
v_contextDependent_1128_ = lean_ctor_get_uint8(v_a_1107_, sizeof(void*)*2 + 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_a_1107_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1130_ = v_a_1107_;
v_isShared_1131_ = v_isSharedCheck_1178_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_proof_1127_);
lean_inc(v_e_x27_1126_);
lean_dec(v_a_1107_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1178_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; 
lean_inc(v___y_1103_);
lean_inc_ref(v___y_1102_);
lean_inc(v___y_1101_);
lean_inc_ref(v___y_1100_);
lean_inc(v___y_1099_);
lean_inc_ref(v___y_1098_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc_ref(v_e_x27_1126_);
v___x_1132_ = lean_apply_12(v___f_1092_, v___x_1105_, v_e_x27_1126_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, lean_box(0));
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1177_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1177_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1177_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
if (lean_obj_tag(v_a_1133_) == 0)
{
uint8_t v_done_1137_; uint8_t v_contextDependent_1138_; uint8_t v___y_1140_; 
lean_dec_ref(v___y_1094_);
v_done_1137_ = lean_ctor_get_uint8(v_a_1133_, 0);
v_contextDependent_1138_ = lean_ctor_get_uint8(v_a_1133_, 1);
lean_dec_ref_known(v_a_1133_, 0);
if (v_contextDependent_1128_ == 0)
{
v___y_1140_ = v_contextDependent_1138_;
goto v___jp_1139_;
}
else
{
v___y_1140_ = v_contextDependent_1128_;
goto v___jp_1139_;
}
v___jp_1139_:
{
lean_object* v___x_1142_; 
if (v_isShared_1131_ == 0)
{
v___x_1142_ = v___x_1130_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_e_x27_1126_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_proof_1127_);
v___x_1142_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
lean_ctor_set_uint8(v___x_1142_, sizeof(void*)*2, v_done_1137_);
lean_ctor_set_uint8(v___x_1142_, sizeof(void*)*2 + 1, v___y_1140_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1142_);
v___x_1144_ = v___x_1135_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_object* v_e_x27_1147_; lean_object* v_proof_1148_; uint8_t v_done_1149_; uint8_t v_contextDependent_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1176_; 
lean_del_object(v___x_1135_);
lean_del_object(v___x_1130_);
v_e_x27_1147_ = lean_ctor_get(v_a_1133_, 0);
v_proof_1148_ = lean_ctor_get(v_a_1133_, 1);
v_done_1149_ = lean_ctor_get_uint8(v_a_1133_, sizeof(void*)*2);
v_contextDependent_1150_ = lean_ctor_get_uint8(v_a_1133_, sizeof(void*)*2 + 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_a_1133_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1152_ = v_a_1133_;
v_isShared_1153_ = v_isSharedCheck_1176_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_proof_1148_);
lean_inc(v_e_x27_1147_);
lean_dec(v_a_1133_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1176_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; 
lean_inc_ref(v_e_x27_1147_);
v___x_1154_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1094_, v_e_x27_1126_, v_proof_1127_, v_e_x27_1147_, v_proof_1148_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1167_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1167_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1167_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v___y_1160_; 
if (v_contextDependent_1128_ == 0)
{
v___y_1160_ = v_contextDependent_1150_;
goto v___jp_1159_;
}
else
{
v___y_1160_ = v_contextDependent_1128_;
goto v___jp_1159_;
}
v___jp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v_a_1155_);
v___x_1162_ = v___x_1152_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_e_x27_1147_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_a_1155_);
lean_ctor_set_uint8(v_reuseFailAlloc_1166_, sizeof(void*)*2, v_done_1149_);
v___x_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; 
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*2 + 1, v___y_1160_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1162_);
v___x_1164_ = v___x_1157_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_del_object(v___x_1152_);
lean_dec_ref(v_e_x27_1147_);
v_a_1168_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1154_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1154_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1130_);
lean_dec_ref(v_proof_1127_);
lean_dec_ref(v_e_x27_1126_);
lean_dec_ref(v___y_1094_);
return v___x_1132_;
}
}
}
else
{
lean_dec_ref_known(v_a_1107_, 2);
lean_dec_ref(v___y_1094_);
lean_dec_ref(v___f_1092_);
return v___x_1106_;
}
}
}
else
{
lean_dec_ref(v___y_1094_);
lean_dec_ref(v___f_1092_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1___boxed(lean_object* v___f_1179_, lean_object* v_x_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__1(v___f_1179_, v_x_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2(lean_object* v_x_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; 
lean_inc_ref(v___y_1194_);
v___x_1205_ = l_Lean_Meta_Grind_NormSym_simpForall(v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
if (lean_obj_tag(v_a_1206_) == 0)
{
uint8_t v_done_1207_; 
v_done_1207_ = lean_ctor_get_uint8(v_a_1206_, 0);
if (v_done_1207_ == 0)
{
uint8_t v_contextDependent_1208_; lean_object* v___x_1209_; 
lean_dec_ref_known(v___x_1205_, 1);
v_contextDependent_1208_ = lean_ctor_get_uint8(v_a_1206_, 1);
lean_dec_ref_known(v_a_1206_, 0);
v___x_1209_ = l_Lean_Meta_Grind_NormSym_simpExists(v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; uint8_t v___y_1212_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
if (v_contextDependent_1208_ == 0)
{
return v___x_1209_;
}
else
{
if (lean_obj_tag(v_a_1210_) == 0)
{
uint8_t v_contextDependent_1222_; 
v_contextDependent_1222_ = lean_ctor_get_uint8(v_a_1210_, 1);
v___y_1212_ = v_contextDependent_1222_;
goto v___jp_1211_;
}
else
{
uint8_t v_contextDependent_1223_; 
v_contextDependent_1223_ = lean_ctor_get_uint8(v_a_1210_, sizeof(void*)*2 + 1);
v___y_1212_ = v_contextDependent_1223_;
goto v___jp_1211_;
}
}
v___jp_1211_:
{
if (v___y_1212_ == 0)
{
lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1220_; 
lean_inc(v_a_1210_);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v___x_1209_, 0);
lean_dec(v_unused_1221_);
v___x_1214_ = v___x_1209_;
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
else
{
lean_dec(v___x_1209_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1210_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
return v___x_1209_;
}
}
}
else
{
return v___x_1209_;
}
}
else
{
lean_dec_ref_known(v_a_1206_, 0);
lean_dec_ref(v___y_1194_);
return v___x_1205_;
}
}
else
{
uint8_t v_done_1224_; 
v_done_1224_ = lean_ctor_get_uint8(v_a_1206_, sizeof(void*)*2);
if (v_done_1224_ == 0)
{
lean_object* v_e_x27_1225_; lean_object* v_proof_1226_; uint8_t v_contextDependent_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref_known(v___x_1205_, 1);
v_e_x27_1225_ = lean_ctor_get(v_a_1206_, 0);
v_proof_1226_ = lean_ctor_get(v_a_1206_, 1);
v_contextDependent_1227_ = lean_ctor_get_uint8(v_a_1206_, sizeof(void*)*2 + 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_a_1206_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1229_ = v_a_1206_;
v_isShared_1230_ = v_isSharedCheck_1277_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_proof_1226_);
lean_inc(v_e_x27_1225_);
lean_dec(v_a_1206_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1277_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; 
lean_inc_ref(v_e_x27_1225_);
v___x_1231_ = l_Lean_Meta_Grind_NormSym_simpExists(v_e_x27_1225_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1276_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1276_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1276_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
if (lean_obj_tag(v_a_1232_) == 0)
{
uint8_t v_done_1236_; uint8_t v_contextDependent_1237_; uint8_t v___y_1239_; 
lean_dec_ref(v___y_1194_);
v_done_1236_ = lean_ctor_get_uint8(v_a_1232_, 0);
v_contextDependent_1237_ = lean_ctor_get_uint8(v_a_1232_, 1);
lean_dec_ref_known(v_a_1232_, 0);
if (v_contextDependent_1227_ == 0)
{
v___y_1239_ = v_contextDependent_1237_;
goto v___jp_1238_;
}
else
{
v___y_1239_ = v_contextDependent_1227_;
goto v___jp_1238_;
}
v___jp_1238_:
{
lean_object* v___x_1241_; 
if (v_isShared_1230_ == 0)
{
v___x_1241_ = v___x_1229_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_e_x27_1225_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_proof_1226_);
v___x_1241_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1243_; 
lean_ctor_set_uint8(v___x_1241_, sizeof(void*)*2, v_done_1236_);
lean_ctor_set_uint8(v___x_1241_, sizeof(void*)*2 + 1, v___y_1239_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1241_);
v___x_1243_ = v___x_1234_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
else
{
lean_object* v_e_x27_1246_; lean_object* v_proof_1247_; uint8_t v_done_1248_; uint8_t v_contextDependent_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1275_; 
lean_del_object(v___x_1234_);
lean_del_object(v___x_1229_);
v_e_x27_1246_ = lean_ctor_get(v_a_1232_, 0);
v_proof_1247_ = lean_ctor_get(v_a_1232_, 1);
v_done_1248_ = lean_ctor_get_uint8(v_a_1232_, sizeof(void*)*2);
v_contextDependent_1249_ = lean_ctor_get_uint8(v_a_1232_, sizeof(void*)*2 + 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_a_1232_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1251_ = v_a_1232_;
v_isShared_1252_ = v_isSharedCheck_1275_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_proof_1247_);
lean_inc(v_e_x27_1246_);
lean_dec(v_a_1232_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1275_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; 
lean_inc_ref(v_e_x27_1246_);
v___x_1253_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1194_, v_e_x27_1225_, v_proof_1226_, v_e_x27_1246_, v_proof_1247_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1266_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1266_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1266_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
uint8_t v___y_1259_; 
if (v_contextDependent_1227_ == 0)
{
v___y_1259_ = v_contextDependent_1249_;
goto v___jp_1258_;
}
else
{
v___y_1259_ = v_contextDependent_1227_;
goto v___jp_1258_;
}
v___jp_1258_:
{
lean_object* v___x_1261_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v_a_1254_);
v___x_1261_ = v___x_1251_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_e_x27_1246_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_a_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*2, v_done_1248_);
v___x_1261_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1263_; 
lean_ctor_set_uint8(v___x_1261_, sizeof(void*)*2 + 1, v___y_1259_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1261_);
v___x_1263_ = v___x_1256_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_del_object(v___x_1251_);
lean_dec_ref(v_e_x27_1246_);
v_a_1267_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1253_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1253_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1229_);
lean_dec_ref(v_proof_1226_);
lean_dec_ref(v_e_x27_1225_);
lean_dec_ref(v___y_1194_);
return v___x_1231_;
}
}
}
else
{
lean_dec_ref_known(v_a_1206_, 2);
lean_dec_ref(v___y_1194_);
return v___x_1205_;
}
}
}
else
{
lean_dec_ref(v___y_1194_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2___boxed(lean_object* v_x_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__2(v_x_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3(lean_object* v___f_1291_, lean_object* v_x_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = lean_box(0);
lean_inc_ref(v___y_1293_);
v___x_1305_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
if (lean_obj_tag(v_a_1306_) == 0)
{
uint8_t v_done_1307_; 
v_done_1307_ = lean_ctor_get_uint8(v_a_1306_, 0);
if (v_done_1307_ == 0)
{
uint8_t v_contextDependent_1308_; lean_object* v___x_1309_; 
lean_dec_ref_known(v___x_1305_, 1);
v_contextDependent_1308_ = lean_ctor_get_uint8(v_a_1306_, 1);
lean_dec_ref_known(v_a_1306_, 0);
lean_inc(v___y_1302_);
lean_inc_ref(v___y_1301_);
lean_inc(v___y_1300_);
lean_inc_ref(v___y_1299_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v___y_1294_);
v___x_1309_ = lean_apply_12(v___f_1291_, v___x_1304_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, lean_box(0));
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; uint8_t v___y_1312_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
if (v_contextDependent_1308_ == 0)
{
lean_dec(v_a_1310_);
return v___x_1309_;
}
else
{
if (lean_obj_tag(v_a_1310_) == 0)
{
uint8_t v_contextDependent_1322_; 
v_contextDependent_1322_ = lean_ctor_get_uint8(v_a_1310_, 1);
v___y_1312_ = v_contextDependent_1322_;
goto v___jp_1311_;
}
else
{
uint8_t v_contextDependent_1323_; 
v_contextDependent_1323_ = lean_ctor_get_uint8(v_a_1310_, sizeof(void*)*2 + 1);
v___y_1312_ = v_contextDependent_1323_;
goto v___jp_1311_;
}
}
v___jp_1311_:
{
if (v___y_1312_ == 0)
{
lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1320_; 
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v___x_1309_, 0);
lean_dec(v_unused_1321_);
v___x_1314_ = v___x_1309_;
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
else
{
lean_dec(v___x_1309_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1310_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1316_);
v___x_1318_ = v___x_1314_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
else
{
lean_dec(v_a_1310_);
return v___x_1309_;
}
}
}
else
{
return v___x_1309_;
}
}
else
{
lean_dec_ref_known(v_a_1306_, 0);
lean_dec_ref(v___y_1293_);
lean_dec_ref(v___f_1291_);
return v___x_1305_;
}
}
else
{
uint8_t v_done_1324_; 
v_done_1324_ = lean_ctor_get_uint8(v_a_1306_, sizeof(void*)*2);
if (v_done_1324_ == 0)
{
lean_object* v_e_x27_1325_; lean_object* v_proof_1326_; uint8_t v_contextDependent_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref_known(v___x_1305_, 1);
v_e_x27_1325_ = lean_ctor_get(v_a_1306_, 0);
v_proof_1326_ = lean_ctor_get(v_a_1306_, 1);
v_contextDependent_1327_ = lean_ctor_get_uint8(v_a_1306_, sizeof(void*)*2 + 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_a_1306_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1329_ = v_a_1306_;
v_isShared_1330_ = v_isSharedCheck_1377_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_proof_1326_);
lean_inc(v_e_x27_1325_);
lean_dec(v_a_1306_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1377_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; 
lean_inc(v___y_1302_);
lean_inc_ref(v___y_1301_);
lean_inc(v___y_1300_);
lean_inc_ref(v___y_1299_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v___y_1294_);
lean_inc_ref(v_e_x27_1325_);
v___x_1331_ = lean_apply_12(v___f_1291_, v___x_1304_, v_e_x27_1325_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, lean_box(0));
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1376_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1376_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1376_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
if (lean_obj_tag(v_a_1332_) == 0)
{
uint8_t v_done_1336_; uint8_t v_contextDependent_1337_; uint8_t v___y_1339_; 
lean_dec_ref(v___y_1293_);
v_done_1336_ = lean_ctor_get_uint8(v_a_1332_, 0);
v_contextDependent_1337_ = lean_ctor_get_uint8(v_a_1332_, 1);
lean_dec_ref_known(v_a_1332_, 0);
if (v_contextDependent_1327_ == 0)
{
v___y_1339_ = v_contextDependent_1337_;
goto v___jp_1338_;
}
else
{
v___y_1339_ = v_contextDependent_1327_;
goto v___jp_1338_;
}
v___jp_1338_:
{
lean_object* v___x_1341_; 
if (v_isShared_1330_ == 0)
{
v___x_1341_ = v___x_1329_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_e_x27_1325_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_proof_1326_);
v___x_1341_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1343_; 
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*2, v_done_1336_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*2 + 1, v___y_1339_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1341_);
v___x_1343_ = v___x_1334_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_object* v_e_x27_1346_; lean_object* v_proof_1347_; uint8_t v_done_1348_; uint8_t v_contextDependent_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1375_; 
lean_del_object(v___x_1334_);
lean_del_object(v___x_1329_);
v_e_x27_1346_ = lean_ctor_get(v_a_1332_, 0);
v_proof_1347_ = lean_ctor_get(v_a_1332_, 1);
v_done_1348_ = lean_ctor_get_uint8(v_a_1332_, sizeof(void*)*2);
v_contextDependent_1349_ = lean_ctor_get_uint8(v_a_1332_, sizeof(void*)*2 + 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_a_1332_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1351_ = v_a_1332_;
v_isShared_1352_ = v_isSharedCheck_1375_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_proof_1347_);
lean_inc(v_e_x27_1346_);
lean_dec(v_a_1332_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1375_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; 
lean_inc_ref(v_e_x27_1346_);
v___x_1353_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1293_, v_e_x27_1325_, v_proof_1326_, v_e_x27_1346_, v_proof_1347_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1366_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1366_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1366_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
uint8_t v___y_1359_; 
if (v_contextDependent_1327_ == 0)
{
v___y_1359_ = v_contextDependent_1349_;
goto v___jp_1358_;
}
else
{
v___y_1359_ = v_contextDependent_1327_;
goto v___jp_1358_;
}
v___jp_1358_:
{
lean_object* v___x_1361_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 1, v_a_1354_);
v___x_1361_ = v___x_1351_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_e_x27_1346_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_a_1354_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*2, v_done_1348_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
lean_ctor_set_uint8(v___x_1361_, sizeof(void*)*2 + 1, v___y_1359_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1361_);
v___x_1363_ = v___x_1356_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_del_object(v___x_1351_);
lean_dec_ref(v_e_x27_1346_);
v_a_1367_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1353_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1353_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1329_);
lean_dec_ref(v_proof_1326_);
lean_dec_ref(v_e_x27_1325_);
lean_dec_ref(v___y_1293_);
return v___x_1331_;
}
}
}
else
{
lean_dec_ref_known(v_a_1306_, 2);
lean_dec_ref(v___y_1293_);
lean_dec_ref(v___f_1291_);
return v___x_1305_;
}
}
}
else
{
lean_dec_ref(v___y_1293_);
lean_dec_ref(v___f_1291_);
return v___x_1305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3___boxed(lean_object* v___f_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__3(v___f_1378_, v_x_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4(lean_object* v___f_1392_, lean_object* v_x_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_box(0);
lean_inc_ref(v___y_1394_);
v___x_1406_ = l_Lean_Meta_Grind_NormSym_simpDIte(v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
if (lean_obj_tag(v_a_1407_) == 0)
{
uint8_t v_done_1408_; 
v_done_1408_ = lean_ctor_get_uint8(v_a_1407_, 0);
if (v_done_1408_ == 0)
{
uint8_t v_contextDependent_1409_; lean_object* v___x_1410_; 
lean_dec_ref_known(v___x_1406_, 1);
v_contextDependent_1409_ = lean_ctor_get_uint8(v_a_1407_, 1);
lean_dec_ref_known(v_a_1407_, 0);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
lean_inc(v___y_1395_);
v___x_1410_ = lean_apply_12(v___f_1392_, v___x_1405_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, lean_box(0));
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; uint8_t v___y_1413_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
if (v_contextDependent_1409_ == 0)
{
lean_dec(v_a_1411_);
return v___x_1410_;
}
else
{
if (lean_obj_tag(v_a_1411_) == 0)
{
uint8_t v_contextDependent_1423_; 
v_contextDependent_1423_ = lean_ctor_get_uint8(v_a_1411_, 1);
v___y_1413_ = v_contextDependent_1423_;
goto v___jp_1412_;
}
else
{
uint8_t v_contextDependent_1424_; 
v_contextDependent_1424_ = lean_ctor_get_uint8(v_a_1411_, sizeof(void*)*2 + 1);
v___y_1413_ = v_contextDependent_1424_;
goto v___jp_1412_;
}
}
v___jp_1412_:
{
if (v___y_1413_ == 0)
{
lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1421_; 
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v___x_1410_, 0);
lean_dec(v_unused_1422_);
v___x_1415_ = v___x_1410_;
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
else
{
lean_dec(v___x_1410_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1411_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
else
{
lean_dec(v_a_1411_);
return v___x_1410_;
}
}
}
else
{
return v___x_1410_;
}
}
else
{
lean_dec_ref_known(v_a_1407_, 0);
lean_dec_ref(v___y_1394_);
lean_dec_ref(v___f_1392_);
return v___x_1406_;
}
}
else
{
uint8_t v_done_1425_; 
v_done_1425_ = lean_ctor_get_uint8(v_a_1407_, sizeof(void*)*2);
if (v_done_1425_ == 0)
{
lean_object* v_e_x27_1426_; lean_object* v_proof_1427_; uint8_t v_contextDependent_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref_known(v___x_1406_, 1);
v_e_x27_1426_ = lean_ctor_get(v_a_1407_, 0);
v_proof_1427_ = lean_ctor_get(v_a_1407_, 1);
v_contextDependent_1428_ = lean_ctor_get_uint8(v_a_1407_, sizeof(void*)*2 + 1);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_a_1407_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1430_ = v_a_1407_;
v_isShared_1431_ = v_isSharedCheck_1478_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_proof_1427_);
lean_inc(v_e_x27_1426_);
lean_dec(v_a_1407_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1478_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; 
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
lean_inc(v___y_1395_);
lean_inc_ref(v_e_x27_1426_);
v___x_1432_ = lean_apply_12(v___f_1392_, v___x_1405_, v_e_x27_1426_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, lean_box(0));
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1477_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1477_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1477_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
if (lean_obj_tag(v_a_1433_) == 0)
{
uint8_t v_done_1437_; uint8_t v_contextDependent_1438_; uint8_t v___y_1440_; 
lean_dec_ref(v___y_1394_);
v_done_1437_ = lean_ctor_get_uint8(v_a_1433_, 0);
v_contextDependent_1438_ = lean_ctor_get_uint8(v_a_1433_, 1);
lean_dec_ref_known(v_a_1433_, 0);
if (v_contextDependent_1428_ == 0)
{
v___y_1440_ = v_contextDependent_1438_;
goto v___jp_1439_;
}
else
{
v___y_1440_ = v_contextDependent_1428_;
goto v___jp_1439_;
}
v___jp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1431_ == 0)
{
v___x_1442_ = v___x_1430_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_e_x27_1426_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_proof_1427_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
lean_ctor_set_uint8(v___x_1442_, sizeof(void*)*2, v_done_1437_);
lean_ctor_set_uint8(v___x_1442_, sizeof(void*)*2 + 1, v___y_1440_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1442_);
v___x_1444_ = v___x_1435_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_e_x27_1447_; lean_object* v_proof_1448_; uint8_t v_done_1449_; uint8_t v_contextDependent_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1476_; 
lean_del_object(v___x_1435_);
lean_del_object(v___x_1430_);
v_e_x27_1447_ = lean_ctor_get(v_a_1433_, 0);
v_proof_1448_ = lean_ctor_get(v_a_1433_, 1);
v_done_1449_ = lean_ctor_get_uint8(v_a_1433_, sizeof(void*)*2);
v_contextDependent_1450_ = lean_ctor_get_uint8(v_a_1433_, sizeof(void*)*2 + 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_a_1433_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1452_ = v_a_1433_;
v_isShared_1453_ = v_isSharedCheck_1476_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_proof_1448_);
lean_inc(v_e_x27_1447_);
lean_dec(v_a_1433_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1476_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; 
lean_inc_ref(v_e_x27_1447_);
v___x_1454_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1394_, v_e_x27_1426_, v_proof_1427_, v_e_x27_1447_, v_proof_1448_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1467_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1467_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1467_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
uint8_t v___y_1460_; 
if (v_contextDependent_1428_ == 0)
{
v___y_1460_ = v_contextDependent_1450_;
goto v___jp_1459_;
}
else
{
v___y_1460_ = v_contextDependent_1428_;
goto v___jp_1459_;
}
v___jp_1459_:
{
lean_object* v___x_1462_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 1, v_a_1455_);
v___x_1462_ = v___x_1452_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_e_x27_1447_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_a_1455_);
lean_ctor_set_uint8(v_reuseFailAlloc_1466_, sizeof(void*)*2, v_done_1449_);
v___x_1462_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; 
lean_ctor_set_uint8(v___x_1462_, sizeof(void*)*2 + 1, v___y_1460_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1462_);
v___x_1464_ = v___x_1457_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_del_object(v___x_1452_);
lean_dec_ref(v_e_x27_1447_);
v_a_1468_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1454_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1454_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1430_);
lean_dec_ref(v_proof_1427_);
lean_dec_ref(v_e_x27_1426_);
lean_dec_ref(v___y_1394_);
return v___x_1432_;
}
}
}
else
{
lean_dec_ref_known(v_a_1407_, 2);
lean_dec_ref(v___y_1394_);
lean_dec_ref(v___f_1392_);
return v___x_1406_;
}
}
}
else
{
lean_dec_ref(v___y_1394_);
lean_dec_ref(v___f_1392_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4___boxed(lean_object* v___f_1479_, lean_object* v_x_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__4(v___f_1479_, v_x_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5(lean_object* v___f_1493_, lean_object* v_x_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_box(0);
lean_inc_ref(v___y_1495_);
v___x_1507_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v___y_1495_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
if (lean_obj_tag(v_a_1508_) == 0)
{
uint8_t v_done_1509_; 
v_done_1509_ = lean_ctor_get_uint8(v_a_1508_, 0);
if (v_done_1509_ == 0)
{
uint8_t v_contextDependent_1510_; lean_object* v___x_1511_; 
lean_dec_ref_known(v___x_1507_, 1);
v_contextDependent_1510_ = lean_ctor_get_uint8(v_a_1508_, 1);
lean_dec_ref_known(v_a_1508_, 0);
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
lean_inc(v___y_1500_);
lean_inc_ref(v___y_1499_);
lean_inc(v___y_1498_);
lean_inc_ref(v___y_1497_);
lean_inc(v___y_1496_);
v___x_1511_ = lean_apply_12(v___f_1493_, v___x_1506_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, lean_box(0));
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; uint8_t v___y_1514_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
if (v_contextDependent_1510_ == 0)
{
lean_dec(v_a_1512_);
return v___x_1511_;
}
else
{
if (lean_obj_tag(v_a_1512_) == 0)
{
uint8_t v_contextDependent_1524_; 
v_contextDependent_1524_ = lean_ctor_get_uint8(v_a_1512_, 1);
v___y_1514_ = v_contextDependent_1524_;
goto v___jp_1513_;
}
else
{
uint8_t v_contextDependent_1525_; 
v_contextDependent_1525_ = lean_ctor_get_uint8(v_a_1512_, sizeof(void*)*2 + 1);
v___y_1514_ = v_contextDependent_1525_;
goto v___jp_1513_;
}
}
v___jp_1513_:
{
if (v___y_1514_ == 0)
{
lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1522_; 
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v___x_1511_, 0);
lean_dec(v_unused_1523_);
v___x_1516_ = v___x_1511_;
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
else
{
lean_dec(v___x_1511_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1512_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1518_);
v___x_1520_ = v___x_1516_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
else
{
lean_dec(v_a_1512_);
return v___x_1511_;
}
}
}
else
{
return v___x_1511_;
}
}
else
{
lean_dec_ref_known(v_a_1508_, 0);
lean_dec_ref(v___y_1495_);
lean_dec_ref(v___f_1493_);
return v___x_1507_;
}
}
else
{
uint8_t v_done_1526_; 
v_done_1526_ = lean_ctor_get_uint8(v_a_1508_, sizeof(void*)*2);
if (v_done_1526_ == 0)
{
lean_object* v_e_x27_1527_; lean_object* v_proof_1528_; uint8_t v_contextDependent_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref_known(v___x_1507_, 1);
v_e_x27_1527_ = lean_ctor_get(v_a_1508_, 0);
v_proof_1528_ = lean_ctor_get(v_a_1508_, 1);
v_contextDependent_1529_ = lean_ctor_get_uint8(v_a_1508_, sizeof(void*)*2 + 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_a_1508_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1531_ = v_a_1508_;
v_isShared_1532_ = v_isSharedCheck_1579_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_proof_1528_);
lean_inc(v_e_x27_1527_);
lean_dec(v_a_1508_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1579_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; 
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
lean_inc(v___y_1500_);
lean_inc_ref(v___y_1499_);
lean_inc(v___y_1498_);
lean_inc_ref(v___y_1497_);
lean_inc(v___y_1496_);
lean_inc_ref(v_e_x27_1527_);
v___x_1533_ = lean_apply_12(v___f_1493_, v___x_1506_, v_e_x27_1527_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, lean_box(0));
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1578_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1578_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1578_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
if (lean_obj_tag(v_a_1534_) == 0)
{
uint8_t v_done_1538_; uint8_t v_contextDependent_1539_; uint8_t v___y_1541_; 
lean_dec_ref(v___y_1495_);
v_done_1538_ = lean_ctor_get_uint8(v_a_1534_, 0);
v_contextDependent_1539_ = lean_ctor_get_uint8(v_a_1534_, 1);
lean_dec_ref_known(v_a_1534_, 0);
if (v_contextDependent_1529_ == 0)
{
v___y_1541_ = v_contextDependent_1539_;
goto v___jp_1540_;
}
else
{
v___y_1541_ = v_contextDependent_1529_;
goto v___jp_1540_;
}
v___jp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1532_ == 0)
{
v___x_1543_ = v___x_1531_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_e_x27_1527_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_proof_1528_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*2, v_done_1538_);
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*2 + 1, v___y_1541_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1543_);
v___x_1545_ = v___x_1536_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v_e_x27_1548_; lean_object* v_proof_1549_; uint8_t v_done_1550_; uint8_t v_contextDependent_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1577_; 
lean_del_object(v___x_1536_);
lean_del_object(v___x_1531_);
v_e_x27_1548_ = lean_ctor_get(v_a_1534_, 0);
v_proof_1549_ = lean_ctor_get(v_a_1534_, 1);
v_done_1550_ = lean_ctor_get_uint8(v_a_1534_, sizeof(void*)*2);
v_contextDependent_1551_ = lean_ctor_get_uint8(v_a_1534_, sizeof(void*)*2 + 1);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_a_1534_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1553_ = v_a_1534_;
v_isShared_1554_ = v_isSharedCheck_1577_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_proof_1549_);
lean_inc(v_e_x27_1548_);
lean_dec(v_a_1534_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1577_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; 
lean_inc_ref(v_e_x27_1548_);
v___x_1555_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1495_, v_e_x27_1527_, v_proof_1528_, v_e_x27_1548_, v_proof_1549_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1568_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1568_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1568_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
uint8_t v___y_1561_; 
if (v_contextDependent_1529_ == 0)
{
v___y_1561_ = v_contextDependent_1551_;
goto v___jp_1560_;
}
else
{
v___y_1561_ = v_contextDependent_1529_;
goto v___jp_1560_;
}
v___jp_1560_:
{
lean_object* v___x_1563_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 1, v_a_1556_);
v___x_1563_ = v___x_1553_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_e_x27_1548_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_a_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*2, v_done_1550_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*2 + 1, v___y_1561_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1563_);
v___x_1565_ = v___x_1558_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_del_object(v___x_1553_);
lean_dec_ref(v_e_x27_1548_);
v_a_1569_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1555_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1555_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1531_);
lean_dec_ref(v_proof_1528_);
lean_dec_ref(v_e_x27_1527_);
lean_dec_ref(v___y_1495_);
return v___x_1533_;
}
}
}
else
{
lean_dec_ref_known(v_a_1508_, 2);
lean_dec_ref(v___y_1495_);
lean_dec_ref(v___f_1493_);
return v___x_1507_;
}
}
}
else
{
lean_dec_ref(v___y_1495_);
lean_dec_ref(v___f_1493_);
return v___x_1507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed(lean_object* v___f_1580_, lean_object* v_x_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__5(v___f_1580_, v_x_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6(lean_object* v___f_1594_, lean_object* v_x_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_box(0);
lean_inc_ref(v___y_1596_);
v___x_1608_ = l_Lean_Meta_Grind_NormSym_simpEq(v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
if (lean_obj_tag(v_a_1609_) == 0)
{
uint8_t v_done_1610_; 
v_done_1610_ = lean_ctor_get_uint8(v_a_1609_, 0);
if (v_done_1610_ == 0)
{
uint8_t v_contextDependent_1611_; lean_object* v___x_1612_; 
lean_dec_ref_known(v___x_1608_, 1);
v_contextDependent_1611_ = lean_ctor_get_uint8(v_a_1609_, 1);
lean_dec_ref_known(v_a_1609_, 0);
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
lean_inc(v___y_1603_);
lean_inc_ref(v___y_1602_);
lean_inc(v___y_1601_);
lean_inc_ref(v___y_1600_);
lean_inc(v___y_1599_);
lean_inc_ref(v___y_1598_);
lean_inc(v___y_1597_);
v___x_1612_ = lean_apply_12(v___f_1594_, v___x_1607_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, lean_box(0));
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; uint8_t v___y_1615_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
if (v_contextDependent_1611_ == 0)
{
lean_dec(v_a_1613_);
return v___x_1612_;
}
else
{
if (lean_obj_tag(v_a_1613_) == 0)
{
uint8_t v_contextDependent_1625_; 
v_contextDependent_1625_ = lean_ctor_get_uint8(v_a_1613_, 1);
v___y_1615_ = v_contextDependent_1625_;
goto v___jp_1614_;
}
else
{
uint8_t v_contextDependent_1626_; 
v_contextDependent_1626_ = lean_ctor_get_uint8(v_a_1613_, sizeof(void*)*2 + 1);
v___y_1615_ = v_contextDependent_1626_;
goto v___jp_1614_;
}
}
v___jp_1614_:
{
if (v___y_1615_ == 0)
{
lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1623_; 
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v___x_1612_, 0);
lean_dec(v_unused_1624_);
v___x_1617_ = v___x_1612_;
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
else
{
lean_dec(v___x_1612_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1613_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1619_);
v___x_1621_ = v___x_1617_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
else
{
lean_dec(v_a_1613_);
return v___x_1612_;
}
}
}
else
{
return v___x_1612_;
}
}
else
{
lean_dec_ref_known(v_a_1609_, 0);
lean_dec_ref(v___y_1596_);
lean_dec_ref(v___f_1594_);
return v___x_1608_;
}
}
else
{
uint8_t v_done_1627_; 
v_done_1627_ = lean_ctor_get_uint8(v_a_1609_, sizeof(void*)*2);
if (v_done_1627_ == 0)
{
lean_object* v_e_x27_1628_; lean_object* v_proof_1629_; uint8_t v_contextDependent_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref_known(v___x_1608_, 1);
v_e_x27_1628_ = lean_ctor_get(v_a_1609_, 0);
v_proof_1629_ = lean_ctor_get(v_a_1609_, 1);
v_contextDependent_1630_ = lean_ctor_get_uint8(v_a_1609_, sizeof(void*)*2 + 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_a_1609_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1632_ = v_a_1609_;
v_isShared_1633_ = v_isSharedCheck_1680_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_proof_1629_);
lean_inc(v_e_x27_1628_);
lean_dec(v_a_1609_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1680_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; 
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
lean_inc(v___y_1603_);
lean_inc_ref(v___y_1602_);
lean_inc(v___y_1601_);
lean_inc_ref(v___y_1600_);
lean_inc(v___y_1599_);
lean_inc_ref(v___y_1598_);
lean_inc(v___y_1597_);
lean_inc_ref(v_e_x27_1628_);
v___x_1634_ = lean_apply_12(v___f_1594_, v___x_1607_, v_e_x27_1628_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, lean_box(0));
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1679_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1679_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1679_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
if (lean_obj_tag(v_a_1635_) == 0)
{
uint8_t v_done_1639_; uint8_t v_contextDependent_1640_; uint8_t v___y_1642_; 
lean_dec_ref(v___y_1596_);
v_done_1639_ = lean_ctor_get_uint8(v_a_1635_, 0);
v_contextDependent_1640_ = lean_ctor_get_uint8(v_a_1635_, 1);
lean_dec_ref_known(v_a_1635_, 0);
if (v_contextDependent_1630_ == 0)
{
v___y_1642_ = v_contextDependent_1640_;
goto v___jp_1641_;
}
else
{
v___y_1642_ = v_contextDependent_1630_;
goto v___jp_1641_;
}
v___jp_1641_:
{
lean_object* v___x_1644_; 
if (v_isShared_1633_ == 0)
{
v___x_1644_ = v___x_1632_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_e_x27_1628_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_proof_1629_);
v___x_1644_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1646_; 
lean_ctor_set_uint8(v___x_1644_, sizeof(void*)*2, v_done_1639_);
lean_ctor_set_uint8(v___x_1644_, sizeof(void*)*2 + 1, v___y_1642_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1644_);
v___x_1646_ = v___x_1637_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
else
{
lean_object* v_e_x27_1649_; lean_object* v_proof_1650_; uint8_t v_done_1651_; uint8_t v_contextDependent_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1678_; 
lean_del_object(v___x_1637_);
lean_del_object(v___x_1632_);
v_e_x27_1649_ = lean_ctor_get(v_a_1635_, 0);
v_proof_1650_ = lean_ctor_get(v_a_1635_, 1);
v_done_1651_ = lean_ctor_get_uint8(v_a_1635_, sizeof(void*)*2);
v_contextDependent_1652_ = lean_ctor_get_uint8(v_a_1635_, sizeof(void*)*2 + 1);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_a_1635_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1654_ = v_a_1635_;
v_isShared_1655_ = v_isSharedCheck_1678_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_proof_1650_);
lean_inc(v_e_x27_1649_);
lean_dec(v_a_1635_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1678_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; 
lean_inc_ref(v_e_x27_1649_);
v___x_1656_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1596_, v_e_x27_1628_, v_proof_1629_, v_e_x27_1649_, v_proof_1650_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1669_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1669_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1669_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
uint8_t v___y_1662_; 
if (v_contextDependent_1630_ == 0)
{
v___y_1662_ = v_contextDependent_1652_;
goto v___jp_1661_;
}
else
{
v___y_1662_ = v_contextDependent_1630_;
goto v___jp_1661_;
}
v___jp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 1, v_a_1657_);
v___x_1664_ = v___x_1654_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_e_x27_1649_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_a_1657_);
lean_ctor_set_uint8(v_reuseFailAlloc_1668_, sizeof(void*)*2, v_done_1651_);
v___x_1664_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
lean_ctor_set_uint8(v___x_1664_, sizeof(void*)*2 + 1, v___y_1662_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1664_);
v___x_1666_ = v___x_1659_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_del_object(v___x_1654_);
lean_dec_ref(v_e_x27_1649_);
v_a_1670_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1656_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1656_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1632_);
lean_dec_ref(v_proof_1629_);
lean_dec_ref(v_e_x27_1628_);
lean_dec_ref(v___y_1596_);
return v___x_1634_;
}
}
}
else
{
lean_dec_ref_known(v_a_1609_, 2);
lean_dec_ref(v___y_1596_);
lean_dec_ref(v___f_1594_);
return v___x_1608_;
}
}
}
else
{
lean_dec_ref(v___y_1596_);
lean_dec_ref(v___f_1594_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed(lean_object* v___f_1681_, lean_object* v_x_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__6(v___f_1681_, v_x_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7(lean_object* v___f_1695_, lean_object* v_x_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = lean_box(0);
lean_inc_ref(v___y_1697_);
v___x_1709_ = l_Lean_Meta_Sym_Simp_simpNatRel___redArg(v___y_1697_, v___y_1701_, v___y_1704_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
if (lean_obj_tag(v_a_1710_) == 0)
{
uint8_t v_done_1711_; 
v_done_1711_ = lean_ctor_get_uint8(v_a_1710_, 0);
if (v_done_1711_ == 0)
{
uint8_t v_contextDependent_1712_; lean_object* v___x_1713_; 
lean_dec_ref_known(v___x_1709_, 1);
v_contextDependent_1712_ = lean_ctor_get_uint8(v_a_1710_, 1);
lean_dec_ref_known(v_a_1710_, 0);
lean_inc(v___y_1706_);
lean_inc_ref(v___y_1705_);
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1701_);
lean_inc(v___y_1700_);
lean_inc_ref(v___y_1699_);
lean_inc(v___y_1698_);
v___x_1713_ = lean_apply_12(v___f_1695_, v___x_1708_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, lean_box(0));
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; uint8_t v___y_1716_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
if (v_contextDependent_1712_ == 0)
{
lean_dec(v_a_1714_);
return v___x_1713_;
}
else
{
if (lean_obj_tag(v_a_1714_) == 0)
{
uint8_t v_contextDependent_1726_; 
v_contextDependent_1726_ = lean_ctor_get_uint8(v_a_1714_, 1);
v___y_1716_ = v_contextDependent_1726_;
goto v___jp_1715_;
}
else
{
uint8_t v_contextDependent_1727_; 
v_contextDependent_1727_ = lean_ctor_get_uint8(v_a_1714_, sizeof(void*)*2 + 1);
v___y_1716_ = v_contextDependent_1727_;
goto v___jp_1715_;
}
}
v___jp_1715_:
{
if (v___y_1716_ == 0)
{
lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1724_; 
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v___x_1713_, 0);
lean_dec(v_unused_1725_);
v___x_1718_ = v___x_1713_;
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
else
{
lean_dec(v___x_1713_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1720_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1714_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1720_);
v___x_1722_ = v___x_1718_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
lean_dec(v_a_1714_);
return v___x_1713_;
}
}
}
else
{
return v___x_1713_;
}
}
else
{
lean_dec_ref_known(v_a_1710_, 0);
lean_dec_ref(v___y_1697_);
lean_dec_ref(v___f_1695_);
return v___x_1709_;
}
}
else
{
uint8_t v_done_1728_; 
v_done_1728_ = lean_ctor_get_uint8(v_a_1710_, sizeof(void*)*2);
if (v_done_1728_ == 0)
{
lean_object* v_e_x27_1729_; lean_object* v_proof_1730_; uint8_t v_contextDependent_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1781_; 
lean_dec_ref_known(v___x_1709_, 1);
v_e_x27_1729_ = lean_ctor_get(v_a_1710_, 0);
v_proof_1730_ = lean_ctor_get(v_a_1710_, 1);
v_contextDependent_1731_ = lean_ctor_get_uint8(v_a_1710_, sizeof(void*)*2 + 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_a_1710_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1733_ = v_a_1710_;
v_isShared_1734_ = v_isSharedCheck_1781_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_proof_1730_);
lean_inc(v_e_x27_1729_);
lean_dec(v_a_1710_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1781_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; 
lean_inc(v___y_1706_);
lean_inc_ref(v___y_1705_);
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1701_);
lean_inc(v___y_1700_);
lean_inc_ref(v___y_1699_);
lean_inc(v___y_1698_);
lean_inc_ref(v_e_x27_1729_);
v___x_1735_ = lean_apply_12(v___f_1695_, v___x_1708_, v_e_x27_1729_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, lean_box(0));
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1780_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1780_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1780_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
if (lean_obj_tag(v_a_1736_) == 0)
{
uint8_t v_done_1740_; uint8_t v_contextDependent_1741_; uint8_t v___y_1743_; 
lean_dec_ref(v___y_1697_);
v_done_1740_ = lean_ctor_get_uint8(v_a_1736_, 0);
v_contextDependent_1741_ = lean_ctor_get_uint8(v_a_1736_, 1);
lean_dec_ref_known(v_a_1736_, 0);
if (v_contextDependent_1731_ == 0)
{
v___y_1743_ = v_contextDependent_1741_;
goto v___jp_1742_;
}
else
{
v___y_1743_ = v_contextDependent_1731_;
goto v___jp_1742_;
}
v___jp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1734_ == 0)
{
v___x_1745_ = v___x_1733_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_e_x27_1729_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_proof_1730_);
v___x_1745_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1747_; 
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*2, v_done_1740_);
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*2 + 1, v___y_1743_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1745_);
v___x_1747_ = v___x_1738_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v_e_x27_1750_; lean_object* v_proof_1751_; uint8_t v_done_1752_; uint8_t v_contextDependent_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1779_; 
lean_del_object(v___x_1738_);
lean_del_object(v___x_1733_);
v_e_x27_1750_ = lean_ctor_get(v_a_1736_, 0);
v_proof_1751_ = lean_ctor_get(v_a_1736_, 1);
v_done_1752_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*2);
v_contextDependent_1753_ = lean_ctor_get_uint8(v_a_1736_, sizeof(void*)*2 + 1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_a_1736_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1755_ = v_a_1736_;
v_isShared_1756_ = v_isSharedCheck_1779_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_proof_1751_);
lean_inc(v_e_x27_1750_);
lean_dec(v_a_1736_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1779_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; 
lean_inc_ref(v_e_x27_1750_);
v___x_1757_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1697_, v_e_x27_1729_, v_proof_1730_, v_e_x27_1750_, v_proof_1751_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1770_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1770_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1770_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
uint8_t v___y_1763_; 
if (v_contextDependent_1731_ == 0)
{
v___y_1763_ = v_contextDependent_1753_;
goto v___jp_1762_;
}
else
{
v___y_1763_ = v_contextDependent_1731_;
goto v___jp_1762_;
}
v___jp_1762_:
{
lean_object* v___x_1765_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v_a_1758_);
v___x_1765_ = v___x_1755_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_e_x27_1750_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_a_1758_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*2, v_done_1752_);
v___x_1765_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1767_; 
lean_ctor_set_uint8(v___x_1765_, sizeof(void*)*2 + 1, v___y_1763_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1765_);
v___x_1767_ = v___x_1760_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_del_object(v___x_1755_);
lean_dec_ref(v_e_x27_1750_);
v_a_1771_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1757_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1757_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1733_);
lean_dec_ref(v_proof_1730_);
lean_dec_ref(v_e_x27_1729_);
lean_dec_ref(v___y_1697_);
return v___x_1735_;
}
}
}
else
{
lean_dec_ref_known(v_a_1710_, 2);
lean_dec_ref(v___y_1697_);
lean_dec_ref(v___f_1695_);
return v___x_1709_;
}
}
}
else
{
lean_dec_ref(v___y_1697_);
lean_dec_ref(v___f_1695_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7___boxed(lean_object* v___f_1782_, lean_object* v_x_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__7(v___f_1782_, v_x_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8(lean_object* v___f_1799_, lean_object* v_x_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__8___closed__0));
v___x_1813_ = lean_box(0);
lean_inc_ref(v___y_1801_);
v___x_1814_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_1801_, v___x_1812_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
if (lean_obj_tag(v_a_1815_) == 0)
{
uint8_t v_done_1816_; 
v_done_1816_ = lean_ctor_get_uint8(v_a_1815_, 0);
if (v_done_1816_ == 0)
{
uint8_t v_contextDependent_1817_; lean_object* v___x_1818_; 
lean_dec_ref_known(v___x_1814_, 1);
v_contextDependent_1817_ = lean_ctor_get_uint8(v_a_1815_, 1);
lean_dec_ref_known(v_a_1815_, 0);
lean_inc(v___y_1810_);
lean_inc_ref(v___y_1809_);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1806_);
lean_inc_ref(v___y_1805_);
lean_inc(v___y_1804_);
lean_inc_ref(v___y_1803_);
lean_inc(v___y_1802_);
v___x_1818_ = lean_apply_12(v___f_1799_, v___x_1813_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, lean_box(0));
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; uint8_t v___y_1821_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
if (v_contextDependent_1817_ == 0)
{
lean_dec(v_a_1819_);
return v___x_1818_;
}
else
{
if (lean_obj_tag(v_a_1819_) == 0)
{
uint8_t v_contextDependent_1831_; 
v_contextDependent_1831_ = lean_ctor_get_uint8(v_a_1819_, 1);
v___y_1821_ = v_contextDependent_1831_;
goto v___jp_1820_;
}
else
{
uint8_t v_contextDependent_1832_; 
v_contextDependent_1832_ = lean_ctor_get_uint8(v_a_1819_, sizeof(void*)*2 + 1);
v___y_1821_ = v_contextDependent_1832_;
goto v___jp_1820_;
}
}
v___jp_1820_:
{
if (v___y_1821_ == 0)
{
lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1829_; 
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v___x_1818_, 0);
lean_dec(v_unused_1830_);
v___x_1823_ = v___x_1818_;
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
else
{
lean_dec(v___x_1818_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1829_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1825_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1819_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1825_);
v___x_1827_ = v___x_1823_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
lean_dec(v_a_1819_);
return v___x_1818_;
}
}
}
else
{
return v___x_1818_;
}
}
else
{
lean_dec_ref_known(v_a_1815_, 0);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v___f_1799_);
return v___x_1814_;
}
}
else
{
uint8_t v_done_1833_; 
v_done_1833_ = lean_ctor_get_uint8(v_a_1815_, sizeof(void*)*2);
if (v_done_1833_ == 0)
{
lean_object* v_e_x27_1834_; lean_object* v_proof_1835_; uint8_t v_contextDependent_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref_known(v___x_1814_, 1);
v_e_x27_1834_ = lean_ctor_get(v_a_1815_, 0);
v_proof_1835_ = lean_ctor_get(v_a_1815_, 1);
v_contextDependent_1836_ = lean_ctor_get_uint8(v_a_1815_, sizeof(void*)*2 + 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_a_1815_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1838_ = v_a_1815_;
v_isShared_1839_ = v_isSharedCheck_1886_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_proof_1835_);
lean_inc(v_e_x27_1834_);
lean_dec(v_a_1815_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1886_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; 
lean_inc(v___y_1810_);
lean_inc_ref(v___y_1809_);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1806_);
lean_inc_ref(v___y_1805_);
lean_inc(v___y_1804_);
lean_inc_ref(v___y_1803_);
lean_inc(v___y_1802_);
lean_inc_ref(v_e_x27_1834_);
v___x_1840_ = lean_apply_12(v___f_1799_, v___x_1813_, v_e_x27_1834_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, lean_box(0));
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1885_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1885_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1885_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
if (lean_obj_tag(v_a_1841_) == 0)
{
uint8_t v_done_1845_; uint8_t v_contextDependent_1846_; uint8_t v___y_1848_; 
lean_dec_ref(v___y_1801_);
v_done_1845_ = lean_ctor_get_uint8(v_a_1841_, 0);
v_contextDependent_1846_ = lean_ctor_get_uint8(v_a_1841_, 1);
lean_dec_ref_known(v_a_1841_, 0);
if (v_contextDependent_1836_ == 0)
{
v___y_1848_ = v_contextDependent_1846_;
goto v___jp_1847_;
}
else
{
v___y_1848_ = v_contextDependent_1836_;
goto v___jp_1847_;
}
v___jp_1847_:
{
lean_object* v___x_1850_; 
if (v_isShared_1839_ == 0)
{
v___x_1850_ = v___x_1838_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_e_x27_1834_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_proof_1835_);
v___x_1850_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1852_; 
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*2, v_done_1845_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*2 + 1, v___y_1848_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1850_);
v___x_1852_ = v___x_1843_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v_e_x27_1855_; lean_object* v_proof_1856_; uint8_t v_done_1857_; uint8_t v_contextDependent_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1884_; 
lean_del_object(v___x_1843_);
lean_del_object(v___x_1838_);
v_e_x27_1855_ = lean_ctor_get(v_a_1841_, 0);
v_proof_1856_ = lean_ctor_get(v_a_1841_, 1);
v_done_1857_ = lean_ctor_get_uint8(v_a_1841_, sizeof(void*)*2);
v_contextDependent_1858_ = lean_ctor_get_uint8(v_a_1841_, sizeof(void*)*2 + 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_a_1841_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1860_ = v_a_1841_;
v_isShared_1861_ = v_isSharedCheck_1884_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_proof_1856_);
lean_inc(v_e_x27_1855_);
lean_dec(v_a_1841_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1884_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; 
lean_inc_ref(v_e_x27_1855_);
v___x_1862_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1801_, v_e_x27_1834_, v_proof_1835_, v_e_x27_1855_, v_proof_1856_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1875_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1875_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1875_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
uint8_t v___y_1868_; 
if (v_contextDependent_1836_ == 0)
{
v___y_1868_ = v_contextDependent_1858_;
goto v___jp_1867_;
}
else
{
v___y_1868_ = v_contextDependent_1836_;
goto v___jp_1867_;
}
v___jp_1867_:
{
lean_object* v___x_1870_; 
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 1, v_a_1863_);
v___x_1870_ = v___x_1860_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_e_x27_1855_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_a_1863_);
lean_ctor_set_uint8(v_reuseFailAlloc_1874_, sizeof(void*)*2, v_done_1857_);
v___x_1870_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1872_; 
lean_ctor_set_uint8(v___x_1870_, sizeof(void*)*2 + 1, v___y_1868_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1870_);
v___x_1872_ = v___x_1865_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_del_object(v___x_1860_);
lean_dec_ref(v_e_x27_1855_);
v_a_1876_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1862_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1862_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1838_);
lean_dec_ref(v_proof_1835_);
lean_dec_ref(v_e_x27_1834_);
lean_dec_ref(v___y_1801_);
return v___x_1840_;
}
}
}
else
{
lean_dec_ref_known(v_a_1815_, 2);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v___f_1799_);
return v___x_1814_;
}
}
}
else
{
lean_dec_ref(v___y_1801_);
lean_dec_ref(v___f_1799_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8___boxed(lean_object* v___f_1887_, lean_object* v_x_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__8(v___f_1887_, v_x_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9(lean_object* v_thms_1901_, lean_object* v_d_1902_, lean_object* v_x_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_pre_1915_; lean_object* v___x_1916_; 
v_pre_1915_ = lean_ctor_get(v_thms_1901_, 0);
v___x_1916_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_pre_1915_, v_d_1902_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9___boxed(lean_object* v_thms_1917_, lean_object* v_d_1918_, lean_object* v_x_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__9(v_thms_1917_, v_d_1918_, v_x_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v_thms_1917_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10(lean_object* v_d_1932_, lean_object* v___f_1933_, lean_object* v_x_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
uint8_t v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = 1;
v___x_1947_ = lean_box(0);
lean_inc_ref(v___y_1935_);
v___x_1948_ = l_Lean_Meta_Sym_Simp_simpArith(v_d_1932_, v___x_1946_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
if (lean_obj_tag(v_a_1949_) == 0)
{
uint8_t v_done_1950_; 
v_done_1950_ = lean_ctor_get_uint8(v_a_1949_, 0);
if (v_done_1950_ == 0)
{
uint8_t v_contextDependent_1951_; lean_object* v___x_1952_; 
lean_dec_ref_known(v___x_1948_, 1);
v_contextDependent_1951_ = lean_ctor_get_uint8(v_a_1949_, 1);
lean_dec_ref_known(v_a_1949_, 0);
lean_inc(v___y_1944_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1937_);
lean_inc(v___y_1936_);
v___x_1952_ = lean_apply_12(v___f_1933_, v___x_1947_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, lean_box(0));
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; uint8_t v___y_1955_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
if (v_contextDependent_1951_ == 0)
{
lean_dec(v_a_1953_);
return v___x_1952_;
}
else
{
if (lean_obj_tag(v_a_1953_) == 0)
{
uint8_t v_contextDependent_1965_; 
v_contextDependent_1965_ = lean_ctor_get_uint8(v_a_1953_, 1);
v___y_1955_ = v_contextDependent_1965_;
goto v___jp_1954_;
}
else
{
uint8_t v_contextDependent_1966_; 
v_contextDependent_1966_ = lean_ctor_get_uint8(v_a_1953_, sizeof(void*)*2 + 1);
v___y_1955_ = v_contextDependent_1966_;
goto v___jp_1954_;
}
}
v___jp_1954_:
{
if (v___y_1955_ == 0)
{
lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1963_; 
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v___x_1952_, 0);
lean_dec(v_unused_1964_);
v___x_1957_ = v___x_1952_;
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
else
{
lean_dec(v___x_1952_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1959_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1953_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1959_);
v___x_1961_ = v___x_1957_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
else
{
lean_dec(v_a_1953_);
return v___x_1952_;
}
}
}
else
{
return v___x_1952_;
}
}
else
{
lean_dec_ref_known(v_a_1949_, 0);
lean_dec_ref(v___y_1935_);
lean_dec_ref(v___f_1933_);
return v___x_1948_;
}
}
else
{
uint8_t v_done_1967_; 
v_done_1967_ = lean_ctor_get_uint8(v_a_1949_, sizeof(void*)*2);
if (v_done_1967_ == 0)
{
lean_object* v_e_x27_1968_; lean_object* v_proof_1969_; uint8_t v_contextDependent_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref_known(v___x_1948_, 1);
v_e_x27_1968_ = lean_ctor_get(v_a_1949_, 0);
v_proof_1969_ = lean_ctor_get(v_a_1949_, 1);
v_contextDependent_1970_ = lean_ctor_get_uint8(v_a_1949_, sizeof(void*)*2 + 1);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_a_1949_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_1972_ = v_a_1949_;
v_isShared_1973_ = v_isSharedCheck_2020_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_proof_1969_);
lean_inc(v_e_x27_1968_);
lean_dec(v_a_1949_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2020_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; 
lean_inc(v___y_1944_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1937_);
lean_inc(v___y_1936_);
lean_inc_ref(v_e_x27_1968_);
v___x_1974_ = lean_apply_12(v___f_1933_, v___x_1947_, v_e_x27_1968_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, lean_box(0));
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2019_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_2019_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2019_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
if (lean_obj_tag(v_a_1975_) == 0)
{
uint8_t v_done_1979_; uint8_t v_contextDependent_1980_; uint8_t v___y_1982_; 
lean_dec_ref(v___y_1935_);
v_done_1979_ = lean_ctor_get_uint8(v_a_1975_, 0);
v_contextDependent_1980_ = lean_ctor_get_uint8(v_a_1975_, 1);
lean_dec_ref_known(v_a_1975_, 0);
if (v_contextDependent_1970_ == 0)
{
v___y_1982_ = v_contextDependent_1980_;
goto v___jp_1981_;
}
else
{
v___y_1982_ = v_contextDependent_1970_;
goto v___jp_1981_;
}
v___jp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1973_ == 0)
{
v___x_1984_ = v___x_1972_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_e_x27_1968_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_proof_1969_);
v___x_1984_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*2, v_done_1979_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*2 + 1, v___y_1982_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1984_);
v___x_1986_ = v___x_1977_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_object* v_e_x27_1989_; lean_object* v_proof_1990_; uint8_t v_done_1991_; uint8_t v_contextDependent_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2018_; 
lean_del_object(v___x_1977_);
lean_del_object(v___x_1972_);
v_e_x27_1989_ = lean_ctor_get(v_a_1975_, 0);
v_proof_1990_ = lean_ctor_get(v_a_1975_, 1);
v_done_1991_ = lean_ctor_get_uint8(v_a_1975_, sizeof(void*)*2);
v_contextDependent_1992_ = lean_ctor_get_uint8(v_a_1975_, sizeof(void*)*2 + 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_a_1975_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1994_ = v_a_1975_;
v_isShared_1995_ = v_isSharedCheck_2018_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_proof_1990_);
lean_inc(v_e_x27_1989_);
lean_dec(v_a_1975_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2018_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; 
lean_inc_ref(v_e_x27_1989_);
v___x_1996_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1935_, v_e_x27_1968_, v_proof_1969_, v_e_x27_1989_, v_proof_1990_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2009_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2009_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2009_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
uint8_t v___y_2002_; 
if (v_contextDependent_1970_ == 0)
{
v___y_2002_ = v_contextDependent_1992_;
goto v___jp_2001_;
}
else
{
v___y_2002_ = v_contextDependent_1970_;
goto v___jp_2001_;
}
v___jp_2001_:
{
lean_object* v___x_2004_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 1, v_a_1997_);
v___x_2004_ = v___x_1994_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_e_x27_1989_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_a_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*2, v_done_1991_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*2 + 1, v___y_2002_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2004_);
v___x_2006_ = v___x_1999_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_del_object(v___x_1994_);
lean_dec_ref(v_e_x27_1989_);
v_a_2010_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1996_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1996_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1972_);
lean_dec_ref(v_proof_1969_);
lean_dec_ref(v_e_x27_1968_);
lean_dec_ref(v___y_1935_);
return v___x_1974_;
}
}
}
else
{
lean_dec_ref_known(v_a_1949_, 2);
lean_dec_ref(v___y_1935_);
lean_dec_ref(v___f_1933_);
return v___x_1948_;
}
}
}
else
{
lean_dec_ref(v___y_1935_);
lean_dec_ref(v___f_1933_);
return v___x_1948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10___boxed(lean_object* v_d_2021_, lean_object* v___f_2022_, lean_object* v_x_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__10(v_d_2021_, v___f_2022_, v_x_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11(lean_object* v___f_2036_, lean_object* v_x_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_box(0);
lean_inc_ref(v___y_2038_);
v___x_2050_ = l_Lean_Meta_Grind_NormSym_pushNot(v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
if (lean_obj_tag(v_a_2051_) == 0)
{
uint8_t v_done_2052_; 
v_done_2052_ = lean_ctor_get_uint8(v_a_2051_, 0);
if (v_done_2052_ == 0)
{
uint8_t v_contextDependent_2053_; lean_object* v___x_2054_; 
lean_dec_ref_known(v___x_2050_, 1);
v_contextDependent_2053_ = lean_ctor_get_uint8(v_a_2051_, 1);
lean_dec_ref_known(v_a_2051_, 0);
lean_inc(v___y_2047_);
lean_inc_ref(v___y_2046_);
lean_inc(v___y_2045_);
lean_inc_ref(v___y_2044_);
lean_inc(v___y_2043_);
lean_inc_ref(v___y_2042_);
lean_inc(v___y_2041_);
lean_inc_ref(v___y_2040_);
lean_inc(v___y_2039_);
v___x_2054_ = lean_apply_12(v___f_2036_, v___x_2049_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, lean_box(0));
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; uint8_t v___y_2057_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
if (v_contextDependent_2053_ == 0)
{
lean_dec(v_a_2055_);
return v___x_2054_;
}
else
{
if (lean_obj_tag(v_a_2055_) == 0)
{
uint8_t v_contextDependent_2067_; 
v_contextDependent_2067_ = lean_ctor_get_uint8(v_a_2055_, 1);
v___y_2057_ = v_contextDependent_2067_;
goto v___jp_2056_;
}
else
{
uint8_t v_contextDependent_2068_; 
v_contextDependent_2068_ = lean_ctor_get_uint8(v_a_2055_, sizeof(void*)*2 + 1);
v___y_2057_ = v_contextDependent_2068_;
goto v___jp_2056_;
}
}
v___jp_2056_:
{
if (v___y_2057_ == 0)
{
lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2065_; 
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v___x_2054_, 0);
lean_dec(v_unused_2066_);
v___x_2059_ = v___x_2054_;
v_isShared_2060_ = v_isSharedCheck_2065_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v___x_2054_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2065_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2061_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2055_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2061_);
v___x_2063_ = v___x_2059_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
else
{
lean_dec(v_a_2055_);
return v___x_2054_;
}
}
}
else
{
return v___x_2054_;
}
}
else
{
lean_dec_ref_known(v_a_2051_, 0);
lean_dec_ref(v___y_2038_);
lean_dec_ref(v___f_2036_);
return v___x_2050_;
}
}
else
{
uint8_t v_done_2069_; 
v_done_2069_ = lean_ctor_get_uint8(v_a_2051_, sizeof(void*)*2);
if (v_done_2069_ == 0)
{
lean_object* v_e_x27_2070_; lean_object* v_proof_2071_; uint8_t v_contextDependent_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref_known(v___x_2050_, 1);
v_e_x27_2070_ = lean_ctor_get(v_a_2051_, 0);
v_proof_2071_ = lean_ctor_get(v_a_2051_, 1);
v_contextDependent_2072_ = lean_ctor_get_uint8(v_a_2051_, sizeof(void*)*2 + 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_a_2051_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2074_ = v_a_2051_;
v_isShared_2075_ = v_isSharedCheck_2122_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_proof_2071_);
lean_inc(v_e_x27_2070_);
lean_dec(v_a_2051_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2122_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; 
lean_inc(v___y_2047_);
lean_inc_ref(v___y_2046_);
lean_inc(v___y_2045_);
lean_inc_ref(v___y_2044_);
lean_inc(v___y_2043_);
lean_inc_ref(v___y_2042_);
lean_inc(v___y_2041_);
lean_inc_ref(v___y_2040_);
lean_inc(v___y_2039_);
lean_inc_ref(v_e_x27_2070_);
v___x_2076_ = lean_apply_12(v___f_2036_, v___x_2049_, v_e_x27_2070_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, lean_box(0));
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2121_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2121_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2121_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
if (lean_obj_tag(v_a_2077_) == 0)
{
uint8_t v_done_2081_; uint8_t v_contextDependent_2082_; uint8_t v___y_2084_; 
lean_dec_ref(v___y_2038_);
v_done_2081_ = lean_ctor_get_uint8(v_a_2077_, 0);
v_contextDependent_2082_ = lean_ctor_get_uint8(v_a_2077_, 1);
lean_dec_ref_known(v_a_2077_, 0);
if (v_contextDependent_2072_ == 0)
{
v___y_2084_ = v_contextDependent_2082_;
goto v___jp_2083_;
}
else
{
v___y_2084_ = v_contextDependent_2072_;
goto v___jp_2083_;
}
v___jp_2083_:
{
lean_object* v___x_2086_; 
if (v_isShared_2075_ == 0)
{
v___x_2086_ = v___x_2074_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_e_x27_2070_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_proof_2071_);
v___x_2086_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2088_; 
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*2, v_done_2081_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*2 + 1, v___y_2084_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2086_);
v___x_2088_ = v___x_2079_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_e_x27_2091_; lean_object* v_proof_2092_; uint8_t v_done_2093_; uint8_t v_contextDependent_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2120_; 
lean_del_object(v___x_2079_);
lean_del_object(v___x_2074_);
v_e_x27_2091_ = lean_ctor_get(v_a_2077_, 0);
v_proof_2092_ = lean_ctor_get(v_a_2077_, 1);
v_done_2093_ = lean_ctor_get_uint8(v_a_2077_, sizeof(void*)*2);
v_contextDependent_2094_ = lean_ctor_get_uint8(v_a_2077_, sizeof(void*)*2 + 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_a_2077_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2096_ = v_a_2077_;
v_isShared_2097_ = v_isSharedCheck_2120_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_proof_2092_);
lean_inc(v_e_x27_2091_);
lean_dec(v_a_2077_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2120_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; 
lean_inc_ref(v_e_x27_2091_);
v___x_2098_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2038_, v_e_x27_2070_, v_proof_2071_, v_e_x27_2091_, v_proof_2092_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2111_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2111_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2111_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
uint8_t v___y_2104_; 
if (v_contextDependent_2072_ == 0)
{
v___y_2104_ = v_contextDependent_2094_;
goto v___jp_2103_;
}
else
{
v___y_2104_ = v_contextDependent_2072_;
goto v___jp_2103_;
}
v___jp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v_a_2099_);
v___x_2106_ = v___x_2096_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_e_x27_2091_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_a_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2110_, sizeof(void*)*2, v_done_2093_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
lean_ctor_set_uint8(v___x_2106_, sizeof(void*)*2 + 1, v___y_2104_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2106_);
v___x_2108_ = v___x_2101_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_del_object(v___x_2096_);
lean_dec_ref(v_e_x27_2091_);
v_a_2112_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2098_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2098_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2074_);
lean_dec_ref(v_proof_2071_);
lean_dec_ref(v_e_x27_2070_);
lean_dec_ref(v___y_2038_);
return v___x_2076_;
}
}
}
else
{
lean_dec_ref_known(v_a_2051_, 2);
lean_dec_ref(v___y_2038_);
lean_dec_ref(v___f_2036_);
return v___x_2050_;
}
}
}
else
{
lean_dec_ref(v___y_2038_);
lean_dec_ref(v___f_2036_);
return v___x_2050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed(lean_object* v___f_2123_, lean_object* v_x_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__11(v___f_2123_, v_x_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12(lean_object* v_pre_2137_, lean_object* v___f_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = lean_box(0);
lean_inc(v___y_2148_);
lean_inc_ref(v___y_2147_);
lean_inc(v___y_2146_);
lean_inc_ref(v___y_2145_);
lean_inc(v___y_2144_);
lean_inc_ref(v___y_2143_);
lean_inc(v___y_2142_);
lean_inc_ref(v___y_2141_);
lean_inc(v___y_2140_);
lean_inc_ref(v___y_2139_);
v___x_2151_ = lean_apply_11(v_pre_2137_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, lean_box(0));
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
if (lean_obj_tag(v_a_2152_) == 0)
{
uint8_t v_done_2153_; 
v_done_2153_ = lean_ctor_get_uint8(v_a_2152_, 0);
if (v_done_2153_ == 0)
{
uint8_t v_contextDependent_2154_; lean_object* v___x_2155_; 
lean_dec_ref_known(v___x_2151_, 1);
v_contextDependent_2154_ = lean_ctor_get_uint8(v_a_2152_, 1);
lean_dec_ref_known(v_a_2152_, 0);
v___x_2155_ = lean_apply_12(v___f_2138_, v___x_2150_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, lean_box(0));
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; uint8_t v___y_2158_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
if (v_contextDependent_2154_ == 0)
{
lean_dec(v_a_2156_);
return v___x_2155_;
}
else
{
if (lean_obj_tag(v_a_2156_) == 0)
{
uint8_t v_contextDependent_2168_; 
v_contextDependent_2168_ = lean_ctor_get_uint8(v_a_2156_, 1);
v___y_2158_ = v_contextDependent_2168_;
goto v___jp_2157_;
}
else
{
uint8_t v_contextDependent_2169_; 
v_contextDependent_2169_ = lean_ctor_get_uint8(v_a_2156_, sizeof(void*)*2 + 1);
v___y_2158_ = v_contextDependent_2169_;
goto v___jp_2157_;
}
}
v___jp_2157_:
{
if (v___y_2158_ == 0)
{
lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2166_; 
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; 
v_unused_2167_ = lean_ctor_get(v___x_2155_, 0);
lean_dec(v_unused_2167_);
v___x_2160_ = v___x_2155_;
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
else
{
lean_dec(v___x_2155_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2162_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2156_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2162_);
v___x_2164_ = v___x_2160_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
else
{
lean_dec(v_a_2156_);
return v___x_2155_;
}
}
}
else
{
return v___x_2155_;
}
}
else
{
lean_dec_ref_known(v_a_2152_, 0);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec_ref(v___f_2138_);
return v___x_2151_;
}
}
else
{
uint8_t v_done_2170_; 
v_done_2170_ = lean_ctor_get_uint8(v_a_2152_, sizeof(void*)*2);
if (v_done_2170_ == 0)
{
lean_object* v_e_x27_2171_; lean_object* v_proof_2172_; uint8_t v_contextDependent_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref_known(v___x_2151_, 1);
v_e_x27_2171_ = lean_ctor_get(v_a_2152_, 0);
v_proof_2172_ = lean_ctor_get(v_a_2152_, 1);
v_contextDependent_2173_ = lean_ctor_get_uint8(v_a_2152_, sizeof(void*)*2 + 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_a_2152_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2175_ = v_a_2152_;
v_isShared_2176_ = v_isSharedCheck_2223_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_proof_2172_);
lean_inc(v_e_x27_2171_);
lean_dec(v_a_2152_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2223_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; 
lean_inc(v___y_2148_);
lean_inc_ref(v___y_2147_);
lean_inc(v___y_2146_);
lean_inc_ref(v___y_2145_);
lean_inc(v___y_2144_);
lean_inc_ref(v___y_2143_);
lean_inc_ref(v_e_x27_2171_);
v___x_2177_ = lean_apply_12(v___f_2138_, v___x_2150_, v_e_x27_2171_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, lean_box(0));
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2222_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2222_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2222_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
if (lean_obj_tag(v_a_2178_) == 0)
{
uint8_t v_done_2182_; uint8_t v_contextDependent_2183_; uint8_t v___y_2185_; 
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec_ref(v___y_2139_);
v_done_2182_ = lean_ctor_get_uint8(v_a_2178_, 0);
v_contextDependent_2183_ = lean_ctor_get_uint8(v_a_2178_, 1);
lean_dec_ref_known(v_a_2178_, 0);
if (v_contextDependent_2173_ == 0)
{
v___y_2185_ = v_contextDependent_2183_;
goto v___jp_2184_;
}
else
{
v___y_2185_ = v_contextDependent_2173_;
goto v___jp_2184_;
}
v___jp_2184_:
{
lean_object* v___x_2187_; 
if (v_isShared_2176_ == 0)
{
v___x_2187_ = v___x_2175_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_e_x27_2171_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_proof_2172_);
v___x_2187_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*2, v_done_2182_);
lean_ctor_set_uint8(v___x_2187_, sizeof(void*)*2 + 1, v___y_2185_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2187_);
v___x_2189_ = v___x_2180_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_object* v_e_x27_2192_; lean_object* v_proof_2193_; uint8_t v_done_2194_; uint8_t v_contextDependent_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2221_; 
lean_del_object(v___x_2180_);
lean_del_object(v___x_2175_);
v_e_x27_2192_ = lean_ctor_get(v_a_2178_, 0);
v_proof_2193_ = lean_ctor_get(v_a_2178_, 1);
v_done_2194_ = lean_ctor_get_uint8(v_a_2178_, sizeof(void*)*2);
v_contextDependent_2195_ = lean_ctor_get_uint8(v_a_2178_, sizeof(void*)*2 + 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_a_2178_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2197_ = v_a_2178_;
v_isShared_2198_ = v_isSharedCheck_2221_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_proof_2193_);
lean_inc(v_e_x27_2192_);
lean_dec(v_a_2178_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2221_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; 
lean_inc_ref(v_e_x27_2192_);
v___x_2199_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2139_, v_e_x27_2171_, v_proof_2172_, v_e_x27_2192_, v_proof_2193_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2212_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2212_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2212_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
uint8_t v___y_2205_; 
if (v_contextDependent_2173_ == 0)
{
v___y_2205_ = v_contextDependent_2195_;
goto v___jp_2204_;
}
else
{
v___y_2205_ = v_contextDependent_2173_;
goto v___jp_2204_;
}
v___jp_2204_:
{
lean_object* v___x_2207_; 
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 1, v_a_2200_);
v___x_2207_ = v___x_2197_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_e_x27_2192_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_a_2200_);
lean_ctor_set_uint8(v_reuseFailAlloc_2211_, sizeof(void*)*2, v_done_2194_);
v___x_2207_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2209_; 
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*2 + 1, v___y_2205_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2207_);
v___x_2209_ = v___x_2202_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_del_object(v___x_2197_);
lean_dec_ref(v_e_x27_2192_);
v_a_2213_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2199_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2199_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2175_);
lean_dec_ref(v_proof_2172_);
lean_dec_ref(v_e_x27_2171_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec_ref(v___y_2139_);
return v___x_2177_;
}
}
}
else
{
lean_dec_ref_known(v_a_2152_, 2);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec_ref(v___f_2138_);
return v___x_2151_;
}
}
}
else
{
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec_ref(v___f_2138_);
return v___x_2151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed(lean_object* v_pre_2224_, lean_object* v___f_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__12(v_pre_2224_, v___f_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13(lean_object* v_post_2238_, lean_object* v_d_2239_, lean_object* v___f_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_box(0);
lean_inc_ref(v___y_2241_);
v___x_2253_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_post_2238_, v_d_2239_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
if (lean_obj_tag(v_a_2254_) == 0)
{
uint8_t v_done_2255_; 
v_done_2255_ = lean_ctor_get_uint8(v_a_2254_, 0);
if (v_done_2255_ == 0)
{
uint8_t v_contextDependent_2256_; lean_object* v___x_2257_; 
lean_dec_ref_known(v___x_2253_, 1);
v_contextDependent_2256_ = lean_ctor_get_uint8(v_a_2254_, 1);
lean_dec_ref_known(v_a_2254_, 0);
v___x_2257_ = lean_apply_12(v___f_2240_, v___x_2252_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, lean_box(0));
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; uint8_t v___y_2260_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
if (v_contextDependent_2256_ == 0)
{
lean_dec(v_a_2258_);
return v___x_2257_;
}
else
{
if (lean_obj_tag(v_a_2258_) == 0)
{
uint8_t v_contextDependent_2270_; 
v_contextDependent_2270_ = lean_ctor_get_uint8(v_a_2258_, 1);
v___y_2260_ = v_contextDependent_2270_;
goto v___jp_2259_;
}
else
{
uint8_t v_contextDependent_2271_; 
v_contextDependent_2271_ = lean_ctor_get_uint8(v_a_2258_, sizeof(void*)*2 + 1);
v___y_2260_ = v_contextDependent_2271_;
goto v___jp_2259_;
}
}
v___jp_2259_:
{
if (v___y_2260_ == 0)
{
lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2268_; 
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2268_ == 0)
{
lean_object* v_unused_2269_; 
v_unused_2269_ = lean_ctor_get(v___x_2257_, 0);
lean_dec(v_unused_2269_);
v___x_2262_ = v___x_2257_;
v_isShared_2263_ = v_isSharedCheck_2268_;
goto v_resetjp_2261_;
}
else
{
lean_dec(v___x_2257_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2268_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2264_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2258_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2264_);
v___x_2266_ = v___x_2262_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
else
{
lean_dec(v_a_2258_);
return v___x_2257_;
}
}
}
else
{
return v___x_2257_;
}
}
else
{
lean_dec_ref_known(v_a_2254_, 0);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec_ref(v___f_2240_);
return v___x_2253_;
}
}
else
{
uint8_t v_done_2272_; 
v_done_2272_ = lean_ctor_get_uint8(v_a_2254_, sizeof(void*)*2);
if (v_done_2272_ == 0)
{
lean_object* v_e_x27_2273_; lean_object* v_proof_2274_; uint8_t v_contextDependent_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref_known(v___x_2253_, 1);
v_e_x27_2273_ = lean_ctor_get(v_a_2254_, 0);
v_proof_2274_ = lean_ctor_get(v_a_2254_, 1);
v_contextDependent_2275_ = lean_ctor_get_uint8(v_a_2254_, sizeof(void*)*2 + 1);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_a_2254_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2277_ = v_a_2254_;
v_isShared_2278_ = v_isSharedCheck_2325_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_proof_2274_);
lean_inc(v_e_x27_2273_);
lean_dec(v_a_2254_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2325_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; 
lean_inc(v___y_2250_);
lean_inc_ref(v___y_2249_);
lean_inc(v___y_2248_);
lean_inc_ref(v___y_2247_);
lean_inc(v___y_2246_);
lean_inc_ref(v___y_2245_);
lean_inc_ref(v_e_x27_2273_);
v___x_2279_ = lean_apply_12(v___f_2240_, v___x_2252_, v_e_x27_2273_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, lean_box(0));
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2324_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2324_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2324_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
if (lean_obj_tag(v_a_2280_) == 0)
{
uint8_t v_done_2284_; uint8_t v_contextDependent_2285_; uint8_t v___y_2287_; 
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec_ref(v___y_2241_);
v_done_2284_ = lean_ctor_get_uint8(v_a_2280_, 0);
v_contextDependent_2285_ = lean_ctor_get_uint8(v_a_2280_, 1);
lean_dec_ref_known(v_a_2280_, 0);
if (v_contextDependent_2275_ == 0)
{
v___y_2287_ = v_contextDependent_2285_;
goto v___jp_2286_;
}
else
{
v___y_2287_ = v_contextDependent_2275_;
goto v___jp_2286_;
}
v___jp_2286_:
{
lean_object* v___x_2289_; 
if (v_isShared_2278_ == 0)
{
v___x_2289_ = v___x_2277_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_e_x27_2273_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_proof_2274_);
v___x_2289_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2291_; 
lean_ctor_set_uint8(v___x_2289_, sizeof(void*)*2, v_done_2284_);
lean_ctor_set_uint8(v___x_2289_, sizeof(void*)*2 + 1, v___y_2287_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2289_);
v___x_2291_ = v___x_2282_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_e_x27_2294_; lean_object* v_proof_2295_; uint8_t v_done_2296_; uint8_t v_contextDependent_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2323_; 
lean_del_object(v___x_2282_);
lean_del_object(v___x_2277_);
v_e_x27_2294_ = lean_ctor_get(v_a_2280_, 0);
v_proof_2295_ = lean_ctor_get(v_a_2280_, 1);
v_done_2296_ = lean_ctor_get_uint8(v_a_2280_, sizeof(void*)*2);
v_contextDependent_2297_ = lean_ctor_get_uint8(v_a_2280_, sizeof(void*)*2 + 1);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_a_2280_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2299_ = v_a_2280_;
v_isShared_2300_ = v_isSharedCheck_2323_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_proof_2295_);
lean_inc(v_e_x27_2294_);
lean_dec(v_a_2280_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2323_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; 
lean_inc_ref(v_e_x27_2294_);
v___x_2301_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2241_, v_e_x27_2273_, v_proof_2274_, v_e_x27_2294_, v_proof_2295_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2314_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2314_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2314_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
uint8_t v___y_2307_; 
if (v_contextDependent_2275_ == 0)
{
v___y_2307_ = v_contextDependent_2297_;
goto v___jp_2306_;
}
else
{
v___y_2307_ = v_contextDependent_2275_;
goto v___jp_2306_;
}
v___jp_2306_:
{
lean_object* v___x_2309_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 1, v_a_2302_);
v___x_2309_ = v___x_2299_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_e_x27_2294_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_a_2302_);
lean_ctor_set_uint8(v_reuseFailAlloc_2313_, sizeof(void*)*2, v_done_2296_);
v___x_2309_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2311_; 
lean_ctor_set_uint8(v___x_2309_, sizeof(void*)*2 + 1, v___y_2307_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2309_);
v___x_2311_ = v___x_2304_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_del_object(v___x_2299_);
lean_dec_ref(v_e_x27_2294_);
v_a_2315_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2301_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2301_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2277_);
lean_dec_ref(v_proof_2274_);
lean_dec_ref(v_e_x27_2273_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec_ref(v___y_2241_);
return v___x_2279_;
}
}
}
else
{
lean_dec_ref_known(v_a_2254_, 2);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec_ref(v___f_2240_);
return v___x_2253_;
}
}
}
else
{
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec_ref(v___f_2240_);
return v___x_2253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed(lean_object* v_post_2326_, lean_object* v_d_2327_, lean_object* v___f_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__13(v_post_2326_, v_d_2327_, v___f_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec_ref(v_post_2326_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14(lean_object* v_pre_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; 
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc_ref(v___y_2342_);
v___x_2353_ = lean_apply_11(v_pre_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, lean_box(0));
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
if (lean_obj_tag(v_a_2354_) == 0)
{
uint8_t v_done_2355_; 
v_done_2355_ = lean_ctor_get_uint8(v_a_2354_, 0);
if (v_done_2355_ == 0)
{
uint8_t v_contextDependent_2356_; lean_object* v___x_2357_; 
lean_dec_ref_known(v___x_2353_, 1);
v_contextDependent_2356_ = lean_ctor_get_uint8(v_a_2354_, 1);
lean_dec_ref_known(v_a_2354_, 0);
v___x_2357_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v___y_2342_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; uint8_t v___y_2360_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
if (v_contextDependent_2356_ == 0)
{
return v___x_2357_;
}
else
{
if (lean_obj_tag(v_a_2358_) == 0)
{
uint8_t v_contextDependent_2370_; 
v_contextDependent_2370_ = lean_ctor_get_uint8(v_a_2358_, 1);
v___y_2360_ = v_contextDependent_2370_;
goto v___jp_2359_;
}
else
{
uint8_t v_contextDependent_2371_; 
v_contextDependent_2371_ = lean_ctor_get_uint8(v_a_2358_, sizeof(void*)*2 + 1);
v___y_2360_ = v_contextDependent_2371_;
goto v___jp_2359_;
}
}
v___jp_2359_:
{
if (v___y_2360_ == 0)
{
lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2368_; 
lean_inc(v_a_2358_);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; 
v_unused_2369_ = lean_ctor_get(v___x_2357_, 0);
lean_dec(v_unused_2369_);
v___x_2362_ = v___x_2357_;
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
else
{
lean_dec(v___x_2357_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2364_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2358_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2364_);
v___x_2366_ = v___x_2362_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
return v___x_2357_;
}
}
}
else
{
return v___x_2357_;
}
}
else
{
lean_dec_ref_known(v_a_2354_, 0);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec_ref(v___y_2342_);
return v___x_2353_;
}
}
else
{
uint8_t v_done_2372_; 
v_done_2372_ = lean_ctor_get_uint8(v_a_2354_, sizeof(void*)*2);
if (v_done_2372_ == 0)
{
lean_object* v_e_x27_2373_; lean_object* v_proof_2374_; uint8_t v_contextDependent_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2425_; 
lean_dec_ref_known(v___x_2353_, 1);
v_e_x27_2373_ = lean_ctor_get(v_a_2354_, 0);
v_proof_2374_ = lean_ctor_get(v_a_2354_, 1);
v_contextDependent_2375_ = lean_ctor_get_uint8(v_a_2354_, sizeof(void*)*2 + 1);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_a_2354_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2377_ = v_a_2354_;
v_isShared_2378_ = v_isSharedCheck_2425_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_proof_2374_);
lean_inc(v_e_x27_2373_);
lean_dec(v_a_2354_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2425_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; 
lean_inc_ref(v_e_x27_2373_);
v___x_2379_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v_e_x27_2373_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2424_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2424_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2424_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
if (lean_obj_tag(v_a_2380_) == 0)
{
uint8_t v_done_2384_; uint8_t v_contextDependent_2385_; uint8_t v___y_2387_; 
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec_ref(v___y_2342_);
v_done_2384_ = lean_ctor_get_uint8(v_a_2380_, 0);
v_contextDependent_2385_ = lean_ctor_get_uint8(v_a_2380_, 1);
lean_dec_ref_known(v_a_2380_, 0);
if (v_contextDependent_2375_ == 0)
{
v___y_2387_ = v_contextDependent_2385_;
goto v___jp_2386_;
}
else
{
v___y_2387_ = v_contextDependent_2375_;
goto v___jp_2386_;
}
v___jp_2386_:
{
lean_object* v___x_2389_; 
if (v_isShared_2378_ == 0)
{
v___x_2389_ = v___x_2377_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_e_x27_2373_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_proof_2374_);
v___x_2389_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2391_; 
lean_ctor_set_uint8(v___x_2389_, sizeof(void*)*2, v_done_2384_);
lean_ctor_set_uint8(v___x_2389_, sizeof(void*)*2 + 1, v___y_2387_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2389_);
v___x_2391_ = v___x_2382_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_object* v_e_x27_2394_; lean_object* v_proof_2395_; uint8_t v_done_2396_; uint8_t v_contextDependent_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2423_; 
lean_del_object(v___x_2382_);
lean_del_object(v___x_2377_);
v_e_x27_2394_ = lean_ctor_get(v_a_2380_, 0);
v_proof_2395_ = lean_ctor_get(v_a_2380_, 1);
v_done_2396_ = lean_ctor_get_uint8(v_a_2380_, sizeof(void*)*2);
v_contextDependent_2397_ = lean_ctor_get_uint8(v_a_2380_, sizeof(void*)*2 + 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_a_2380_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2399_ = v_a_2380_;
v_isShared_2400_ = v_isSharedCheck_2423_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_proof_2395_);
lean_inc(v_e_x27_2394_);
lean_dec(v_a_2380_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2423_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; 
lean_inc_ref(v_e_x27_2394_);
v___x_2401_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2342_, v_e_x27_2373_, v_proof_2374_, v_e_x27_2394_, v_proof_2395_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2414_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2414_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2414_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
uint8_t v___y_2407_; 
if (v_contextDependent_2375_ == 0)
{
v___y_2407_ = v_contextDependent_2397_;
goto v___jp_2406_;
}
else
{
v___y_2407_ = v_contextDependent_2375_;
goto v___jp_2406_;
}
v___jp_2406_:
{
lean_object* v___x_2409_; 
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 1, v_a_2402_);
v___x_2409_ = v___x_2399_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_e_x27_2394_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_a_2402_);
lean_ctor_set_uint8(v_reuseFailAlloc_2413_, sizeof(void*)*2, v_done_2396_);
v___x_2409_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2411_; 
lean_ctor_set_uint8(v___x_2409_, sizeof(void*)*2 + 1, v___y_2407_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2409_);
v___x_2411_ = v___x_2404_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_del_object(v___x_2399_);
lean_dec_ref(v_e_x27_2394_);
v_a_2415_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2401_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2401_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2377_);
lean_dec_ref(v_proof_2374_);
lean_dec_ref(v_e_x27_2373_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec_ref(v___y_2342_);
return v___x_2379_;
}
}
}
else
{
lean_dec_ref_known(v_a_2354_, 2);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec_ref(v___y_2342_);
return v___x_2353_;
}
}
}
else
{
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec_ref(v___y_2342_);
return v___x_2353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed(lean_object* v_pre_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__14(v_pre_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15(lean_object* v___f_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_box(0);
lean_inc_ref(v___y_2440_);
v___x_2452_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_2440_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
if (lean_obj_tag(v_a_2453_) == 0)
{
uint8_t v_done_2454_; 
v_done_2454_ = lean_ctor_get_uint8(v_a_2453_, 0);
if (v_done_2454_ == 0)
{
uint8_t v_contextDependent_2455_; lean_object* v___x_2456_; 
lean_dec_ref_known(v___x_2452_, 1);
v_contextDependent_2455_ = lean_ctor_get_uint8(v_a_2453_, 1);
lean_dec_ref_known(v_a_2453_, 0);
v___x_2456_ = lean_apply_12(v___f_2439_, v___x_2451_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, lean_box(0));
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; uint8_t v___y_2459_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
if (v_contextDependent_2455_ == 0)
{
lean_dec(v_a_2457_);
return v___x_2456_;
}
else
{
if (lean_obj_tag(v_a_2457_) == 0)
{
uint8_t v_contextDependent_2469_; 
v_contextDependent_2469_ = lean_ctor_get_uint8(v_a_2457_, 1);
v___y_2459_ = v_contextDependent_2469_;
goto v___jp_2458_;
}
else
{
uint8_t v_contextDependent_2470_; 
v_contextDependent_2470_ = lean_ctor_get_uint8(v_a_2457_, sizeof(void*)*2 + 1);
v___y_2459_ = v_contextDependent_2470_;
goto v___jp_2458_;
}
}
v___jp_2458_:
{
if (v___y_2459_ == 0)
{
lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2467_; 
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; 
v_unused_2468_ = lean_ctor_get(v___x_2456_, 0);
lean_dec(v_unused_2468_);
v___x_2461_ = v___x_2456_;
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
else
{
lean_dec(v___x_2456_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2463_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2457_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2463_);
v___x_2465_ = v___x_2461_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
else
{
lean_dec(v_a_2457_);
return v___x_2456_;
}
}
}
else
{
return v___x_2456_;
}
}
else
{
lean_dec_ref_known(v_a_2453_, 0);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec_ref(v___f_2439_);
return v___x_2452_;
}
}
else
{
uint8_t v_done_2471_; 
v_done_2471_ = lean_ctor_get_uint8(v_a_2453_, sizeof(void*)*2);
if (v_done_2471_ == 0)
{
lean_object* v_e_x27_2472_; lean_object* v_proof_2473_; uint8_t v_contextDependent_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref_known(v___x_2452_, 1);
v_e_x27_2472_ = lean_ctor_get(v_a_2453_, 0);
v_proof_2473_ = lean_ctor_get(v_a_2453_, 1);
v_contextDependent_2474_ = lean_ctor_get_uint8(v_a_2453_, sizeof(void*)*2 + 1);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_a_2453_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2476_ = v_a_2453_;
v_isShared_2477_ = v_isSharedCheck_2524_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_proof_2473_);
lean_inc(v_e_x27_2472_);
lean_dec(v_a_2453_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2524_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; 
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
lean_inc(v___y_2447_);
lean_inc_ref(v___y_2446_);
lean_inc(v___y_2445_);
lean_inc_ref(v___y_2444_);
lean_inc_ref(v_e_x27_2472_);
v___x_2478_ = lean_apply_12(v___f_2439_, v___x_2451_, v_e_x27_2472_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, lean_box(0));
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2523_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2523_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2523_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
if (lean_obj_tag(v_a_2479_) == 0)
{
uint8_t v_done_2483_; uint8_t v_contextDependent_2484_; uint8_t v___y_2486_; 
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec_ref(v___y_2440_);
v_done_2483_ = lean_ctor_get_uint8(v_a_2479_, 0);
v_contextDependent_2484_ = lean_ctor_get_uint8(v_a_2479_, 1);
lean_dec_ref_known(v_a_2479_, 0);
if (v_contextDependent_2474_ == 0)
{
v___y_2486_ = v_contextDependent_2484_;
goto v___jp_2485_;
}
else
{
v___y_2486_ = v_contextDependent_2474_;
goto v___jp_2485_;
}
v___jp_2485_:
{
lean_object* v___x_2488_; 
if (v_isShared_2477_ == 0)
{
v___x_2488_ = v___x_2476_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_e_x27_2472_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_proof_2473_);
v___x_2488_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2490_; 
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*2, v_done_2483_);
lean_ctor_set_uint8(v___x_2488_, sizeof(void*)*2 + 1, v___y_2486_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2488_);
v___x_2490_ = v___x_2481_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
else
{
lean_object* v_e_x27_2493_; lean_object* v_proof_2494_; uint8_t v_done_2495_; uint8_t v_contextDependent_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2522_; 
lean_del_object(v___x_2481_);
lean_del_object(v___x_2476_);
v_e_x27_2493_ = lean_ctor_get(v_a_2479_, 0);
v_proof_2494_ = lean_ctor_get(v_a_2479_, 1);
v_done_2495_ = lean_ctor_get_uint8(v_a_2479_, sizeof(void*)*2);
v_contextDependent_2496_ = lean_ctor_get_uint8(v_a_2479_, sizeof(void*)*2 + 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_a_2479_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2498_ = v_a_2479_;
v_isShared_2499_ = v_isSharedCheck_2522_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_proof_2494_);
lean_inc(v_e_x27_2493_);
lean_dec(v_a_2479_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2522_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; 
lean_inc_ref(v_e_x27_2493_);
v___x_2500_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2440_, v_e_x27_2472_, v_proof_2473_, v_e_x27_2493_, v_proof_2494_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2513_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2503_ = v___x_2500_;
v_isShared_2504_ = v_isSharedCheck_2513_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2513_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
uint8_t v___y_2506_; 
if (v_contextDependent_2474_ == 0)
{
v___y_2506_ = v_contextDependent_2496_;
goto v___jp_2505_;
}
else
{
v___y_2506_ = v_contextDependent_2474_;
goto v___jp_2505_;
}
v___jp_2505_:
{
lean_object* v___x_2508_; 
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v_a_2501_);
v___x_2508_ = v___x_2498_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_e_x27_2493_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_a_2501_);
lean_ctor_set_uint8(v_reuseFailAlloc_2512_, sizeof(void*)*2, v_done_2495_);
v___x_2508_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2510_; 
lean_ctor_set_uint8(v___x_2508_, sizeof(void*)*2 + 1, v___y_2506_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 0, v___x_2508_);
v___x_2510_ = v___x_2503_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_del_object(v___x_2498_);
lean_dec_ref(v_e_x27_2493_);
v_a_2514_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2500_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2500_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2476_);
lean_dec_ref(v_proof_2473_);
lean_dec_ref(v_e_x27_2472_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec_ref(v___y_2440_);
return v___x_2478_;
}
}
}
else
{
lean_dec_ref_known(v_a_2453_, 2);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec_ref(v___f_2439_);
return v___x_2452_;
}
}
}
else
{
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec_ref(v___f_2439_);
return v___x_2452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed(lean_object* v___f_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__15(v___f_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16(lean_object* v___f_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
uint8_t v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; uint8_t v___y_2554_; lean_object* v___y_2558_; lean_object* v___y_2559_; uint8_t v___y_2560_; uint8_t v___y_2561_; lean_object* v___y_2565_; lean_object* v_e_x27_2566_; lean_object* v_proof_2567_; uint8_t v_done_2568_; uint8_t v_contextDependent_2569_; lean_object* v___y_2591_; lean_object* v___y_2592_; uint8_t v___y_2593_; lean_object* v___y_2597_; lean_object* v_a_2598_; lean_object* v___y_2610_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_box(0);
lean_inc_ref(v___y_2539_);
v___x_2613_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_2539_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
if (lean_obj_tag(v_a_2614_) == 0)
{
uint8_t v_done_2615_; 
v_done_2615_ = lean_ctor_get_uint8(v_a_2614_, 0);
if (v_done_2615_ == 0)
{
uint8_t v_contextDependent_2616_; lean_object* v___x_2617_; 
lean_dec_ref_known(v___x_2613_, 1);
v_contextDependent_2616_ = lean_ctor_get_uint8(v_a_2614_, 1);
lean_dec_ref_known(v_a_2614_, 0);
lean_inc(v___y_2548_);
lean_inc_ref(v___y_2547_);
lean_inc(v___y_2546_);
lean_inc_ref(v___y_2545_);
lean_inc(v___y_2544_);
lean_inc_ref(v___y_2543_);
lean_inc_ref(v___y_2539_);
v___x_2617_ = lean_apply_12(v___f_2538_, v___x_2612_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, lean_box(0));
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; uint8_t v___y_2620_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
if (v_contextDependent_2616_ == 0)
{
v___y_2597_ = v___x_2617_;
v_a_2598_ = v_a_2618_;
goto v___jp_2596_;
}
else
{
if (lean_obj_tag(v_a_2618_) == 0)
{
uint8_t v_contextDependent_2630_; 
v_contextDependent_2630_ = lean_ctor_get_uint8(v_a_2618_, 1);
v___y_2620_ = v_contextDependent_2630_;
goto v___jp_2619_;
}
else
{
uint8_t v_contextDependent_2631_; 
v_contextDependent_2631_ = lean_ctor_get_uint8(v_a_2618_, sizeof(void*)*2 + 1);
v___y_2620_ = v_contextDependent_2631_;
goto v___jp_2619_;
}
}
v___jp_2619_:
{
if (v___y_2620_ == 0)
{
lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2628_; 
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2628_ == 0)
{
lean_object* v_unused_2629_; 
v_unused_2629_ = lean_ctor_get(v___x_2617_, 0);
lean_dec(v_unused_2629_);
v___x_2622_ = v___x_2617_;
v_isShared_2623_ = v_isSharedCheck_2628_;
goto v_resetjp_2621_;
}
else
{
lean_dec(v___x_2617_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2628_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2618_);
lean_inc_ref(v___x_2624_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2624_);
v___x_2626_ = v___x_2622_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
v___y_2597_ = v___x_2626_;
v_a_2598_ = v___x_2624_;
goto v___jp_2596_;
}
}
}
else
{
v___y_2597_ = v___x_2617_;
v_a_2598_ = v_a_2618_;
goto v___jp_2596_;
}
}
}
else
{
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v___y_2539_);
return v___x_2617_;
}
}
else
{
lean_dec_ref_known(v_a_2614_, 0);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___f_2538_);
v___y_2610_ = v___x_2613_;
goto v___jp_2609_;
}
}
else
{
uint8_t v_done_2632_; 
v_done_2632_ = lean_ctor_get_uint8(v_a_2614_, sizeof(void*)*2);
if (v_done_2632_ == 0)
{
lean_object* v_e_x27_2633_; lean_object* v_proof_2634_; uint8_t v_contextDependent_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2685_; 
lean_dec_ref_known(v___x_2613_, 1);
v_e_x27_2633_ = lean_ctor_get(v_a_2614_, 0);
v_proof_2634_ = lean_ctor_get(v_a_2614_, 1);
v_contextDependent_2635_ = lean_ctor_get_uint8(v_a_2614_, sizeof(void*)*2 + 1);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_a_2614_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2637_ = v_a_2614_;
v_isShared_2638_ = v_isSharedCheck_2685_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_proof_2634_);
lean_inc(v_e_x27_2633_);
lean_dec(v_a_2614_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2685_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; 
lean_inc(v___y_2548_);
lean_inc_ref(v___y_2547_);
lean_inc(v___y_2546_);
lean_inc_ref(v___y_2545_);
lean_inc(v___y_2544_);
lean_inc_ref(v___y_2543_);
lean_inc_ref(v_e_x27_2633_);
v___x_2639_ = lean_apply_12(v___f_2538_, v___x_2612_, v_e_x27_2633_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, lean_box(0));
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2684_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2684_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2684_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
if (lean_obj_tag(v_a_2640_) == 0)
{
uint8_t v_done_2644_; uint8_t v_contextDependent_2645_; uint8_t v___y_2647_; 
v_done_2644_ = lean_ctor_get_uint8(v_a_2640_, 0);
v_contextDependent_2645_ = lean_ctor_get_uint8(v_a_2640_, 1);
lean_dec_ref_known(v_a_2640_, 0);
if (v_contextDependent_2635_ == 0)
{
v___y_2647_ = v_contextDependent_2645_;
goto v___jp_2646_;
}
else
{
v___y_2647_ = v_contextDependent_2635_;
goto v___jp_2646_;
}
v___jp_2646_:
{
lean_object* v___x_2649_; 
lean_inc_ref(v_proof_2634_);
lean_inc_ref(v_e_x27_2633_);
if (v_isShared_2638_ == 0)
{
v___x_2649_ = v___x_2637_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_e_x27_2633_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_proof_2634_);
v___x_2649_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2651_; 
lean_ctor_set_uint8(v___x_2649_, sizeof(void*)*2, v_done_2644_);
lean_ctor_set_uint8(v___x_2649_, sizeof(void*)*2 + 1, v___y_2647_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2649_);
v___x_2651_ = v___x_2642_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
v___y_2565_ = v___x_2651_;
v_e_x27_2566_ = v_e_x27_2633_;
v_proof_2567_ = v_proof_2634_;
v_done_2568_ = v_done_2644_;
v_contextDependent_2569_ = v___y_2647_;
goto v___jp_2564_;
}
}
}
}
else
{
lean_object* v_e_x27_2654_; lean_object* v_proof_2655_; uint8_t v_done_2656_; uint8_t v_contextDependent_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2683_; 
lean_del_object(v___x_2642_);
lean_del_object(v___x_2637_);
v_e_x27_2654_ = lean_ctor_get(v_a_2640_, 0);
v_proof_2655_ = lean_ctor_get(v_a_2640_, 1);
v_done_2656_ = lean_ctor_get_uint8(v_a_2640_, sizeof(void*)*2);
v_contextDependent_2657_ = lean_ctor_get_uint8(v_a_2640_, sizeof(void*)*2 + 1);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_a_2640_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2659_ = v_a_2640_;
v_isShared_2660_ = v_isSharedCheck_2683_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_proof_2655_);
lean_inc(v_e_x27_2654_);
lean_dec(v_a_2640_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2683_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; 
lean_inc_ref(v_e_x27_2654_);
lean_inc_ref(v___y_2539_);
v___x_2661_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2539_, v_e_x27_2633_, v_proof_2634_, v_e_x27_2654_, v_proof_2655_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2674_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2664_ = v___x_2661_;
v_isShared_2665_ = v_isSharedCheck_2674_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2674_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
uint8_t v___y_2667_; 
if (v_contextDependent_2635_ == 0)
{
v___y_2667_ = v_contextDependent_2657_;
goto v___jp_2666_;
}
else
{
v___y_2667_ = v_contextDependent_2635_;
goto v___jp_2666_;
}
v___jp_2666_:
{
lean_object* v___x_2669_; 
lean_inc(v_a_2662_);
lean_inc_ref(v_e_x27_2654_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v_a_2662_);
v___x_2669_ = v___x_2659_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_e_x27_2654_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_a_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, sizeof(void*)*2, v_done_2656_);
v___x_2669_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2671_; 
lean_ctor_set_uint8(v___x_2669_, sizeof(void*)*2 + 1, v___y_2667_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2669_);
v___x_2671_ = v___x_2664_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
v___y_2565_ = v___x_2671_;
v_e_x27_2566_ = v_e_x27_2654_;
v_proof_2567_ = v_a_2662_;
v_done_2568_ = v_done_2656_;
v_contextDependent_2569_ = v___y_2667_;
goto v___jp_2564_;
}
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_del_object(v___x_2659_);
lean_dec_ref(v_e_x27_2654_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v___y_2539_);
v_a_2675_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2661_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2661_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2637_);
lean_dec_ref(v_proof_2634_);
lean_dec_ref(v_e_x27_2633_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v___y_2539_);
return v___x_2639_;
}
}
}
else
{
lean_dec_ref_known(v_a_2614_, 2);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___f_2538_);
v___y_2610_ = v___x_2613_;
goto v___jp_2609_;
}
}
}
else
{
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___f_2538_);
v___y_2610_ = v___x_2613_;
goto v___jp_2609_;
}
v___jp_2550_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2555_, 0, v___y_2552_);
lean_ctor_set(v___x_2555_, 1, v___y_2553_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*2, v___y_2551_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*2 + 1, v___y_2554_);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
return v___x_2556_;
}
v___jp_2557_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2562_, 0, v___y_2559_);
lean_ctor_set(v___x_2562_, 1, v___y_2558_);
lean_ctor_set_uint8(v___x_2562_, sizeof(void*)*2, v___y_2560_);
lean_ctor_set_uint8(v___x_2562_, sizeof(void*)*2 + 1, v___y_2561_);
v___x_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
return v___x_2563_;
}
v___jp_2564_:
{
if (v_done_2568_ == 0)
{
lean_object* v___x_2570_; 
lean_dec_ref(v___y_2565_);
lean_inc_ref(v_e_x27_2566_);
v___x_2570_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v_e_x27_2566_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2570_, 1);
if (lean_obj_tag(v_a_2571_) == 0)
{
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v___y_2539_);
if (v_contextDependent_2569_ == 0)
{
uint8_t v_done_2572_; uint8_t v_contextDependent_2573_; 
v_done_2572_ = lean_ctor_get_uint8(v_a_2571_, 0);
v_contextDependent_2573_ = lean_ctor_get_uint8(v_a_2571_, 1);
lean_dec_ref_known(v_a_2571_, 0);
v___y_2551_ = v_done_2572_;
v___y_2552_ = v_e_x27_2566_;
v___y_2553_ = v_proof_2567_;
v___y_2554_ = v_contextDependent_2573_;
goto v___jp_2550_;
}
else
{
uint8_t v_done_2574_; 
v_done_2574_ = lean_ctor_get_uint8(v_a_2571_, 0);
lean_dec_ref_known(v_a_2571_, 0);
v___y_2551_ = v_done_2574_;
v___y_2552_ = v_e_x27_2566_;
v___y_2553_ = v_proof_2567_;
v___y_2554_ = v_contextDependent_2569_;
goto v___jp_2550_;
}
}
else
{
lean_object* v_e_x27_2575_; lean_object* v_proof_2576_; uint8_t v_done_2577_; uint8_t v_contextDependent_2578_; lean_object* v___x_2579_; 
v_e_x27_2575_ = lean_ctor_get(v_a_2571_, 0);
lean_inc_ref_n(v_e_x27_2575_, 2);
v_proof_2576_ = lean_ctor_get(v_a_2571_, 1);
lean_inc_ref(v_proof_2576_);
v_done_2577_ = lean_ctor_get_uint8(v_a_2571_, sizeof(void*)*2);
v_contextDependent_2578_ = lean_ctor_get_uint8(v_a_2571_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2571_, 2);
v___x_2579_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2539_, v_e_x27_2566_, v_proof_2567_, v_e_x27_2575_, v_proof_2576_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
if (lean_obj_tag(v___x_2579_) == 0)
{
if (v_contextDependent_2569_ == 0)
{
lean_object* v_a_2580_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___y_2558_ = v_a_2580_;
v___y_2559_ = v_e_x27_2575_;
v___y_2560_ = v_done_2577_;
v___y_2561_ = v_contextDependent_2578_;
goto v___jp_2557_;
}
else
{
lean_object* v_a_2581_; 
v_a_2581_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2579_, 1);
v___y_2558_ = v_a_2581_;
v___y_2559_ = v_e_x27_2575_;
v___y_2560_ = v_done_2577_;
v___y_2561_ = v_contextDependent_2569_;
goto v___jp_2557_;
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec_ref(v_e_x27_2575_);
v_a_2582_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2579_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2579_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_2567_);
lean_dec_ref(v_e_x27_2566_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v___y_2539_);
return v___x_2570_;
}
}
else
{
lean_dec_ref(v_proof_2567_);
lean_dec_ref(v_e_x27_2566_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v___y_2539_);
return v___y_2565_;
}
}
v___jp_2590_:
{
if (v___y_2593_ == 0)
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_dec_ref(v___y_2592_);
v___x_2594_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_2591_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
else
{
lean_dec_ref(v___y_2591_);
return v___y_2592_;
}
}
v___jp_2596_:
{
if (lean_obj_tag(v_a_2598_) == 0)
{
uint8_t v_done_2599_; 
v_done_2599_ = lean_ctor_get_uint8(v_a_2598_, 0);
if (v_done_2599_ == 0)
{
uint8_t v_contextDependent_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v___y_2597_);
v_contextDependent_2600_ = lean_ctor_get_uint8(v_a_2598_, 1);
lean_dec_ref_known(v_a_2598_, 0);
v___x_2601_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v___y_2539_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
if (lean_obj_tag(v___x_2601_) == 0)
{
if (v_contextDependent_2600_ == 0)
{
return v___x_2601_;
}
else
{
lean_object* v_a_2602_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
if (lean_obj_tag(v_a_2602_) == 0)
{
uint8_t v_contextDependent_2603_; 
v_contextDependent_2603_ = lean_ctor_get_uint8(v_a_2602_, 1);
v___y_2591_ = v_a_2602_;
v___y_2592_ = v___x_2601_;
v___y_2593_ = v_contextDependent_2603_;
goto v___jp_2590_;
}
else
{
uint8_t v_contextDependent_2604_; 
v_contextDependent_2604_ = lean_ctor_get_uint8(v_a_2602_, sizeof(void*)*2 + 1);
v___y_2591_ = v_a_2602_;
v___y_2592_ = v___x_2601_;
v___y_2593_ = v_contextDependent_2604_;
goto v___jp_2590_;
}
}
}
else
{
return v___x_2601_;
}
}
else
{
lean_dec_ref_known(v_a_2598_, 0);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v___y_2539_);
return v___y_2597_;
}
}
else
{
lean_object* v_e_x27_2605_; lean_object* v_proof_2606_; uint8_t v_done_2607_; uint8_t v_contextDependent_2608_; 
v_e_x27_2605_ = lean_ctor_get(v_a_2598_, 0);
lean_inc_ref(v_e_x27_2605_);
v_proof_2606_ = lean_ctor_get(v_a_2598_, 1);
lean_inc_ref(v_proof_2606_);
v_done_2607_ = lean_ctor_get_uint8(v_a_2598_, sizeof(void*)*2);
v_contextDependent_2608_ = lean_ctor_get_uint8(v_a_2598_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2598_, 2);
v___y_2565_ = v___y_2597_;
v_e_x27_2566_ = v_e_x27_2605_;
v_proof_2567_ = v_proof_2606_;
v_done_2568_ = v_done_2607_;
v_contextDependent_2569_ = v_contextDependent_2608_;
goto v___jp_2564_;
}
}
v___jp_2609_:
{
if (lean_obj_tag(v___y_2610_) == 0)
{
lean_object* v_a_2611_; 
v_a_2611_ = lean_ctor_get(v___y_2610_, 0);
lean_inc(v_a_2611_);
v___y_2597_ = v___y_2610_;
v_a_2598_ = v_a_2611_;
goto v___jp_2596_;
}
else
{
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v___y_2539_);
return v___y_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed(lean_object* v___f_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__16(v___f_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object* v_config_2720_, lean_object* v_thms_2721_){
_start:
{
uint8_t v_zetaDelta_2722_; uint8_t v_zeta_2723_; lean_object* v___f_2724_; lean_object* v_d_2725_; lean_object* v___f_2726_; lean_object* v___f_2727_; lean_object* v___f_2728_; lean_object* v_pre_2730_; lean_object* v_pre_2743_; 
v_zetaDelta_2722_ = lean_ctor_get_uint8(v_config_2720_, sizeof(void*)*14 + 19);
v_zeta_2723_ = lean_ctor_get_uint8(v_config_2720_, sizeof(void*)*14 + 20);
v___f_2724_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__8));
v_d_2725_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__9));
lean_inc_ref(v_thms_2721_);
v___f_2726_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__9___boxed), 14, 2);
lean_closure_set(v___f_2726_, 0, v_thms_2721_);
lean_closure_set(v___f_2726_, 1, v_d_2725_);
v___f_2727_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__10___boxed), 14, 2);
lean_closure_set(v___f_2727_, 0, v_d_2725_);
lean_closure_set(v___f_2727_, 1, v___f_2726_);
v___f_2728_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed), 13, 1);
lean_closure_set(v___f_2728_, 0, v___f_2727_);
if (v_zeta_2723_ == 0)
{
lean_object* v_pre_2745_; 
v_pre_2745_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__10));
v_pre_2743_ = v_pre_2745_;
goto v___jp_2742_;
}
else
{
lean_object* v_pre_2746_; 
v_pre_2746_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__11));
v_pre_2743_ = v_pre_2746_;
goto v___jp_2742_;
}
v___jp_2729_:
{
lean_object* v_post_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2740_; 
v_post_2731_ = lean_ctor_get(v_thms_2721_, 1);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_thms_2721_);
if (v_isSharedCheck_2740_ == 0)
{
lean_object* v_unused_2741_; 
v_unused_2741_ = lean_ctor_get(v_thms_2721_, 0);
lean_dec(v_unused_2741_);
v___x_2733_ = v_thms_2721_;
v_isShared_2734_ = v_isSharedCheck_2740_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_post_2731_);
lean_dec(v_thms_2721_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2740_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_pre_2735_; lean_object* v_post_2736_; lean_object* v___x_2738_; 
v_pre_2735_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed), 13, 2);
lean_closure_set(v_pre_2735_, 0, v_pre_2730_);
lean_closure_set(v_pre_2735_, 1, v___f_2728_);
v_post_2736_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed), 14, 3);
lean_closure_set(v_post_2736_, 0, v_post_2731_);
lean_closure_set(v_post_2736_, 1, v_d_2725_);
lean_closure_set(v_post_2736_, 2, v___f_2724_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v_post_2736_);
lean_ctor_set(v___x_2733_, 0, v_pre_2735_);
v___x_2738_ = v___x_2733_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_pre_2735_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_post_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
v___jp_2742_:
{
if (v_zetaDelta_2722_ == 0)
{
lean_inc_ref(v_pre_2743_);
v_pre_2730_ = v_pre_2743_;
goto v___jp_2729_;
}
else
{
lean_object* v_pre_2744_; 
lean_inc_ref(v_pre_2743_);
v_pre_2744_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed), 12, 1);
lean_closure_set(v_pre_2744_, 0, v_pre_2743_);
v_pre_2730_ = v_pre_2744_;
goto v___jp_2729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___boxed(lean_object* v_config_2747_, lean_object* v_thms_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_Meta_Grind_mkNormSymMethods(v_config_2747_, v_thms_2748_);
lean_dec_ref(v_config_2747_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(lean_object* v_e_2750_, lean_object* v___y_2751_){
_start:
{
uint8_t v___x_2753_; 
v___x_2753_ = l_Lean_Expr_hasMVar(v_e_2750_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; 
v___x_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_e_2750_);
return v___x_2754_;
}
else
{
lean_object* v___x_2755_; lean_object* v_mctx_2756_; lean_object* v___x_2757_; lean_object* v_fst_2758_; lean_object* v_snd_2759_; lean_object* v___x_2760_; lean_object* v_cache_2761_; lean_object* v_zetaDeltaFVarIds_2762_; lean_object* v_postponed_2763_; lean_object* v_diag_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2773_; 
v___x_2755_ = lean_st_ref_get(v___y_2751_);
v_mctx_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc_ref(v_mctx_2756_);
lean_dec(v___x_2755_);
v___x_2757_ = l_Lean_instantiateMVarsCore(v_mctx_2756_, v_e_2750_);
v_fst_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_fst_2758_);
v_snd_2759_ = lean_ctor_get(v___x_2757_, 1);
lean_inc(v_snd_2759_);
lean_dec_ref(v___x_2757_);
v___x_2760_ = lean_st_ref_take(v___y_2751_);
v_cache_2761_ = lean_ctor_get(v___x_2760_, 1);
v_zetaDeltaFVarIds_2762_ = lean_ctor_get(v___x_2760_, 2);
v_postponed_2763_ = lean_ctor_get(v___x_2760_, 3);
v_diag_2764_ = lean_ctor_get(v___x_2760_, 4);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2773_ == 0)
{
lean_object* v_unused_2774_; 
v_unused_2774_ = lean_ctor_get(v___x_2760_, 0);
lean_dec(v_unused_2774_);
v___x_2766_ = v___x_2760_;
v_isShared_2767_ = v_isSharedCheck_2773_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_diag_2764_);
lean_inc(v_postponed_2763_);
lean_inc(v_zetaDeltaFVarIds_2762_);
lean_inc(v_cache_2761_);
lean_dec(v___x_2760_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2773_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v_snd_2759_);
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_snd_2759_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_cache_2761_);
lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_zetaDeltaFVarIds_2762_);
lean_ctor_set(v_reuseFailAlloc_2772_, 3, v_postponed_2763_);
lean_ctor_set(v_reuseFailAlloc_2772_, 4, v_diag_2764_);
v___x_2769_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = lean_st_ref_put(v___y_2751_, v___x_2769_);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_fst_2758_);
return v___x_2771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg___boxed(lean_object* v_e_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2775_, v___y_2776_);
lean_dec(v___y_2776_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(lean_object* v_e_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2779_, v___y_2786_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___boxed(lean_object* v_e_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(v_e_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy(lean_object* v_e_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v___x_2814_; lean_object* v_a_2815_; lean_object* v___x_2816_; 
v___x_2814_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2803_, v_a_2810_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
v___x_2816_ = l_Lean_Meta_Grind_simpCore(v_a_2815_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy___boxed(lean_object* v_e_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_Meta_Grind_normLegacy(v_e_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
return v_res_2828_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__1(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__1, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__1_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1);
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__2(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2834_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__1, &l_Lean_Meta_Grind_normSym___redArg___closed__1_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__1);
v___x_2835_ = lean_unsigned_to_nat(0u);
v___x_2836_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
lean_ctor_set(v___x_2836_, 1, v___x_2834_);
lean_ctor_set(v___x_2836_, 2, v___x_2834_);
lean_ctor_set(v___x_2836_, 3, v___x_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg(lean_object* v_e_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_Meta_Sym_preprocessExpr(v_e_2837_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = l_Lean_Meta_Grind_mkNormSymTheorems(v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v___x_2850_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2838_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = l_Lean_Meta_Grind_mkNormSymMethods(v_a_2851_, v_a_2849_);
lean_dec(v_a_2851_);
lean_inc(v_a_2847_);
v___x_2853_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_2853_, 0, v_a_2847_);
v___x_2854_ = ((lean_object*)(l_Lean_Meta_Grind_normSym___redArg___closed__0));
v___x_2855_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__2, &l_Lean_Meta_Grind_normSym___redArg___closed__2_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__2);
v___x_2856_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_2853_, v___x_2852_, v___x_2854_, v___x_2855_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2876_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2859_ = v___x_2856_;
v_isShared_2860_ = v_isSharedCheck_2876_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2876_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v_fst_2861_; 
v_fst_2861_ = lean_ctor_get(v_a_2857_, 0);
lean_inc(v_fst_2861_);
lean_dec(v_a_2857_);
if (lean_obj_tag(v_fst_2861_) == 0)
{
lean_object* v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
lean_dec_ref_known(v_fst_2861_, 0);
v___x_2862_ = lean_box(0);
v___x_2863_ = 1;
v___x_2864_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2864_, 0, v_a_2847_);
lean_ctor_set(v___x_2864_, 1, v___x_2862_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*2, v___x_2863_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2864_);
v___x_2866_ = v___x_2859_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
else
{
lean_object* v_e_x27_2868_; lean_object* v_proof_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
lean_dec(v_a_2847_);
v_e_x27_2868_ = lean_ctor_get(v_fst_2861_, 0);
lean_inc_ref(v_e_x27_2868_);
v_proof_2869_ = lean_ctor_get(v_fst_2861_, 1);
lean_inc_ref(v_proof_2869_);
lean_dec_ref_known(v_fst_2861_, 2);
v___x_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2870_, 0, v_proof_2869_);
v___x_2871_ = 1;
v___x_2872_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2872_, 0, v_e_x27_2868_);
lean_ctor_set(v___x_2872_, 1, v___x_2870_);
lean_ctor_set_uint8(v___x_2872_, sizeof(void*)*2, v___x_2871_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2872_);
v___x_2874_ = v___x_2859_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec(v_a_2847_);
v_a_2877_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2856_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2856_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v_a_2849_);
lean_dec(v_a_2847_);
v_a_2885_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2850_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2850_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec(v_a_2847_);
v_a_2893_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2848_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2848_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
v_a_2901_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2846_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2846_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg___boxed(lean_object* v_e_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_Meta_Grind_normSym___redArg(v_e_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec_ref(v_a_2910_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym(lean_object* v_e_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_Meta_Grind_normSym___redArg(v_e_2919_, v_a_2921_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___boxed(lean_object* v_e_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_Meta_Grind_normSym(v_e_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
return v_res_2942_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Arith(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_NormSymProcs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DiscrTree(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_NormSym(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Arith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_NormSymProcs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_NormSym(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Arith(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_NormSymProcs(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Reduce(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_NormSym(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Arith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_NormSymProcs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_NormSym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_NormSym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_NormSym(builtin);
}
#ifdef __cplusplus
}
#endif
