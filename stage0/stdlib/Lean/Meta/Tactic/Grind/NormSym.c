// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.NormSym
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.Simp.Theorems import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.SimpUtil import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Sym.Simp.Main import Lean.Meta.Sym.Simp.Simproc import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.EvalGround import Lean.Meta.Sym.Simp.Arith import Lean.Meta.Sym.Simp.Discharger import Lean.Meta.Tactic.Grind.NormSymProcs import Lean.Meta.Sym.Simp.Reduce public import Lean.Meta.Sym.DSimp import Lean.Meta.Sym.Simp.ControlFlow import Lean.Meta.Sym.Util import Lean.Meta.DiscrTree
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
lean_object* l_Lean_Meta_Sym_DSimp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_Decls_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_Simp_reduceControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_symNorm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_simpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "skipping unfold `"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Grind_mkNormSymTheorems___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__12;
static lean_once_cell_t l_Lean_Meta_Grind_mkNormSymTheorems___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___closed__13;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymMethods___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___lam__10___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__0_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__2___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__1_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__3___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__2_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__4___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__4_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__5_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__6_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__7___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__6_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__7_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__8___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__7_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__8_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__9___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__8_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__9_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__10___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__9_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__10_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__11_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__3_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__12_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__18___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__3_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__0_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__0_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_normSym___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normSym___redArg___closed__0;
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
lean_object* v___x_111_; lean_object* v_env_112_; uint8_t v___x_113_; lean_object* v_env_114_; lean_object* v___x_115_; lean_object* v_toCold_116_; lean_object* v_mctx_117_; lean_object* v_lctx_118_; lean_object* v_options_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_111_ = lean_st_ref_get(v___y_109_);
v_env_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref(v_env_112_);
lean_dec(v___x_111_);
v___x_113_ = 0;
v_env_114_ = l_Lean_Environment_setRecordingDeps(v_env_112_, v___x_113_);
v___x_115_ = lean_st_ref_get(v___y_107_);
v_toCold_116_ = lean_ctor_get(v___y_108_, 0);
v_mctx_117_ = lean_ctor_get(v___x_115_, 0);
lean_inc_ref(v_mctx_117_);
lean_dec(v___x_115_);
v_lctx_118_ = lean_ctor_get(v___y_106_, 2);
v_options_119_ = lean_ctor_get(v_toCold_116_, 2);
lean_inc_ref(v_options_119_);
lean_inc_ref(v_lctx_118_);
v___x_120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_120_, 0, v_env_114_);
lean_ctor_set(v___x_120_, 1, v_mctx_117_);
lean_ctor_set(v___x_120_, 2, v_lctx_118_);
lean_ctor_set(v___x_120_, 3, v_options_119_);
v___x_121_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v_msgData_105_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0___boxed(lean_object* v_msgData_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0(v_msgData_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_129_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0(void){
_start:
{
lean_object* v___x_130_; double v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_float_of_nat(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(lean_object* v_cls_135_, lean_object* v_msg_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_ref_142_; lean_object* v___x_143_; lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_189_; 
v_ref_142_ = lean_ctor_get(v___y_139_, 2);
v___x_143_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0(v_msg_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_189_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_189_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_189_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v_traceState_149_; lean_object* v_env_150_; lean_object* v_nextMacroScope_151_; lean_object* v_ngen_152_; lean_object* v_auxDeclNGen_153_; lean_object* v_cache_154_; lean_object* v_recordedDeps_155_; lean_object* v_messages_156_; lean_object* v_infoState_157_; lean_object* v_snapshotTasks_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_188_; 
v___x_148_ = lean_st_ref_take(v___y_140_);
v_traceState_149_ = lean_ctor_get(v___x_148_, 4);
v_env_150_ = lean_ctor_get(v___x_148_, 0);
v_nextMacroScope_151_ = lean_ctor_get(v___x_148_, 1);
v_ngen_152_ = lean_ctor_get(v___x_148_, 2);
v_auxDeclNGen_153_ = lean_ctor_get(v___x_148_, 3);
v_cache_154_ = lean_ctor_get(v___x_148_, 5);
v_recordedDeps_155_ = lean_ctor_get(v___x_148_, 6);
v_messages_156_ = lean_ctor_get(v___x_148_, 7);
v_infoState_157_ = lean_ctor_get(v___x_148_, 8);
v_snapshotTasks_158_ = lean_ctor_get(v___x_148_, 9);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_188_ == 0)
{
v___x_160_ = v___x_148_;
v_isShared_161_ = v_isSharedCheck_188_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_snapshotTasks_158_);
lean_inc(v_infoState_157_);
lean_inc(v_messages_156_);
lean_inc(v_recordedDeps_155_);
lean_inc(v_cache_154_);
lean_inc(v_traceState_149_);
lean_inc(v_auxDeclNGen_153_);
lean_inc(v_ngen_152_);
lean_inc(v_nextMacroScope_151_);
lean_inc(v_env_150_);
lean_dec(v___x_148_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_188_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
uint64_t v_tid_162_; lean_object* v_traces_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_187_; 
v_tid_162_ = lean_ctor_get_uint64(v_traceState_149_, sizeof(void*)*1);
v_traces_163_ = lean_ctor_get(v_traceState_149_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v_traceState_149_);
if (v_isSharedCheck_187_ == 0)
{
v___x_165_ = v_traceState_149_;
v_isShared_166_ = v_isSharedCheck_187_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_traces_163_);
lean_dec(v_traceState_149_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_187_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; double v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_167_ = lean_box(0);
v___x_168_ = lean_box(0);
v___x_169_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0);
v___x_170_ = 0;
v___x_171_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__1));
v___x_172_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_172_, 0, v_cls_135_);
lean_ctor_set(v___x_172_, 1, v___x_168_);
lean_ctor_set(v___x_172_, 2, v___x_171_);
lean_ctor_set_float(v___x_172_, sizeof(void*)*3, v___x_169_);
lean_ctor_set_float(v___x_172_, sizeof(void*)*3 + 8, v___x_169_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*3 + 16, v___x_170_);
v___x_173_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__2));
v___x_174_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v_a_144_);
lean_ctor_set(v___x_174_, 2, v___x_173_);
lean_inc(v_ref_142_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_ref_142_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = l_Lean_PersistentArray_push___redArg(v_traces_163_, v___x_175_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_176_);
v___x_178_ = v___x_165_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_176_);
lean_ctor_set_uint64(v_reuseFailAlloc_186_, sizeof(void*)*1, v_tid_162_);
v___x_178_ = v_reuseFailAlloc_186_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_180_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 4, v___x_178_);
v___x_180_ = v___x_160_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_env_150_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_nextMacroScope_151_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_ngen_152_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_auxDeclNGen_153_);
lean_ctor_set(v_reuseFailAlloc_185_, 4, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_185_, 5, v_cache_154_);
lean_ctor_set(v_reuseFailAlloc_185_, 6, v_recordedDeps_155_);
lean_ctor_set(v_reuseFailAlloc_185_, 7, v_messages_156_);
lean_ctor_set(v_reuseFailAlloc_185_, 8, v_infoState_157_);
lean_ctor_set(v_reuseFailAlloc_185_, 9, v_snapshotTasks_158_);
v___x_180_ = v_reuseFailAlloc_185_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = lean_st_ref_put(v___y_140_, v___x_180_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_167_);
v___x_183_ = v___x_146_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_167_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___boxed(lean_object* v_cls_190_, lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v_cls_190_, v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__1));
v___x_203_ = l_Lean_Name_append(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__3));
v___x_206_ = l_Lean_stringToMessageData(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__5));
v___x_209_ = l_Lean_stringToMessageData(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__7));
v___x_212_ = l_Lean_stringToMessageData(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(lean_object* v_thms_213_, lean_object* v_thm_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___y_221_; lean_object* v_proof_231_; 
v_proof_231_ = lean_ctor_get(v_thm_214_, 2);
if (lean_obj_tag(v_proof_231_) == 4)
{
lean_object* v_declName_232_; lean_object* v___x_236_; 
lean_inc_ref(v_proof_231_);
lean_dec_ref(v_thm_214_);
v_declName_232_ = lean_ctor_get(v_proof_231_, 0);
lean_inc_n(v_declName_232_, 2);
lean_dec_ref_known(v_proof_231_, 2);
v___x_236_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_232_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_declName_232_);
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_245_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_241_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_thms_213_, v_a_237_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_241_);
v___x_243_ = v___x_239_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_282_; 
v_a_246_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_282_ == 0)
{
v___x_248_ = v___x_236_;
v_isShared_249_ = v_isSharedCheck_282_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_236_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_282_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
uint8_t v___y_251_; uint8_t v___x_280_; 
v___x_280_ = l_Lean_Exception_isInterrupt(v_a_246_);
if (v___x_280_ == 0)
{
uint8_t v___x_281_; 
lean_inc(v_a_246_);
v___x_281_ = l_Lean_Exception_isRuntime(v_a_246_);
v___y_251_ = v___x_281_;
goto v___jp_250_;
}
else
{
v___y_251_ = v___x_280_;
goto v___jp_250_;
}
v___jp_250_:
{
if (v___y_251_ == 0)
{
lean_object* v_toCold_252_; lean_object* v_options_253_; uint8_t v_hasTrace_254_; 
lean_del_object(v___x_248_);
v_toCold_252_ = lean_ctor_get(v_a_217_, 0);
v_options_253_ = lean_ctor_get(v_toCold_252_, 2);
v_hasTrace_254_ = lean_ctor_get_uint8(v_options_253_, sizeof(void*)*1);
if (v_hasTrace_254_ == 0)
{
lean_dec(v_a_246_);
lean_dec(v_declName_232_);
goto v___jp_233_;
}
else
{
lean_object* v_inheritedTraceOptions_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_inheritedTraceOptions_255_ = lean_ctor_get(v_toCold_252_, 11);
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2);
v___x_258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_255_, v_options_253_, v___x_257_);
if (v___x_258_ == 0)
{
lean_dec(v_a_246_);
lean_dec(v_declName_232_);
goto v___jp_233_;
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_259_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4);
v___x_260_ = l_Lean_MessageData_ofConstName(v_declName_232_, v___y_251_);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = l_Lean_Exception_toMessageData(v_a_246_);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v___x_256_, v___x_265_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_268_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_266_, 1);
v___x_268_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(v_thms_213_, v_a_267_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
v___y_221_ = v___x_268_;
goto v___jp_220_;
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec_ref(v_thms_213_);
v_a_269_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_266_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_266_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
}
else
{
lean_object* v___x_278_; 
lean_dec(v_declName_232_);
lean_dec_ref(v_thms_213_);
if (v_isShared_249_ == 0)
{
v___x_278_ = v___x_248_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_246_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
v___jp_233_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_box(0);
v___x_235_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(v_thms_213_, v___x_234_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
v___y_221_ = v___x_235_;
goto v___jp_220_;
}
}
else
{
lean_object* v_toCold_283_; lean_object* v_options_284_; uint8_t v_hasTrace_285_; 
v_toCold_283_ = lean_ctor_get(v_a_217_, 0);
v_options_284_ = lean_ctor_get(v_toCold_283_, 2);
v_hasTrace_285_ = lean_ctor_get_uint8(v_options_284_, sizeof(void*)*1);
if (v_hasTrace_285_ == 0)
{
lean_object* v___x_286_; 
lean_dec_ref(v_thm_214_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_thms_213_);
return v___x_286_;
}
else
{
lean_object* v_origin_287_; lean_object* v_inheritedTraceOptions_288_; lean_object* v_cls_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_origin_287_ = lean_ctor_get(v_thm_214_, 4);
lean_inc_ref(v_origin_287_);
lean_dec_ref(v_thm_214_);
v_inheritedTraceOptions_288_ = lean_ctor_get(v_toCold_283_, 11);
v_cls_289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_290_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2);
v___x_291_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_288_, v_options_284_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
lean_dec_ref(v_origin_287_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v_thms_213_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_293_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4);
v___x_294_ = l_Lean_Meta_Origin_key(v_origin_287_);
lean_dec_ref(v_origin_287_);
v___x_295_ = l_Lean_MessageData_ofName(v___x_294_);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_293_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v_cls_289_, v___x_298_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v___x_299_, 0);
lean_dec(v_unused_307_);
v___x_301_ = v___x_299_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_dec(v___x_299_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v_thms_213_);
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_thms_213_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v_thms_213_);
v_a_308_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_299_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_299_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
}
v___jp_220_:
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_230_; 
v_a_222_ = lean_ctor_get(v___y_221_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___y_221_);
if (v_isSharedCheck_230_ == 0)
{
v___x_224_ = v___y_221_;
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___y_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v_a_226_; lean_object* v___x_228_; 
v_a_226_ = lean_ctor_get(v_a_222_, 0);
lean_inc(v_a_226_);
lean_dec(v_a_222_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v_a_226_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___boxed(lean_object* v_thms_316_, lean_object* v_thm_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_thms_316_, v_thm_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(lean_object* v_as_324_, size_t v_i_325_, size_t v_stop_326_, lean_object* v_b_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_eq(v_i_325_, v_stop_326_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; size_t v___x_331_; size_t v___x_332_; 
v___x_329_ = lean_array_uget_borrowed(v_as_324_, v_i_325_);
lean_inc(v___x_329_);
v___x_330_ = lean_array_push(v_b_327_, v___x_329_);
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_add(v_i_325_, v___x_331_);
v_i_325_ = v___x_332_;
v_b_327_ = v___x_330_;
goto _start;
}
else
{
return v_b_327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4___boxed(lean_object* v_as_334_, lean_object* v_i_335_, lean_object* v_stop_336_, lean_object* v_b_337_){
_start:
{
size_t v_i_boxed_338_; size_t v_stop_boxed_339_; lean_object* v_res_340_; 
v_i_boxed_338_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_stop_boxed_339_ = lean_unbox_usize(v_stop_336_);
lean_dec(v_stop_336_);
v_res_340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(v_as_334_, v_i_boxed_338_, v_stop_boxed_339_, v_b_337_);
lean_dec_ref(v_as_334_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
lean_object* v_child_343_; 
v_child_343_ = lean_ctor_get(v_x_342_, 1);
v_x_342_ = v_child_343_;
goto _start;
}
else
{
lean_object* v_vs_345_; lean_object* v_children_346_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_vs_345_ = lean_ctor_get(v_x_342_, 0);
v_children_346_ = lean_ctor_get(v_x_342_, 1);
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_array_get_size(v_vs_345_);
v___x_349_ = lean_nat_dec_lt(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_array_get_size(v_children_346_);
v___x_351_ = lean_nat_dec_lt(v___x_347_, v___x_350_);
if (v___x_351_ == 0)
{
return v_x_341_;
}
else
{
size_t v___x_352_; size_t v___x_353_; lean_object* v___x_354_; 
v___x_352_ = ((size_t)0ULL);
v___x_353_ = lean_usize_of_nat(v___x_350_);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_children_346_, v___x_352_, v___x_353_, v_x_341_);
return v___x_354_;
}
}
else
{
size_t v___x_355_; size_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_355_ = ((size_t)0ULL);
v___x_356_ = lean_usize_of_nat(v___x_348_);
v___x_357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(v_vs_345_, v___x_355_, v___x_356_, v_x_341_);
v___x_358_ = lean_array_get_size(v_children_346_);
v___x_359_ = lean_nat_dec_lt(v___x_347_, v___x_358_);
if (v___x_359_ == 0)
{
return v___x_357_;
}
else
{
size_t v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_usize_of_nat(v___x_358_);
v___x_361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_children_346_, v___x_355_, v___x_360_, v___x_357_);
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(lean_object* v_as_362_, size_t v_i_363_, size_t v_stop_364_, lean_object* v_b_365_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = lean_usize_dec_eq(v_i_363_, v_stop_364_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v_snd_368_; lean_object* v___x_369_; size_t v___x_370_; size_t v___x_371_; 
v___x_367_ = lean_array_uget_borrowed(v_as_362_, v_i_363_);
v_snd_368_ = lean_ctor_get(v___x_367_, 1);
v___x_369_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_b_365_, v_snd_368_);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_add(v_i_363_, v___x_370_);
v_i_363_ = v___x_371_;
v_b_365_ = v___x_369_;
goto _start;
}
else
{
return v_b_365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3___boxed(lean_object* v_as_373_, lean_object* v_i_374_, lean_object* v_stop_375_, lean_object* v_b_376_){
_start:
{
size_t v_i_boxed_377_; size_t v_stop_boxed_378_; lean_object* v_res_379_; 
v_i_boxed_377_ = lean_unbox_usize(v_i_374_);
lean_dec(v_i_374_);
v_stop_boxed_378_ = lean_unbox_usize(v_stop_375_);
lean_dec(v_stop_375_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_as_373_, v_i_boxed_377_, v_stop_boxed_378_, v_b_376_);
lean_dec_ref(v_as_373_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2___boxed(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_x_380_, v_x_381_);
lean_dec_ref(v_x_381_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___lam__0(lean_object* v_s_383_, lean_object* v_x_384_, lean_object* v_t_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_s_383_, v_t_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___lam__0___boxed(lean_object* v_s_387_, lean_object* v_x_388_, lean_object* v_t_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_Grind_mkNormSymTheorems___lam__0(v_s_387_, v_x_388_, v_t_389_);
lean_dec_ref(v_t_389_);
lean_dec(v_x_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(lean_object* v_as_391_, size_t v_sz_392_, size_t v_i_393_, lean_object* v_b_394_){
_start:
{
uint8_t v___x_396_; 
v___x_396_ = lean_usize_dec_lt(v_i_393_, v_sz_392_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v_b_394_);
return v___x_397_;
}
else
{
lean_object* v_a_398_; lean_object* v___x_399_; size_t v___x_400_; size_t v___x_401_; 
v_a_398_ = lean_array_uget_borrowed(v_as_391_, v_i_393_);
lean_inc(v_a_398_);
v___x_399_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_394_, v_a_398_);
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_add(v_i_393_, v___x_400_);
v_i_393_ = v___x_401_;
v_b_394_ = v___x_399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg___boxed(lean_object* v_as_403_, lean_object* v_sz_404_, lean_object* v_i_405_, lean_object* v_b_406_, lean_object* v___y_407_){
_start:
{
size_t v_sz_boxed_408_; size_t v_i_boxed_409_; lean_object* v_res_410_; 
v_sz_boxed_408_ = lean_unbox_usize(v_sz_404_);
lean_dec(v_sz_404_);
v_i_boxed_409_ = lean_unbox_usize(v_i_405_);
lean_dec(v_i_405_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_as_403_, v_sz_boxed_408_, v_i_boxed_409_, v_b_406_);
lean_dec_ref(v_as_403_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(lean_object* v_declName_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; lean_object* v_env_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_414_ = lean_st_ref_get(v___y_412_);
v_env_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_ref(v_env_415_);
lean_dec(v___x_414_);
v___x_416_ = l_Lean_getReducibilityStatusCore(v_env_415_, v_declName_411_);
v___x_417_ = lean_box(v___x_416_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg___boxed(lean_object* v_declName_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_419_, v___y_420_);
lean_dec(v___y_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(lean_object* v_declName_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_445_; 
v___x_429_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_423_, v___y_427_);
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_445_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_445_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_445_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
uint8_t v___x_434_; 
v___x_434_ = lean_unbox(v_a_430_);
lean_dec(v_a_430_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_435_ = 1;
v___x_436_ = lean_box(v___x_435_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_436_);
v___x_438_ = v___x_432_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = 0;
v___x_441_ = lean_box(v___x_440_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_441_);
v___x_443_ = v___x_432_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0___boxed(lean_object* v_declName_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(v_declName_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_452_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__0));
v___x_455_ = l_Lean_stringToMessageData(v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(lean_object* v_as_x27_456_, lean_object* v_b_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
if (lean_obj_tag(v_as_x27_456_) == 0)
{
lean_object* v___x_463_; 
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v_b_457_);
return v___x_463_;
}
else
{
lean_object* v_head_464_; lean_object* v_tail_465_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_540_; 
v_head_464_ = lean_ctor_get(v_as_x27_456_, 0);
v_tail_465_ = lean_ctor_get(v_as_x27_456_, 1);
v_fst_471_ = lean_ctor_get(v_b_457_, 0);
v_snd_472_ = lean_ctor_get(v_b_457_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_b_457_);
if (v_isSharedCheck_540_ == 0)
{
v___x_474_ = v_b_457_;
v_isShared_475_ = v_isSharedCheck_540_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_inc(v_fst_471_);
lean_dec(v_b_457_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_540_;
goto v_resetjp_473_;
}
v___jp_466_:
{
lean_object* v___x_469_; 
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v_fst_467_);
lean_ctor_set(v___x_469_, 1, v_snd_468_);
v_as_x27_456_ = v_tail_465_;
v_b_457_ = v___x_469_;
goto _start;
}
v_resetjp_473_:
{
lean_object* v___x_476_; 
lean_inc(v_head_464_);
v___x_476_ = l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(v_head_464_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_531_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_531_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_531_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_531_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___y_482_; uint8_t v___y_483_; lean_object* v_a_512_; uint8_t v___x_515_; 
v___x_515_ = lean_unbox(v_a_477_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
lean_del_object(v___x_474_);
lean_inc(v_head_464_);
v___x_516_ = l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(v_head_464_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; size_t v_sz_518_; size_t v___x_519_; lean_object* v___x_520_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v_sz_518_ = lean_array_size(v_a_517_);
v___x_519_ = ((size_t)0ULL);
lean_inc(v_fst_471_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_a_517_, v_sz_518_, v___x_519_, v_fst_471_);
lean_dec(v_a_517_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
lean_inc(v_head_464_);
lean_inc(v_snd_472_);
v___x_522_ = l_Lean_Meta_Sym_DSimp_Decls_add(v_snd_472_, v_head_464_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; 
lean_del_object(v___x_479_);
lean_dec(v_a_477_);
lean_dec(v_snd_472_);
lean_dec(v_fst_471_);
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v_fst_467_ = v_a_521_;
v_snd_468_ = v_a_523_;
goto v___jp_466_;
}
else
{
lean_object* v_a_524_; 
lean_dec(v_a_521_);
v_a_524_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_522_, 1);
v_a_512_ = v_a_524_;
goto v___jp_511_;
}
}
else
{
lean_object* v_a_525_; 
v_a_525_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_520_, 1);
v_a_512_ = v_a_525_;
goto v___jp_511_;
}
}
else
{
lean_object* v_a_526_; 
v_a_526_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_516_, 1);
v_a_512_ = v_a_526_;
goto v___jp_511_;
}
}
else
{
lean_object* v___x_528_; 
lean_del_object(v___x_479_);
lean_dec(v_a_477_);
if (v_isShared_475_ == 0)
{
v___x_528_ = v___x_474_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_fst_471_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_snd_472_);
v___x_528_ = v_reuseFailAlloc_530_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v_as_x27_456_ = v_tail_465_;
v_b_457_ = v___x_528_;
goto _start;
}
}
v___jp_481_:
{
if (v___y_483_ == 0)
{
lean_object* v_toCold_484_; lean_object* v_options_485_; uint8_t v_hasTrace_486_; 
lean_del_object(v___x_479_);
v_toCold_484_ = lean_ctor_get(v___y_460_, 0);
v_options_485_ = lean_ctor_get(v_toCold_484_, 2);
v_hasTrace_486_ = lean_ctor_get_uint8(v_options_485_, sizeof(void*)*1);
if (v_hasTrace_486_ == 0)
{
lean_dec_ref(v___y_482_);
lean_dec(v_a_477_);
v_fst_467_ = v_fst_471_;
v_snd_468_ = v_snd_472_;
goto v___jp_466_;
}
else
{
lean_object* v_inheritedTraceOptions_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_inheritedTraceOptions_487_ = lean_ctor_get(v_toCold_484_, 11);
v___x_488_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2);
v___x_490_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_487_, v_options_485_, v___x_489_);
if (v___x_490_ == 0)
{
lean_dec_ref(v___y_482_);
lean_dec(v_a_477_);
v_fst_467_ = v_fst_471_;
v_snd_468_ = v_snd_472_;
goto v___jp_466_;
}
else
{
lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_491_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1);
v___x_492_ = lean_unbox(v_a_477_);
lean_dec(v_a_477_);
lean_inc(v_head_464_);
v___x_493_ = l_Lean_MessageData_ofConstName(v_head_464_, v___x_492_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_491_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = l_Lean_Exception_toMessageData(v___y_482_);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v___x_488_, v___x_498_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_dec_ref_known(v___x_499_, 1);
v_fst_467_ = v_fst_471_;
v_snd_468_ = v_snd_472_;
goto v___jp_466_;
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec(v_snd_472_);
lean_dec(v_fst_471_);
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
}
else
{
lean_object* v___x_509_; 
lean_dec(v_a_477_);
lean_dec(v_snd_472_);
lean_dec(v_fst_471_);
if (v_isShared_480_ == 0)
{
lean_ctor_set_tag(v___x_479_, 1);
lean_ctor_set(v___x_479_, 0, v___y_482_);
v___x_509_ = v___x_479_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___y_482_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
v___jp_511_:
{
uint8_t v___x_513_; 
v___x_513_ = l_Lean_Exception_isInterrupt(v_a_512_);
if (v___x_513_ == 0)
{
uint8_t v___x_514_; 
lean_inc_ref(v_a_512_);
v___x_514_ = l_Lean_Exception_isRuntime(v_a_512_);
v___y_482_ = v_a_512_;
v___y_483_ = v___x_514_;
goto v___jp_481_;
}
else
{
v___y_482_ = v_a_512_;
v___y_483_ = v___x_513_;
goto v___jp_481_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_del_object(v___x_474_);
lean_dec(v_snd_472_);
lean_dec(v_fst_471_);
v_a_532_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_476_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_476_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___boxed(lean_object* v_as_x27_541_, lean_object* v_b_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(v_as_x27_541_, v_b_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v_as_x27_541_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(lean_object* v_as_549_, size_t v_sz_550_, size_t v_i_551_, lean_object* v_b_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_a_559_; uint8_t v___x_563_; 
v___x_563_ = lean_usize_dec_lt(v_i_551_, v_sz_550_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v_b_552_);
return v___x_564_;
}
else
{
lean_object* v_fst_565_; lean_object* v_snd_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_605_; 
v_fst_565_ = lean_ctor_get(v_b_552_, 0);
v_snd_566_ = lean_ctor_get(v_b_552_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_b_552_);
if (v_isSharedCheck_605_ == 0)
{
v___x_568_ = v_b_552_;
v_isShared_569_ = v_isSharedCheck_605_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_snd_566_);
lean_inc(v_fst_565_);
lean_dec(v_b_552_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_605_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v_a_570_; lean_object* v___x_571_; 
v_a_570_ = lean_array_uget_borrowed(v_as_549_, v_i_551_);
lean_inc(v_a_570_);
v___x_571_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_fst_565_, v_a_570_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_571_) == 0)
{
uint8_t v_rfl_572_; 
v_rfl_572_ = lean_ctor_get_uint8(v_a_570_, sizeof(void*)*5 + 2);
if (v_rfl_572_ == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; 
v_a_573_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_571_, 1);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v_a_573_);
v___x_575_ = v___x_568_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_573_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_snd_566_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
v_a_559_ = v___x_575_;
goto v___jp_558_;
}
}
else
{
lean_object* v_proof_577_; 
v_proof_577_ = lean_ctor_get(v_a_570_, 2);
if (lean_obj_tag(v_proof_577_) == 4)
{
lean_object* v_a_578_; lean_object* v_declName_579_; lean_object* v___x_580_; 
v_a_578_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_571_, 1);
v_declName_579_ = lean_ctor_get(v_proof_577_, 0);
lean_inc(v_declName_579_);
v___x_580_ = l_Lean_Meta_Sym_DSimp_Decls_add(v_snd_566_, v_declName_579_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 1, v_a_581_);
lean_ctor_set(v___x_568_, 0, v_a_578_);
v___x_583_ = v___x_568_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_a_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
v_a_559_ = v___x_583_;
goto v___jp_558_;
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec(v_a_578_);
lean_del_object(v___x_568_);
v_a_585_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_580_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_580_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; 
v_a_593_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_571_, 1);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v_a_593_);
v___x_595_ = v___x_568_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_593_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_snd_566_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
v_a_559_ = v___x_595_;
goto v___jp_558_;
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_del_object(v___x_568_);
lean_dec(v_snd_566_);
v_a_597_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_571_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_571_);
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
}
v___jp_558_:
{
size_t v___x_560_; size_t v___x_561_; 
v___x_560_ = ((size_t)1ULL);
v___x_561_ = lean_usize_add(v_i_551_, v___x_560_);
v_i_551_ = v___x_561_;
v_b_552_ = v_a_559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6___boxed(lean_object* v_as_606_, lean_object* v_sz_607_, lean_object* v_i_608_, lean_object* v_b_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
size_t v_sz_boxed_615_; size_t v_i_boxed_616_; lean_object* v_res_617_; 
v_sz_boxed_615_ = lean_unbox_usize(v_sz_607_);
lean_dec(v_sz_607_);
v_i_boxed_616_ = lean_unbox_usize(v_i_608_);
lean_dec(v_i_608_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(v_as_606_, v_sz_boxed_615_, v_i_boxed_616_, v_b_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec_ref(v_as_606_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(lean_object* v_as_618_, size_t v_sz_619_, size_t v_i_620_, lean_object* v_b_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = lean_usize_dec_lt(v_i_620_, v_sz_619_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_b_621_);
return v___x_628_;
}
else
{
lean_object* v_a_629_; lean_object* v___x_630_; 
v_a_629_ = lean_array_uget_borrowed(v_as_618_, v_i_620_);
lean_inc(v_a_629_);
v___x_630_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_b_621_, v_a_629_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; size_t v___x_632_; size_t v___x_633_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_add(v_i_620_, v___x_632_);
v_i_620_ = v___x_633_;
v_b_621_ = v_a_631_;
goto _start;
}
else
{
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4___boxed(lean_object* v_as_635_, lean_object* v_sz_636_, lean_object* v_i_637_, lean_object* v_b_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
size_t v_sz_boxed_644_; size_t v_i_boxed_645_; lean_object* v_res_646_; 
v_sz_boxed_644_ = lean_unbox_usize(v_sz_636_);
lean_dec(v_sz_636_);
v_i_boxed_645_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_res_646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(v_as_635_, v_sz_boxed_644_, v_i_boxed_645_, v_b_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec_ref(v_as_635_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__12(lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
if (lean_obj_tag(v_a_647_) == 0)
{
lean_object* v___x_649_; 
v___x_649_ = l_List_reverse___redArg(v_a_648_);
return v___x_649_;
}
else
{
lean_object* v_head_650_; lean_object* v_tail_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_660_; 
v_head_650_ = lean_ctor_get(v_a_647_, 0);
v_tail_651_ = lean_ctor_get(v_a_647_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v_a_647_);
if (v_isSharedCheck_660_ == 0)
{
v___x_653_ = v_a_647_;
v_isShared_654_ = v_isSharedCheck_660_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_tail_651_);
lean_inc(v_head_650_);
lean_dec(v_a_647_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_660_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v_fst_655_; lean_object* v___x_657_; 
v_fst_655_ = lean_ctor_get(v_head_650_, 0);
lean_inc(v_fst_655_);
lean_dec(v_head_650_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v_a_648_);
lean_ctor_set(v___x_653_, 0, v_fst_655_);
v___x_657_ = v___x_653_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_fst_655_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_a_648_);
v___x_657_ = v_reuseFailAlloc_659_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
v_a_647_ = v_tail_651_;
v_a_648_ = v___x_657_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg___lam__0(lean_object* v_f_661_, lean_object* v_x1_662_, lean_object* v_x2_663_, lean_object* v_x3_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lean_apply_3(v_f_661_, v_x1_662_, v_x2_663_, v_x3_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(lean_object* v_f_666_, lean_object* v_keys_667_, lean_object* v_vals_668_, lean_object* v_i_669_, lean_object* v_acc_670_){
_start:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_array_get_size(v_keys_667_);
v___x_672_ = lean_nat_dec_lt(v_i_669_, v___x_671_);
if (v___x_672_ == 0)
{
lean_dec(v_i_669_);
lean_dec(v_f_666_);
return v_acc_670_;
}
else
{
lean_object* v_k_673_; lean_object* v_v_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_k_673_ = lean_array_fget_borrowed(v_keys_667_, v_i_669_);
v_v_674_ = lean_array_fget_borrowed(v_vals_668_, v_i_669_);
lean_inc(v_f_666_);
lean_inc(v_v_674_);
lean_inc(v_k_673_);
v___x_675_ = lean_apply_3(v_f_666_, v_acc_670_, v_k_673_, v_v_674_);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_add(v_i_669_, v___x_676_);
lean_dec(v_i_669_);
v_i_669_ = v___x_677_;
v_acc_670_ = v___x_675_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_f_679_, lean_object* v_keys_680_, lean_object* v_vals_681_, lean_object* v_i_682_, lean_object* v_acc_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_679_, v_keys_680_, v_vals_681_, v_i_682_, v_acc_683_);
lean_dec_ref(v_vals_681_);
lean_dec_ref(v_keys_680_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(lean_object* v_f_685_, lean_object* v_as_686_, size_t v_i_687_, size_t v_stop_688_, lean_object* v_b_689_){
_start:
{
lean_object* v___y_691_; uint8_t v___x_695_; 
v___x_695_ = lean_usize_dec_eq(v_i_687_, v_stop_688_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
v___x_696_ = lean_array_uget_borrowed(v_as_686_, v_i_687_);
switch(lean_obj_tag(v___x_696_))
{
case 0:
{
lean_object* v_key_697_; lean_object* v_val_698_; lean_object* v___x_699_; 
v_key_697_ = lean_ctor_get(v___x_696_, 0);
v_val_698_ = lean_ctor_get(v___x_696_, 1);
lean_inc(v_f_685_);
lean_inc(v_val_698_);
lean_inc(v_key_697_);
v___x_699_ = lean_apply_3(v_f_685_, v_b_689_, v_key_697_, v_val_698_);
v___y_691_ = v___x_699_;
goto v___jp_690_;
}
case 1:
{
lean_object* v_node_700_; lean_object* v___x_701_; 
v_node_700_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_f_685_);
v___x_701_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_685_, v_node_700_, v_b_689_);
v___y_691_ = v___x_701_;
goto v___jp_690_;
}
default: 
{
v___y_691_ = v_b_689_;
goto v___jp_690_;
}
}
}
else
{
lean_dec(v_f_685_);
return v_b_689_;
}
v___jp_690_:
{
size_t v___x_692_; size_t v___x_693_; 
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_687_, v___x_692_);
v_i_687_ = v___x_693_;
v_b_689_ = v___y_691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(lean_object* v_f_702_, lean_object* v_x_703_, lean_object* v_x_704_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_object* v_es_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_es_705_ = lean_ctor_get(v_x_703_, 0);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_array_get_size(v_es_705_);
v___x_708_ = lean_nat_dec_lt(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_dec(v_f_702_);
return v_x_704_;
}
else
{
size_t v___x_709_; size_t v___x_710_; lean_object* v___x_711_; 
v___x_709_ = ((size_t)0ULL);
v___x_710_ = lean_usize_of_nat(v___x_707_);
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_702_, v_es_705_, v___x_709_, v___x_710_, v_x_704_);
return v___x_711_;
}
}
else
{
lean_object* v_ks_712_; lean_object* v_vs_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_ks_712_ = lean_ctor_get(v_x_703_, 0);
v_vs_713_ = lean_ctor_get(v_x_703_, 1);
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_702_, v_ks_712_, v_vs_713_, v___x_714_, v_x_704_);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg___boxed(lean_object* v_f_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_716_, v_x_717_, v_x_718_);
lean_dec_ref(v_x_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v_f_720_, lean_object* v_as_721_, lean_object* v_i_722_, lean_object* v_stop_723_, lean_object* v_b_724_){
_start:
{
size_t v_i_boxed_725_; size_t v_stop_boxed_726_; lean_object* v_res_727_; 
v_i_boxed_725_ = lean_unbox_usize(v_i_722_);
lean_dec(v_i_722_);
v_stop_boxed_726_ = lean_unbox_usize(v_stop_723_);
lean_dec(v_stop_723_);
v_res_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_720_, v_as_721_, v_i_boxed_725_, v_stop_boxed_726_, v_b_724_);
lean_dec_ref(v_as_721_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(lean_object* v_map_728_, lean_object* v_f_729_, lean_object* v_init_730_){
_start:
{
lean_object* v___f_731_; lean_object* v___x_732_; 
v___f_731_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg___lam__0), 4, 1);
lean_closure_set(v___f_731_, 0, v_f_729_);
v___x_732_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_731_, v_map_728_, v_init_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg___boxed(lean_object* v_map_733_, lean_object* v_f_734_, lean_object* v_init_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(v_map_733_, v_f_734_, v_init_735_);
lean_dec_ref(v_map_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___lam__0(lean_object* v_ps_737_, lean_object* v_k_738_, lean_object* v_v_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v_k_738_);
lean_ctor_set(v___x_740_, 1, v_v_739_);
v___x_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_ps_737_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(lean_object* v_m_743_){
_start:
{
lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___f_744_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___closed__0));
v___x_745_ = lean_box(0);
v___x_746_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(v_m_743_, v___f_744_, v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___boxed(lean_object* v_m_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(v_m_747_);
lean_dec_ref(v_m_747_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(lean_object* v_s_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(v_s_749_);
v___x_751_ = lean_box(0);
v___x_752_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__12(v___x_750_, v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___boxed(lean_object* v_s_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(v_s_753_);
lean_dec_ref(v_s_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(lean_object* v_as_x27_755_, lean_object* v_b_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
if (lean_obj_tag(v_as_x27_755_) == 0)
{
lean_object* v___x_762_; 
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v_b_756_);
return v___x_762_;
}
else
{
lean_object* v_head_763_; lean_object* v_tail_764_; lean_object* v___x_765_; 
v_head_763_ = lean_ctor_get(v_as_x27_755_, 0);
v_tail_764_ = lean_ctor_get(v_as_x27_755_, 1);
lean_inc(v_head_763_);
v___x_765_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_head_763_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_756_, v_a_766_);
v_as_x27_755_ = v_tail_764_;
v_b_756_ = v___x_767_;
goto _start;
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_b_756_);
v_a_769_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_765_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_765_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg___boxed(lean_object* v_as_x27_777_, lean_object* v_b_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v_as_x27_777_, v_b_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_as_x27_777_);
return v_res_784_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1(void){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_786_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__2(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__1, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__1_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__2, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__2_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__2);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__12(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = l_Lean_NameSet_empty;
v___x_809_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__3, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__3_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v___x_808_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__13(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__12, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__12_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__12);
v___x_812_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__3, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__3_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems(lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v___f_819_; lean_object* v___x_820_; 
v___f_819_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__0));
v___x_820_ = l_Lean_Meta_Grind_getNormTheorems(v_a_814_, v_a_815_, v_a_816_, v_a_817_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; lean_object* v_pre_823_; lean_object* v_post_824_; lean_object* v_toUnfold_825_; lean_object* v___x_826_; lean_object* v___x_827_; size_t v_sz_828_; size_t v___x_829_; lean_object* v___x_830_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
v___x_822_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__3, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__3_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3);
v_pre_823_ = lean_ctor_get(v_a_821_, 0);
lean_inc_ref(v_pre_823_);
v_post_824_ = lean_ctor_get(v_a_821_, 1);
lean_inc_ref(v_post_824_);
v_toUnfold_825_ = lean_ctor_get(v_a_821_, 3);
lean_inc_ref(v_toUnfold_825_);
lean_dec(v_a_821_);
v___x_826_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__4));
v___x_827_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_819_, v_pre_823_, v___x_826_);
lean_dec_ref(v_pre_823_);
v_sz_828_ = lean_array_size(v___x_827_);
v___x_829_ = ((size_t)0ULL);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(v___x_827_, v_sz_828_, v___x_829_, v___x_822_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v___x_827_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_830_, 1);
v___x_832_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__11));
v___x_833_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v___x_832_, v_a_831_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_835_; lean_object* v___x_836_; size_t v_sz_837_; lean_object* v___x_838_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
v___x_835_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_819_, v_post_824_, v___x_826_);
lean_dec_ref(v_post_824_);
v___x_836_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__13, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__13_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__13);
v_sz_837_ = lean_array_size(v___x_835_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(v___x_835_, v_sz_837_, v___x_829_, v___x_836_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v___x_835_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v_fst_840_; lean_object* v_snd_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_869_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
v_fst_840_ = lean_ctor_get(v_a_839_, 0);
v_snd_841_ = lean_ctor_get(v_a_839_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v_a_839_);
if (v_isSharedCheck_869_ == 0)
{
v___x_843_ = v_a_839_;
v_isShared_844_ = v_isSharedCheck_869_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_snd_841_);
lean_inc(v_fst_840_);
lean_dec(v_a_839_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_869_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(v_toUnfold_825_);
lean_dec_ref(v_toUnfold_825_);
if (v_isShared_844_ == 0)
{
v___x_847_ = v___x_843_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_fst_840_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_snd_841_);
v___x_847_ = v_reuseFailAlloc_868_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; 
v___x_848_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(v___x_845_, v___x_847_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v___x_845_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_859_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_859_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_859_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_859_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_fst_853_; lean_object* v_snd_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v_fst_853_ = lean_ctor_get(v_a_849_, 0);
lean_inc(v_fst_853_);
v_snd_854_ = lean_ctor_get(v_a_849_, 1);
lean_inc(v_snd_854_);
lean_dec(v_a_849_);
v___x_855_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_855_, 0, v_a_834_);
lean_ctor_set(v___x_855_, 1, v_fst_853_);
lean_ctor_set(v___x_855_, 2, v_snd_854_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_855_);
v___x_857_ = v___x_851_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_a_834_);
v_a_860_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_848_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_848_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_a_834_);
lean_dec_ref(v_toUnfold_825_);
v_a_870_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_838_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_838_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v_toUnfold_825_);
lean_dec_ref(v_post_824_);
v_a_878_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_833_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_833_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v_toUnfold_825_);
lean_dec_ref(v_post_824_);
v_a_886_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_830_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_830_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
v_a_894_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_820_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_820_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___boxed(lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Meta_Grind_mkNormSymTheorems(v_a_902_, v_a_903_, v_a_904_, v_a_905_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0(lean_object* v_declName_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_908_, v___y_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___boxed(lean_object* v_declName_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0(v_declName_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1(lean_object* v_as_922_, size_t v_sz_923_, size_t v_i_924_, lean_object* v_b_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_as_922_, v_sz_923_, v_i_924_, v_b_925_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___boxed(lean_object* v_as_932_, lean_object* v_sz_933_, lean_object* v_i_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_933_);
lean_dec(v_sz_933_);
v_i_boxed_942_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1(v_as_932_, v_sz_boxed_941_, v_i_boxed_942_, v_b_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec_ref(v_as_932_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg(lean_object* v_map_944_, lean_object* v_f_945_, lean_object* v_init_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_945_, v_map_944_, v_init_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg___boxed(lean_object* v_map_948_, lean_object* v_f_949_, lean_object* v_init_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg(v_map_948_, v_f_949_, v_init_950_);
lean_dec_ref(v_map_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3(lean_object* v_00_u03c3_952_, lean_object* v_00_u03b2_953_, lean_object* v_map_954_, lean_object* v_f_955_, lean_object* v_init_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_955_, v_map_954_, v_init_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___boxed(lean_object* v_00_u03c3_958_, lean_object* v_00_u03b2_959_, lean_object* v_map_960_, lean_object* v_f_961_, lean_object* v_init_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3(v_00_u03c3_958_, v_00_u03b2_959_, v_map_960_, v_f_961_, v_init_962_);
lean_dec_ref(v_map_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5(lean_object* v_as_964_, lean_object* v_as_x27_965_, lean_object* v_b_966_, lean_object* v_a_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v_as_x27_965_, v_b_966_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___boxed(lean_object* v_as_974_, lean_object* v_as_x27_975_, lean_object* v_b_976_, lean_object* v_a_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5(v_as_974_, v_as_x27_975_, v_b_976_, v_a_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v_as_x27_975_);
lean_dec(v_as_974_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8(lean_object* v_as_984_, lean_object* v_as_x27_985_, lean_object* v_b_986_, lean_object* v_a_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(v_as_x27_985_, v_b_986_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___boxed(lean_object* v_as_994_, lean_object* v_as_x27_995_, lean_object* v_b_996_, lean_object* v_a_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8(v_as_994_, v_as_x27_995_, v_b_996_, v_a_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v_as_x27_995_);
lean_dec(v_as_994_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6(lean_object* v_00_u03c3_1004_, lean_object* v_00_u03b1_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_f_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_1007_, v_x_1008_, v_x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1011_, lean_object* v_00_u03b1_1012_, lean_object* v_00_u03b2_1013_, lean_object* v_f_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6(v_00_u03c3_1011_, v_00_u03b1_1012_, v_00_u03b2_1013_, v_f_1014_, v_x_1015_, v_x_1016_);
lean_dec_ref(v_x_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11(lean_object* v_00_u03b2_1018_, lean_object* v_m_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(v_m_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1021_, lean_object* v_m_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11(v_00_u03b2_1021_, v_m_1022_);
lean_dec_ref(v_m_1022_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7(lean_object* v_00_u03b1_1024_, lean_object* v_00_u03b2_1025_, lean_object* v_00_u03c3_1026_, lean_object* v_f_1027_, lean_object* v_as_1028_, size_t v_i_1029_, size_t v_stop_1030_, lean_object* v_b_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_1027_, v_as_1028_, v_i_1029_, v_stop_1030_, v_b_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___boxed(lean_object* v_00_u03b1_1033_, lean_object* v_00_u03b2_1034_, lean_object* v_00_u03c3_1035_, lean_object* v_f_1036_, lean_object* v_as_1037_, lean_object* v_i_1038_, lean_object* v_stop_1039_, lean_object* v_b_1040_){
_start:
{
size_t v_i_boxed_1041_; size_t v_stop_boxed_1042_; lean_object* v_res_1043_; 
v_i_boxed_1041_ = lean_unbox_usize(v_i_1038_);
lean_dec(v_i_1038_);
v_stop_boxed_1042_ = lean_unbox_usize(v_stop_1039_);
lean_dec(v_stop_1039_);
v_res_1043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7(v_00_u03b1_1033_, v_00_u03b2_1034_, v_00_u03c3_1035_, v_f_1036_, v_as_1037_, v_i_boxed_1041_, v_stop_boxed_1042_, v_b_1040_);
lean_dec_ref(v_as_1037_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8(lean_object* v_00_u03c3_1044_, lean_object* v_00_u03b1_1045_, lean_object* v_00_u03b2_1046_, lean_object* v_f_1047_, lean_object* v_keys_1048_, lean_object* v_vals_1049_, lean_object* v_heq_1050_, lean_object* v_i_1051_, lean_object* v_acc_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_1047_, v_keys_1048_, v_vals_1049_, v_i_1051_, v_acc_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03c3_1054_, lean_object* v_00_u03b1_1055_, lean_object* v_00_u03b2_1056_, lean_object* v_f_1057_, lean_object* v_keys_1058_, lean_object* v_vals_1059_, lean_object* v_heq_1060_, lean_object* v_i_1061_, lean_object* v_acc_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8(v_00_u03c3_1054_, v_00_u03b1_1055_, v_00_u03b2_1056_, v_f_1057_, v_keys_1058_, v_vals_1059_, v_heq_1060_, v_i_1061_, v_acc_1062_);
lean_dec_ref(v_vals_1059_);
lean_dec_ref(v_keys_1058_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14(lean_object* v_00_u03c3_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_map_1066_, lean_object* v_f_1067_, lean_object* v_init_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(v_map_1066_, v_f_1067_, v_init_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___boxed(lean_object* v_00_u03c3_1070_, lean_object* v_00_u03b2_1071_, lean_object* v_map_1072_, lean_object* v_f_1073_, lean_object* v_init_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14(v_00_u03c3_1070_, v_00_u03b2_1071_, v_map_1072_, v_f_1073_, v_init_1074_);
lean_dec_ref(v_map_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___redArg(lean_object* v_map_1076_, lean_object* v_f_1077_, lean_object* v_init_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_1077_, v_map_1076_, v_init_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___redArg___boxed(lean_object* v_map_1080_, lean_object* v_f_1081_, lean_object* v_init_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___redArg(v_map_1080_, v_f_1081_, v_init_1082_);
lean_dec_ref(v_map_1080_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16(lean_object* v_00_u03c3_1084_, lean_object* v_00_u03b2_1085_, lean_object* v_map_1086_, lean_object* v_f_1087_, lean_object* v_init_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_1087_, v_map_1086_, v_init_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___boxed(lean_object* v_00_u03c3_1090_, lean_object* v_00_u03b2_1091_, lean_object* v_map_1092_, lean_object* v_f_1093_, lean_object* v_init_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16(v_00_u03c3_1090_, v_00_u03b2_1091_, v_map_1092_, v_f_1093_, v_init_1094_);
lean_dec_ref(v_map_1092_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0(lean_object* v_x_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; 
lean_inc_ref(v___y_1097_);
v___x_1108_ = l_Lean_Meta_Sym_Simp_reduceProj___redArg(v___y_1097_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
if (lean_obj_tag(v_a_1109_) == 0)
{
uint8_t v_done_1110_; 
v_done_1110_ = lean_ctor_get_uint8(v_a_1109_, 0);
if (v_done_1110_ == 0)
{
uint8_t v_contextDependent_1111_; lean_object* v___x_1112_; 
lean_dec_ref_known(v___x_1108_, 1);
v_contextDependent_1111_ = lean_ctor_get_uint8(v_a_1109_, 1);
lean_dec_ref_known(v_a_1109_, 0);
v___x_1112_ = l_Lean_Meta_Sym_Simp_reduceControl(v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; uint8_t v___y_1115_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
if (v_contextDependent_1111_ == 0)
{
return v___x_1112_;
}
else
{
if (lean_obj_tag(v_a_1113_) == 0)
{
uint8_t v_contextDependent_1125_; 
v_contextDependent_1125_ = lean_ctor_get_uint8(v_a_1113_, 1);
v___y_1115_ = v_contextDependent_1125_;
goto v___jp_1114_;
}
else
{
uint8_t v_contextDependent_1126_; 
v_contextDependent_1126_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*2 + 1);
v___y_1115_ = v_contextDependent_1126_;
goto v___jp_1114_;
}
}
v___jp_1114_:
{
if (v___y_1115_ == 0)
{
lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1123_; 
lean_inc(v_a_1113_);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v___x_1112_, 0);
lean_dec(v_unused_1124_);
v___x_1117_ = v___x_1112_;
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
else
{
lean_dec(v___x_1112_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1119_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1113_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1119_);
v___x_1121_ = v___x_1117_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
else
{
return v___x_1112_;
}
}
}
else
{
return v___x_1112_;
}
}
else
{
lean_dec_ref_known(v_a_1109_, 0);
lean_dec_ref(v___y_1097_);
return v___x_1108_;
}
}
else
{
uint8_t v_done_1127_; 
v_done_1127_ = lean_ctor_get_uint8(v_a_1109_, sizeof(void*)*2);
if (v_done_1127_ == 0)
{
lean_object* v_e_x27_1128_; lean_object* v_proof_1129_; uint8_t v_contextDependent_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref_known(v___x_1108_, 1);
v_e_x27_1128_ = lean_ctor_get(v_a_1109_, 0);
v_proof_1129_ = lean_ctor_get(v_a_1109_, 1);
v_contextDependent_1130_ = lean_ctor_get_uint8(v_a_1109_, sizeof(void*)*2 + 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_a_1109_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1132_ = v_a_1109_;
v_isShared_1133_ = v_isSharedCheck_1180_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_proof_1129_);
lean_inc(v_e_x27_1128_);
lean_dec(v_a_1109_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1180_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; 
lean_inc_ref(v_e_x27_1128_);
v___x_1134_ = l_Lean_Meta_Sym_Simp_reduceControl(v_e_x27_1128_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1179_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1179_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1179_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
if (lean_obj_tag(v_a_1135_) == 0)
{
uint8_t v_done_1139_; uint8_t v_contextDependent_1140_; uint8_t v___y_1142_; 
lean_dec_ref(v___y_1097_);
v_done_1139_ = lean_ctor_get_uint8(v_a_1135_, 0);
v_contextDependent_1140_ = lean_ctor_get_uint8(v_a_1135_, 1);
lean_dec_ref_known(v_a_1135_, 0);
if (v_contextDependent_1130_ == 0)
{
v___y_1142_ = v_contextDependent_1140_;
goto v___jp_1141_;
}
else
{
v___y_1142_ = v_contextDependent_1130_;
goto v___jp_1141_;
}
v___jp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1133_ == 0)
{
v___x_1144_ = v___x_1132_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_e_x27_1128_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_proof_1129_);
v___x_1144_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*2, v_done_1139_);
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*2 + 1, v___y_1142_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1144_);
v___x_1146_ = v___x_1137_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
lean_object* v_e_x27_1149_; lean_object* v_proof_1150_; uint8_t v_done_1151_; uint8_t v_contextDependent_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1178_; 
lean_del_object(v___x_1137_);
lean_del_object(v___x_1132_);
v_e_x27_1149_ = lean_ctor_get(v_a_1135_, 0);
v_proof_1150_ = lean_ctor_get(v_a_1135_, 1);
v_done_1151_ = lean_ctor_get_uint8(v_a_1135_, sizeof(void*)*2);
v_contextDependent_1152_ = lean_ctor_get_uint8(v_a_1135_, sizeof(void*)*2 + 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_a_1135_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1154_ = v_a_1135_;
v_isShared_1155_ = v_isSharedCheck_1178_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_proof_1150_);
lean_inc(v_e_x27_1149_);
lean_dec(v_a_1135_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1178_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; 
lean_inc_ref(v_e_x27_1149_);
v___x_1156_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1097_, v_e_x27_1128_, v_proof_1129_, v_e_x27_1149_, v_proof_1150_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1169_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1169_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1169_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
uint8_t v___y_1162_; 
if (v_contextDependent_1130_ == 0)
{
v___y_1162_ = v_contextDependent_1152_;
goto v___jp_1161_;
}
else
{
v___y_1162_ = v_contextDependent_1130_;
goto v___jp_1161_;
}
v___jp_1161_:
{
lean_object* v___x_1164_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_a_1157_);
v___x_1164_ = v___x_1154_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_e_x27_1149_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_a_1157_);
lean_ctor_set_uint8(v_reuseFailAlloc_1168_, sizeof(void*)*2, v_done_1151_);
v___x_1164_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1166_; 
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*2 + 1, v___y_1162_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1164_);
v___x_1166_ = v___x_1159_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_del_object(v___x_1154_);
lean_dec_ref(v_e_x27_1149_);
v_a_1170_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1156_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1156_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1132_);
lean_dec_ref(v_proof_1129_);
lean_dec_ref(v_e_x27_1128_);
lean_dec_ref(v___y_1097_);
return v___x_1134_;
}
}
}
else
{
lean_dec_ref_known(v_a_1109_, 2);
lean_dec_ref(v___y_1097_);
return v___x_1108_;
}
}
}
else
{
lean_dec_ref(v___y_1097_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0___boxed(lean_object* v_x_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__0(v_x_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1(lean_object* v___f_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_box(0);
lean_inc_ref(v___y_1196_);
v___x_1208_ = l_Lean_Meta_Sym_Simp_beta___redArg(v___y_1196_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
if (lean_obj_tag(v_a_1209_) == 0)
{
uint8_t v_done_1210_; 
v_done_1210_ = lean_ctor_get_uint8(v_a_1209_, 0);
if (v_done_1210_ == 0)
{
uint8_t v_contextDependent_1211_; lean_object* v___x_1212_; 
lean_dec_ref_known(v___x_1208_, 1);
v_contextDependent_1211_ = lean_ctor_get_uint8(v_a_1209_, 1);
lean_dec_ref_known(v_a_1209_, 0);
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1204_);
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
v___x_1212_ = lean_apply_12(v___f_1194_, v___x_1207_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, lean_box(0));
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; uint8_t v___y_1215_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
if (v_contextDependent_1211_ == 0)
{
lean_dec(v_a_1213_);
return v___x_1212_;
}
else
{
if (lean_obj_tag(v_a_1213_) == 0)
{
uint8_t v_contextDependent_1225_; 
v_contextDependent_1225_ = lean_ctor_get_uint8(v_a_1213_, 1);
v___y_1215_ = v_contextDependent_1225_;
goto v___jp_1214_;
}
else
{
uint8_t v_contextDependent_1226_; 
v_contextDependent_1226_ = lean_ctor_get_uint8(v_a_1213_, sizeof(void*)*2 + 1);
v___y_1215_ = v_contextDependent_1226_;
goto v___jp_1214_;
}
}
v___jp_1214_:
{
if (v___y_1215_ == 0)
{
lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v___x_1212_, 0);
lean_dec(v_unused_1224_);
v___x_1217_ = v___x_1212_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_dec(v___x_1212_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1213_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
else
{
lean_dec(v_a_1213_);
return v___x_1212_;
}
}
}
else
{
return v___x_1212_;
}
}
else
{
lean_dec_ref_known(v_a_1209_, 0);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___f_1194_);
return v___x_1208_;
}
}
else
{
uint8_t v_done_1227_; 
v_done_1227_ = lean_ctor_get_uint8(v_a_1209_, sizeof(void*)*2);
if (v_done_1227_ == 0)
{
lean_object* v_e_x27_1228_; lean_object* v_proof_1229_; uint8_t v_contextDependent_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref_known(v___x_1208_, 1);
v_e_x27_1228_ = lean_ctor_get(v_a_1209_, 0);
v_proof_1229_ = lean_ctor_get(v_a_1209_, 1);
v_contextDependent_1230_ = lean_ctor_get_uint8(v_a_1209_, sizeof(void*)*2 + 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_a_1209_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1232_ = v_a_1209_;
v_isShared_1233_ = v_isSharedCheck_1280_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_proof_1229_);
lean_inc(v_e_x27_1228_);
lean_dec(v_a_1209_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1280_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; 
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1204_);
lean_inc(v___y_1203_);
lean_inc_ref(v___y_1202_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
lean_inc(v___y_1199_);
lean_inc_ref(v___y_1198_);
lean_inc(v___y_1197_);
lean_inc_ref(v_e_x27_1228_);
v___x_1234_ = lean_apply_12(v___f_1194_, v___x_1207_, v_e_x27_1228_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, lean_box(0));
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1279_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1279_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1279_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
if (lean_obj_tag(v_a_1235_) == 0)
{
uint8_t v_done_1239_; uint8_t v_contextDependent_1240_; uint8_t v___y_1242_; 
lean_dec_ref(v___y_1196_);
v_done_1239_ = lean_ctor_get_uint8(v_a_1235_, 0);
v_contextDependent_1240_ = lean_ctor_get_uint8(v_a_1235_, 1);
lean_dec_ref_known(v_a_1235_, 0);
if (v_contextDependent_1230_ == 0)
{
v___y_1242_ = v_contextDependent_1240_;
goto v___jp_1241_;
}
else
{
v___y_1242_ = v_contextDependent_1230_;
goto v___jp_1241_;
}
v___jp_1241_:
{
lean_object* v___x_1244_; 
if (v_isShared_1233_ == 0)
{
v___x_1244_ = v___x_1232_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_e_x27_1228_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_proof_1229_);
v___x_1244_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*2, v_done_1239_);
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*2 + 1, v___y_1242_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1244_);
v___x_1246_ = v___x_1237_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_e_x27_1249_; lean_object* v_proof_1250_; uint8_t v_done_1251_; uint8_t v_contextDependent_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1278_; 
lean_del_object(v___x_1237_);
lean_del_object(v___x_1232_);
v_e_x27_1249_ = lean_ctor_get(v_a_1235_, 0);
v_proof_1250_ = lean_ctor_get(v_a_1235_, 1);
v_done_1251_ = lean_ctor_get_uint8(v_a_1235_, sizeof(void*)*2);
v_contextDependent_1252_ = lean_ctor_get_uint8(v_a_1235_, sizeof(void*)*2 + 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_a_1235_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1254_ = v_a_1235_;
v_isShared_1255_ = v_isSharedCheck_1278_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_proof_1250_);
lean_inc(v_e_x27_1249_);
lean_dec(v_a_1235_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1278_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; 
lean_inc_ref(v_e_x27_1249_);
v___x_1256_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1196_, v_e_x27_1228_, v_proof_1229_, v_e_x27_1249_, v_proof_1250_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1269_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
uint8_t v___y_1262_; 
if (v_contextDependent_1230_ == 0)
{
v___y_1262_ = v_contextDependent_1252_;
goto v___jp_1261_;
}
else
{
v___y_1262_ = v_contextDependent_1230_;
goto v___jp_1261_;
}
v___jp_1261_:
{
lean_object* v___x_1264_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v_a_1257_);
v___x_1264_ = v___x_1254_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_e_x27_1249_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_a_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1268_, sizeof(void*)*2, v_done_1251_);
v___x_1264_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1266_; 
lean_ctor_set_uint8(v___x_1264_, sizeof(void*)*2 + 1, v___y_1262_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1264_);
v___x_1266_ = v___x_1259_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_del_object(v___x_1254_);
lean_dec_ref(v_e_x27_1249_);
v_a_1270_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1256_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1256_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1232_);
lean_dec_ref(v_proof_1229_);
lean_dec_ref(v_e_x27_1228_);
lean_dec_ref(v___y_1196_);
return v___x_1234_;
}
}
}
else
{
lean_dec_ref_known(v_a_1209_, 2);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___f_1194_);
return v___x_1208_;
}
}
}
else
{
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___f_1194_);
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1___boxed(lean_object* v___f_1281_, lean_object* v_x_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__1(v___f_1281_, v_x_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2(lean_object* v___f_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_box(0);
lean_inc_ref(v___y_1297_);
v___x_1309_ = l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
if (lean_obj_tag(v_a_1310_) == 0)
{
uint8_t v_done_1311_; 
v_done_1311_ = lean_ctor_get_uint8(v_a_1310_, 0);
if (v_done_1311_ == 0)
{
uint8_t v_contextDependent_1312_; lean_object* v___x_1313_; 
lean_dec_ref_known(v___x_1309_, 1);
v_contextDependent_1312_ = lean_ctor_get_uint8(v_a_1310_, 1);
lean_dec_ref_known(v_a_1310_, 0);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
lean_inc(v___y_1302_);
lean_inc_ref(v___y_1301_);
lean_inc(v___y_1300_);
lean_inc_ref(v___y_1299_);
lean_inc(v___y_1298_);
v___x_1313_ = lean_apply_12(v___f_1295_, v___x_1308_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, lean_box(0));
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; uint8_t v___y_1316_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
if (v_contextDependent_1312_ == 0)
{
lean_dec(v_a_1314_);
return v___x_1313_;
}
else
{
if (lean_obj_tag(v_a_1314_) == 0)
{
uint8_t v_contextDependent_1326_; 
v_contextDependent_1326_ = lean_ctor_get_uint8(v_a_1314_, 1);
v___y_1316_ = v_contextDependent_1326_;
goto v___jp_1315_;
}
else
{
uint8_t v_contextDependent_1327_; 
v_contextDependent_1327_ = lean_ctor_get_uint8(v_a_1314_, sizeof(void*)*2 + 1);
v___y_1316_ = v_contextDependent_1327_;
goto v___jp_1315_;
}
}
v___jp_1315_:
{
if (v___y_1316_ == 0)
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v___x_1313_, 0);
lean_dec(v_unused_1325_);
v___x_1318_ = v___x_1313_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v___x_1313_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1314_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_dec(v_a_1314_);
return v___x_1313_;
}
}
}
else
{
return v___x_1313_;
}
}
else
{
lean_dec_ref_known(v_a_1310_, 0);
lean_dec_ref(v___y_1297_);
lean_dec_ref(v___f_1295_);
return v___x_1309_;
}
}
else
{
uint8_t v_done_1328_; 
v_done_1328_ = lean_ctor_get_uint8(v_a_1310_, sizeof(void*)*2);
if (v_done_1328_ == 0)
{
lean_object* v_e_x27_1329_; lean_object* v_proof_1330_; uint8_t v_contextDependent_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1381_; 
lean_dec_ref_known(v___x_1309_, 1);
v_e_x27_1329_ = lean_ctor_get(v_a_1310_, 0);
v_proof_1330_ = lean_ctor_get(v_a_1310_, 1);
v_contextDependent_1331_ = lean_ctor_get_uint8(v_a_1310_, sizeof(void*)*2 + 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_a_1310_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1333_ = v_a_1310_;
v_isShared_1334_ = v_isSharedCheck_1381_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_proof_1330_);
lean_inc(v_e_x27_1329_);
lean_dec(v_a_1310_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1381_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; 
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
lean_inc(v___y_1302_);
lean_inc_ref(v___y_1301_);
lean_inc(v___y_1300_);
lean_inc_ref(v___y_1299_);
lean_inc(v___y_1298_);
lean_inc_ref(v_e_x27_1329_);
v___x_1335_ = lean_apply_12(v___f_1295_, v___x_1308_, v_e_x27_1329_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, lean_box(0));
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1380_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1380_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1380_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
if (lean_obj_tag(v_a_1336_) == 0)
{
uint8_t v_done_1340_; uint8_t v_contextDependent_1341_; uint8_t v___y_1343_; 
lean_dec_ref(v___y_1297_);
v_done_1340_ = lean_ctor_get_uint8(v_a_1336_, 0);
v_contextDependent_1341_ = lean_ctor_get_uint8(v_a_1336_, 1);
lean_dec_ref_known(v_a_1336_, 0);
if (v_contextDependent_1331_ == 0)
{
v___y_1343_ = v_contextDependent_1341_;
goto v___jp_1342_;
}
else
{
v___y_1343_ = v_contextDependent_1331_;
goto v___jp_1342_;
}
v___jp_1342_:
{
lean_object* v___x_1345_; 
if (v_isShared_1334_ == 0)
{
v___x_1345_ = v___x_1333_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_e_x27_1329_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_proof_1330_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
lean_ctor_set_uint8(v___x_1345_, sizeof(void*)*2, v_done_1340_);
lean_ctor_set_uint8(v___x_1345_, sizeof(void*)*2 + 1, v___y_1343_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1345_);
v___x_1347_ = v___x_1338_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v_e_x27_1350_; lean_object* v_proof_1351_; uint8_t v_done_1352_; uint8_t v_contextDependent_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1379_; 
lean_del_object(v___x_1338_);
lean_del_object(v___x_1333_);
v_e_x27_1350_ = lean_ctor_get(v_a_1336_, 0);
v_proof_1351_ = lean_ctor_get(v_a_1336_, 1);
v_done_1352_ = lean_ctor_get_uint8(v_a_1336_, sizeof(void*)*2);
v_contextDependent_1353_ = lean_ctor_get_uint8(v_a_1336_, sizeof(void*)*2 + 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_a_1336_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1355_ = v_a_1336_;
v_isShared_1356_ = v_isSharedCheck_1379_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_proof_1351_);
lean_inc(v_e_x27_1350_);
lean_dec(v_a_1336_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1379_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; 
lean_inc_ref(v_e_x27_1350_);
v___x_1357_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1297_, v_e_x27_1329_, v_proof_1330_, v_e_x27_1350_, v_proof_1351_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1370_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1370_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1370_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
uint8_t v___y_1363_; 
if (v_contextDependent_1331_ == 0)
{
v___y_1363_ = v_contextDependent_1353_;
goto v___jp_1362_;
}
else
{
v___y_1363_ = v_contextDependent_1331_;
goto v___jp_1362_;
}
v___jp_1362_:
{
lean_object* v___x_1365_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v_a_1358_);
v___x_1365_ = v___x_1355_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_e_x27_1350_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_a_1358_);
lean_ctor_set_uint8(v_reuseFailAlloc_1369_, sizeof(void*)*2, v_done_1352_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
lean_ctor_set_uint8(v___x_1365_, sizeof(void*)*2 + 1, v___y_1363_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1365_);
v___x_1367_ = v___x_1360_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_del_object(v___x_1355_);
lean_dec_ref(v_e_x27_1350_);
v_a_1371_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1357_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1357_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1333_);
lean_dec_ref(v_proof_1330_);
lean_dec_ref(v_e_x27_1329_);
lean_dec_ref(v___y_1297_);
return v___x_1335_;
}
}
}
else
{
lean_dec_ref_known(v_a_1310_, 2);
lean_dec_ref(v___y_1297_);
lean_dec_ref(v___f_1295_);
return v___x_1309_;
}
}
}
else
{
lean_dec_ref(v___y_1297_);
lean_dec_ref(v___f_1295_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2___boxed(lean_object* v___f_1382_, lean_object* v_x_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__2(v___f_1382_, v_x_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3(lean_object* v___f_1396_, lean_object* v_x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_box(0);
lean_inc_ref(v___y_1398_);
v___x_1410_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v___y_1398_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
if (lean_obj_tag(v_a_1411_) == 0)
{
uint8_t v_done_1412_; 
v_done_1412_ = lean_ctor_get_uint8(v_a_1411_, 0);
if (v_done_1412_ == 0)
{
uint8_t v_contextDependent_1413_; lean_object* v___x_1414_; 
lean_dec_ref_known(v___x_1410_, 1);
v_contextDependent_1413_ = lean_ctor_get_uint8(v_a_1411_, 1);
lean_dec_ref_known(v_a_1411_, 0);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v___y_1399_);
v___x_1414_ = lean_apply_12(v___f_1396_, v___x_1409_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, lean_box(0));
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; uint8_t v___y_1417_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
if (v_contextDependent_1413_ == 0)
{
lean_dec(v_a_1415_);
return v___x_1414_;
}
else
{
if (lean_obj_tag(v_a_1415_) == 0)
{
uint8_t v_contextDependent_1427_; 
v_contextDependent_1427_ = lean_ctor_get_uint8(v_a_1415_, 1);
v___y_1417_ = v_contextDependent_1427_;
goto v___jp_1416_;
}
else
{
uint8_t v_contextDependent_1428_; 
v_contextDependent_1428_ = lean_ctor_get_uint8(v_a_1415_, sizeof(void*)*2 + 1);
v___y_1417_ = v_contextDependent_1428_;
goto v___jp_1416_;
}
}
v___jp_1416_:
{
if (v___y_1417_ == 0)
{
lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1425_; 
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v___x_1414_, 0);
lean_dec(v_unused_1426_);
v___x_1419_ = v___x_1414_;
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
else
{
lean_dec(v___x_1414_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1415_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1421_);
v___x_1423_ = v___x_1419_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_dec(v_a_1415_);
return v___x_1414_;
}
}
}
else
{
return v___x_1414_;
}
}
else
{
lean_dec_ref_known(v_a_1411_, 0);
lean_dec_ref(v___y_1398_);
lean_dec_ref(v___f_1396_);
return v___x_1410_;
}
}
else
{
uint8_t v_done_1429_; 
v_done_1429_ = lean_ctor_get_uint8(v_a_1411_, sizeof(void*)*2);
if (v_done_1429_ == 0)
{
lean_object* v_e_x27_1430_; lean_object* v_proof_1431_; uint8_t v_contextDependent_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref_known(v___x_1410_, 1);
v_e_x27_1430_ = lean_ctor_get(v_a_1411_, 0);
v_proof_1431_ = lean_ctor_get(v_a_1411_, 1);
v_contextDependent_1432_ = lean_ctor_get_uint8(v_a_1411_, sizeof(void*)*2 + 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_a_1411_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1434_ = v_a_1411_;
v_isShared_1435_ = v_isSharedCheck_1482_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_proof_1431_);
lean_inc(v_e_x27_1430_);
lean_dec(v_a_1411_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1482_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; 
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v___y_1399_);
lean_inc_ref(v_e_x27_1430_);
v___x_1436_ = lean_apply_12(v___f_1396_, v___x_1409_, v_e_x27_1430_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, lean_box(0));
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1481_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1481_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1481_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
if (lean_obj_tag(v_a_1437_) == 0)
{
uint8_t v_done_1441_; uint8_t v_contextDependent_1442_; uint8_t v___y_1444_; 
lean_dec_ref(v___y_1398_);
v_done_1441_ = lean_ctor_get_uint8(v_a_1437_, 0);
v_contextDependent_1442_ = lean_ctor_get_uint8(v_a_1437_, 1);
lean_dec_ref_known(v_a_1437_, 0);
if (v_contextDependent_1432_ == 0)
{
v___y_1444_ = v_contextDependent_1442_;
goto v___jp_1443_;
}
else
{
v___y_1444_ = v_contextDependent_1432_;
goto v___jp_1443_;
}
v___jp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1435_ == 0)
{
v___x_1446_ = v___x_1434_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_e_x27_1430_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_proof_1431_);
v___x_1446_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1448_; 
lean_ctor_set_uint8(v___x_1446_, sizeof(void*)*2, v_done_1441_);
lean_ctor_set_uint8(v___x_1446_, sizeof(void*)*2 + 1, v___y_1444_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1446_);
v___x_1448_ = v___x_1439_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v_e_x27_1451_; lean_object* v_proof_1452_; uint8_t v_done_1453_; uint8_t v_contextDependent_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1480_; 
lean_del_object(v___x_1439_);
lean_del_object(v___x_1434_);
v_e_x27_1451_ = lean_ctor_get(v_a_1437_, 0);
v_proof_1452_ = lean_ctor_get(v_a_1437_, 1);
v_done_1453_ = lean_ctor_get_uint8(v_a_1437_, sizeof(void*)*2);
v_contextDependent_1454_ = lean_ctor_get_uint8(v_a_1437_, sizeof(void*)*2 + 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_a_1437_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1456_ = v_a_1437_;
v_isShared_1457_ = v_isSharedCheck_1480_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_proof_1452_);
lean_inc(v_e_x27_1451_);
lean_dec(v_a_1437_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1480_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; 
lean_inc_ref(v_e_x27_1451_);
v___x_1458_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1398_, v_e_x27_1430_, v_proof_1431_, v_e_x27_1451_, v_proof_1452_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1471_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1471_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1471_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
uint8_t v___y_1464_; 
if (v_contextDependent_1432_ == 0)
{
v___y_1464_ = v_contextDependent_1454_;
goto v___jp_1463_;
}
else
{
v___y_1464_ = v_contextDependent_1432_;
goto v___jp_1463_;
}
v___jp_1463_:
{
lean_object* v___x_1466_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 1, v_a_1459_);
v___x_1466_ = v___x_1456_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_e_x27_1451_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_a_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*2, v_done_1453_);
v___x_1466_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1468_; 
lean_ctor_set_uint8(v___x_1466_, sizeof(void*)*2 + 1, v___y_1464_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1466_);
v___x_1468_ = v___x_1461_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_del_object(v___x_1456_);
lean_dec_ref(v_e_x27_1451_);
v_a_1472_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1458_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1458_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1434_);
lean_dec_ref(v_proof_1431_);
lean_dec_ref(v_e_x27_1430_);
lean_dec_ref(v___y_1398_);
return v___x_1436_;
}
}
}
else
{
lean_dec_ref_known(v_a_1411_, 2);
lean_dec_ref(v___y_1398_);
lean_dec_ref(v___f_1396_);
return v___x_1410_;
}
}
}
else
{
lean_dec_ref(v___y_1398_);
lean_dec_ref(v___f_1396_);
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3___boxed(lean_object* v___f_1483_, lean_object* v_x_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__3(v___f_1483_, v_x_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4(lean_object* v_x_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
lean_inc_ref(v___y_1498_);
v___x_1509_ = l_Lean_Meta_Grind_NormSym_simpForall(v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
if (lean_obj_tag(v_a_1510_) == 0)
{
uint8_t v_done_1511_; 
v_done_1511_ = lean_ctor_get_uint8(v_a_1510_, 0);
if (v_done_1511_ == 0)
{
uint8_t v_contextDependent_1512_; lean_object* v___x_1513_; 
lean_dec_ref_known(v___x_1509_, 1);
v_contextDependent_1512_ = lean_ctor_get_uint8(v_a_1510_, 1);
lean_dec_ref_known(v_a_1510_, 0);
v___x_1513_ = l_Lean_Meta_Grind_NormSym_simpExists(v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; uint8_t v___y_1516_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
if (v_contextDependent_1512_ == 0)
{
return v___x_1513_;
}
else
{
if (lean_obj_tag(v_a_1514_) == 0)
{
uint8_t v_contextDependent_1526_; 
v_contextDependent_1526_ = lean_ctor_get_uint8(v_a_1514_, 1);
v___y_1516_ = v_contextDependent_1526_;
goto v___jp_1515_;
}
else
{
uint8_t v_contextDependent_1527_; 
v_contextDependent_1527_ = lean_ctor_get_uint8(v_a_1514_, sizeof(void*)*2 + 1);
v___y_1516_ = v_contextDependent_1527_;
goto v___jp_1515_;
}
}
v___jp_1515_:
{
if (v___y_1516_ == 0)
{
lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1524_; 
lean_inc(v_a_1514_);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; 
v_unused_1525_ = lean_ctor_get(v___x_1513_, 0);
lean_dec(v_unused_1525_);
v___x_1518_ = v___x_1513_;
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v___x_1513_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1514_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1520_);
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
else
{
return v___x_1513_;
}
}
}
else
{
return v___x_1513_;
}
}
else
{
lean_dec_ref_known(v_a_1510_, 0);
lean_dec_ref(v___y_1498_);
return v___x_1509_;
}
}
else
{
uint8_t v_done_1528_; 
v_done_1528_ = lean_ctor_get_uint8(v_a_1510_, sizeof(void*)*2);
if (v_done_1528_ == 0)
{
lean_object* v_e_x27_1529_; lean_object* v_proof_1530_; uint8_t v_contextDependent_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref_known(v___x_1509_, 1);
v_e_x27_1529_ = lean_ctor_get(v_a_1510_, 0);
v_proof_1530_ = lean_ctor_get(v_a_1510_, 1);
v_contextDependent_1531_ = lean_ctor_get_uint8(v_a_1510_, sizeof(void*)*2 + 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_a_1510_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1533_ = v_a_1510_;
v_isShared_1534_ = v_isSharedCheck_1581_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_proof_1530_);
lean_inc(v_e_x27_1529_);
lean_dec(v_a_1510_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1581_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; 
lean_inc_ref(v_e_x27_1529_);
v___x_1535_ = l_Lean_Meta_Grind_NormSym_simpExists(v_e_x27_1529_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1580_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1580_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1580_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
if (lean_obj_tag(v_a_1536_) == 0)
{
uint8_t v_done_1540_; uint8_t v_contextDependent_1541_; uint8_t v___y_1543_; 
lean_dec_ref(v___y_1498_);
v_done_1540_ = lean_ctor_get_uint8(v_a_1536_, 0);
v_contextDependent_1541_ = lean_ctor_get_uint8(v_a_1536_, 1);
lean_dec_ref_known(v_a_1536_, 0);
if (v_contextDependent_1531_ == 0)
{
v___y_1543_ = v_contextDependent_1541_;
goto v___jp_1542_;
}
else
{
v___y_1543_ = v_contextDependent_1531_;
goto v___jp_1542_;
}
v___jp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1534_ == 0)
{
v___x_1545_ = v___x_1533_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_e_x27_1529_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_proof_1530_);
v___x_1545_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1547_; 
lean_ctor_set_uint8(v___x_1545_, sizeof(void*)*2, v_done_1540_);
lean_ctor_set_uint8(v___x_1545_, sizeof(void*)*2 + 1, v___y_1543_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1545_);
v___x_1547_ = v___x_1538_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v_e_x27_1550_; lean_object* v_proof_1551_; uint8_t v_done_1552_; uint8_t v_contextDependent_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1579_; 
lean_del_object(v___x_1538_);
lean_del_object(v___x_1533_);
v_e_x27_1550_ = lean_ctor_get(v_a_1536_, 0);
v_proof_1551_ = lean_ctor_get(v_a_1536_, 1);
v_done_1552_ = lean_ctor_get_uint8(v_a_1536_, sizeof(void*)*2);
v_contextDependent_1553_ = lean_ctor_get_uint8(v_a_1536_, sizeof(void*)*2 + 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_a_1536_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1555_ = v_a_1536_;
v_isShared_1556_ = v_isSharedCheck_1579_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_proof_1551_);
lean_inc(v_e_x27_1550_);
lean_dec(v_a_1536_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1579_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; 
lean_inc_ref(v_e_x27_1550_);
v___x_1557_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1498_, v_e_x27_1529_, v_proof_1530_, v_e_x27_1550_, v_proof_1551_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1570_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1570_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1570_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
uint8_t v___y_1563_; 
if (v_contextDependent_1531_ == 0)
{
v___y_1563_ = v_contextDependent_1553_;
goto v___jp_1562_;
}
else
{
v___y_1563_ = v_contextDependent_1531_;
goto v___jp_1562_;
}
v___jp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 1, v_a_1558_);
v___x_1565_ = v___x_1555_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_e_x27_1550_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_a_1558_);
lean_ctor_set_uint8(v_reuseFailAlloc_1569_, sizeof(void*)*2, v_done_1552_);
v___x_1565_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*2 + 1, v___y_1563_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1565_);
v___x_1567_ = v___x_1560_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_del_object(v___x_1555_);
lean_dec_ref(v_e_x27_1550_);
v_a_1571_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1557_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1557_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1533_);
lean_dec_ref(v_proof_1530_);
lean_dec_ref(v_e_x27_1529_);
lean_dec_ref(v___y_1498_);
return v___x_1535_;
}
}
}
else
{
lean_dec_ref_known(v_a_1510_, 2);
lean_dec_ref(v___y_1498_);
return v___x_1509_;
}
}
}
else
{
lean_dec_ref(v___y_1498_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4___boxed(lean_object* v_x_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__4(v_x_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5(lean_object* v___f_1595_, lean_object* v_x_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_box(0);
lean_inc_ref(v___y_1597_);
v___x_1609_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
if (lean_obj_tag(v_a_1610_) == 0)
{
uint8_t v_done_1611_; 
v_done_1611_ = lean_ctor_get_uint8(v_a_1610_, 0);
if (v_done_1611_ == 0)
{
uint8_t v_contextDependent_1612_; lean_object* v___x_1613_; 
lean_dec_ref_known(v___x_1609_, 1);
v_contextDependent_1612_ = lean_ctor_get_uint8(v_a_1610_, 1);
lean_dec_ref_known(v_a_1610_, 0);
lean_inc(v___y_1606_);
lean_inc_ref(v___y_1605_);
lean_inc(v___y_1604_);
lean_inc_ref(v___y_1603_);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v___y_1598_);
v___x_1613_ = lean_apply_12(v___f_1595_, v___x_1608_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, lean_box(0));
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; uint8_t v___y_1616_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
if (v_contextDependent_1612_ == 0)
{
lean_dec(v_a_1614_);
return v___x_1613_;
}
else
{
if (lean_obj_tag(v_a_1614_) == 0)
{
uint8_t v_contextDependent_1626_; 
v_contextDependent_1626_ = lean_ctor_get_uint8(v_a_1614_, 1);
v___y_1616_ = v_contextDependent_1626_;
goto v___jp_1615_;
}
else
{
uint8_t v_contextDependent_1627_; 
v_contextDependent_1627_ = lean_ctor_get_uint8(v_a_1614_, sizeof(void*)*2 + 1);
v___y_1616_ = v_contextDependent_1627_;
goto v___jp_1615_;
}
}
v___jp_1615_:
{
if (v___y_1616_ == 0)
{
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1624_; 
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; 
v_unused_1625_ = lean_ctor_get(v___x_1613_, 0);
lean_dec(v_unused_1625_);
v___x_1618_ = v___x_1613_;
v_isShared_1619_ = v_isSharedCheck_1624_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v___x_1613_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1624_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1620_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1614_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1620_);
v___x_1622_ = v___x_1618_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
else
{
lean_dec(v_a_1614_);
return v___x_1613_;
}
}
}
else
{
return v___x_1613_;
}
}
else
{
lean_dec_ref_known(v_a_1610_, 0);
lean_dec_ref(v___y_1597_);
lean_dec_ref(v___f_1595_);
return v___x_1609_;
}
}
else
{
uint8_t v_done_1628_; 
v_done_1628_ = lean_ctor_get_uint8(v_a_1610_, sizeof(void*)*2);
if (v_done_1628_ == 0)
{
lean_object* v_e_x27_1629_; lean_object* v_proof_1630_; uint8_t v_contextDependent_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1681_; 
lean_dec_ref_known(v___x_1609_, 1);
v_e_x27_1629_ = lean_ctor_get(v_a_1610_, 0);
v_proof_1630_ = lean_ctor_get(v_a_1610_, 1);
v_contextDependent_1631_ = lean_ctor_get_uint8(v_a_1610_, sizeof(void*)*2 + 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_a_1610_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1633_ = v_a_1610_;
v_isShared_1634_ = v_isSharedCheck_1681_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_proof_1630_);
lean_inc(v_e_x27_1629_);
lean_dec(v_a_1610_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1681_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; 
lean_inc(v___y_1606_);
lean_inc_ref(v___y_1605_);
lean_inc(v___y_1604_);
lean_inc_ref(v___y_1603_);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v___y_1598_);
lean_inc_ref(v_e_x27_1629_);
v___x_1635_ = lean_apply_12(v___f_1595_, v___x_1608_, v_e_x27_1629_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, lean_box(0));
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1680_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1680_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1680_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
if (lean_obj_tag(v_a_1636_) == 0)
{
uint8_t v_done_1640_; uint8_t v_contextDependent_1641_; uint8_t v___y_1643_; 
lean_dec_ref(v___y_1597_);
v_done_1640_ = lean_ctor_get_uint8(v_a_1636_, 0);
v_contextDependent_1641_ = lean_ctor_get_uint8(v_a_1636_, 1);
lean_dec_ref_known(v_a_1636_, 0);
if (v_contextDependent_1631_ == 0)
{
v___y_1643_ = v_contextDependent_1641_;
goto v___jp_1642_;
}
else
{
v___y_1643_ = v_contextDependent_1631_;
goto v___jp_1642_;
}
v___jp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1634_ == 0)
{
v___x_1645_ = v___x_1633_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_e_x27_1629_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_proof_1630_);
v___x_1645_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1647_; 
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*2, v_done_1640_);
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*2 + 1, v___y_1643_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1645_);
v___x_1647_ = v___x_1638_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_object* v_e_x27_1650_; lean_object* v_proof_1651_; uint8_t v_done_1652_; uint8_t v_contextDependent_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1679_; 
lean_del_object(v___x_1638_);
lean_del_object(v___x_1633_);
v_e_x27_1650_ = lean_ctor_get(v_a_1636_, 0);
v_proof_1651_ = lean_ctor_get(v_a_1636_, 1);
v_done_1652_ = lean_ctor_get_uint8(v_a_1636_, sizeof(void*)*2);
v_contextDependent_1653_ = lean_ctor_get_uint8(v_a_1636_, sizeof(void*)*2 + 1);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_a_1636_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1655_ = v_a_1636_;
v_isShared_1656_ = v_isSharedCheck_1679_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_proof_1651_);
lean_inc(v_e_x27_1650_);
lean_dec(v_a_1636_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1679_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; 
lean_inc_ref(v_e_x27_1650_);
v___x_1657_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1597_, v_e_x27_1629_, v_proof_1630_, v_e_x27_1650_, v_proof_1651_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1670_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1670_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1670_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
uint8_t v___y_1663_; 
if (v_contextDependent_1631_ == 0)
{
v___y_1663_ = v_contextDependent_1653_;
goto v___jp_1662_;
}
else
{
v___y_1663_ = v_contextDependent_1631_;
goto v___jp_1662_;
}
v___jp_1662_:
{
lean_object* v___x_1665_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v_a_1658_);
v___x_1665_ = v___x_1655_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_e_x27_1650_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_a_1658_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*2, v_done_1652_);
v___x_1665_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*2 + 1, v___y_1663_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1665_);
v___x_1667_ = v___x_1660_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_del_object(v___x_1655_);
lean_dec_ref(v_e_x27_1650_);
v_a_1671_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1657_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1657_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1633_);
lean_dec_ref(v_proof_1630_);
lean_dec_ref(v_e_x27_1629_);
lean_dec_ref(v___y_1597_);
return v___x_1635_;
}
}
}
else
{
lean_dec_ref_known(v_a_1610_, 2);
lean_dec_ref(v___y_1597_);
lean_dec_ref(v___f_1595_);
return v___x_1609_;
}
}
}
else
{
lean_dec_ref(v___y_1597_);
lean_dec_ref(v___f_1595_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed(lean_object* v___f_1682_, lean_object* v_x_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__5(v___f_1682_, v_x_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6(lean_object* v___f_1696_, lean_object* v_x_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_box(0);
lean_inc_ref(v___y_1698_);
v___x_1710_ = l_Lean_Meta_Grind_NormSym_simpDIte(v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
if (lean_obj_tag(v_a_1711_) == 0)
{
uint8_t v_done_1712_; 
v_done_1712_ = lean_ctor_get_uint8(v_a_1711_, 0);
if (v_done_1712_ == 0)
{
uint8_t v_contextDependent_1713_; lean_object* v___x_1714_; 
lean_dec_ref_known(v___x_1710_, 1);
v_contextDependent_1713_ = lean_ctor_get_uint8(v_a_1711_, 1);
lean_dec_ref_known(v_a_1711_, 0);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc_ref(v___y_1700_);
lean_inc(v___y_1699_);
v___x_1714_ = lean_apply_12(v___f_1696_, v___x_1709_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, lean_box(0));
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; uint8_t v___y_1717_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
if (v_contextDependent_1713_ == 0)
{
lean_dec(v_a_1715_);
return v___x_1714_;
}
else
{
if (lean_obj_tag(v_a_1715_) == 0)
{
uint8_t v_contextDependent_1727_; 
v_contextDependent_1727_ = lean_ctor_get_uint8(v_a_1715_, 1);
v___y_1717_ = v_contextDependent_1727_;
goto v___jp_1716_;
}
else
{
uint8_t v_contextDependent_1728_; 
v_contextDependent_1728_ = lean_ctor_get_uint8(v_a_1715_, sizeof(void*)*2 + 1);
v___y_1717_ = v_contextDependent_1728_;
goto v___jp_1716_;
}
}
v___jp_1716_:
{
if (v___y_1717_ == 0)
{
lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1725_; 
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v___x_1714_, 0);
lean_dec(v_unused_1726_);
v___x_1719_ = v___x_1714_;
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
else
{
lean_dec(v___x_1714_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1715_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1721_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_dec(v_a_1715_);
return v___x_1714_;
}
}
}
else
{
return v___x_1714_;
}
}
else
{
lean_dec_ref_known(v_a_1711_, 0);
lean_dec_ref(v___y_1698_);
lean_dec_ref(v___f_1696_);
return v___x_1710_;
}
}
else
{
uint8_t v_done_1729_; 
v_done_1729_ = lean_ctor_get_uint8(v_a_1711_, sizeof(void*)*2);
if (v_done_1729_ == 0)
{
lean_object* v_e_x27_1730_; lean_object* v_proof_1731_; uint8_t v_contextDependent_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1782_; 
lean_dec_ref_known(v___x_1710_, 1);
v_e_x27_1730_ = lean_ctor_get(v_a_1711_, 0);
v_proof_1731_ = lean_ctor_get(v_a_1711_, 1);
v_contextDependent_1732_ = lean_ctor_get_uint8(v_a_1711_, sizeof(void*)*2 + 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_a_1711_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1734_ = v_a_1711_;
v_isShared_1735_ = v_isSharedCheck_1782_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_proof_1731_);
lean_inc(v_e_x27_1730_);
lean_dec(v_a_1711_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1782_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; 
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc_ref(v___y_1700_);
lean_inc(v___y_1699_);
lean_inc_ref(v_e_x27_1730_);
v___x_1736_ = lean_apply_12(v___f_1696_, v___x_1709_, v_e_x27_1730_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, lean_box(0));
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1781_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1781_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1781_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
if (lean_obj_tag(v_a_1737_) == 0)
{
uint8_t v_done_1741_; uint8_t v_contextDependent_1742_; uint8_t v___y_1744_; 
lean_dec_ref(v___y_1698_);
v_done_1741_ = lean_ctor_get_uint8(v_a_1737_, 0);
v_contextDependent_1742_ = lean_ctor_get_uint8(v_a_1737_, 1);
lean_dec_ref_known(v_a_1737_, 0);
if (v_contextDependent_1732_ == 0)
{
v___y_1744_ = v_contextDependent_1742_;
goto v___jp_1743_;
}
else
{
v___y_1744_ = v_contextDependent_1732_;
goto v___jp_1743_;
}
v___jp_1743_:
{
lean_object* v___x_1746_; 
if (v_isShared_1735_ == 0)
{
v___x_1746_ = v___x_1734_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_e_x27_1730_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_proof_1731_);
v___x_1746_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1748_; 
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*2, v_done_1741_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*2 + 1, v___y_1744_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1746_);
v___x_1748_ = v___x_1739_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
else
{
lean_object* v_e_x27_1751_; lean_object* v_proof_1752_; uint8_t v_done_1753_; uint8_t v_contextDependent_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1780_; 
lean_del_object(v___x_1739_);
lean_del_object(v___x_1734_);
v_e_x27_1751_ = lean_ctor_get(v_a_1737_, 0);
v_proof_1752_ = lean_ctor_get(v_a_1737_, 1);
v_done_1753_ = lean_ctor_get_uint8(v_a_1737_, sizeof(void*)*2);
v_contextDependent_1754_ = lean_ctor_get_uint8(v_a_1737_, sizeof(void*)*2 + 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_a_1737_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1756_ = v_a_1737_;
v_isShared_1757_ = v_isSharedCheck_1780_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_proof_1752_);
lean_inc(v_e_x27_1751_);
lean_dec(v_a_1737_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1780_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; 
lean_inc_ref(v_e_x27_1751_);
v___x_1758_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1698_, v_e_x27_1730_, v_proof_1731_, v_e_x27_1751_, v_proof_1752_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1771_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1771_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1771_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
uint8_t v___y_1764_; 
if (v_contextDependent_1732_ == 0)
{
v___y_1764_ = v_contextDependent_1754_;
goto v___jp_1763_;
}
else
{
v___y_1764_ = v_contextDependent_1732_;
goto v___jp_1763_;
}
v___jp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v_a_1759_);
v___x_1766_ = v___x_1756_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_e_x27_1751_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_a_1759_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*2, v_done_1753_);
v___x_1766_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1768_; 
lean_ctor_set_uint8(v___x_1766_, sizeof(void*)*2 + 1, v___y_1764_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1766_);
v___x_1768_ = v___x_1761_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_del_object(v___x_1756_);
lean_dec_ref(v_e_x27_1751_);
v_a_1772_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1758_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1758_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1734_);
lean_dec_ref(v_proof_1731_);
lean_dec_ref(v_e_x27_1730_);
lean_dec_ref(v___y_1698_);
return v___x_1736_;
}
}
}
else
{
lean_dec_ref_known(v_a_1711_, 2);
lean_dec_ref(v___y_1698_);
lean_dec_ref(v___f_1696_);
return v___x_1710_;
}
}
}
else
{
lean_dec_ref(v___y_1698_);
lean_dec_ref(v___f_1696_);
return v___x_1710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed(lean_object* v___f_1783_, lean_object* v_x_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__6(v___f_1783_, v_x_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7(lean_object* v___f_1797_, lean_object* v_x_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_box(0);
lean_inc_ref(v___y_1799_);
v___x_1811_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v___y_1799_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
if (lean_obj_tag(v_a_1812_) == 0)
{
uint8_t v_done_1813_; 
v_done_1813_ = lean_ctor_get_uint8(v_a_1812_, 0);
if (v_done_1813_ == 0)
{
uint8_t v_contextDependent_1814_; lean_object* v___x_1815_; 
lean_dec_ref_known(v___x_1811_, 1);
v_contextDependent_1814_ = lean_ctor_get_uint8(v_a_1812_, 1);
lean_dec_ref_known(v_a_1812_, 0);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1806_);
lean_inc_ref(v___y_1805_);
lean_inc(v___y_1804_);
lean_inc_ref(v___y_1803_);
lean_inc(v___y_1802_);
lean_inc_ref(v___y_1801_);
lean_inc(v___y_1800_);
v___x_1815_ = lean_apply_12(v___f_1797_, v___x_1810_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, lean_box(0));
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; uint8_t v___y_1818_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
if (v_contextDependent_1814_ == 0)
{
lean_dec(v_a_1816_);
return v___x_1815_;
}
else
{
if (lean_obj_tag(v_a_1816_) == 0)
{
uint8_t v_contextDependent_1828_; 
v_contextDependent_1828_ = lean_ctor_get_uint8(v_a_1816_, 1);
v___y_1818_ = v_contextDependent_1828_;
goto v___jp_1817_;
}
else
{
uint8_t v_contextDependent_1829_; 
v_contextDependent_1829_ = lean_ctor_get_uint8(v_a_1816_, sizeof(void*)*2 + 1);
v___y_1818_ = v_contextDependent_1829_;
goto v___jp_1817_;
}
}
v___jp_1817_:
{
if (v___y_1818_ == 0)
{
lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1826_; 
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; 
v_unused_1827_ = lean_ctor_get(v___x_1815_, 0);
lean_dec(v_unused_1827_);
v___x_1820_ = v___x_1815_;
v_isShared_1821_ = v_isSharedCheck_1826_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v___x_1815_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1826_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1816_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1822_);
v___x_1824_ = v___x_1820_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
else
{
lean_dec(v_a_1816_);
return v___x_1815_;
}
}
}
else
{
return v___x_1815_;
}
}
else
{
lean_dec_ref_known(v_a_1812_, 0);
lean_dec_ref(v___y_1799_);
lean_dec_ref(v___f_1797_);
return v___x_1811_;
}
}
else
{
uint8_t v_done_1830_; 
v_done_1830_ = lean_ctor_get_uint8(v_a_1812_, sizeof(void*)*2);
if (v_done_1830_ == 0)
{
lean_object* v_e_x27_1831_; lean_object* v_proof_1832_; uint8_t v_contextDependent_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref_known(v___x_1811_, 1);
v_e_x27_1831_ = lean_ctor_get(v_a_1812_, 0);
v_proof_1832_ = lean_ctor_get(v_a_1812_, 1);
v_contextDependent_1833_ = lean_ctor_get_uint8(v_a_1812_, sizeof(void*)*2 + 1);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_a_1812_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1835_ = v_a_1812_;
v_isShared_1836_ = v_isSharedCheck_1883_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_proof_1832_);
lean_inc(v_e_x27_1831_);
lean_dec(v_a_1812_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1883_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; 
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
lean_inc(v___y_1806_);
lean_inc_ref(v___y_1805_);
lean_inc(v___y_1804_);
lean_inc_ref(v___y_1803_);
lean_inc(v___y_1802_);
lean_inc_ref(v___y_1801_);
lean_inc(v___y_1800_);
lean_inc_ref(v_e_x27_1831_);
v___x_1837_ = lean_apply_12(v___f_1797_, v___x_1810_, v_e_x27_1831_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, lean_box(0));
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1882_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1882_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1882_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
if (lean_obj_tag(v_a_1838_) == 0)
{
uint8_t v_done_1842_; uint8_t v_contextDependent_1843_; uint8_t v___y_1845_; 
lean_dec_ref(v___y_1799_);
v_done_1842_ = lean_ctor_get_uint8(v_a_1838_, 0);
v_contextDependent_1843_ = lean_ctor_get_uint8(v_a_1838_, 1);
lean_dec_ref_known(v_a_1838_, 0);
if (v_contextDependent_1833_ == 0)
{
v___y_1845_ = v_contextDependent_1843_;
goto v___jp_1844_;
}
else
{
v___y_1845_ = v_contextDependent_1833_;
goto v___jp_1844_;
}
v___jp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1836_ == 0)
{
v___x_1847_ = v___x_1835_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_e_x27_1831_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_proof_1832_);
v___x_1847_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*2, v_done_1842_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*2 + 1, v___y_1845_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1847_);
v___x_1849_ = v___x_1840_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_e_x27_1852_; lean_object* v_proof_1853_; uint8_t v_done_1854_; uint8_t v_contextDependent_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1881_; 
lean_del_object(v___x_1840_);
lean_del_object(v___x_1835_);
v_e_x27_1852_ = lean_ctor_get(v_a_1838_, 0);
v_proof_1853_ = lean_ctor_get(v_a_1838_, 1);
v_done_1854_ = lean_ctor_get_uint8(v_a_1838_, sizeof(void*)*2);
v_contextDependent_1855_ = lean_ctor_get_uint8(v_a_1838_, sizeof(void*)*2 + 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_a_1838_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1857_ = v_a_1838_;
v_isShared_1858_ = v_isSharedCheck_1881_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_proof_1853_);
lean_inc(v_e_x27_1852_);
lean_dec(v_a_1838_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1881_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; 
lean_inc_ref(v_e_x27_1852_);
v___x_1859_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1799_, v_e_x27_1831_, v_proof_1832_, v_e_x27_1852_, v_proof_1853_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1872_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1872_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1872_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
uint8_t v___y_1865_; 
if (v_contextDependent_1833_ == 0)
{
v___y_1865_ = v_contextDependent_1855_;
goto v___jp_1864_;
}
else
{
v___y_1865_ = v_contextDependent_1833_;
goto v___jp_1864_;
}
v___jp_1864_:
{
lean_object* v___x_1867_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 1, v_a_1860_);
v___x_1867_ = v___x_1857_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_e_x27_1852_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_a_1860_);
lean_ctor_set_uint8(v_reuseFailAlloc_1871_, sizeof(void*)*2, v_done_1854_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*2 + 1, v___y_1865_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1867_);
v___x_1869_ = v___x_1862_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_del_object(v___x_1857_);
lean_dec_ref(v_e_x27_1852_);
v_a_1873_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1859_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1859_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1835_);
lean_dec_ref(v_proof_1832_);
lean_dec_ref(v_e_x27_1831_);
lean_dec_ref(v___y_1799_);
return v___x_1837_;
}
}
}
else
{
lean_dec_ref_known(v_a_1812_, 2);
lean_dec_ref(v___y_1799_);
lean_dec_ref(v___f_1797_);
return v___x_1811_;
}
}
}
else
{
lean_dec_ref(v___y_1799_);
lean_dec_ref(v___f_1797_);
return v___x_1811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7___boxed(lean_object* v___f_1884_, lean_object* v_x_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__7(v___f_1884_, v_x_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8(lean_object* v___f_1898_, lean_object* v_x_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = lean_box(0);
lean_inc_ref(v___y_1900_);
v___x_1912_ = l_Lean_Meta_Grind_NormSym_simpEq(v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
if (lean_obj_tag(v_a_1913_) == 0)
{
uint8_t v_done_1914_; 
v_done_1914_ = lean_ctor_get_uint8(v_a_1913_, 0);
if (v_done_1914_ == 0)
{
uint8_t v_contextDependent_1915_; lean_object* v___x_1916_; 
lean_dec_ref_known(v___x_1912_, 1);
v_contextDependent_1915_ = lean_ctor_get_uint8(v_a_1913_, 1);
lean_dec_ref_known(v_a_1913_, 0);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
lean_inc(v___y_1901_);
v___x_1916_ = lean_apply_12(v___f_1898_, v___x_1911_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, lean_box(0));
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; uint8_t v___y_1919_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
if (v_contextDependent_1915_ == 0)
{
lean_dec(v_a_1917_);
return v___x_1916_;
}
else
{
if (lean_obj_tag(v_a_1917_) == 0)
{
uint8_t v_contextDependent_1929_; 
v_contextDependent_1929_ = lean_ctor_get_uint8(v_a_1917_, 1);
v___y_1919_ = v_contextDependent_1929_;
goto v___jp_1918_;
}
else
{
uint8_t v_contextDependent_1930_; 
v_contextDependent_1930_ = lean_ctor_get_uint8(v_a_1917_, sizeof(void*)*2 + 1);
v___y_1919_ = v_contextDependent_1930_;
goto v___jp_1918_;
}
}
v___jp_1918_:
{
if (v___y_1919_ == 0)
{
lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1927_; 
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v___x_1916_, 0);
lean_dec(v_unused_1928_);
v___x_1921_ = v___x_1916_;
v_isShared_1922_ = v_isSharedCheck_1927_;
goto v_resetjp_1920_;
}
else
{
lean_dec(v___x_1916_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1927_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1917_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1923_);
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
else
{
lean_dec(v_a_1917_);
return v___x_1916_;
}
}
}
else
{
return v___x_1916_;
}
}
else
{
lean_dec_ref_known(v_a_1913_, 0);
lean_dec_ref(v___y_1900_);
lean_dec_ref(v___f_1898_);
return v___x_1912_;
}
}
else
{
uint8_t v_done_1931_; 
v_done_1931_ = lean_ctor_get_uint8(v_a_1913_, sizeof(void*)*2);
if (v_done_1931_ == 0)
{
lean_object* v_e_x27_1932_; lean_object* v_proof_1933_; uint8_t v_contextDependent_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref_known(v___x_1912_, 1);
v_e_x27_1932_ = lean_ctor_get(v_a_1913_, 0);
v_proof_1933_ = lean_ctor_get(v_a_1913_, 1);
v_contextDependent_1934_ = lean_ctor_get_uint8(v_a_1913_, sizeof(void*)*2 + 1);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_a_1913_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1936_ = v_a_1913_;
v_isShared_1937_ = v_isSharedCheck_1984_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_proof_1933_);
lean_inc(v_e_x27_1932_);
lean_dec(v_a_1913_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1984_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; 
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
lean_inc(v___y_1901_);
lean_inc_ref(v_e_x27_1932_);
v___x_1938_ = lean_apply_12(v___f_1898_, v___x_1911_, v_e_x27_1932_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, lean_box(0));
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1983_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1983_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1983_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
if (lean_obj_tag(v_a_1939_) == 0)
{
uint8_t v_done_1943_; uint8_t v_contextDependent_1944_; uint8_t v___y_1946_; 
lean_dec_ref(v___y_1900_);
v_done_1943_ = lean_ctor_get_uint8(v_a_1939_, 0);
v_contextDependent_1944_ = lean_ctor_get_uint8(v_a_1939_, 1);
lean_dec_ref_known(v_a_1939_, 0);
if (v_contextDependent_1934_ == 0)
{
v___y_1946_ = v_contextDependent_1944_;
goto v___jp_1945_;
}
else
{
v___y_1946_ = v_contextDependent_1934_;
goto v___jp_1945_;
}
v___jp_1945_:
{
lean_object* v___x_1948_; 
if (v_isShared_1937_ == 0)
{
v___x_1948_ = v___x_1936_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_e_x27_1932_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_proof_1933_);
v___x_1948_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1950_; 
lean_ctor_set_uint8(v___x_1948_, sizeof(void*)*2, v_done_1943_);
lean_ctor_set_uint8(v___x_1948_, sizeof(void*)*2 + 1, v___y_1946_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1948_);
v___x_1950_ = v___x_1941_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_e_x27_1953_; lean_object* v_proof_1954_; uint8_t v_done_1955_; uint8_t v_contextDependent_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1982_; 
lean_del_object(v___x_1941_);
lean_del_object(v___x_1936_);
v_e_x27_1953_ = lean_ctor_get(v_a_1939_, 0);
v_proof_1954_ = lean_ctor_get(v_a_1939_, 1);
v_done_1955_ = lean_ctor_get_uint8(v_a_1939_, sizeof(void*)*2);
v_contextDependent_1956_ = lean_ctor_get_uint8(v_a_1939_, sizeof(void*)*2 + 1);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_a_1939_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1958_ = v_a_1939_;
v_isShared_1959_ = v_isSharedCheck_1982_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_proof_1954_);
lean_inc(v_e_x27_1953_);
lean_dec(v_a_1939_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1982_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; 
lean_inc_ref(v_e_x27_1953_);
v___x_1960_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1900_, v_e_x27_1932_, v_proof_1933_, v_e_x27_1953_, v_proof_1954_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1973_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1973_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1973_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
uint8_t v___y_1966_; 
if (v_contextDependent_1934_ == 0)
{
v___y_1966_ = v_contextDependent_1956_;
goto v___jp_1965_;
}
else
{
v___y_1966_ = v_contextDependent_1934_;
goto v___jp_1965_;
}
v___jp_1965_:
{
lean_object* v___x_1968_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v_a_1961_);
v___x_1968_ = v___x_1958_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_e_x27_1953_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_a_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1972_, sizeof(void*)*2, v_done_1955_);
v___x_1968_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1970_; 
lean_ctor_set_uint8(v___x_1968_, sizeof(void*)*2 + 1, v___y_1966_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1968_);
v___x_1970_ = v___x_1963_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_del_object(v___x_1958_);
lean_dec_ref(v_e_x27_1953_);
v_a_1974_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1960_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1960_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1936_);
lean_dec_ref(v_proof_1933_);
lean_dec_ref(v_e_x27_1932_);
lean_dec_ref(v___y_1900_);
return v___x_1938_;
}
}
}
else
{
lean_dec_ref_known(v_a_1913_, 2);
lean_dec_ref(v___y_1900_);
lean_dec_ref(v___f_1898_);
return v___x_1912_;
}
}
}
else
{
lean_dec_ref(v___y_1900_);
lean_dec_ref(v___f_1898_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8___boxed(lean_object* v___f_1985_, lean_object* v_x_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__8(v___f_1985_, v_x_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9(lean_object* v___f_1999_, lean_object* v_x_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_box(0);
lean_inc_ref(v___y_2001_);
v___x_2013_ = l_Lean_Meta_Sym_Simp_simpNatRel___redArg(v___y_2001_, v___y_2005_, v___y_2008_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
if (lean_obj_tag(v_a_2014_) == 0)
{
uint8_t v_done_2015_; 
v_done_2015_ = lean_ctor_get_uint8(v_a_2014_, 0);
if (v_done_2015_ == 0)
{
uint8_t v_contextDependent_2016_; lean_object* v___x_2017_; 
lean_dec_ref_known(v___x_2013_, 1);
v_contextDependent_2016_ = lean_ctor_get_uint8(v_a_2014_, 1);
lean_dec_ref_known(v_a_2014_, 0);
lean_inc(v___y_2010_);
lean_inc_ref(v___y_2009_);
lean_inc(v___y_2008_);
lean_inc_ref(v___y_2007_);
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
lean_inc(v___y_2002_);
v___x_2017_ = lean_apply_12(v___f_1999_, v___x_2012_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, lean_box(0));
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; uint8_t v___y_2020_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
if (v_contextDependent_2016_ == 0)
{
lean_dec(v_a_2018_);
return v___x_2017_;
}
else
{
if (lean_obj_tag(v_a_2018_) == 0)
{
uint8_t v_contextDependent_2030_; 
v_contextDependent_2030_ = lean_ctor_get_uint8(v_a_2018_, 1);
v___y_2020_ = v_contextDependent_2030_;
goto v___jp_2019_;
}
else
{
uint8_t v_contextDependent_2031_; 
v_contextDependent_2031_ = lean_ctor_get_uint8(v_a_2018_, sizeof(void*)*2 + 1);
v___y_2020_ = v_contextDependent_2031_;
goto v___jp_2019_;
}
}
v___jp_2019_:
{
if (v___y_2020_ == 0)
{
lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2028_; 
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v___x_2017_, 0);
lean_dec(v_unused_2029_);
v___x_2022_ = v___x_2017_;
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
else
{
lean_dec(v___x_2017_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2018_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_dec(v_a_2018_);
return v___x_2017_;
}
}
}
else
{
return v___x_2017_;
}
}
else
{
lean_dec_ref_known(v_a_2014_, 0);
lean_dec_ref(v___y_2001_);
lean_dec_ref(v___f_1999_);
return v___x_2013_;
}
}
else
{
uint8_t v_done_2032_; 
v_done_2032_ = lean_ctor_get_uint8(v_a_2014_, sizeof(void*)*2);
if (v_done_2032_ == 0)
{
lean_object* v_e_x27_2033_; lean_object* v_proof_2034_; uint8_t v_contextDependent_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref_known(v___x_2013_, 1);
v_e_x27_2033_ = lean_ctor_get(v_a_2014_, 0);
v_proof_2034_ = lean_ctor_get(v_a_2014_, 1);
v_contextDependent_2035_ = lean_ctor_get_uint8(v_a_2014_, sizeof(void*)*2 + 1);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_a_2014_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2037_ = v_a_2014_;
v_isShared_2038_ = v_isSharedCheck_2085_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_proof_2034_);
lean_inc(v_e_x27_2033_);
lean_dec(v_a_2014_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2085_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; 
lean_inc(v___y_2010_);
lean_inc_ref(v___y_2009_);
lean_inc(v___y_2008_);
lean_inc_ref(v___y_2007_);
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
lean_inc(v___y_2002_);
lean_inc_ref(v_e_x27_2033_);
v___x_2039_ = lean_apply_12(v___f_1999_, v___x_2012_, v_e_x27_2033_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, lean_box(0));
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2084_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2084_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2084_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
if (lean_obj_tag(v_a_2040_) == 0)
{
uint8_t v_done_2044_; uint8_t v_contextDependent_2045_; uint8_t v___y_2047_; 
lean_dec_ref(v___y_2001_);
v_done_2044_ = lean_ctor_get_uint8(v_a_2040_, 0);
v_contextDependent_2045_ = lean_ctor_get_uint8(v_a_2040_, 1);
lean_dec_ref_known(v_a_2040_, 0);
if (v_contextDependent_2035_ == 0)
{
v___y_2047_ = v_contextDependent_2045_;
goto v___jp_2046_;
}
else
{
v___y_2047_ = v_contextDependent_2035_;
goto v___jp_2046_;
}
v___jp_2046_:
{
lean_object* v___x_2049_; 
if (v_isShared_2038_ == 0)
{
v___x_2049_ = v___x_2037_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_e_x27_2033_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_proof_2034_);
v___x_2049_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*2, v_done_2044_);
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*2 + 1, v___y_2047_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2049_);
v___x_2051_ = v___x_2042_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_object* v_e_x27_2054_; lean_object* v_proof_2055_; uint8_t v_done_2056_; uint8_t v_contextDependent_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2083_; 
lean_del_object(v___x_2042_);
lean_del_object(v___x_2037_);
v_e_x27_2054_ = lean_ctor_get(v_a_2040_, 0);
v_proof_2055_ = lean_ctor_get(v_a_2040_, 1);
v_done_2056_ = lean_ctor_get_uint8(v_a_2040_, sizeof(void*)*2);
v_contextDependent_2057_ = lean_ctor_get_uint8(v_a_2040_, sizeof(void*)*2 + 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_a_2040_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2059_ = v_a_2040_;
v_isShared_2060_ = v_isSharedCheck_2083_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_proof_2055_);
lean_inc(v_e_x27_2054_);
lean_dec(v_a_2040_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2083_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; 
lean_inc_ref(v_e_x27_2054_);
v___x_2061_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2001_, v_e_x27_2033_, v_proof_2034_, v_e_x27_2054_, v_proof_2055_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2074_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2074_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2074_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
uint8_t v___y_2067_; 
if (v_contextDependent_2035_ == 0)
{
v___y_2067_ = v_contextDependent_2057_;
goto v___jp_2066_;
}
else
{
v___y_2067_ = v_contextDependent_2035_;
goto v___jp_2066_;
}
v___jp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v_a_2062_);
v___x_2069_ = v___x_2059_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_e_x27_2054_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_a_2062_);
lean_ctor_set_uint8(v_reuseFailAlloc_2073_, sizeof(void*)*2, v_done_2056_);
v___x_2069_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*2 + 1, v___y_2067_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2069_);
v___x_2071_ = v___x_2064_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_del_object(v___x_2059_);
lean_dec_ref(v_e_x27_2054_);
v_a_2075_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2061_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2061_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2037_);
lean_dec_ref(v_proof_2034_);
lean_dec_ref(v_e_x27_2033_);
lean_dec_ref(v___y_2001_);
return v___x_2039_;
}
}
}
else
{
lean_dec_ref_known(v_a_2014_, 2);
lean_dec_ref(v___y_2001_);
lean_dec_ref(v___f_1999_);
return v___x_2013_;
}
}
}
else
{
lean_dec_ref(v___y_2001_);
lean_dec_ref(v___f_1999_);
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9___boxed(lean_object* v___f_2086_, lean_object* v_x_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__9(v___f_2086_, v_x_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10(lean_object* v___f_2103_, lean_object* v_x_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__10___closed__0));
v___x_2117_ = lean_box(0);
lean_inc_ref(v___y_2105_);
v___x_2118_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_2105_, v___x_2116_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
if (lean_obj_tag(v_a_2119_) == 0)
{
uint8_t v_done_2120_; 
v_done_2120_ = lean_ctor_get_uint8(v_a_2119_, 0);
if (v_done_2120_ == 0)
{
uint8_t v_contextDependent_2121_; lean_object* v___x_2122_; 
lean_dec_ref_known(v___x_2118_, 1);
v_contextDependent_2121_ = lean_ctor_get_uint8(v_a_2119_, 1);
lean_dec_ref_known(v_a_2119_, 0);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
lean_inc(v___y_2106_);
v___x_2122_ = lean_apply_12(v___f_2103_, v___x_2117_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, lean_box(0));
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; uint8_t v___y_2125_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
if (v_contextDependent_2121_ == 0)
{
lean_dec(v_a_2123_);
return v___x_2122_;
}
else
{
if (lean_obj_tag(v_a_2123_) == 0)
{
uint8_t v_contextDependent_2135_; 
v_contextDependent_2135_ = lean_ctor_get_uint8(v_a_2123_, 1);
v___y_2125_ = v_contextDependent_2135_;
goto v___jp_2124_;
}
else
{
uint8_t v_contextDependent_2136_; 
v_contextDependent_2136_ = lean_ctor_get_uint8(v_a_2123_, sizeof(void*)*2 + 1);
v___y_2125_ = v_contextDependent_2136_;
goto v___jp_2124_;
}
}
v___jp_2124_:
{
if (v___y_2125_ == 0)
{
lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2133_; 
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v___x_2122_, 0);
lean_dec(v_unused_2134_);
v___x_2127_ = v___x_2122_;
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
else
{
lean_dec(v___x_2122_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2123_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2129_);
v___x_2131_ = v___x_2127_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
else
{
lean_dec(v_a_2123_);
return v___x_2122_;
}
}
}
else
{
return v___x_2122_;
}
}
else
{
lean_dec_ref_known(v_a_2119_, 0);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v___f_2103_);
return v___x_2118_;
}
}
else
{
uint8_t v_done_2137_; 
v_done_2137_ = lean_ctor_get_uint8(v_a_2119_, sizeof(void*)*2);
if (v_done_2137_ == 0)
{
lean_object* v_e_x27_2138_; lean_object* v_proof_2139_; uint8_t v_contextDependent_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2190_; 
lean_dec_ref_known(v___x_2118_, 1);
v_e_x27_2138_ = lean_ctor_get(v_a_2119_, 0);
v_proof_2139_ = lean_ctor_get(v_a_2119_, 1);
v_contextDependent_2140_ = lean_ctor_get_uint8(v_a_2119_, sizeof(void*)*2 + 1);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_a_2119_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2142_ = v_a_2119_;
v_isShared_2143_ = v_isSharedCheck_2190_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_proof_2139_);
lean_inc(v_e_x27_2138_);
lean_dec(v_a_2119_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2190_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; 
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
lean_inc(v___y_2106_);
lean_inc_ref(v_e_x27_2138_);
v___x_2144_ = lean_apply_12(v___f_2103_, v___x_2117_, v_e_x27_2138_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, lean_box(0));
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2189_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2189_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2189_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
if (lean_obj_tag(v_a_2145_) == 0)
{
uint8_t v_done_2149_; uint8_t v_contextDependent_2150_; uint8_t v___y_2152_; 
lean_dec_ref(v___y_2105_);
v_done_2149_ = lean_ctor_get_uint8(v_a_2145_, 0);
v_contextDependent_2150_ = lean_ctor_get_uint8(v_a_2145_, 1);
lean_dec_ref_known(v_a_2145_, 0);
if (v_contextDependent_2140_ == 0)
{
v___y_2152_ = v_contextDependent_2150_;
goto v___jp_2151_;
}
else
{
v___y_2152_ = v_contextDependent_2140_;
goto v___jp_2151_;
}
v___jp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2143_ == 0)
{
v___x_2154_ = v___x_2142_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_e_x27_2138_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_proof_2139_);
v___x_2154_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2156_; 
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*2, v_done_2149_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*2 + 1, v___y_2152_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2154_);
v___x_2156_ = v___x_2147_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_e_x27_2159_; lean_object* v_proof_2160_; uint8_t v_done_2161_; uint8_t v_contextDependent_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2188_; 
lean_del_object(v___x_2147_);
lean_del_object(v___x_2142_);
v_e_x27_2159_ = lean_ctor_get(v_a_2145_, 0);
v_proof_2160_ = lean_ctor_get(v_a_2145_, 1);
v_done_2161_ = lean_ctor_get_uint8(v_a_2145_, sizeof(void*)*2);
v_contextDependent_2162_ = lean_ctor_get_uint8(v_a_2145_, sizeof(void*)*2 + 1);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_a_2145_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2164_ = v_a_2145_;
v_isShared_2165_ = v_isSharedCheck_2188_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_proof_2160_);
lean_inc(v_e_x27_2159_);
lean_dec(v_a_2145_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2188_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; 
lean_inc_ref(v_e_x27_2159_);
v___x_2166_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2105_, v_e_x27_2138_, v_proof_2139_, v_e_x27_2159_, v_proof_2160_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2179_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2179_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2179_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
uint8_t v___y_2172_; 
if (v_contextDependent_2140_ == 0)
{
v___y_2172_ = v_contextDependent_2162_;
goto v___jp_2171_;
}
else
{
v___y_2172_ = v_contextDependent_2140_;
goto v___jp_2171_;
}
v___jp_2171_:
{
lean_object* v___x_2174_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v_a_2167_);
v___x_2174_ = v___x_2164_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_e_x27_2159_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_a_2167_);
lean_ctor_set_uint8(v_reuseFailAlloc_2178_, sizeof(void*)*2, v_done_2161_);
v___x_2174_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2176_; 
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*2 + 1, v___y_2172_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2174_);
v___x_2176_ = v___x_2169_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_del_object(v___x_2164_);
lean_dec_ref(v_e_x27_2159_);
v_a_2180_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2166_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2166_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2142_);
lean_dec_ref(v_proof_2139_);
lean_dec_ref(v_e_x27_2138_);
lean_dec_ref(v___y_2105_);
return v___x_2144_;
}
}
}
else
{
lean_dec_ref_known(v_a_2119_, 2);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v___f_2103_);
return v___x_2118_;
}
}
}
else
{
lean_dec_ref(v___y_2105_);
lean_dec_ref(v___f_2103_);
return v___x_2118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10___boxed(lean_object* v___f_2191_, lean_object* v_x_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__10(v___f_2191_, v_x_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11(lean_object* v_thms_2205_, lean_object* v_d_2206_, lean_object* v_x_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_pre_2219_; lean_object* v___x_2220_; 
v_pre_2219_ = lean_ctor_get(v_thms_2205_, 0);
v___x_2220_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_pre_2219_, v_d_2206_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed(lean_object* v_thms_2221_, lean_object* v_d_2222_, lean_object* v_x_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__11(v_thms_2221_, v_d_2222_, v_x_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v_thms_2221_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12(lean_object* v_d_2236_, lean_object* v___f_2237_, lean_object* v_x_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = 1;
v___x_2251_ = lean_box(0);
lean_inc_ref(v___y_2239_);
v___x_2252_ = l_Lean_Meta_Sym_Simp_simpArith(v_d_2236_, v___x_2250_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
if (lean_obj_tag(v_a_2253_) == 0)
{
uint8_t v_done_2254_; 
v_done_2254_ = lean_ctor_get_uint8(v_a_2253_, 0);
if (v_done_2254_ == 0)
{
uint8_t v_contextDependent_2255_; lean_object* v___x_2256_; 
lean_dec_ref_known(v___x_2252_, 1);
v_contextDependent_2255_ = lean_ctor_get_uint8(v_a_2253_, 1);
lean_dec_ref_known(v_a_2253_, 0);
lean_inc(v___y_2248_);
lean_inc_ref(v___y_2247_);
lean_inc(v___y_2246_);
lean_inc_ref(v___y_2245_);
lean_inc(v___y_2244_);
lean_inc_ref(v___y_2243_);
lean_inc(v___y_2242_);
lean_inc_ref(v___y_2241_);
lean_inc(v___y_2240_);
v___x_2256_ = lean_apply_12(v___f_2237_, v___x_2251_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, lean_box(0));
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; uint8_t v___y_2259_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
if (v_contextDependent_2255_ == 0)
{
lean_dec(v_a_2257_);
return v___x_2256_;
}
else
{
if (lean_obj_tag(v_a_2257_) == 0)
{
uint8_t v_contextDependent_2269_; 
v_contextDependent_2269_ = lean_ctor_get_uint8(v_a_2257_, 1);
v___y_2259_ = v_contextDependent_2269_;
goto v___jp_2258_;
}
else
{
uint8_t v_contextDependent_2270_; 
v_contextDependent_2270_ = lean_ctor_get_uint8(v_a_2257_, sizeof(void*)*2 + 1);
v___y_2259_ = v_contextDependent_2270_;
goto v___jp_2258_;
}
}
v___jp_2258_:
{
if (v___y_2259_ == 0)
{
lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2267_; 
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; 
v_unused_2268_ = lean_ctor_get(v___x_2256_, 0);
lean_dec(v_unused_2268_);
v___x_2261_ = v___x_2256_;
v_isShared_2262_ = v_isSharedCheck_2267_;
goto v_resetjp_2260_;
}
else
{
lean_dec(v___x_2256_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2267_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2263_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2257_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___x_2263_);
v___x_2265_ = v___x_2261_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
else
{
lean_dec(v_a_2257_);
return v___x_2256_;
}
}
}
else
{
return v___x_2256_;
}
}
else
{
lean_dec_ref_known(v_a_2253_, 0);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v___f_2237_);
return v___x_2252_;
}
}
else
{
uint8_t v_done_2271_; 
v_done_2271_ = lean_ctor_get_uint8(v_a_2253_, sizeof(void*)*2);
if (v_done_2271_ == 0)
{
lean_object* v_e_x27_2272_; lean_object* v_proof_2273_; uint8_t v_contextDependent_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2324_; 
lean_dec_ref_known(v___x_2252_, 1);
v_e_x27_2272_ = lean_ctor_get(v_a_2253_, 0);
v_proof_2273_ = lean_ctor_get(v_a_2253_, 1);
v_contextDependent_2274_ = lean_ctor_get_uint8(v_a_2253_, sizeof(void*)*2 + 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_a_2253_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2276_ = v_a_2253_;
v_isShared_2277_ = v_isSharedCheck_2324_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_proof_2273_);
lean_inc(v_e_x27_2272_);
lean_dec(v_a_2253_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2324_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; 
lean_inc(v___y_2248_);
lean_inc_ref(v___y_2247_);
lean_inc(v___y_2246_);
lean_inc_ref(v___y_2245_);
lean_inc(v___y_2244_);
lean_inc_ref(v___y_2243_);
lean_inc(v___y_2242_);
lean_inc_ref(v___y_2241_);
lean_inc(v___y_2240_);
lean_inc_ref(v_e_x27_2272_);
v___x_2278_ = lean_apply_12(v___f_2237_, v___x_2251_, v_e_x27_2272_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, lean_box(0));
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2323_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2323_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2323_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
if (lean_obj_tag(v_a_2279_) == 0)
{
uint8_t v_done_2283_; uint8_t v_contextDependent_2284_; uint8_t v___y_2286_; 
lean_dec_ref(v___y_2239_);
v_done_2283_ = lean_ctor_get_uint8(v_a_2279_, 0);
v_contextDependent_2284_ = lean_ctor_get_uint8(v_a_2279_, 1);
lean_dec_ref_known(v_a_2279_, 0);
if (v_contextDependent_2274_ == 0)
{
v___y_2286_ = v_contextDependent_2284_;
goto v___jp_2285_;
}
else
{
v___y_2286_ = v_contextDependent_2274_;
goto v___jp_2285_;
}
v___jp_2285_:
{
lean_object* v___x_2288_; 
if (v_isShared_2277_ == 0)
{
v___x_2288_ = v___x_2276_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_e_x27_2272_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_proof_2273_);
v___x_2288_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*2, v_done_2283_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*2 + 1, v___y_2286_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2288_);
v___x_2290_ = v___x_2281_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
else
{
lean_object* v_e_x27_2293_; lean_object* v_proof_2294_; uint8_t v_done_2295_; uint8_t v_contextDependent_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2322_; 
lean_del_object(v___x_2281_);
lean_del_object(v___x_2276_);
v_e_x27_2293_ = lean_ctor_get(v_a_2279_, 0);
v_proof_2294_ = lean_ctor_get(v_a_2279_, 1);
v_done_2295_ = lean_ctor_get_uint8(v_a_2279_, sizeof(void*)*2);
v_contextDependent_2296_ = lean_ctor_get_uint8(v_a_2279_, sizeof(void*)*2 + 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_a_2279_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2298_ = v_a_2279_;
v_isShared_2299_ = v_isSharedCheck_2322_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_proof_2294_);
lean_inc(v_e_x27_2293_);
lean_dec(v_a_2279_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2322_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; 
lean_inc_ref(v_e_x27_2293_);
v___x_2300_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2239_, v_e_x27_2272_, v_proof_2273_, v_e_x27_2293_, v_proof_2294_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2313_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2313_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2313_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
uint8_t v___y_2306_; 
if (v_contextDependent_2274_ == 0)
{
v___y_2306_ = v_contextDependent_2296_;
goto v___jp_2305_;
}
else
{
v___y_2306_ = v_contextDependent_2274_;
goto v___jp_2305_;
}
v___jp_2305_:
{
lean_object* v___x_2308_; 
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v_a_2301_);
v___x_2308_ = v___x_2298_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_e_x27_2293_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_a_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2312_, sizeof(void*)*2, v_done_2295_);
v___x_2308_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
lean_ctor_set_uint8(v___x_2308_, sizeof(void*)*2 + 1, v___y_2306_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2308_);
v___x_2310_ = v___x_2303_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_del_object(v___x_2298_);
lean_dec_ref(v_e_x27_2293_);
v_a_2314_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2300_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2300_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2276_);
lean_dec_ref(v_proof_2273_);
lean_dec_ref(v_e_x27_2272_);
lean_dec_ref(v___y_2239_);
return v___x_2278_;
}
}
}
else
{
lean_dec_ref_known(v_a_2253_, 2);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v___f_2237_);
return v___x_2252_;
}
}
}
else
{
lean_dec_ref(v___y_2239_);
lean_dec_ref(v___f_2237_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed(lean_object* v_d_2325_, lean_object* v___f_2326_, lean_object* v_x_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__12(v_d_2325_, v___f_2326_, v_x_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13(lean_object* v___f_2340_, lean_object* v_x_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_box(0);
lean_inc_ref(v___y_2342_);
v___x_2354_ = l_Lean_Meta_Grind_NormSym_pushNot(v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
if (lean_obj_tag(v_a_2355_) == 0)
{
uint8_t v_done_2356_; 
v_done_2356_ = lean_ctor_get_uint8(v_a_2355_, 0);
if (v_done_2356_ == 0)
{
uint8_t v_contextDependent_2357_; lean_object* v___x_2358_; 
lean_dec_ref_known(v___x_2354_, 1);
v_contextDependent_2357_ = lean_ctor_get_uint8(v_a_2355_, 1);
lean_dec_ref_known(v_a_2355_, 0);
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___y_2343_);
v___x_2358_ = lean_apply_12(v___f_2340_, v___x_2353_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, lean_box(0));
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; uint8_t v___y_2361_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
if (v_contextDependent_2357_ == 0)
{
lean_dec(v_a_2359_);
return v___x_2358_;
}
else
{
if (lean_obj_tag(v_a_2359_) == 0)
{
uint8_t v_contextDependent_2371_; 
v_contextDependent_2371_ = lean_ctor_get_uint8(v_a_2359_, 1);
v___y_2361_ = v_contextDependent_2371_;
goto v___jp_2360_;
}
else
{
uint8_t v_contextDependent_2372_; 
v_contextDependent_2372_ = lean_ctor_get_uint8(v_a_2359_, sizeof(void*)*2 + 1);
v___y_2361_ = v_contextDependent_2372_;
goto v___jp_2360_;
}
}
v___jp_2360_:
{
if (v___y_2361_ == 0)
{
lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2369_; 
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; 
v_unused_2370_ = lean_ctor_get(v___x_2358_, 0);
lean_dec(v_unused_2370_);
v___x_2363_ = v___x_2358_;
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
else
{
lean_dec(v___x_2358_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2365_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2359_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2365_);
v___x_2367_ = v___x_2363_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
else
{
lean_dec(v_a_2359_);
return v___x_2358_;
}
}
}
else
{
return v___x_2358_;
}
}
else
{
lean_dec_ref_known(v_a_2355_, 0);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___f_2340_);
return v___x_2354_;
}
}
else
{
uint8_t v_done_2373_; 
v_done_2373_ = lean_ctor_get_uint8(v_a_2355_, sizeof(void*)*2);
if (v_done_2373_ == 0)
{
lean_object* v_e_x27_2374_; lean_object* v_proof_2375_; uint8_t v_contextDependent_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2426_; 
lean_dec_ref_known(v___x_2354_, 1);
v_e_x27_2374_ = lean_ctor_get(v_a_2355_, 0);
v_proof_2375_ = lean_ctor_get(v_a_2355_, 1);
v_contextDependent_2376_ = lean_ctor_get_uint8(v_a_2355_, sizeof(void*)*2 + 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_a_2355_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2378_ = v_a_2355_;
v_isShared_2379_ = v_isSharedCheck_2426_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_proof_2375_);
lean_inc(v_e_x27_2374_);
lean_dec(v_a_2355_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2426_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; 
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___y_2343_);
lean_inc_ref(v_e_x27_2374_);
v___x_2380_ = lean_apply_12(v___f_2340_, v___x_2353_, v_e_x27_2374_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, lean_box(0));
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2425_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2383_ = v___x_2380_;
v_isShared_2384_ = v_isSharedCheck_2425_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2380_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2425_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
if (lean_obj_tag(v_a_2381_) == 0)
{
uint8_t v_done_2385_; uint8_t v_contextDependent_2386_; uint8_t v___y_2388_; 
lean_dec_ref(v___y_2342_);
v_done_2385_ = lean_ctor_get_uint8(v_a_2381_, 0);
v_contextDependent_2386_ = lean_ctor_get_uint8(v_a_2381_, 1);
lean_dec_ref_known(v_a_2381_, 0);
if (v_contextDependent_2376_ == 0)
{
v___y_2388_ = v_contextDependent_2386_;
goto v___jp_2387_;
}
else
{
v___y_2388_ = v_contextDependent_2376_;
goto v___jp_2387_;
}
v___jp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2379_ == 0)
{
v___x_2390_ = v___x_2378_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_e_x27_2374_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_proof_2375_);
v___x_2390_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2392_; 
lean_ctor_set_uint8(v___x_2390_, sizeof(void*)*2, v_done_2385_);
lean_ctor_set_uint8(v___x_2390_, sizeof(void*)*2 + 1, v___y_2388_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2390_);
v___x_2392_ = v___x_2383_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
else
{
lean_object* v_e_x27_2395_; lean_object* v_proof_2396_; uint8_t v_done_2397_; uint8_t v_contextDependent_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2424_; 
lean_del_object(v___x_2383_);
lean_del_object(v___x_2378_);
v_e_x27_2395_ = lean_ctor_get(v_a_2381_, 0);
v_proof_2396_ = lean_ctor_get(v_a_2381_, 1);
v_done_2397_ = lean_ctor_get_uint8(v_a_2381_, sizeof(void*)*2);
v_contextDependent_2398_ = lean_ctor_get_uint8(v_a_2381_, sizeof(void*)*2 + 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_a_2381_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2400_ = v_a_2381_;
v_isShared_2401_ = v_isSharedCheck_2424_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_proof_2396_);
lean_inc(v_e_x27_2395_);
lean_dec(v_a_2381_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2424_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; 
lean_inc_ref(v_e_x27_2395_);
v___x_2402_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2342_, v_e_x27_2374_, v_proof_2375_, v_e_x27_2395_, v_proof_2396_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2415_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2415_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2415_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
uint8_t v___y_2408_; 
if (v_contextDependent_2376_ == 0)
{
v___y_2408_ = v_contextDependent_2398_;
goto v___jp_2407_;
}
else
{
v___y_2408_ = v_contextDependent_2376_;
goto v___jp_2407_;
}
v___jp_2407_:
{
lean_object* v___x_2410_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 1, v_a_2403_);
v___x_2410_ = v___x_2400_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_e_x27_2395_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_a_2403_);
lean_ctor_set_uint8(v_reuseFailAlloc_2414_, sizeof(void*)*2, v_done_2397_);
v___x_2410_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2412_; 
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*2 + 1, v___y_2408_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2410_);
v___x_2412_ = v___x_2405_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_del_object(v___x_2400_);
lean_dec_ref(v_e_x27_2395_);
v_a_2416_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2402_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2402_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2378_);
lean_dec_ref(v_proof_2375_);
lean_dec_ref(v_e_x27_2374_);
lean_dec_ref(v___y_2342_);
return v___x_2380_;
}
}
}
else
{
lean_dec_ref_known(v_a_2355_, 2);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___f_2340_);
return v___x_2354_;
}
}
}
else
{
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___f_2340_);
return v___x_2354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed(lean_object* v___f_2427_, lean_object* v_x_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__13(v___f_2427_, v_x_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14(lean_object* v_pre_2441_, lean_object* v___f_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_box(0);
lean_inc(v___y_2452_);
lean_inc_ref(v___y_2451_);
lean_inc(v___y_2450_);
lean_inc_ref(v___y_2449_);
lean_inc(v___y_2448_);
lean_inc_ref(v___y_2447_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
v___x_2455_ = lean_apply_11(v_pre_2441_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, lean_box(0));
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
if (lean_obj_tag(v_a_2456_) == 0)
{
uint8_t v_done_2457_; 
v_done_2457_ = lean_ctor_get_uint8(v_a_2456_, 0);
if (v_done_2457_ == 0)
{
uint8_t v_contextDependent_2458_; lean_object* v___x_2459_; 
lean_dec_ref_known(v___x_2455_, 1);
v_contextDependent_2458_ = lean_ctor_get_uint8(v_a_2456_, 1);
lean_dec_ref_known(v_a_2456_, 0);
v___x_2459_ = lean_apply_12(v___f_2442_, v___x_2454_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, lean_box(0));
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; uint8_t v___y_2462_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
if (v_contextDependent_2458_ == 0)
{
lean_dec(v_a_2460_);
return v___x_2459_;
}
else
{
if (lean_obj_tag(v_a_2460_) == 0)
{
uint8_t v_contextDependent_2472_; 
v_contextDependent_2472_ = lean_ctor_get_uint8(v_a_2460_, 1);
v___y_2462_ = v_contextDependent_2472_;
goto v___jp_2461_;
}
else
{
uint8_t v_contextDependent_2473_; 
v_contextDependent_2473_ = lean_ctor_get_uint8(v_a_2460_, sizeof(void*)*2 + 1);
v___y_2462_ = v_contextDependent_2473_;
goto v___jp_2461_;
}
}
v___jp_2461_:
{
if (v___y_2462_ == 0)
{
lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2470_; 
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v___x_2459_, 0);
lean_dec(v_unused_2471_);
v___x_2464_ = v___x_2459_;
v_isShared_2465_ = v_isSharedCheck_2470_;
goto v_resetjp_2463_;
}
else
{
lean_dec(v___x_2459_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2470_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2466_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2460_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2466_);
v___x_2468_ = v___x_2464_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
else
{
lean_dec(v_a_2460_);
return v___x_2459_;
}
}
}
else
{
return v___x_2459_;
}
}
else
{
lean_dec_ref_known(v_a_2456_, 0);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___f_2442_);
return v___x_2455_;
}
}
else
{
uint8_t v_done_2474_; 
v_done_2474_ = lean_ctor_get_uint8(v_a_2456_, sizeof(void*)*2);
if (v_done_2474_ == 0)
{
lean_object* v_e_x27_2475_; lean_object* v_proof_2476_; uint8_t v_contextDependent_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2527_; 
lean_dec_ref_known(v___x_2455_, 1);
v_e_x27_2475_ = lean_ctor_get(v_a_2456_, 0);
v_proof_2476_ = lean_ctor_get(v_a_2456_, 1);
v_contextDependent_2477_ = lean_ctor_get_uint8(v_a_2456_, sizeof(void*)*2 + 1);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_a_2456_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2479_ = v_a_2456_;
v_isShared_2480_ = v_isSharedCheck_2527_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_proof_2476_);
lean_inc(v_e_x27_2475_);
lean_dec(v_a_2456_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2527_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; 
lean_inc(v___y_2452_);
lean_inc_ref(v___y_2451_);
lean_inc(v___y_2450_);
lean_inc_ref(v___y_2449_);
lean_inc(v___y_2448_);
lean_inc_ref(v___y_2447_);
lean_inc_ref(v_e_x27_2475_);
v___x_2481_ = lean_apply_12(v___f_2442_, v___x_2454_, v_e_x27_2475_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, lean_box(0));
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2526_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2526_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2526_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
if (lean_obj_tag(v_a_2482_) == 0)
{
uint8_t v_done_2486_; uint8_t v_contextDependent_2487_; uint8_t v___y_2489_; 
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___y_2443_);
v_done_2486_ = lean_ctor_get_uint8(v_a_2482_, 0);
v_contextDependent_2487_ = lean_ctor_get_uint8(v_a_2482_, 1);
lean_dec_ref_known(v_a_2482_, 0);
if (v_contextDependent_2477_ == 0)
{
v___y_2489_ = v_contextDependent_2487_;
goto v___jp_2488_;
}
else
{
v___y_2489_ = v_contextDependent_2477_;
goto v___jp_2488_;
}
v___jp_2488_:
{
lean_object* v___x_2491_; 
if (v_isShared_2480_ == 0)
{
v___x_2491_ = v___x_2479_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_e_x27_2475_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_proof_2476_);
v___x_2491_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2493_; 
lean_ctor_set_uint8(v___x_2491_, sizeof(void*)*2, v_done_2486_);
lean_ctor_set_uint8(v___x_2491_, sizeof(void*)*2 + 1, v___y_2489_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v___x_2491_);
v___x_2493_ = v___x_2484_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_object* v_e_x27_2496_; lean_object* v_proof_2497_; uint8_t v_done_2498_; uint8_t v_contextDependent_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2525_; 
lean_del_object(v___x_2484_);
lean_del_object(v___x_2479_);
v_e_x27_2496_ = lean_ctor_get(v_a_2482_, 0);
v_proof_2497_ = lean_ctor_get(v_a_2482_, 1);
v_done_2498_ = lean_ctor_get_uint8(v_a_2482_, sizeof(void*)*2);
v_contextDependent_2499_ = lean_ctor_get_uint8(v_a_2482_, sizeof(void*)*2 + 1);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_a_2482_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2501_ = v_a_2482_;
v_isShared_2502_ = v_isSharedCheck_2525_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_proof_2497_);
lean_inc(v_e_x27_2496_);
lean_dec(v_a_2482_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2525_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; 
lean_inc_ref(v_e_x27_2496_);
v___x_2503_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2443_, v_e_x27_2475_, v_proof_2476_, v_e_x27_2496_, v_proof_2497_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2516_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2516_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2516_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
uint8_t v___y_2509_; 
if (v_contextDependent_2477_ == 0)
{
v___y_2509_ = v_contextDependent_2499_;
goto v___jp_2508_;
}
else
{
v___y_2509_ = v_contextDependent_2477_;
goto v___jp_2508_;
}
v___jp_2508_:
{
lean_object* v___x_2511_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v_a_2504_);
v___x_2511_ = v___x_2501_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_e_x27_2496_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_a_2504_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, sizeof(void*)*2, v_done_2498_);
v___x_2511_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2513_; 
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*2 + 1, v___y_2509_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2511_);
v___x_2513_ = v___x_2506_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_del_object(v___x_2501_);
lean_dec_ref(v_e_x27_2496_);
v_a_2517_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2503_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2503_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2479_);
lean_dec_ref(v_proof_2476_);
lean_dec_ref(v_e_x27_2475_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___y_2443_);
return v___x_2481_;
}
}
}
else
{
lean_dec_ref_known(v_a_2456_, 2);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___f_2442_);
return v___x_2455_;
}
}
}
else
{
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___f_2442_);
return v___x_2455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed(lean_object* v_pre_2528_, lean_object* v___f_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__14(v_pre_2528_, v___f_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15(lean_object* v_post_2542_, lean_object* v_d_2543_, lean_object* v___f_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_box(0);
lean_inc_ref(v___y_2545_);
v___x_2557_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_post_2542_, v_d_2543_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
if (lean_obj_tag(v_a_2558_) == 0)
{
uint8_t v_done_2559_; 
v_done_2559_ = lean_ctor_get_uint8(v_a_2558_, 0);
if (v_done_2559_ == 0)
{
uint8_t v_contextDependent_2560_; lean_object* v___x_2561_; 
lean_dec_ref_known(v___x_2557_, 1);
v_contextDependent_2560_ = lean_ctor_get_uint8(v_a_2558_, 1);
lean_dec_ref_known(v_a_2558_, 0);
v___x_2561_ = lean_apply_12(v___f_2544_, v___x_2556_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, lean_box(0));
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; uint8_t v___y_2564_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
if (v_contextDependent_2560_ == 0)
{
lean_dec(v_a_2562_);
return v___x_2561_;
}
else
{
if (lean_obj_tag(v_a_2562_) == 0)
{
uint8_t v_contextDependent_2574_; 
v_contextDependent_2574_ = lean_ctor_get_uint8(v_a_2562_, 1);
v___y_2564_ = v_contextDependent_2574_;
goto v___jp_2563_;
}
else
{
uint8_t v_contextDependent_2575_; 
v_contextDependent_2575_ = lean_ctor_get_uint8(v_a_2562_, sizeof(void*)*2 + 1);
v___y_2564_ = v_contextDependent_2575_;
goto v___jp_2563_;
}
}
v___jp_2563_:
{
if (v___y_2564_ == 0)
{
lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2572_; 
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2572_ == 0)
{
lean_object* v_unused_2573_; 
v_unused_2573_ = lean_ctor_get(v___x_2561_, 0);
lean_dec(v_unused_2573_);
v___x_2566_ = v___x_2561_;
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
else
{
lean_dec(v___x_2561_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2572_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2568_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2562_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2568_);
v___x_2570_ = v___x_2566_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
else
{
lean_dec(v_a_2562_);
return v___x_2561_;
}
}
}
else
{
return v___x_2561_;
}
}
else
{
lean_dec_ref_known(v_a_2558_, 0);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec_ref(v___f_2544_);
return v___x_2557_;
}
}
else
{
uint8_t v_done_2576_; 
v_done_2576_ = lean_ctor_get_uint8(v_a_2558_, sizeof(void*)*2);
if (v_done_2576_ == 0)
{
lean_object* v_e_x27_2577_; lean_object* v_proof_2578_; uint8_t v_contextDependent_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2629_; 
lean_dec_ref_known(v___x_2557_, 1);
v_e_x27_2577_ = lean_ctor_get(v_a_2558_, 0);
v_proof_2578_ = lean_ctor_get(v_a_2558_, 1);
v_contextDependent_2579_ = lean_ctor_get_uint8(v_a_2558_, sizeof(void*)*2 + 1);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_a_2558_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2581_ = v_a_2558_;
v_isShared_2582_ = v_isSharedCheck_2629_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_proof_2578_);
lean_inc(v_e_x27_2577_);
lean_dec(v_a_2558_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2629_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; 
lean_inc(v___y_2554_);
lean_inc_ref(v___y_2553_);
lean_inc(v___y_2552_);
lean_inc_ref(v___y_2551_);
lean_inc(v___y_2550_);
lean_inc_ref(v___y_2549_);
lean_inc_ref(v_e_x27_2577_);
v___x_2583_ = lean_apply_12(v___f_2544_, v___x_2556_, v_e_x27_2577_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, lean_box(0));
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2628_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2628_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2628_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
if (lean_obj_tag(v_a_2584_) == 0)
{
uint8_t v_done_2588_; uint8_t v_contextDependent_2589_; uint8_t v___y_2591_; 
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec_ref(v___y_2545_);
v_done_2588_ = lean_ctor_get_uint8(v_a_2584_, 0);
v_contextDependent_2589_ = lean_ctor_get_uint8(v_a_2584_, 1);
lean_dec_ref_known(v_a_2584_, 0);
if (v_contextDependent_2579_ == 0)
{
v___y_2591_ = v_contextDependent_2589_;
goto v___jp_2590_;
}
else
{
v___y_2591_ = v_contextDependent_2579_;
goto v___jp_2590_;
}
v___jp_2590_:
{
lean_object* v___x_2593_; 
if (v_isShared_2582_ == 0)
{
v___x_2593_ = v___x_2581_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_e_x27_2577_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_proof_2578_);
v___x_2593_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2595_; 
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*2, v_done_2588_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*2 + 1, v___y_2591_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2593_);
v___x_2595_ = v___x_2586_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
else
{
lean_object* v_e_x27_2598_; lean_object* v_proof_2599_; uint8_t v_done_2600_; uint8_t v_contextDependent_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2627_; 
lean_del_object(v___x_2586_);
lean_del_object(v___x_2581_);
v_e_x27_2598_ = lean_ctor_get(v_a_2584_, 0);
v_proof_2599_ = lean_ctor_get(v_a_2584_, 1);
v_done_2600_ = lean_ctor_get_uint8(v_a_2584_, sizeof(void*)*2);
v_contextDependent_2601_ = lean_ctor_get_uint8(v_a_2584_, sizeof(void*)*2 + 1);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_a_2584_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2603_ = v_a_2584_;
v_isShared_2604_ = v_isSharedCheck_2627_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_proof_2599_);
lean_inc(v_e_x27_2598_);
lean_dec(v_a_2584_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2627_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; 
lean_inc_ref(v_e_x27_2598_);
v___x_2605_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2545_, v_e_x27_2577_, v_proof_2578_, v_e_x27_2598_, v_proof_2599_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2618_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2618_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2618_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
uint8_t v___y_2611_; 
if (v_contextDependent_2579_ == 0)
{
v___y_2611_ = v_contextDependent_2601_;
goto v___jp_2610_;
}
else
{
v___y_2611_ = v_contextDependent_2579_;
goto v___jp_2610_;
}
v___jp_2610_:
{
lean_object* v___x_2613_; 
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 1, v_a_2606_);
v___x_2613_ = v___x_2603_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_e_x27_2598_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_a_2606_);
lean_ctor_set_uint8(v_reuseFailAlloc_2617_, sizeof(void*)*2, v_done_2600_);
v___x_2613_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2615_; 
lean_ctor_set_uint8(v___x_2613_, sizeof(void*)*2 + 1, v___y_2611_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2613_);
v___x_2615_ = v___x_2608_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_del_object(v___x_2603_);
lean_dec_ref(v_e_x27_2598_);
v_a_2619_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2605_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2605_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2581_);
lean_dec_ref(v_proof_2578_);
lean_dec_ref(v_e_x27_2577_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec_ref(v___y_2545_);
return v___x_2583_;
}
}
}
else
{
lean_dec_ref_known(v_a_2558_, 2);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec_ref(v___f_2544_);
return v___x_2557_;
}
}
}
else
{
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec_ref(v___f_2544_);
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed(lean_object* v_post_2630_, lean_object* v_d_2631_, lean_object* v___f_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__15(v_post_2630_, v_d_2631_, v___f_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec_ref(v_post_2630_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16(lean_object* v_pre_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; 
lean_inc(v___y_2655_);
lean_inc_ref(v___y_2654_);
lean_inc(v___y_2653_);
lean_inc_ref(v___y_2652_);
lean_inc(v___y_2651_);
lean_inc_ref(v___y_2650_);
lean_inc_ref(v___y_2646_);
v___x_2657_ = lean_apply_11(v_pre_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, lean_box(0));
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
if (lean_obj_tag(v_a_2658_) == 0)
{
uint8_t v_done_2659_; 
v_done_2659_ = lean_ctor_get_uint8(v_a_2658_, 0);
if (v_done_2659_ == 0)
{
uint8_t v_contextDependent_2660_; lean_object* v___x_2661_; 
lean_dec_ref_known(v___x_2657_, 1);
v_contextDependent_2660_ = lean_ctor_get_uint8(v_a_2658_, 1);
lean_dec_ref_known(v_a_2658_, 0);
v___x_2661_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v___y_2646_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; uint8_t v___y_2664_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
if (v_contextDependent_2660_ == 0)
{
return v___x_2661_;
}
else
{
if (lean_obj_tag(v_a_2662_) == 0)
{
uint8_t v_contextDependent_2674_; 
v_contextDependent_2674_ = lean_ctor_get_uint8(v_a_2662_, 1);
v___y_2664_ = v_contextDependent_2674_;
goto v___jp_2663_;
}
else
{
uint8_t v_contextDependent_2675_; 
v_contextDependent_2675_ = lean_ctor_get_uint8(v_a_2662_, sizeof(void*)*2 + 1);
v___y_2664_ = v_contextDependent_2675_;
goto v___jp_2663_;
}
}
v___jp_2663_:
{
if (v___y_2664_ == 0)
{
lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2672_; 
lean_inc(v_a_2662_);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; 
v_unused_2673_ = lean_ctor_get(v___x_2661_, 0);
lean_dec(v_unused_2673_);
v___x_2666_ = v___x_2661_;
v_isShared_2667_ = v_isSharedCheck_2672_;
goto v_resetjp_2665_;
}
else
{
lean_dec(v___x_2661_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2672_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2668_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2662_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2668_);
v___x_2670_ = v___x_2666_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
else
{
return v___x_2661_;
}
}
}
else
{
return v___x_2661_;
}
}
else
{
lean_dec_ref_known(v_a_2658_, 0);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___y_2646_);
return v___x_2657_;
}
}
else
{
uint8_t v_done_2676_; 
v_done_2676_ = lean_ctor_get_uint8(v_a_2658_, sizeof(void*)*2);
if (v_done_2676_ == 0)
{
lean_object* v_e_x27_2677_; lean_object* v_proof_2678_; uint8_t v_contextDependent_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2729_; 
lean_dec_ref_known(v___x_2657_, 1);
v_e_x27_2677_ = lean_ctor_get(v_a_2658_, 0);
v_proof_2678_ = lean_ctor_get(v_a_2658_, 1);
v_contextDependent_2679_ = lean_ctor_get_uint8(v_a_2658_, sizeof(void*)*2 + 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_a_2658_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2681_ = v_a_2658_;
v_isShared_2682_ = v_isSharedCheck_2729_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_proof_2678_);
lean_inc(v_e_x27_2677_);
lean_dec(v_a_2658_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2729_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; 
lean_inc_ref(v_e_x27_2677_);
v___x_2683_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v_e_x27_2677_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2728_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2728_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2728_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
if (lean_obj_tag(v_a_2684_) == 0)
{
uint8_t v_done_2688_; uint8_t v_contextDependent_2689_; uint8_t v___y_2691_; 
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___y_2646_);
v_done_2688_ = lean_ctor_get_uint8(v_a_2684_, 0);
v_contextDependent_2689_ = lean_ctor_get_uint8(v_a_2684_, 1);
lean_dec_ref_known(v_a_2684_, 0);
if (v_contextDependent_2679_ == 0)
{
v___y_2691_ = v_contextDependent_2689_;
goto v___jp_2690_;
}
else
{
v___y_2691_ = v_contextDependent_2679_;
goto v___jp_2690_;
}
v___jp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2682_ == 0)
{
v___x_2693_ = v___x_2681_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_e_x27_2677_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_proof_2678_);
v___x_2693_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2695_; 
lean_ctor_set_uint8(v___x_2693_, sizeof(void*)*2, v_done_2688_);
lean_ctor_set_uint8(v___x_2693_, sizeof(void*)*2 + 1, v___y_2691_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2693_);
v___x_2695_ = v___x_2686_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
lean_object* v_e_x27_2698_; lean_object* v_proof_2699_; uint8_t v_done_2700_; uint8_t v_contextDependent_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2727_; 
lean_del_object(v___x_2686_);
lean_del_object(v___x_2681_);
v_e_x27_2698_ = lean_ctor_get(v_a_2684_, 0);
v_proof_2699_ = lean_ctor_get(v_a_2684_, 1);
v_done_2700_ = lean_ctor_get_uint8(v_a_2684_, sizeof(void*)*2);
v_contextDependent_2701_ = lean_ctor_get_uint8(v_a_2684_, sizeof(void*)*2 + 1);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_a_2684_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2703_ = v_a_2684_;
v_isShared_2704_ = v_isSharedCheck_2727_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_proof_2699_);
lean_inc(v_e_x27_2698_);
lean_dec(v_a_2684_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2727_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; 
lean_inc_ref(v_e_x27_2698_);
v___x_2705_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2646_, v_e_x27_2677_, v_proof_2678_, v_e_x27_2698_, v_proof_2699_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2718_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2708_ = v___x_2705_;
v_isShared_2709_ = v_isSharedCheck_2718_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2718_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
uint8_t v___y_2711_; 
if (v_contextDependent_2679_ == 0)
{
v___y_2711_ = v_contextDependent_2701_;
goto v___jp_2710_;
}
else
{
v___y_2711_ = v_contextDependent_2679_;
goto v___jp_2710_;
}
v___jp_2710_:
{
lean_object* v___x_2713_; 
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 1, v_a_2706_);
v___x_2713_ = v___x_2703_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_e_x27_2698_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_a_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2717_, sizeof(void*)*2, v_done_2700_);
v___x_2713_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_object* v___x_2715_; 
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*2 + 1, v___y_2711_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v___x_2713_);
v___x_2715_ = v___x_2708_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_del_object(v___x_2703_);
lean_dec_ref(v_e_x27_2698_);
v_a_2719_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2705_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2705_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2681_);
lean_dec_ref(v_proof_2678_);
lean_dec_ref(v_e_x27_2677_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___y_2646_);
return v___x_2683_;
}
}
}
else
{
lean_dec_ref_known(v_a_2658_, 2);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___y_2646_);
return v___x_2657_;
}
}
}
else
{
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___y_2646_);
return v___x_2657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed(lean_object* v_pre_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__16(v_pre_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17(lean_object* v___f_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_box(0);
lean_inc_ref(v___y_2744_);
v___x_2756_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_2744_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
if (lean_obj_tag(v_a_2757_) == 0)
{
uint8_t v_done_2758_; 
v_done_2758_ = lean_ctor_get_uint8(v_a_2757_, 0);
if (v_done_2758_ == 0)
{
uint8_t v_contextDependent_2759_; lean_object* v___x_2760_; 
lean_dec_ref_known(v___x_2756_, 1);
v_contextDependent_2759_ = lean_ctor_get_uint8(v_a_2757_, 1);
lean_dec_ref_known(v_a_2757_, 0);
v___x_2760_ = lean_apply_12(v___f_2743_, v___x_2755_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, lean_box(0));
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; uint8_t v___y_2763_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
if (v_contextDependent_2759_ == 0)
{
lean_dec(v_a_2761_);
return v___x_2760_;
}
else
{
if (lean_obj_tag(v_a_2761_) == 0)
{
uint8_t v_contextDependent_2773_; 
v_contextDependent_2773_ = lean_ctor_get_uint8(v_a_2761_, 1);
v___y_2763_ = v_contextDependent_2773_;
goto v___jp_2762_;
}
else
{
uint8_t v_contextDependent_2774_; 
v_contextDependent_2774_ = lean_ctor_get_uint8(v_a_2761_, sizeof(void*)*2 + 1);
v___y_2763_ = v_contextDependent_2774_;
goto v___jp_2762_;
}
}
v___jp_2762_:
{
if (v___y_2763_ == 0)
{
lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2771_; 
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2771_ == 0)
{
lean_object* v_unused_2772_; 
v_unused_2772_ = lean_ctor_get(v___x_2760_, 0);
lean_dec(v_unused_2772_);
v___x_2765_ = v___x_2760_;
v_isShared_2766_ = v_isSharedCheck_2771_;
goto v_resetjp_2764_;
}
else
{
lean_dec(v___x_2760_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2771_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v___x_2769_; 
v___x_2767_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2761_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v___x_2767_);
v___x_2769_ = v___x_2765_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
else
{
lean_dec(v_a_2761_);
return v___x_2760_;
}
}
}
else
{
return v___x_2760_;
}
}
else
{
lean_dec_ref_known(v_a_2757_, 0);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v___f_2743_);
return v___x_2756_;
}
}
else
{
uint8_t v_done_2775_; 
v_done_2775_ = lean_ctor_get_uint8(v_a_2757_, sizeof(void*)*2);
if (v_done_2775_ == 0)
{
lean_object* v_e_x27_2776_; lean_object* v_proof_2777_; uint8_t v_contextDependent_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2828_; 
lean_dec_ref_known(v___x_2756_, 1);
v_e_x27_2776_ = lean_ctor_get(v_a_2757_, 0);
v_proof_2777_ = lean_ctor_get(v_a_2757_, 1);
v_contextDependent_2778_ = lean_ctor_get_uint8(v_a_2757_, sizeof(void*)*2 + 1);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_a_2757_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2780_ = v_a_2757_;
v_isShared_2781_ = v_isSharedCheck_2828_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_proof_2777_);
lean_inc(v_e_x27_2776_);
lean_dec(v_a_2757_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2828_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; 
lean_inc(v___y_2753_);
lean_inc_ref(v___y_2752_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___y_2749_);
lean_inc_ref(v___y_2748_);
lean_inc_ref(v_e_x27_2776_);
v___x_2782_ = lean_apply_12(v___f_2743_, v___x_2755_, v_e_x27_2776_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, lean_box(0));
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2827_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2827_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2827_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
if (lean_obj_tag(v_a_2783_) == 0)
{
uint8_t v_done_2787_; uint8_t v_contextDependent_2788_; uint8_t v___y_2790_; 
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2744_);
v_done_2787_ = lean_ctor_get_uint8(v_a_2783_, 0);
v_contextDependent_2788_ = lean_ctor_get_uint8(v_a_2783_, 1);
lean_dec_ref_known(v_a_2783_, 0);
if (v_contextDependent_2778_ == 0)
{
v___y_2790_ = v_contextDependent_2788_;
goto v___jp_2789_;
}
else
{
v___y_2790_ = v_contextDependent_2778_;
goto v___jp_2789_;
}
v___jp_2789_:
{
lean_object* v___x_2792_; 
if (v_isShared_2781_ == 0)
{
v___x_2792_ = v___x_2780_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_e_x27_2776_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_proof_2777_);
v___x_2792_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2794_; 
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*2, v_done_2787_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*2 + 1, v___y_2790_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2792_);
v___x_2794_ = v___x_2785_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
else
{
lean_object* v_e_x27_2797_; lean_object* v_proof_2798_; uint8_t v_done_2799_; uint8_t v_contextDependent_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2826_; 
lean_del_object(v___x_2785_);
lean_del_object(v___x_2780_);
v_e_x27_2797_ = lean_ctor_get(v_a_2783_, 0);
v_proof_2798_ = lean_ctor_get(v_a_2783_, 1);
v_done_2799_ = lean_ctor_get_uint8(v_a_2783_, sizeof(void*)*2);
v_contextDependent_2800_ = lean_ctor_get_uint8(v_a_2783_, sizeof(void*)*2 + 1);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_a_2783_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2802_ = v_a_2783_;
v_isShared_2803_ = v_isSharedCheck_2826_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_proof_2798_);
lean_inc(v_e_x27_2797_);
lean_dec(v_a_2783_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2826_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; 
lean_inc_ref(v_e_x27_2797_);
v___x_2804_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2744_, v_e_x27_2776_, v_proof_2777_, v_e_x27_2797_, v_proof_2798_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2817_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2807_ = v___x_2804_;
v_isShared_2808_ = v_isSharedCheck_2817_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2804_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2817_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
uint8_t v___y_2810_; 
if (v_contextDependent_2778_ == 0)
{
v___y_2810_ = v_contextDependent_2800_;
goto v___jp_2809_;
}
else
{
v___y_2810_ = v_contextDependent_2778_;
goto v___jp_2809_;
}
v___jp_2809_:
{
lean_object* v___x_2812_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 1, v_a_2805_);
v___x_2812_ = v___x_2802_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_e_x27_2797_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_a_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2816_, sizeof(void*)*2, v_done_2799_);
v___x_2812_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2814_; 
lean_ctor_set_uint8(v___x_2812_, sizeof(void*)*2 + 1, v___y_2810_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2812_);
v___x_2814_ = v___x_2807_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_del_object(v___x_2802_);
lean_dec_ref(v_e_x27_2797_);
v_a_2818_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2804_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2804_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2780_);
lean_dec_ref(v_proof_2777_);
lean_dec_ref(v_e_x27_2776_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v___y_2744_);
return v___x_2782_;
}
}
}
else
{
lean_dec_ref_known(v_a_2757_, 2);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v___f_2743_);
return v___x_2756_;
}
}
}
else
{
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v___f_2743_);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed(lean_object* v___f_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__17(v___f_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18(lean_object* v___f_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v___y_2855_; lean_object* v___y_2856_; uint8_t v___y_2857_; uint8_t v___y_2858_; lean_object* v___y_2862_; uint8_t v___y_2863_; lean_object* v___y_2864_; uint8_t v___y_2865_; lean_object* v___y_2869_; lean_object* v_e_x27_2870_; lean_object* v_proof_2871_; uint8_t v_done_2872_; uint8_t v_contextDependent_2873_; lean_object* v___y_2895_; lean_object* v___y_2896_; uint8_t v___y_2897_; lean_object* v___y_2901_; lean_object* v_a_2902_; lean_object* v___y_2914_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_box(0);
lean_inc_ref(v___y_2843_);
v___x_2917_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_2843_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
if (lean_obj_tag(v_a_2918_) == 0)
{
uint8_t v_done_2919_; 
v_done_2919_ = lean_ctor_get_uint8(v_a_2918_, 0);
if (v_done_2919_ == 0)
{
uint8_t v_contextDependent_2920_; lean_object* v___x_2921_; 
lean_dec_ref_known(v___x_2917_, 1);
v_contextDependent_2920_ = lean_ctor_get_uint8(v_a_2918_, 1);
lean_dec_ref_known(v_a_2918_, 0);
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
lean_inc_ref(v___y_2843_);
v___x_2921_ = lean_apply_12(v___f_2842_, v___x_2916_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, lean_box(0));
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; uint8_t v___y_2924_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
if (v_contextDependent_2920_ == 0)
{
v___y_2901_ = v___x_2921_;
v_a_2902_ = v_a_2922_;
goto v___jp_2900_;
}
else
{
if (lean_obj_tag(v_a_2922_) == 0)
{
uint8_t v_contextDependent_2934_; 
v_contextDependent_2934_ = lean_ctor_get_uint8(v_a_2922_, 1);
v___y_2924_ = v_contextDependent_2934_;
goto v___jp_2923_;
}
else
{
uint8_t v_contextDependent_2935_; 
v_contextDependent_2935_ = lean_ctor_get_uint8(v_a_2922_, sizeof(void*)*2 + 1);
v___y_2924_ = v_contextDependent_2935_;
goto v___jp_2923_;
}
}
v___jp_2923_:
{
if (v___y_2924_ == 0)
{
lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2932_; 
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v___x_2921_, 0);
lean_dec(v_unused_2933_);
v___x_2926_ = v___x_2921_;
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
else
{
lean_dec(v___x_2921_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2932_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2928_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2922_);
lean_inc_ref(v___x_2928_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2928_);
v___x_2930_ = v___x_2926_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
v___y_2901_ = v___x_2930_;
v_a_2902_ = v___x_2928_;
goto v___jp_2900_;
}
}
}
else
{
v___y_2901_ = v___x_2921_;
v_a_2902_ = v_a_2922_;
goto v___jp_2900_;
}
}
}
else
{
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v___y_2843_);
return v___x_2921_;
}
}
else
{
lean_dec_ref_known(v_a_2918_, 0);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___f_2842_);
v___y_2914_ = v___x_2917_;
goto v___jp_2913_;
}
}
else
{
uint8_t v_done_2936_; 
v_done_2936_ = lean_ctor_get_uint8(v_a_2918_, sizeof(void*)*2);
if (v_done_2936_ == 0)
{
lean_object* v_e_x27_2937_; lean_object* v_proof_2938_; uint8_t v_contextDependent_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2989_; 
lean_dec_ref_known(v___x_2917_, 1);
v_e_x27_2937_ = lean_ctor_get(v_a_2918_, 0);
v_proof_2938_ = lean_ctor_get(v_a_2918_, 1);
v_contextDependent_2939_ = lean_ctor_get_uint8(v_a_2918_, sizeof(void*)*2 + 1);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_a_2918_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2941_ = v_a_2918_;
v_isShared_2942_ = v_isSharedCheck_2989_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_proof_2938_);
lean_inc(v_e_x27_2937_);
lean_dec(v_a_2918_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2989_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; 
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
lean_inc_ref(v_e_x27_2937_);
v___x_2943_ = lean_apply_12(v___f_2842_, v___x_2916_, v_e_x27_2937_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, lean_box(0));
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2988_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_2988_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2988_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
if (lean_obj_tag(v_a_2944_) == 0)
{
uint8_t v_done_2948_; uint8_t v_contextDependent_2949_; uint8_t v___y_2951_; 
v_done_2948_ = lean_ctor_get_uint8(v_a_2944_, 0);
v_contextDependent_2949_ = lean_ctor_get_uint8(v_a_2944_, 1);
lean_dec_ref_known(v_a_2944_, 0);
if (v_contextDependent_2939_ == 0)
{
v___y_2951_ = v_contextDependent_2949_;
goto v___jp_2950_;
}
else
{
v___y_2951_ = v_contextDependent_2939_;
goto v___jp_2950_;
}
v___jp_2950_:
{
lean_object* v___x_2953_; 
lean_inc_ref(v_proof_2938_);
lean_inc_ref(v_e_x27_2937_);
if (v_isShared_2942_ == 0)
{
v___x_2953_ = v___x_2941_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_e_x27_2937_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_proof_2938_);
v___x_2953_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2955_; 
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*2, v_done_2948_);
lean_ctor_set_uint8(v___x_2953_, sizeof(void*)*2 + 1, v___y_2951_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2953_);
v___x_2955_ = v___x_2946_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
v___y_2869_ = v___x_2955_;
v_e_x27_2870_ = v_e_x27_2937_;
v_proof_2871_ = v_proof_2938_;
v_done_2872_ = v_done_2948_;
v_contextDependent_2873_ = v___y_2951_;
goto v___jp_2868_;
}
}
}
}
else
{
lean_object* v_e_x27_2958_; lean_object* v_proof_2959_; uint8_t v_done_2960_; uint8_t v_contextDependent_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2987_; 
lean_del_object(v___x_2946_);
lean_del_object(v___x_2941_);
v_e_x27_2958_ = lean_ctor_get(v_a_2944_, 0);
v_proof_2959_ = lean_ctor_get(v_a_2944_, 1);
v_done_2960_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*2);
v_contextDependent_2961_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*2 + 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_a_2944_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2963_ = v_a_2944_;
v_isShared_2964_ = v_isSharedCheck_2987_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_proof_2959_);
lean_inc(v_e_x27_2958_);
lean_dec(v_a_2944_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2987_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; 
lean_inc_ref(v_e_x27_2958_);
lean_inc_ref(v___y_2843_);
v___x_2965_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2843_, v_e_x27_2937_, v_proof_2938_, v_e_x27_2958_, v_proof_2959_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2978_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_2978_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2978_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
uint8_t v___y_2971_; 
if (v_contextDependent_2939_ == 0)
{
v___y_2971_ = v_contextDependent_2961_;
goto v___jp_2970_;
}
else
{
v___y_2971_ = v_contextDependent_2939_;
goto v___jp_2970_;
}
v___jp_2970_:
{
lean_object* v___x_2973_; 
lean_inc(v_a_2966_);
lean_inc_ref(v_e_x27_2958_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v_a_2966_);
v___x_2973_ = v___x_2963_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_e_x27_2958_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_a_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_2977_, sizeof(void*)*2, v_done_2960_);
v___x_2973_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2975_; 
lean_ctor_set_uint8(v___x_2973_, sizeof(void*)*2 + 1, v___y_2971_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2973_);
v___x_2975_ = v___x_2968_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
v___y_2869_ = v___x_2975_;
v_e_x27_2870_ = v_e_x27_2958_;
v_proof_2871_ = v_a_2966_;
v_done_2872_ = v_done_2960_;
v_contextDependent_2873_ = v___y_2971_;
goto v___jp_2868_;
}
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_del_object(v___x_2963_);
lean_dec_ref(v_e_x27_2958_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v___y_2843_);
v_a_2979_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2965_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2965_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2941_);
lean_dec_ref(v_proof_2938_);
lean_dec_ref(v_e_x27_2937_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v___y_2843_);
return v___x_2943_;
}
}
}
else
{
lean_dec_ref_known(v_a_2918_, 2);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___f_2842_);
v___y_2914_ = v___x_2917_;
goto v___jp_2913_;
}
}
}
else
{
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___f_2842_);
v___y_2914_ = v___x_2917_;
goto v___jp_2913_;
}
v___jp_2854_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2859_, 0, v___y_2856_);
lean_ctor_set(v___x_2859_, 1, v___y_2855_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*2, v___y_2857_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*2 + 1, v___y_2858_);
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
return v___x_2860_;
}
v___jp_2861_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2866_, 0, v___y_2862_);
lean_ctor_set(v___x_2866_, 1, v___y_2864_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*2, v___y_2863_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*2 + 1, v___y_2865_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
return v___x_2867_;
}
v___jp_2868_:
{
if (v_done_2872_ == 0)
{
lean_object* v___x_2874_; 
lean_dec_ref(v___y_2869_);
lean_inc_ref(v_e_x27_2870_);
v___x_2874_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v_e_x27_2870_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
if (lean_obj_tag(v_a_2875_) == 0)
{
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v___y_2843_);
if (v_contextDependent_2873_ == 0)
{
uint8_t v_done_2876_; uint8_t v_contextDependent_2877_; 
v_done_2876_ = lean_ctor_get_uint8(v_a_2875_, 0);
v_contextDependent_2877_ = lean_ctor_get_uint8(v_a_2875_, 1);
lean_dec_ref_known(v_a_2875_, 0);
v___y_2855_ = v_proof_2871_;
v___y_2856_ = v_e_x27_2870_;
v___y_2857_ = v_done_2876_;
v___y_2858_ = v_contextDependent_2877_;
goto v___jp_2854_;
}
else
{
uint8_t v_done_2878_; 
v_done_2878_ = lean_ctor_get_uint8(v_a_2875_, 0);
lean_dec_ref_known(v_a_2875_, 0);
v___y_2855_ = v_proof_2871_;
v___y_2856_ = v_e_x27_2870_;
v___y_2857_ = v_done_2878_;
v___y_2858_ = v_contextDependent_2873_;
goto v___jp_2854_;
}
}
else
{
lean_object* v_e_x27_2879_; lean_object* v_proof_2880_; uint8_t v_done_2881_; uint8_t v_contextDependent_2882_; lean_object* v___x_2883_; 
v_e_x27_2879_ = lean_ctor_get(v_a_2875_, 0);
lean_inc_ref_n(v_e_x27_2879_, 2);
v_proof_2880_ = lean_ctor_get(v_a_2875_, 1);
lean_inc_ref(v_proof_2880_);
v_done_2881_ = lean_ctor_get_uint8(v_a_2875_, sizeof(void*)*2);
v_contextDependent_2882_ = lean_ctor_get_uint8(v_a_2875_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2875_, 2);
v___x_2883_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2843_, v_e_x27_2870_, v_proof_2871_, v_e_x27_2879_, v_proof_2880_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
if (lean_obj_tag(v___x_2883_) == 0)
{
if (v_contextDependent_2873_ == 0)
{
lean_object* v_a_2884_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___y_2862_ = v_e_x27_2879_;
v___y_2863_ = v_done_2881_;
v___y_2864_ = v_a_2884_;
v___y_2865_ = v_contextDependent_2882_;
goto v___jp_2861_;
}
else
{
lean_object* v_a_2885_; 
v_a_2885_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2883_, 1);
v___y_2862_ = v_e_x27_2879_;
v___y_2863_ = v_done_2881_;
v___y_2864_ = v_a_2885_;
v___y_2865_ = v_contextDependent_2873_;
goto v___jp_2861_;
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec_ref(v_e_x27_2879_);
v_a_2886_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2883_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2883_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_2871_);
lean_dec_ref(v_e_x27_2870_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v___y_2843_);
return v___x_2874_;
}
}
else
{
lean_dec_ref(v_proof_2871_);
lean_dec_ref(v_e_x27_2870_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v___y_2843_);
return v___y_2869_;
}
}
v___jp_2894_:
{
if (v___y_2897_ == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_dec_ref(v___y_2896_);
v___x_2898_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_2895_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
else
{
lean_dec_ref(v___y_2895_);
return v___y_2896_;
}
}
v___jp_2900_:
{
if (lean_obj_tag(v_a_2902_) == 0)
{
uint8_t v_done_2903_; 
v_done_2903_ = lean_ctor_get_uint8(v_a_2902_, 0);
if (v_done_2903_ == 0)
{
uint8_t v_contextDependent_2904_; lean_object* v___x_2905_; 
lean_dec_ref(v___y_2901_);
v_contextDependent_2904_ = lean_ctor_get_uint8(v_a_2902_, 1);
lean_dec_ref_known(v_a_2902_, 0);
v___x_2905_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v___y_2843_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
if (lean_obj_tag(v___x_2905_) == 0)
{
if (v_contextDependent_2904_ == 0)
{
return v___x_2905_;
}
else
{
lean_object* v_a_2906_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
if (lean_obj_tag(v_a_2906_) == 0)
{
uint8_t v_contextDependent_2907_; 
v_contextDependent_2907_ = lean_ctor_get_uint8(v_a_2906_, 1);
v___y_2895_ = v_a_2906_;
v___y_2896_ = v___x_2905_;
v___y_2897_ = v_contextDependent_2907_;
goto v___jp_2894_;
}
else
{
uint8_t v_contextDependent_2908_; 
v_contextDependent_2908_ = lean_ctor_get_uint8(v_a_2906_, sizeof(void*)*2 + 1);
v___y_2895_ = v_a_2906_;
v___y_2896_ = v___x_2905_;
v___y_2897_ = v_contextDependent_2908_;
goto v___jp_2894_;
}
}
}
else
{
return v___x_2905_;
}
}
else
{
lean_dec_ref_known(v_a_2902_, 0);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v___y_2843_);
return v___y_2901_;
}
}
else
{
lean_object* v_e_x27_2909_; lean_object* v_proof_2910_; uint8_t v_done_2911_; uint8_t v_contextDependent_2912_; 
v_e_x27_2909_ = lean_ctor_get(v_a_2902_, 0);
lean_inc_ref(v_e_x27_2909_);
v_proof_2910_ = lean_ctor_get(v_a_2902_, 1);
lean_inc_ref(v_proof_2910_);
v_done_2911_ = lean_ctor_get_uint8(v_a_2902_, sizeof(void*)*2);
v_contextDependent_2912_ = lean_ctor_get_uint8(v_a_2902_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2902_, 2);
v___y_2869_ = v___y_2901_;
v_e_x27_2870_ = v_e_x27_2909_;
v_proof_2871_ = v_proof_2910_;
v_done_2872_ = v_done_2911_;
v_contextDependent_2873_ = v_contextDependent_2912_;
goto v___jp_2868_;
}
}
v___jp_2913_:
{
if (lean_obj_tag(v___y_2914_) == 0)
{
lean_object* v_a_2915_; 
v_a_2915_ = lean_ctor_get(v___y_2914_, 0);
lean_inc(v_a_2915_);
v___y_2901_ = v___y_2914_;
v_a_2902_ = v_a_2915_;
goto v___jp_2900_;
}
else
{
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v___y_2843_);
return v___y_2914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18___boxed(lean_object* v___f_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__18(v___f_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object* v_config_3028_, lean_object* v_thms_3029_){
_start:
{
uint8_t v_zetaDelta_3030_; uint8_t v_zeta_3031_; lean_object* v___f_3032_; lean_object* v_d_3033_; lean_object* v___f_3034_; lean_object* v___f_3035_; lean_object* v___f_3036_; lean_object* v_pre_3038_; lean_object* v_pre_3044_; 
v_zetaDelta_3030_ = lean_ctor_get_uint8(v_config_3028_, sizeof(void*)*14 + 19);
v_zeta_3031_ = lean_ctor_get_uint8(v_config_3028_, sizeof(void*)*14 + 20);
v___f_3032_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__10));
v_d_3033_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__11));
lean_inc_ref(v_thms_3029_);
v___f_3034_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed), 14, 2);
lean_closure_set(v___f_3034_, 0, v_thms_3029_);
lean_closure_set(v___f_3034_, 1, v_d_3033_);
v___f_3035_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed), 14, 2);
lean_closure_set(v___f_3035_, 0, v_d_3033_);
lean_closure_set(v___f_3035_, 1, v___f_3034_);
v___f_3036_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed), 13, 1);
lean_closure_set(v___f_3036_, 0, v___f_3035_);
if (v_zeta_3031_ == 0)
{
lean_object* v_pre_3046_; 
v_pre_3046_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__12));
v_pre_3044_ = v_pre_3046_;
goto v___jp_3043_;
}
else
{
lean_object* v_pre_3047_; 
v_pre_3047_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__13));
v_pre_3044_ = v_pre_3047_;
goto v___jp_3043_;
}
v___jp_3037_:
{
lean_object* v_post_3039_; lean_object* v_pre_3040_; lean_object* v_post_3041_; lean_object* v___x_3042_; 
v_post_3039_ = lean_ctor_get(v_thms_3029_, 1);
lean_inc_ref(v_post_3039_);
lean_dec_ref(v_thms_3029_);
v_pre_3040_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed), 13, 2);
lean_closure_set(v_pre_3040_, 0, v_pre_3038_);
lean_closure_set(v_pre_3040_, 1, v___f_3036_);
v_post_3041_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed), 14, 3);
lean_closure_set(v_post_3041_, 0, v_post_3039_);
lean_closure_set(v_post_3041_, 1, v_d_3033_);
lean_closure_set(v_post_3041_, 2, v___f_3032_);
v___x_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3042_, 0, v_pre_3040_);
lean_ctor_set(v___x_3042_, 1, v_post_3041_);
return v___x_3042_;
}
v___jp_3043_:
{
if (v_zetaDelta_3030_ == 0)
{
lean_inc_ref(v_pre_3044_);
v_pre_3038_ = v_pre_3044_;
goto v___jp_3037_;
}
else
{
lean_object* v_pre_3045_; 
lean_inc_ref(v_pre_3044_);
v_pre_3045_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed), 12, 1);
lean_closure_set(v_pre_3045_, 0, v_pre_3044_);
v_pre_3038_ = v_pre_3045_;
goto v___jp_3037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___boxed(lean_object* v_config_3048_, lean_object* v_thms_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_Meta_Grind_mkNormSymMethods(v_config_3048_, v_thms_3049_);
lean_dec_ref(v_config_3048_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(lean_object* v_x_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v___x_3063_; 
lean_inc_ref(v___y_3052_);
v___x_3063_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v___y_3052_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
if (lean_obj_tag(v_a_3064_) == 0)
{
uint8_t v_done_3065_; 
v_done_3065_ = lean_ctor_get_uint8(v_a_3064_, 0);
lean_dec_ref_known(v_a_3064_, 0);
if (v_done_3065_ == 0)
{
lean_object* v___x_3066_; 
lean_dec_ref_known(v___x_3063_, 1);
v___x_3066_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_3052_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec_ref(v___y_3052_);
return v___x_3066_;
}
else
{
lean_dec_ref(v___y_3052_);
return v___x_3063_;
}
}
else
{
uint8_t v_done_3067_; 
lean_dec_ref(v___y_3052_);
v_done_3067_ = lean_ctor_get_uint8(v_a_3064_, sizeof(void*)*1);
if (v_done_3067_ == 0)
{
lean_object* v_e_x27_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref_known(v___x_3063_, 1);
v_e_x27_3068_ = lean_ctor_get(v_a_3064_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_a_3064_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3070_ = v_a_3064_;
v_isShared_3071_ = v_isSharedCheck_3086_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_e_x27_3068_);
lean_dec(v_a_3064_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3086_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_x27_3068_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
if (lean_obj_tag(v_a_3073_) == 0)
{
lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3084_; 
lean_inc_ref(v_a_3073_);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3084_ == 0)
{
lean_object* v_unused_3085_; 
v_unused_3085_ = lean_ctor_get(v___x_3072_, 0);
lean_dec(v_unused_3085_);
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3084_;
goto v_resetjp_3074_;
}
else
{
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3084_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
uint8_t v_done_3077_; lean_object* v___x_3079_; 
v_done_3077_ = lean_ctor_get_uint8(v_a_3073_, 0);
lean_dec_ref_known(v_a_3073_, 0);
if (v_isShared_3071_ == 0)
{
v___x_3079_ = v___x_3070_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_e_x27_3068_);
v___x_3079_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3081_; 
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*1, v_done_3077_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 0, v___x_3079_);
v___x_3081_ = v___x_3075_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_del_object(v___x_3070_);
lean_dec_ref(v_e_x27_3068_);
return v___x_3072_;
}
}
else
{
lean_del_object(v___x_3070_);
lean_dec_ref(v_e_x27_3068_);
return v___x_3072_;
}
}
}
else
{
lean_dec_ref_known(v_a_3064_, 1);
return v___x_3063_;
}
}
}
else
{
lean_dec_ref(v___y_3052_);
return v___x_3063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0___boxed(lean_object* v_x_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(v_x_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec(v___y_3089_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(lean_object* v_x_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = lean_unsigned_to_nat(255u);
v___x_3113_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_3112_, v___y_3101_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___boxed(lean_object* v_x_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(v_x_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(lean_object* v_dsimp_3127_, lean_object* v___f_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3140_ = lean_box(0);
lean_inc_ref(v___y_3129_);
v___x_3141_ = l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(v_dsimp_3127_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
if (lean_obj_tag(v_a_3142_) == 0)
{
uint8_t v_done_3143_; 
v_done_3143_ = lean_ctor_get_uint8(v_a_3142_, 0);
lean_dec_ref_known(v_a_3142_, 0);
if (v_done_3143_ == 0)
{
lean_object* v___x_3144_; 
lean_dec_ref_known(v___x_3141_, 1);
v___x_3144_ = lean_apply_12(v___f_3128_, v___x_3140_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, lean_box(0));
return v___x_3144_;
}
else
{
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v___f_3128_);
return v___x_3141_;
}
}
else
{
uint8_t v_done_3145_; 
lean_dec_ref(v___y_3129_);
v_done_3145_ = lean_ctor_get_uint8(v_a_3142_, sizeof(void*)*1);
if (v_done_3145_ == 0)
{
lean_object* v_e_x27_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3164_; 
lean_dec_ref_known(v___x_3141_, 1);
v_e_x27_3146_ = lean_ctor_get(v_a_3142_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_a_3142_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3148_ = v_a_3142_;
v_isShared_3149_ = v_isSharedCheck_3164_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_e_x27_3146_);
lean_dec(v_a_3142_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3164_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3150_; 
lean_inc_ref(v_e_x27_3146_);
v___x_3150_ = lean_apply_12(v___f_3128_, v___x_3140_, v_e_x27_3146_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, lean_box(0));
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
if (lean_obj_tag(v_a_3151_) == 0)
{
lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3162_; 
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; 
v_unused_3163_ = lean_ctor_get(v___x_3150_, 0);
lean_dec(v_unused_3163_);
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3162_;
goto v_resetjp_3152_;
}
else
{
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3162_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
uint8_t v_done_3155_; lean_object* v___x_3157_; 
v_done_3155_ = lean_ctor_get_uint8(v_a_3151_, 0);
lean_dec_ref_known(v_a_3151_, 0);
if (v_isShared_3149_ == 0)
{
v___x_3157_ = v___x_3148_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_e_x27_3146_);
v___x_3157_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3159_; 
lean_ctor_set_uint8(v___x_3157_, sizeof(void*)*1, v_done_3155_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 0, v___x_3157_);
v___x_3159_ = v___x_3153_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3151_, 1);
lean_del_object(v___x_3148_);
lean_dec_ref(v_e_x27_3146_);
return v___x_3150_;
}
}
else
{
lean_del_object(v___x_3148_);
lean_dec_ref(v_e_x27_3146_);
return v___x_3150_;
}
}
}
else
{
lean_dec_ref_known(v_a_3142_, 1);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___f_3128_);
return v___x_3141_;
}
}
}
else
{
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v___f_3128_);
return v___x_3141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed(lean_object* v_dsimp_3165_, lean_object* v___f_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(v_dsimp_3165_, v___f_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec_ref(v_dsimp_3165_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(lean_object* v_pre_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; 
lean_inc(v___y_3189_);
lean_inc_ref(v___y_3188_);
lean_inc(v___y_3187_);
lean_inc_ref(v___y_3186_);
lean_inc(v___y_3185_);
lean_inc_ref(v___y_3184_);
lean_inc_ref(v___y_3180_);
v___x_3191_ = lean_apply_11(v_pre_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, lean_box(0));
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
if (lean_obj_tag(v_a_3192_) == 0)
{
uint8_t v_done_3193_; 
v_done_3193_ = lean_ctor_get_uint8(v_a_3192_, 0);
lean_dec_ref_known(v_a_3192_, 0);
if (v_done_3193_ == 0)
{
lean_object* v___x_3194_; 
lean_dec_ref_known(v___x_3191_, 1);
v___x_3194_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_3180_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
return v___x_3194_;
}
else
{
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec_ref(v___y_3180_);
return v___x_3191_;
}
}
else
{
uint8_t v_done_3195_; 
lean_dec_ref(v___y_3180_);
v_done_3195_ = lean_ctor_get_uint8(v_a_3192_, sizeof(void*)*1);
if (v_done_3195_ == 0)
{
lean_object* v_e_x27_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3214_; 
lean_dec_ref_known(v___x_3191_, 1);
v_e_x27_3196_ = lean_ctor_get(v_a_3192_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_a_3192_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3198_ = v_a_3192_;
v_isShared_3199_ = v_isSharedCheck_3214_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_e_x27_3196_);
lean_dec(v_a_3192_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3214_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; 
lean_inc_ref(v_e_x27_3196_);
v___x_3200_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_x27_3196_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
if (lean_obj_tag(v_a_3201_) == 0)
{
lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3212_; 
lean_inc_ref(v_a_3201_);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v___x_3200_, 0);
lean_dec(v_unused_3213_);
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3212_;
goto v_resetjp_3202_;
}
else
{
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3212_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
uint8_t v_done_3205_; lean_object* v___x_3207_; 
v_done_3205_ = lean_ctor_get_uint8(v_a_3201_, 0);
lean_dec_ref_known(v_a_3201_, 0);
if (v_isShared_3199_ == 0)
{
v___x_3207_ = v___x_3198_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_e_x27_3196_);
v___x_3207_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3209_; 
lean_ctor_set_uint8(v___x_3207_, sizeof(void*)*1, v_done_3205_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3207_);
v___x_3209_ = v___x_3203_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_del_object(v___x_3198_);
lean_dec_ref(v_e_x27_3196_);
return v___x_3200_;
}
}
else
{
lean_del_object(v___x_3198_);
lean_dec_ref(v_e_x27_3196_);
return v___x_3200_;
}
}
}
else
{
lean_dec_ref_known(v_a_3192_, 1);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
return v___x_3191_;
}
}
}
else
{
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec_ref(v___y_3180_);
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed(lean_object* v_pre_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(v_pre_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(lean_object* v___f_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = lean_box(0);
lean_inc_ref(v___y_3229_);
v___x_3241_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_3229_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
if (lean_obj_tag(v_a_3242_) == 0)
{
uint8_t v_done_3243_; 
v_done_3243_ = lean_ctor_get_uint8(v_a_3242_, 0);
lean_dec_ref_known(v_a_3242_, 0);
if (v_done_3243_ == 0)
{
lean_object* v___x_3244_; 
lean_dec_ref_known(v___x_3241_, 1);
v___x_3244_ = lean_apply_12(v___f_3228_, v___x_3240_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, lean_box(0));
return v___x_3244_;
}
else
{
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v___f_3228_);
return v___x_3241_;
}
}
else
{
uint8_t v_done_3245_; 
lean_dec_ref(v___y_3229_);
v_done_3245_ = lean_ctor_get_uint8(v_a_3242_, sizeof(void*)*1);
if (v_done_3245_ == 0)
{
lean_object* v_e_x27_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3264_; 
lean_dec_ref_known(v___x_3241_, 1);
v_e_x27_3246_ = lean_ctor_get(v_a_3242_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_a_3242_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3248_ = v_a_3242_;
v_isShared_3249_ = v_isSharedCheck_3264_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_e_x27_3246_);
lean_dec(v_a_3242_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3264_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3250_; 
lean_inc_ref(v_e_x27_3246_);
v___x_3250_ = lean_apply_12(v___f_3228_, v___x_3240_, v_e_x27_3246_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, lean_box(0));
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
if (lean_obj_tag(v_a_3251_) == 0)
{
lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3262_; 
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3262_ == 0)
{
lean_object* v_unused_3263_; 
v_unused_3263_ = lean_ctor_get(v___x_3250_, 0);
lean_dec(v_unused_3263_);
v___x_3253_ = v___x_3250_;
v_isShared_3254_ = v_isSharedCheck_3262_;
goto v_resetjp_3252_;
}
else
{
lean_dec(v___x_3250_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3262_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
uint8_t v_done_3255_; lean_object* v___x_3257_; 
v_done_3255_ = lean_ctor_get_uint8(v_a_3251_, 0);
lean_dec_ref_known(v_a_3251_, 0);
if (v_isShared_3249_ == 0)
{
v___x_3257_ = v___x_3248_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_e_x27_3246_);
v___x_3257_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3259_; 
lean_ctor_set_uint8(v___x_3257_, sizeof(void*)*1, v_done_3255_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3257_);
v___x_3259_ = v___x_3253_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3257_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3251_, 1);
lean_del_object(v___x_3248_);
lean_dec_ref(v_e_x27_3246_);
return v___x_3250_;
}
}
else
{
lean_del_object(v___x_3248_);
lean_dec_ref(v_e_x27_3246_);
return v___x_3250_;
}
}
}
else
{
lean_dec_ref_known(v_a_3242_, 1);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___f_3228_);
return v___x_3241_;
}
}
}
else
{
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v___f_3228_);
return v___x_3241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4___boxed(lean_object* v___f_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(v___f_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(lean_object* v___f_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___y_3291_; lean_object* v_e_x27_3292_; uint8_t v_done_3293_; lean_object* v___y_3307_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = lean_box(0);
lean_inc_ref(v___y_3279_);
v___x_3314_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_3279_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
if (lean_obj_tag(v_a_3315_) == 0)
{
uint8_t v_done_3316_; 
v_done_3316_ = lean_ctor_get_uint8(v_a_3315_, 0);
lean_dec_ref_known(v_a_3315_, 0);
if (v_done_3316_ == 0)
{
lean_object* v___x_3317_; 
lean_dec_ref_known(v___x_3314_, 1);
lean_inc(v___y_3288_);
lean_inc_ref(v___y_3287_);
lean_inc(v___y_3286_);
lean_inc_ref(v___y_3285_);
lean_inc(v___y_3284_);
lean_inc_ref(v___y_3283_);
lean_inc_ref(v___y_3279_);
v___x_3317_ = lean_apply_12(v___f_3278_, v___x_3313_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, lean_box(0));
v___y_3307_ = v___x_3317_;
goto v___jp_3306_;
}
else
{
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___f_3278_);
v___y_3307_ = v___x_3314_;
goto v___jp_3306_;
}
}
else
{
uint8_t v_done_3318_; 
v_done_3318_ = lean_ctor_get_uint8(v_a_3315_, sizeof(void*)*1);
if (v_done_3318_ == 0)
{
lean_object* v_e_x27_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3339_; 
lean_dec_ref_known(v___x_3314_, 1);
lean_dec_ref(v___y_3279_);
v_e_x27_3319_ = lean_ctor_get(v_a_3315_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_a_3315_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3321_ = v_a_3315_;
v_isShared_3322_ = v_isSharedCheck_3339_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_e_x27_3319_);
lean_dec(v_a_3315_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3339_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; 
lean_inc(v___y_3288_);
lean_inc_ref(v___y_3287_);
lean_inc(v___y_3286_);
lean_inc_ref(v___y_3285_);
lean_inc(v___y_3284_);
lean_inc_ref(v___y_3283_);
lean_inc_ref(v_e_x27_3319_);
v___x_3323_ = lean_apply_12(v___f_3278_, v___x_3313_, v_e_x27_3319_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, lean_box(0));
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
if (lean_obj_tag(v_a_3324_) == 0)
{
lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3335_; 
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3335_ == 0)
{
lean_object* v_unused_3336_; 
v_unused_3336_ = lean_ctor_get(v___x_3323_, 0);
lean_dec(v_unused_3336_);
v___x_3326_ = v___x_3323_;
v_isShared_3327_ = v_isSharedCheck_3335_;
goto v_resetjp_3325_;
}
else
{
lean_dec(v___x_3323_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3335_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
uint8_t v_done_3328_; lean_object* v___x_3330_; 
v_done_3328_ = lean_ctor_get_uint8(v_a_3324_, 0);
lean_dec_ref_known(v_a_3324_, 0);
lean_inc_ref(v_e_x27_3319_);
if (v_isShared_3322_ == 0)
{
v___x_3330_ = v___x_3321_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_e_x27_3319_);
v___x_3330_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
lean_ctor_set_uint8(v___x_3330_, sizeof(void*)*1, v_done_3328_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3330_);
v___x_3332_ = v___x_3326_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
v___y_3291_ = v___x_3332_;
v_e_x27_3292_ = v_e_x27_3319_;
v_done_3293_ = v_done_3328_;
goto v___jp_3290_;
}
}
}
}
else
{
lean_object* v_e_x27_3337_; uint8_t v_done_3338_; 
lean_del_object(v___x_3321_);
lean_dec_ref(v_e_x27_3319_);
v_e_x27_3337_ = lean_ctor_get(v_a_3324_, 0);
lean_inc_ref(v_e_x27_3337_);
v_done_3338_ = lean_ctor_get_uint8(v_a_3324_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3324_, 1);
v___y_3291_ = v___x_3323_;
v_e_x27_3292_ = v_e_x27_3337_;
v_done_3293_ = v_done_3338_;
goto v___jp_3290_;
}
}
else
{
lean_del_object(v___x_3321_);
lean_dec_ref(v_e_x27_3319_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
return v___x_3323_;
}
}
}
else
{
lean_dec_ref_known(v_a_3315_, 1);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___f_3278_);
v___y_3307_ = v___x_3314_;
goto v___jp_3306_;
}
}
}
else
{
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___f_3278_);
v___y_3307_ = v___x_3314_;
goto v___jp_3306_;
}
v___jp_3290_:
{
if (v_done_3293_ == 0)
{
lean_object* v___x_3294_; 
lean_dec_ref(v___y_3291_);
lean_inc_ref(v_e_x27_3292_);
v___x_3294_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_x27_3292_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
if (lean_obj_tag(v_a_3295_) == 0)
{
lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3304_; 
lean_inc_ref(v_a_3295_);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3304_ == 0)
{
lean_object* v_unused_3305_; 
v_unused_3305_ = lean_ctor_get(v___x_3294_, 0);
lean_dec(v_unused_3305_);
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3304_;
goto v_resetjp_3296_;
}
else
{
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3304_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
uint8_t v_done_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v_done_3299_ = lean_ctor_get_uint8(v_a_3295_, 0);
lean_dec_ref_known(v_a_3295_, 0);
v___x_3300_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3300_, 0, v_e_x27_3292_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*1, v_done_3299_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3300_);
v___x_3302_ = v___x_3297_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
else
{
lean_dec_ref(v_e_x27_3292_);
return v___x_3294_;
}
}
else
{
lean_dec_ref(v_e_x27_3292_);
return v___x_3294_;
}
}
else
{
lean_dec_ref(v_e_x27_3292_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
return v___y_3291_;
}
}
v___jp_3306_:
{
if (lean_obj_tag(v___y_3307_) == 0)
{
lean_object* v_a_3308_; 
v_a_3308_ = lean_ctor_get(v___y_3307_, 0);
if (lean_obj_tag(v_a_3308_) == 0)
{
uint8_t v_done_3309_; 
v_done_3309_ = lean_ctor_get_uint8(v_a_3308_, 0);
if (v_done_3309_ == 0)
{
lean_object* v___x_3310_; 
lean_dec_ref_known(v___y_3307_, 1);
v___x_3310_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_3279_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
return v___x_3310_;
}
else
{
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec_ref(v___y_3279_);
return v___y_3307_;
}
}
else
{
lean_object* v_e_x27_3311_; uint8_t v_done_3312_; 
lean_dec_ref(v___y_3279_);
v_e_x27_3311_ = lean_ctor_get(v_a_3308_, 0);
lean_inc_ref(v_e_x27_3311_);
v_done_3312_ = lean_ctor_get_uint8(v_a_3308_, sizeof(void*)*1);
v___y_3291_ = v___y_3307_;
v_e_x27_3292_ = v_e_x27_3311_;
v_done_3293_ = v_done_3312_;
goto v___jp_3290_;
}
}
else
{
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec_ref(v___y_3279_);
return v___y_3307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5___boxed(lean_object* v___f_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(v___f_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods(lean_object* v_config_3359_, lean_object* v_thms_3360_){
_start:
{
uint8_t v_zetaDelta_3361_; uint8_t v_zeta_3362_; lean_object* v___f_3363_; lean_object* v_pre_3365_; lean_object* v_pre_3370_; 
v_zetaDelta_3361_ = lean_ctor_get_uint8(v_config_3359_, sizeof(void*)*14 + 19);
v_zeta_3362_ = lean_ctor_get_uint8(v_config_3359_, sizeof(void*)*14 + 20);
v___f_3363_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__1));
if (v_zeta_3362_ == 0)
{
lean_object* v_pre_3372_; 
v_pre_3372_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__2));
v_pre_3370_ = v_pre_3372_;
goto v___jp_3369_;
}
else
{
lean_object* v_pre_3373_; 
v_pre_3373_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__3));
v_pre_3370_ = v_pre_3373_;
goto v___jp_3369_;
}
v___jp_3364_:
{
lean_object* v_dsimp_3366_; lean_object* v_post_3367_; lean_object* v___x_3368_; 
v_dsimp_3366_ = lean_ctor_get(v_thms_3360_, 2);
lean_inc_ref(v_dsimp_3366_);
lean_dec_ref(v_thms_3360_);
v_post_3367_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed), 13, 2);
lean_closure_set(v_post_3367_, 0, v_dsimp_3366_);
lean_closure_set(v_post_3367_, 1, v___f_3363_);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v_pre_3365_);
lean_ctor_set(v___x_3368_, 1, v_post_3367_);
return v___x_3368_;
}
v___jp_3369_:
{
if (v_zetaDelta_3361_ == 0)
{
lean_inc_ref(v_pre_3370_);
v_pre_3365_ = v_pre_3370_;
goto v___jp_3364_;
}
else
{
lean_object* v_pre_3371_; 
lean_inc_ref(v_pre_3370_);
v_pre_3371_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed), 12, 1);
lean_closure_set(v_pre_3371_, 0, v_pre_3370_);
v_pre_3365_ = v_pre_3371_;
goto v___jp_3364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___boxed(lean_object* v_config_3374_, lean_object* v_thms_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_config_3374_, v_thms_3375_);
lean_dec_ref(v_config_3374_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(lean_object* v_e_3377_, lean_object* v___y_3378_){
_start:
{
uint8_t v___x_3380_; 
v___x_3380_ = l_Lean_Expr_hasMVar(v_e_3377_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; 
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_e_3377_);
return v___x_3381_;
}
else
{
lean_object* v___x_3382_; lean_object* v_mctx_3383_; lean_object* v___x_3384_; lean_object* v_fst_3385_; lean_object* v_snd_3386_; lean_object* v___x_3387_; lean_object* v_cache_3388_; lean_object* v_zetaDeltaFVarIds_3389_; lean_object* v_postponed_3390_; lean_object* v_diag_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3400_; 
v___x_3382_ = lean_st_ref_get(v___y_3378_);
v_mctx_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc_ref(v_mctx_3383_);
lean_dec(v___x_3382_);
v___x_3384_ = l_Lean_instantiateMVarsCore(v_mctx_3383_, v_e_3377_);
v_fst_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_fst_3385_);
v_snd_3386_ = lean_ctor_get(v___x_3384_, 1);
lean_inc(v_snd_3386_);
lean_dec_ref(v___x_3384_);
v___x_3387_ = lean_st_ref_take(v___y_3378_);
v_cache_3388_ = lean_ctor_get(v___x_3387_, 1);
v_zetaDeltaFVarIds_3389_ = lean_ctor_get(v___x_3387_, 2);
v_postponed_3390_ = lean_ctor_get(v___x_3387_, 3);
v_diag_3391_ = lean_ctor_get(v___x_3387_, 4);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; 
v_unused_3401_ = lean_ctor_get(v___x_3387_, 0);
lean_dec(v_unused_3401_);
v___x_3393_ = v___x_3387_;
v_isShared_3394_ = v_isSharedCheck_3400_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_diag_3391_);
lean_inc(v_postponed_3390_);
lean_inc(v_zetaDeltaFVarIds_3389_);
lean_inc(v_cache_3388_);
lean_dec(v___x_3387_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3400_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v_snd_3386_);
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_snd_3386_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_cache_3388_);
lean_ctor_set(v_reuseFailAlloc_3399_, 2, v_zetaDeltaFVarIds_3389_);
lean_ctor_set(v_reuseFailAlloc_3399_, 3, v_postponed_3390_);
lean_ctor_set(v_reuseFailAlloc_3399_, 4, v_diag_3391_);
v___x_3396_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = lean_st_ref_put(v___y_3378_, v___x_3396_);
v___x_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3398_, 0, v_fst_3385_);
return v___x_3398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg___boxed(lean_object* v_e_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_3402_, v___y_3403_);
lean_dec(v___y_3403_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(lean_object* v_e_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_3406_, v___y_3413_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___boxed(lean_object* v_e_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(v_e_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy(lean_object* v_e_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v___x_3441_; lean_object* v_a_3442_; lean_object* v___x_3443_; 
v___x_3441_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_3430_, v_a_3437_);
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref(v___x_3441_);
v___x_3443_ = l_Lean_Meta_Grind_simpCore(v_a_3442_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v_expr_3445_; lean_object* v_proof_x3f_3446_; uint8_t v_cache_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3471_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref_known(v___x_3443_, 1);
v_expr_3445_ = lean_ctor_get(v_a_3444_, 0);
v_proof_x3f_3446_ = lean_ctor_get(v_a_3444_, 1);
v_cache_3447_ = lean_ctor_get_uint8(v_a_3444_, sizeof(void*)*2);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_a_3444_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3449_ = v_a_3444_;
v_isShared_3450_ = v_isSharedCheck_3471_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_proof_x3f_3446_);
lean_inc(v_expr_3445_);
lean_dec(v_a_3444_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3471_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_expr_3445_, v_a_3438_, v_a_3439_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3462_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3454_ = v___x_3451_;
v_isShared_3455_ = v_isSharedCheck_3462_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3451_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3462_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v_a_3452_);
v___x_3457_ = v___x_3449_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3452_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_proof_x3f_3446_);
lean_ctor_set_uint8(v_reuseFailAlloc_3461_, sizeof(void*)*2, v_cache_3447_);
v___x_3457_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3459_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 0, v___x_3457_);
v___x_3459_ = v___x_3454_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_del_object(v___x_3449_);
lean_dec(v_proof_x3f_3446_);
v_a_3463_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3451_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3451_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
else
{
return v___x_3443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy___boxed(lean_object* v_e_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Lean_Meta_Grind_normLegacy(v_e_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
return v_res_3483_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__0(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__1, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__1_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1);
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
return v___x_3485_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__1(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__0, &l_Lean_Meta_Grind_normSym___redArg___closed__0_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__0);
v___x_3487_ = lean_unsigned_to_nat(0u);
v___x_3488_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v___x_3486_);
lean_ctor_set(v___x_3488_, 2, v___x_3486_);
lean_ctor_set(v___x_3488_, 3, v___x_3486_);
return v___x_3488_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__2(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__0, &l_Lean_Meta_Grind_normSym___redArg___closed__0_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__0);
v___x_3490_ = lean_unsigned_to_nat(0u);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
lean_ctor_set(v___x_3491_, 1, v___x_3489_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg(lean_object* v_e_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_Meta_Grind_mkNormSymTheorems(v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___x_3503_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3493_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
lean_inc(v_a_3502_);
v___x_3505_ = l_Lean_Meta_Grind_mkNormSymMethods(v_a_3504_, v_a_3502_);
v___x_3506_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_a_3504_, v_a_3502_);
lean_dec(v_a_3504_);
v___x_3507_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__1, &l_Lean_Meta_Grind_normSym___redArg___closed__1_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__1);
v___x_3508_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__2, &l_Lean_Meta_Grind_normSym___redArg___closed__2_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__2);
v___x_3509_ = l_Lean_Meta_Grind_symNorm(v_e_3492_, v___x_3505_, v___x_3506_, v___x_3507_, v___x_3508_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3518_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3512_ = v___x_3509_;
v_isShared_3513_ = v_isSharedCheck_3518_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3509_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3518_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v_fst_3514_; lean_object* v___x_3516_; 
v_fst_3514_ = lean_ctor_get(v_a_3510_, 0);
lean_inc(v_fst_3514_);
lean_dec(v_a_3510_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v_fst_3514_);
v___x_3516_ = v___x_3512_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_fst_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
v_a_3519_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3509_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3509_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec(v_a_3502_);
lean_dec_ref(v_e_3492_);
v_a_3527_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3503_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3503_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec_ref(v_e_3492_);
v_a_3535_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3501_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3501_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg___boxed(lean_object* v_e_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lean_Meta_Grind_normSym___redArg(v_e_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
lean_dec_ref(v_a_3544_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym(lean_object* v_e_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Lean_Meta_Grind_normSym___redArg(v_e_3553_, v_a_3555_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___boxed(lean_object* v_e_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Meta_Grind_normSym(v_e_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
return v_res_3576_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Arith(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_NormSymProcs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
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
res = runtime_initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Arith(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_NormSymProcs(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Reduce(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
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
res = initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
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
