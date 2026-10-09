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
lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_86_;
v_res_86_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_();
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2____boxed(lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_();
return v_res_88_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(lean_object* v_thms_89_, lean_object* v_____r_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v_thms_89_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_thms_89_ = stack[0].m_obj;
lean_object* v_____r_90_ = stack[1].m_obj;
lean_object* v___y_91_ = stack[2].m_obj;
lean_object* v___y_92_ = stack[3].m_obj;
lean_object* v___y_93_ = stack[4].m_obj;
lean_object* v___y_94_ = stack[5].m_obj;
lean_object* v_res_98_;
v_res_98_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(v_thms_89_, v_____r_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0___boxed(lean_object* v_thms_99_, lean_object* v_____r_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(v_thms_99_, v_____r_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_106_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0(lean_object* v_msgData_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; lean_object* v_env_114_; uint8_t v___x_115_; lean_object* v_env_116_; lean_object* v___x_117_; lean_object* v_toCold_118_; lean_object* v_mctx_119_; lean_object* v_lctx_120_; lean_object* v_options_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_113_ = lean_st_ref_get(v___y_111_);
v_env_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc_ref(v_env_114_);
lean_dec(v___x_113_);
v___x_115_ = 0;
v_env_116_ = l_Lean_Environment_setRecordingDeps(v_env_114_, v___x_115_);
v___x_117_ = lean_st_ref_get(v___y_109_);
v_toCold_118_ = lean_ctor_get(v___y_110_, 0);
v_mctx_119_ = lean_ctor_get(v___x_117_, 0);
lean_inc_ref(v_mctx_119_);
lean_dec(v___x_117_);
v_lctx_120_ = lean_ctor_get(v___y_108_, 2);
v_options_121_ = lean_ctor_get(v_toCold_118_, 2);
lean_inc_ref(v_options_121_);
lean_inc_ref(v_lctx_120_);
v___x_122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_122_, 0, v_env_116_);
lean_ctor_set(v___x_122_, 1, v_mctx_119_);
lean_ctor_set(v___x_122_, 2, v_lctx_120_);
lean_ctor_set(v___x_122_, 3, v_options_121_);
v___x_123_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v_msgData_107_);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_107_ = stack[0].m_obj;
lean_object* v___y_108_ = stack[1].m_obj;
lean_object* v___y_109_ = stack[2].m_obj;
lean_object* v___y_110_ = stack[3].m_obj;
lean_object* v___y_111_ = stack[4].m_obj;
lean_object* v_res_125_;
v_res_125_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0(v_msgData_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
stack->m_obj
 = v_res_125_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0___boxed(lean_object* v_msgData_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0(v_msgData_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_132_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0(void){
_start:
{
lean_object* v___x_133_; double v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_float_of_nat(v___x_133_);
return v___x_134_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(lean_object* v_cls_138_, lean_object* v_msg_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_ref_145_; lean_object* v___x_146_; lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_192_; 
v_ref_145_ = lean_ctor_get(v___y_142_, 2);
v___x_146_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_spec__0(v_msg_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_192_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_192_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_192_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v_traceState_152_; lean_object* v_env_153_; lean_object* v_nextMacroScope_154_; lean_object* v_ngen_155_; lean_object* v_auxDeclNGen_156_; lean_object* v_cache_157_; lean_object* v_recordedDeps_158_; lean_object* v_messages_159_; lean_object* v_infoState_160_; lean_object* v_snapshotTasks_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_191_; 
v___x_151_ = lean_st_ref_take(v___y_143_);
v_traceState_152_ = lean_ctor_get(v___x_151_, 4);
v_env_153_ = lean_ctor_get(v___x_151_, 0);
v_nextMacroScope_154_ = lean_ctor_get(v___x_151_, 1);
v_ngen_155_ = lean_ctor_get(v___x_151_, 2);
v_auxDeclNGen_156_ = lean_ctor_get(v___x_151_, 3);
v_cache_157_ = lean_ctor_get(v___x_151_, 5);
v_recordedDeps_158_ = lean_ctor_get(v___x_151_, 6);
v_messages_159_ = lean_ctor_get(v___x_151_, 7);
v_infoState_160_ = lean_ctor_get(v___x_151_, 8);
v_snapshotTasks_161_ = lean_ctor_get(v___x_151_, 9);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_191_ == 0)
{
v___x_163_ = v___x_151_;
v_isShared_164_ = v_isSharedCheck_191_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_snapshotTasks_161_);
lean_inc(v_infoState_160_);
lean_inc(v_messages_159_);
lean_inc(v_recordedDeps_158_);
lean_inc(v_cache_157_);
lean_inc(v_traceState_152_);
lean_inc(v_auxDeclNGen_156_);
lean_inc(v_ngen_155_);
lean_inc(v_nextMacroScope_154_);
lean_inc(v_env_153_);
lean_dec(v___x_151_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_191_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
uint64_t v_tid_165_; lean_object* v_traces_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_190_; 
v_tid_165_ = lean_ctor_get_uint64(v_traceState_152_, sizeof(void*)*1);
v_traces_166_ = lean_ctor_get(v_traceState_152_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v_traceState_152_);
if (v_isSharedCheck_190_ == 0)
{
v___x_168_ = v_traceState_152_;
v_isShared_169_ = v_isSharedCheck_190_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_traces_166_);
lean_dec(v_traceState_152_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_190_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_171_; double v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_170_ = lean_box(0);
v___x_171_ = lean_box(0);
v___x_172_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__0);
v___x_173_ = 0;
v___x_174_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__1));
v___x_175_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_175_, 0, v_cls_138_);
lean_ctor_set(v___x_175_, 1, v___x_171_);
lean_ctor_set(v___x_175_, 2, v___x_174_);
lean_ctor_set_float(v___x_175_, sizeof(void*)*3, v___x_172_);
lean_ctor_set_float(v___x_175_, sizeof(void*)*3 + 8, v___x_172_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*3 + 16, v___x_173_);
v___x_176_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___closed__2));
v___x_177_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_177_, 0, v___x_175_);
lean_ctor_set(v___x_177_, 1, v_a_147_);
lean_ctor_set(v___x_177_, 2, v___x_176_);
lean_inc(v_ref_145_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v_ref_145_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = l_Lean_PersistentArray_push___redArg(v_traces_166_, v___x_178_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_179_);
v___x_181_ = v___x_168_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_179_);
lean_ctor_set_uint64(v_reuseFailAlloc_189_, sizeof(void*)*1, v_tid_165_);
v___x_181_ = v_reuseFailAlloc_189_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 4, v___x_181_);
v___x_183_ = v___x_163_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_env_153_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_nextMacroScope_154_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v_ngen_155_);
lean_ctor_set(v_reuseFailAlloc_188_, 3, v_auxDeclNGen_156_);
lean_ctor_set(v_reuseFailAlloc_188_, 4, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_188_, 5, v_cache_157_);
lean_ctor_set(v_reuseFailAlloc_188_, 6, v_recordedDeps_158_);
lean_ctor_set(v_reuseFailAlloc_188_, 7, v_messages_159_);
lean_ctor_set(v_reuseFailAlloc_188_, 8, v_infoState_160_);
lean_ctor_set(v_reuseFailAlloc_188_, 9, v_snapshotTasks_161_);
v___x_183_ = v_reuseFailAlloc_188_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_184_ = lean_st_ref_put(v___y_143_, v___x_183_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_170_);
v___x_186_ = v___x_149_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_170_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_138_ = stack[0].m_obj;
lean_object* v_msg_139_ = stack[1].m_obj;
lean_object* v___y_140_ = stack[2].m_obj;
lean_object* v___y_141_ = stack[3].m_obj;
lean_object* v___y_142_ = stack[4].m_obj;
lean_object* v___y_143_ = stack[5].m_obj;
lean_object* v_res_193_;
v_res_193_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v_cls_138_, v_msg_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
stack->m_obj
 = v_res_193_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0___boxed(lean_object* v_cls_194_, lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v_cls_194_, v_msg_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__1));
v___x_207_ = l_Lean_Name_append(v___x_206_, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__3));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__5));
v___x_213_ = l_Lean_stringToMessageData(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__7));
v___x_216_ = l_Lean_stringToMessageData(v___x_215_);
return v___x_216_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(lean_object* v_thms_217_, lean_object* v_thm_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___y_225_; lean_object* v_proof_235_; 
v_proof_235_ = lean_ctor_get(v_thm_218_, 2);
if (lean_obj_tag(v_proof_235_) == 4)
{
lean_object* v_declName_236_; lean_object* v___x_240_; 
lean_inc_ref(v_proof_235_);
lean_dec_ref(v_thm_218_);
v_declName_236_ = lean_ctor_get(v_proof_235_, 0);
lean_inc_n(v_declName_236_, 2);
lean_dec_ref_known(v_proof_235_, 2);
v___x_240_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_declName_236_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_249_; 
lean_dec(v_declName_236_);
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_249_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_thms_217_, v_a_241_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_245_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_286_; 
v_a_250_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_286_ == 0)
{
v___x_252_ = v___x_240_;
v_isShared_253_ = v_isSharedCheck_286_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_240_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_286_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
uint8_t v___y_255_; uint8_t v___x_284_; 
v___x_284_ = l_Lean_Exception_isInterrupt(v_a_250_);
if (v___x_284_ == 0)
{
uint8_t v___x_285_; 
lean_inc(v_a_250_);
v___x_285_ = l_Lean_Exception_isRuntime(v_a_250_);
v___y_255_ = v___x_285_;
goto v___jp_254_;
}
else
{
v___y_255_ = v___x_284_;
goto v___jp_254_;
}
v___jp_254_:
{
if (v___y_255_ == 0)
{
lean_object* v_toCold_256_; lean_object* v_options_257_; uint8_t v_hasTrace_258_; 
lean_del_object(v___x_252_);
v_toCold_256_ = lean_ctor_get(v_a_221_, 0);
v_options_257_ = lean_ctor_get(v_toCold_256_, 2);
v_hasTrace_258_ = lean_ctor_get_uint8(v_options_257_, sizeof(void*)*1);
if (v_hasTrace_258_ == 0)
{
lean_dec(v_a_250_);
lean_dec(v_declName_236_);
goto v___jp_237_;
}
else
{
lean_object* v_inheritedTraceOptions_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_inheritedTraceOptions_259_ = lean_ctor_get(v_toCold_256_, 11);
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2);
v___x_262_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_259_, v_options_257_, v___x_261_);
if (v___x_262_ == 0)
{
lean_dec(v_a_250_);
lean_dec(v_declName_236_);
goto v___jp_237_;
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4);
v___x_264_ = l_Lean_MessageData_ofConstName(v_declName_236_, v___y_255_);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = l_Lean_Exception_toMessageData(v_a_250_);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v___x_260_, v___x_269_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(v_thms_217_, v_a_271_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
v___y_225_ = v___x_272_;
goto v___jp_224_;
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v_thms_217_);
v_a_273_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_270_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_270_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
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
}
else
{
lean_object* v___x_282_; 
lean_dec(v_declName_236_);
lean_dec_ref(v_thms_217_);
if (v_isShared_253_ == 0)
{
v___x_282_ = v___x_252_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_250_);
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
}
v___jp_237_:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_box(0);
v___x_239_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___lam__0(v_thms_217_, v___x_238_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
v___y_225_ = v___x_239_;
goto v___jp_224_;
}
}
else
{
lean_object* v_toCold_287_; lean_object* v_options_288_; uint8_t v_hasTrace_289_; 
v_toCold_287_ = lean_ctor_get(v_a_221_, 0);
v_options_288_ = lean_ctor_get(v_toCold_287_, 2);
v_hasTrace_289_ = lean_ctor_get_uint8(v_options_288_, sizeof(void*)*1);
if (v_hasTrace_289_ == 0)
{
lean_object* v___x_290_; 
lean_dec_ref(v_thm_218_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v_thms_217_);
return v___x_290_;
}
else
{
lean_object* v_origin_291_; lean_object* v_inheritedTraceOptions_292_; lean_object* v_cls_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_origin_291_ = lean_ctor_get(v_thm_218_, 4);
lean_inc_ref(v_origin_291_);
lean_dec_ref(v_thm_218_);
v_inheritedTraceOptions_292_ = lean_ctor_get(v_toCold_287_, 11);
v_cls_293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_294_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2);
v___x_295_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_292_, v_options_288_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
lean_dec_ref(v_origin_291_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v_thms_217_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4);
v___x_298_ = l_Lean_Meta_Origin_key(v_origin_291_);
lean_dec_ref(v_origin_291_);
v___x_299_ = l_Lean_MessageData_ofName(v___x_298_);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_297_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v_cls_293_, v___x_302_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; 
v_unused_311_ = lean_ctor_get(v___x_303_, 0);
lean_dec(v_unused_311_);
v___x_305_ = v___x_303_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_dec(v___x_303_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_thms_217_);
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_thms_217_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec_ref(v_thms_217_);
v_a_312_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_303_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_303_);
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
}
}
v___jp_224_:
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
v_a_226_ = lean_ctor_get(v___y_225_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___y_225_);
if (v_isSharedCheck_234_ == 0)
{
v___x_228_ = v___y_225_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___y_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_a_230_; lean_object* v___x_232_; 
v_a_230_ = lean_ctor_get(v_a_226_, 0);
lean_inc(v_a_230_);
lean_dec(v_a_226_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v_a_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_0interp(lean_interpreter_value* stack)
{
lean_object* v_thms_217_ = stack[0].m_obj;
lean_object* v_thm_218_ = stack[1].m_obj;
lean_object* v_a_219_ = stack[2].m_obj;
lean_object* v_a_220_ = stack[3].m_obj;
lean_object* v_a_221_ = stack[4].m_obj;
lean_object* v_a_222_ = stack[5].m_obj;
lean_object* v_res_320_;
v_res_320_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_thms_217_, v_thm_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
stack->m_obj
 = v_res_320_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___boxed(lean_object* v_thms_321_, lean_object* v_thm_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_thms_321_, v_thm_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
return v_res_328_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_, lean_object* v_b_332_){
_start:
{
uint8_t v___x_333_; 
v___x_333_ = lean_usize_dec_eq(v_i_330_, v_stop_331_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; size_t v___x_336_; size_t v___x_337_; 
v___x_334_ = lean_array_uget_borrowed(v_as_329_, v_i_330_);
lean_inc(v___x_334_);
v___x_335_ = lean_array_push(v_b_332_, v___x_334_);
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_330_, v___x_336_);
v_i_330_ = v___x_337_;
v_b_332_ = v___x_335_;
goto _start;
}
else
{
return v_b_332_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_329_ = stack[0].m_obj;
size_t v_i_330_ = stack[1].m_num;
size_t v_stop_331_ = stack[2].m_num;
lean_object* v_b_332_ = stack[3].m_obj;
lean_object* v_res_339_;
v_res_339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(v_as_329_, v_i_330_, v_stop_331_, v_b_332_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4___boxed(lean_object* v_as_340_, lean_object* v_i_341_, lean_object* v_stop_342_, lean_object* v_b_343_){
_start:
{
size_t v_i_boxed_344_; size_t v_stop_boxed_345_; lean_object* v_res_346_; 
v_i_boxed_344_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_stop_boxed_345_ = lean_unbox_usize(v_stop_342_);
lean_dec(v_stop_342_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(v_as_340_, v_i_boxed_344_, v_stop_boxed_345_, v_b_343_);
lean_dec_ref(v_as_340_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
if (lean_obj_tag(v_x_348_) == 0)
{
lean_object* v_child_349_; 
v_child_349_ = lean_ctor_get(v_x_348_, 1);
v_x_348_ = v_child_349_;
goto _start;
}
else
{
lean_object* v_vs_351_; lean_object* v_children_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_vs_351_ = lean_ctor_get(v_x_348_, 0);
v_children_352_ = lean_ctor_get(v_x_348_, 1);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_array_get_size(v_vs_351_);
v___x_355_ = lean_nat_dec_lt(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_array_get_size(v_children_352_);
v___x_357_ = lean_nat_dec_lt(v___x_353_, v___x_356_);
if (v___x_357_ == 0)
{
return v_x_347_;
}
else
{
size_t v___x_358_; size_t v___x_359_; lean_object* v___x_360_; 
v___x_358_ = ((size_t)0ULL);
v___x_359_ = lean_usize_of_nat(v___x_356_);
v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_children_352_, v___x_358_, v___x_359_, v_x_347_);
return v___x_360_;
}
}
else
{
size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_361_ = ((size_t)0ULL);
v___x_362_ = lean_usize_of_nat(v___x_354_);
v___x_363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(v_vs_351_, v___x_361_, v___x_362_, v_x_347_);
v___x_364_ = lean_array_get_size(v_children_352_);
v___x_365_ = lean_nat_dec_lt(v___x_353_, v___x_364_);
if (v___x_365_ == 0)
{
return v___x_363_;
}
else
{
size_t v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_usize_of_nat(v___x_364_);
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_children_352_, v___x_361_, v___x_366_, v___x_363_);
return v___x_367_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(lean_object* v_as_368_, size_t v_i_369_, size_t v_stop_370_, lean_object* v_b_371_){
_start:
{
uint8_t v___x_372_; 
v___x_372_ = lean_usize_dec_eq(v_i_369_, v_stop_370_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v_snd_374_; lean_object* v___x_375_; size_t v___x_376_; size_t v___x_377_; 
v___x_373_ = lean_array_uget_borrowed(v_as_368_, v_i_369_);
v_snd_374_ = lean_ctor_get(v___x_373_, 1);
v___x_375_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_b_371_, v_snd_374_);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_add(v_i_369_, v___x_376_);
v_i_369_ = v___x_377_;
v_b_371_ = v___x_375_;
goto _start;
}
else
{
return v_b_371_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_368_ = stack[0].m_obj;
size_t v_i_369_ = stack[1].m_num;
size_t v_stop_370_ = stack[2].m_num;
lean_object* v_b_371_ = stack[3].m_obj;
lean_object* v_res_379_;
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_as_368_, v_i_369_, v_stop_370_, v_b_371_);
stack->m_obj
 = v_res_379_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3___boxed(lean_object* v_as_380_, lean_object* v_i_381_, lean_object* v_stop_382_, lean_object* v_b_383_){
_start:
{
size_t v_i_boxed_384_; size_t v_stop_boxed_385_; lean_object* v_res_386_; 
v_i_boxed_384_ = lean_unbox_usize(v_i_381_);
lean_dec(v_i_381_);
v_stop_boxed_385_ = lean_unbox_usize(v_stop_382_);
lean_dec(v_stop_382_);
v_res_386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_as_380_, v_i_boxed_384_, v_stop_boxed_385_, v_b_383_);
lean_dec_ref(v_as_380_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2___boxed(lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_x_387_, v_x_388_);
lean_dec_ref(v_x_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___lam__0(lean_object* v_s_390_, lean_object* v_x_391_, lean_object* v_t_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_s_390_, v_t_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___lam__0___boxed(lean_object* v_s_394_, lean_object* v_x_395_, lean_object* v_t_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Meta_Grind_mkNormSymTheorems___lam__0(v_s_394_, v_x_395_, v_t_396_);
lean_dec_ref(v_t_396_);
lean_dec(v_x_395_);
return v_res_397_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(lean_object* v_as_398_, size_t v_sz_399_, size_t v_i_400_, lean_object* v_b_401_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = lean_usize_dec_lt(v_i_400_, v_sz_399_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v_b_401_);
return v___x_404_;
}
else
{
lean_object* v_a_405_; lean_object* v___x_406_; size_t v___x_407_; size_t v___x_408_; 
v_a_405_ = lean_array_uget_borrowed(v_as_398_, v_i_400_);
lean_inc(v_a_405_);
v___x_406_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_401_, v_a_405_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_add(v_i_400_, v___x_407_);
v_i_400_ = v___x_408_;
v_b_401_ = v___x_406_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_398_ = stack[0].m_obj;
size_t v_sz_399_ = stack[1].m_num;
size_t v_i_400_ = stack[2].m_num;
lean_object* v_b_401_ = stack[3].m_obj;
lean_object* v_res_410_;
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_as_398_, v_sz_399_, v_i_400_, v_b_401_);
stack->m_obj
 = v_res_410_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg___boxed(lean_object* v_as_411_, lean_object* v_sz_412_, lean_object* v_i_413_, lean_object* v_b_414_, lean_object* v___y_415_){
_start:
{
size_t v_sz_boxed_416_; size_t v_i_boxed_417_; lean_object* v_res_418_; 
v_sz_boxed_416_ = lean_unbox_usize(v_sz_412_);
lean_dec(v_sz_412_);
v_i_boxed_417_ = lean_unbox_usize(v_i_413_);
lean_dec(v_i_413_);
v_res_418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_as_411_, v_sz_boxed_416_, v_i_boxed_417_, v_b_414_);
lean_dec_ref(v_as_411_);
return v_res_418_;
}
}
lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(lean_object* v_declName_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; lean_object* v_env_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_422_ = lean_st_ref_get(v___y_420_);
v_env_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_env_423_);
lean_dec(v___x_422_);
v___x_424_ = l_Lean_getReducibilityStatusCore(v_env_423_, v_declName_419_);
v___x_425_ = lean_box(v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT void l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_419_ = stack[0].m_obj;
lean_object* v___y_420_ = stack[1].m_obj;
lean_object* v_res_427_;
v_res_427_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_419_, v___y_420_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg___boxed(lean_object* v_declName_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_428_, v___y_429_);
lean_dec(v___y_429_);
return v_res_431_;
}
}
lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(lean_object* v_declName_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_454_; 
v___x_438_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_432_, v___y_436_);
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_454_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_454_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_454_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
uint8_t v___x_443_; 
v___x_443_ = lean_unbox(v_a_439_);
lean_dec(v_a_439_);
if (v___x_443_ == 0)
{
uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_444_ = 1;
v___x_445_ = lean_box(v___x_444_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_445_);
v___x_447_ = v___x_441_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
else
{
uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_449_ = 0;
v___x_450_ = lean_box(v___x_449_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_450_);
v___x_452_ = v___x_441_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_432_ = stack[0].m_obj;
lean_object* v___y_433_ = stack[1].m_obj;
lean_object* v___y_434_ = stack[2].m_obj;
lean_object* v___y_435_ = stack[3].m_obj;
lean_object* v___y_436_ = stack[4].m_obj;
lean_object* v_res_455_;
v_res_455_ = l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(v_declName_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
stack->m_obj
 = v_res_455_;
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0___boxed(lean_object* v_declName_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(v_declName_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_462_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__0));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(lean_object* v_as_x27_466_, lean_object* v_b_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
if (lean_obj_tag(v_as_x27_466_) == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v_b_467_);
return v___x_473_;
}
else
{
lean_object* v_head_474_; lean_object* v_tail_475_; lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v_fst_481_; lean_object* v_snd_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_550_; 
v_head_474_ = lean_ctor_get(v_as_x27_466_, 0);
v_tail_475_ = lean_ctor_get(v_as_x27_466_, 1);
v_fst_481_ = lean_ctor_get(v_b_467_, 0);
v_snd_482_ = lean_ctor_get(v_b_467_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_b_467_);
if (v_isSharedCheck_550_ == 0)
{
v___x_484_ = v_b_467_;
v_isShared_485_ = v_isSharedCheck_550_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_snd_482_);
lean_inc(v_fst_481_);
lean_dec(v_b_467_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_550_;
goto v_resetjp_483_;
}
v___jp_476_:
{
lean_object* v___x_479_; 
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v_fst_477_);
lean_ctor_set(v___x_479_, 1, v_snd_478_);
v_as_x27_466_ = v_tail_475_;
v_b_467_ = v___x_479_;
goto _start;
}
v_resetjp_483_:
{
lean_object* v___x_486_; 
lean_inc(v_head_474_);
v___x_486_ = l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(v_head_474_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_541_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_541_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_541_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_541_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___y_492_; uint8_t v___y_493_; lean_object* v_a_522_; uint8_t v___x_525_; 
v___x_525_ = lean_unbox(v_a_487_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
lean_del_object(v___x_484_);
lean_inc(v_head_474_);
v___x_526_ = l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(v_head_474_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; size_t v_sz_528_; size_t v___x_529_; lean_object* v___x_530_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v_sz_528_ = lean_array_size(v_a_527_);
v___x_529_ = ((size_t)0ULL);
lean_inc(v_fst_481_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_a_527_, v_sz_528_, v___x_529_, v_fst_481_);
lean_dec(v_a_527_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
lean_inc(v_head_474_);
lean_inc(v_snd_482_);
v___x_532_ = l_Lean_Meta_Sym_DSimp_Decls_add(v_snd_482_, v_head_474_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; 
lean_del_object(v___x_489_);
lean_dec(v_a_487_);
lean_dec(v_snd_482_);
lean_dec(v_fst_481_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v_fst_477_ = v_a_531_;
v_snd_478_ = v_a_533_;
goto v___jp_476_;
}
else
{
lean_object* v_a_534_; 
lean_dec(v_a_531_);
v_a_534_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_532_, 1);
v_a_522_ = v_a_534_;
goto v___jp_521_;
}
}
else
{
lean_object* v_a_535_; 
v_a_535_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_530_, 1);
v_a_522_ = v_a_535_;
goto v___jp_521_;
}
}
else
{
lean_object* v_a_536_; 
v_a_536_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___x_526_, 1);
v_a_522_ = v_a_536_;
goto v___jp_521_;
}
}
else
{
lean_object* v___x_538_; 
lean_del_object(v___x_489_);
lean_dec(v_a_487_);
if (v_isShared_485_ == 0)
{
v___x_538_ = v___x_484_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_fst_481_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_snd_482_);
v___x_538_ = v_reuseFailAlloc_540_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
v_as_x27_466_ = v_tail_475_;
v_b_467_ = v___x_538_;
goto _start;
}
}
v___jp_491_:
{
if (v___y_493_ == 0)
{
lean_object* v_toCold_494_; lean_object* v_options_495_; uint8_t v_hasTrace_496_; 
lean_del_object(v___x_489_);
v_toCold_494_ = lean_ctor_get(v___y_470_, 0);
v_options_495_ = lean_ctor_get(v_toCold_494_, 2);
v_hasTrace_496_ = lean_ctor_get_uint8(v_options_495_, sizeof(void*)*1);
if (v_hasTrace_496_ == 0)
{
lean_dec_ref(v___y_492_);
lean_dec(v_a_487_);
v_fst_477_ = v_fst_481_;
v_snd_478_ = v_snd_482_;
goto v___jp_476_;
}
else
{
lean_object* v_inheritedTraceOptions_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_inheritedTraceOptions_497_ = lean_ctor_get(v_toCold_494_, 11);
v___x_498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_499_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2);
v___x_500_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_497_, v_options_495_, v___x_499_);
if (v___x_500_ == 0)
{
lean_dec_ref(v___y_492_);
lean_dec(v_a_487_);
v_fst_477_ = v_fst_481_;
v_snd_478_ = v_snd_482_;
goto v___jp_476_;
}
else
{
lean_object* v___x_501_; uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_501_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1);
v___x_502_ = lean_unbox(v_a_487_);
lean_dec(v_a_487_);
lean_inc(v_head_474_);
v___x_503_ = l_Lean_MessageData_ofConstName(v_head_474_, v___x_502_);
v___x_504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_501_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Lean_Exception_toMessageData(v___y_492_);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v___x_498_, v___x_508_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_dec_ref_known(v___x_509_, 1);
v_fst_477_ = v_fst_481_;
v_snd_478_ = v_snd_482_;
goto v___jp_476_;
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec(v_snd_482_);
lean_dec(v_fst_481_);
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
}
else
{
lean_object* v___x_519_; 
lean_dec(v_a_487_);
lean_dec(v_snd_482_);
lean_dec(v_fst_481_);
if (v_isShared_490_ == 0)
{
lean_ctor_set_tag(v___x_489_, 1);
lean_ctor_set(v___x_489_, 0, v___y_492_);
v___x_519_ = v___x_489_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___y_492_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
v___jp_521_:
{
uint8_t v___x_523_; 
v___x_523_ = l_Lean_Exception_isInterrupt(v_a_522_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; 
lean_inc_ref(v_a_522_);
v___x_524_ = l_Lean_Exception_isRuntime(v_a_522_);
v___y_492_ = v_a_522_;
v___y_493_ = v___x_524_;
goto v___jp_491_;
}
else
{
v___y_492_ = v_a_522_;
v___y_493_ = v___x_523_;
goto v___jp_491_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_del_object(v___x_484_);
lean_dec(v_snd_482_);
lean_dec(v_fst_481_);
v_a_542_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_486_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_486_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_466_ = stack[0].m_obj;
lean_object* v_b_467_ = stack[1].m_obj;
lean_object* v___y_468_ = stack[2].m_obj;
lean_object* v___y_469_ = stack[3].m_obj;
lean_object* v___y_470_ = stack[4].m_obj;
lean_object* v___y_471_ = stack[5].m_obj;
lean_object* v_res_551_;
v_res_551_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(v_as_x27_466_, v_b_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
stack->m_obj
 = v_res_551_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___boxed(lean_object* v_as_x27_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(v_as_x27_552_, v_b_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v_as_x27_552_);
return v_res_559_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(lean_object* v_as_560_, size_t v_sz_561_, size_t v_i_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_a_570_; uint8_t v___x_574_; 
v___x_574_ = lean_usize_dec_lt(v_i_562_, v_sz_561_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v_b_563_);
return v___x_575_;
}
else
{
lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_616_; 
v_fst_576_ = lean_ctor_get(v_b_563_, 0);
v_snd_577_ = lean_ctor_get(v_b_563_, 1);
v_isSharedCheck_616_ = !lean_is_exclusive(v_b_563_);
if (v_isSharedCheck_616_ == 0)
{
v___x_579_ = v_b_563_;
v_isShared_580_ = v_isSharedCheck_616_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snd_577_);
lean_inc(v_fst_576_);
lean_dec(v_b_563_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_616_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_array_uget_borrowed(v_as_560_, v_i_562_);
lean_inc(v_a_581_);
v___x_582_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_fst_576_, v_a_581_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_582_) == 0)
{
uint8_t v_rfl_583_; 
v_rfl_583_ = lean_ctor_get_uint8(v_a_581_, sizeof(void*)*5 + 2);
if (v_rfl_583_ == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; 
v_a_584_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_582_, 1);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v_a_584_);
v___x_586_ = v___x_579_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_584_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_snd_577_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v_a_570_ = v___x_586_;
goto v___jp_569_;
}
}
else
{
lean_object* v_proof_588_; 
v_proof_588_ = lean_ctor_get(v_a_581_, 2);
if (lean_obj_tag(v_proof_588_) == 4)
{
lean_object* v_a_589_; lean_object* v_declName_590_; lean_object* v___x_591_; 
v_a_589_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_582_, 1);
v_declName_590_ = lean_ctor_get(v_proof_588_, 0);
lean_inc(v_declName_590_);
v___x_591_ = l_Lean_Meta_Sym_DSimp_Decls_add(v_snd_577_, v_declName_590_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v_a_592_);
lean_ctor_set(v___x_579_, 0, v_a_589_);
v___x_594_ = v___x_579_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_a_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
v_a_570_ = v___x_594_;
goto v___jp_569_;
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_a_589_);
lean_del_object(v___x_579_);
v_a_596_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_591_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_591_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; 
v_a_604_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_582_, 1);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v_a_604_);
v___x_606_ = v___x_579_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_604_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_snd_577_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
v_a_570_ = v___x_606_;
goto v___jp_569_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_del_object(v___x_579_);
lean_dec(v_snd_577_);
v_a_608_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_582_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_582_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
v___jp_569_:
{
size_t v___x_571_; size_t v___x_572_; 
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_562_, v___x_571_);
v_i_562_ = v___x_572_;
v_b_563_ = v_a_570_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_560_ = stack[0].m_obj;
size_t v_sz_561_ = stack[1].m_num;
size_t v_i_562_ = stack[2].m_num;
lean_object* v_b_563_ = stack[3].m_obj;
lean_object* v___y_564_ = stack[4].m_obj;
lean_object* v___y_565_ = stack[5].m_obj;
lean_object* v___y_566_ = stack[6].m_obj;
lean_object* v___y_567_ = stack[7].m_obj;
lean_object* v_res_617_;
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(v_as_560_, v_sz_561_, v_i_562_, v_b_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
stack->m_obj
 = v_res_617_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6___boxed(lean_object* v_as_618_, lean_object* v_sz_619_, lean_object* v_i_620_, lean_object* v_b_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
size_t v_sz_boxed_627_; size_t v_i_boxed_628_; lean_object* v_res_629_; 
v_sz_boxed_627_ = lean_unbox_usize(v_sz_619_);
lean_dec(v_sz_619_);
v_i_boxed_628_ = lean_unbox_usize(v_i_620_);
lean_dec(v_i_620_);
v_res_629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(v_as_618_, v_sz_boxed_627_, v_i_boxed_628_, v_b_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec_ref(v_as_618_);
return v_res_629_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(lean_object* v_as_630_, size_t v_sz_631_, size_t v_i_632_, lean_object* v_b_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_lt(v_i_632_, v_sz_631_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v_b_633_);
return v___x_640_;
}
else
{
lean_object* v_a_641_; lean_object* v___x_642_; 
v_a_641_ = lean_array_uget_borrowed(v_as_630_, v_i_632_);
lean_inc(v_a_641_);
v___x_642_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_b_633_, v_a_641_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; size_t v___x_644_; size_t v___x_645_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_add(v_i_632_, v___x_644_);
v_i_632_ = v___x_645_;
v_b_633_ = v_a_643_;
goto _start;
}
else
{
return v___x_642_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_630_ = stack[0].m_obj;
size_t v_sz_631_ = stack[1].m_num;
size_t v_i_632_ = stack[2].m_num;
lean_object* v_b_633_ = stack[3].m_obj;
lean_object* v___y_634_ = stack[4].m_obj;
lean_object* v___y_635_ = stack[5].m_obj;
lean_object* v___y_636_ = stack[6].m_obj;
lean_object* v___y_637_ = stack[7].m_obj;
lean_object* v_res_647_;
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(v_as_630_, v_sz_631_, v_i_632_, v_b_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
stack->m_obj
 = v_res_647_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4___boxed(lean_object* v_as_648_, lean_object* v_sz_649_, lean_object* v_i_650_, lean_object* v_b_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
size_t v_sz_boxed_657_; size_t v_i_boxed_658_; lean_object* v_res_659_; 
v_sz_boxed_657_ = lean_unbox_usize(v_sz_649_);
lean_dec(v_sz_649_);
v_i_boxed_658_ = lean_unbox_usize(v_i_650_);
lean_dec(v_i_650_);
v_res_659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(v_as_648_, v_sz_boxed_657_, v_i_boxed_658_, v_b_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec_ref(v_as_648_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__12(lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
if (lean_obj_tag(v_a_660_) == 0)
{
lean_object* v___x_662_; 
v___x_662_ = l_List_reverse___redArg(v_a_661_);
return v___x_662_;
}
else
{
lean_object* v_head_663_; lean_object* v_tail_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_673_; 
v_head_663_ = lean_ctor_get(v_a_660_, 0);
v_tail_664_ = lean_ctor_get(v_a_660_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_a_660_);
if (v_isSharedCheck_673_ == 0)
{
v___x_666_ = v_a_660_;
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_tail_664_);
lean_inc(v_head_663_);
lean_dec(v_a_660_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_673_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_fst_668_; lean_object* v___x_670_; 
v_fst_668_ = lean_ctor_get(v_head_663_, 0);
lean_inc(v_fst_668_);
lean_dec(v_head_663_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v_a_661_);
lean_ctor_set(v___x_666_, 0, v_fst_668_);
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_fst_668_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_a_661_);
v___x_670_ = v_reuseFailAlloc_672_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
v_a_660_ = v_tail_664_;
v_a_661_ = v___x_670_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg___lam__0(lean_object* v_f_674_, lean_object* v_x1_675_, lean_object* v_x2_676_, lean_object* v_x3_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_apply_3(v_f_674_, v_x1_675_, v_x2_676_, v_x3_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(lean_object* v_f_679_, lean_object* v_keys_680_, lean_object* v_vals_681_, lean_object* v_i_682_, lean_object* v_acc_683_){
_start:
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_array_get_size(v_keys_680_);
v___x_685_ = lean_nat_dec_lt(v_i_682_, v___x_684_);
if (v___x_685_ == 0)
{
lean_dec(v_i_682_);
lean_dec(v_f_679_);
return v_acc_683_;
}
else
{
lean_object* v_k_686_; lean_object* v_v_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_k_686_ = lean_array_fget_borrowed(v_keys_680_, v_i_682_);
v_v_687_ = lean_array_fget_borrowed(v_vals_681_, v_i_682_);
lean_inc(v_f_679_);
lean_inc(v_v_687_);
lean_inc(v_k_686_);
v___x_688_ = lean_apply_3(v_f_679_, v_acc_683_, v_k_686_, v_v_687_);
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_nat_add(v_i_682_, v___x_689_);
lean_dec(v_i_682_);
v_i_682_ = v___x_690_;
v_acc_683_ = v___x_688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_f_692_, lean_object* v_keys_693_, lean_object* v_vals_694_, lean_object* v_i_695_, lean_object* v_acc_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_692_, v_keys_693_, v_vals_694_, v_i_695_, v_acc_696_);
lean_dec_ref(v_vals_694_);
lean_dec_ref(v_keys_693_);
return v_res_697_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(lean_object* v_f_698_, lean_object* v_as_699_, size_t v_i_700_, size_t v_stop_701_, lean_object* v_b_702_){
_start:
{
lean_object* v___y_704_; uint8_t v___x_708_; 
v___x_708_ = lean_usize_dec_eq(v_i_700_, v_stop_701_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
v___x_709_ = lean_array_uget_borrowed(v_as_699_, v_i_700_);
switch(lean_obj_tag(v___x_709_))
{
case 0:
{
lean_object* v_key_710_; lean_object* v_val_711_; lean_object* v___x_712_; 
v_key_710_ = lean_ctor_get(v___x_709_, 0);
v_val_711_ = lean_ctor_get(v___x_709_, 1);
lean_inc(v_f_698_);
lean_inc(v_val_711_);
lean_inc(v_key_710_);
v___x_712_ = lean_apply_3(v_f_698_, v_b_702_, v_key_710_, v_val_711_);
v___y_704_ = v___x_712_;
goto v___jp_703_;
}
case 1:
{
lean_object* v_node_713_; lean_object* v___x_714_; 
v_node_713_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_f_698_);
v___x_714_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_698_, v_node_713_, v_b_702_);
v___y_704_ = v___x_714_;
goto v___jp_703_;
}
default: 
{
v___y_704_ = v_b_702_;
goto v___jp_703_;
}
}
}
else
{
lean_dec(v_f_698_);
return v_b_702_;
}
v___jp_703_:
{
size_t v___x_705_; size_t v___x_706_; 
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_add(v_i_700_, v___x_705_);
v_i_700_ = v___x_706_;
v_b_702_ = v___y_704_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_698_ = stack[0].m_obj;
lean_object* v_as_699_ = stack[1].m_obj;
size_t v_i_700_ = stack[2].m_num;
size_t v_stop_701_ = stack[3].m_num;
lean_object* v_b_702_ = stack[4].m_obj;
lean_object* v_res_715_;
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_698_, v_as_699_, v_i_700_, v_stop_701_, v_b_702_);
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(lean_object* v_f_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
if (lean_obj_tag(v_x_717_) == 0)
{
lean_object* v_es_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_es_719_ = lean_ctor_get(v_x_717_, 0);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_array_get_size(v_es_719_);
v___x_722_ = lean_nat_dec_lt(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_dec(v_f_716_);
return v_x_718_;
}
else
{
size_t v___x_723_; size_t v___x_724_; lean_object* v___x_725_; 
v___x_723_ = ((size_t)0ULL);
v___x_724_ = lean_usize_of_nat(v___x_721_);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_716_, v_es_719_, v___x_723_, v___x_724_, v_x_718_);
return v___x_725_;
}
}
else
{
lean_object* v_ks_726_; lean_object* v_vs_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_ks_726_ = lean_ctor_get(v_x_717_, 0);
v_vs_727_ = lean_ctor_get(v_x_717_, 1);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_716_, v_ks_726_, v_vs_727_, v___x_728_, v_x_718_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg___boxed(lean_object* v_f_730_, lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_730_, v_x_731_, v_x_732_);
lean_dec_ref(v_x_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v_f_734_, lean_object* v_as_735_, lean_object* v_i_736_, lean_object* v_stop_737_, lean_object* v_b_738_){
_start:
{
size_t v_i_boxed_739_; size_t v_stop_boxed_740_; lean_object* v_res_741_; 
v_i_boxed_739_ = lean_unbox_usize(v_i_736_);
lean_dec(v_i_736_);
v_stop_boxed_740_ = lean_unbox_usize(v_stop_737_);
lean_dec(v_stop_737_);
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_734_, v_as_735_, v_i_boxed_739_, v_stop_boxed_740_, v_b_738_);
lean_dec_ref(v_as_735_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(lean_object* v_map_742_, lean_object* v_f_743_, lean_object* v_init_744_){
_start:
{
lean_object* v___f_745_; lean_object* v___x_746_; 
v___f_745_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg___lam__0), 4, 1);
lean_closure_set(v___f_745_, 0, v_f_743_);
v___x_746_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_745_, v_map_742_, v_init_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg___boxed(lean_object* v_map_747_, lean_object* v_f_748_, lean_object* v_init_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(v_map_747_, v_f_748_, v_init_749_);
lean_dec_ref(v_map_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___lam__0(lean_object* v_ps_751_, lean_object* v_k_752_, lean_object* v_v_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_k_752_);
lean_ctor_set(v___x_754_, 1, v_v_753_);
v___x_755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v_ps_751_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(lean_object* v_m_757_){
_start:
{
lean_object* v___f_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___f_758_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___closed__0));
v___x_759_ = lean_box(0);
v___x_760_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(v_m_757_, v___f_758_, v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___boxed(lean_object* v_m_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(v_m_761_);
lean_dec_ref(v_m_761_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(lean_object* v_s_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(v_s_763_);
v___x_765_ = lean_box(0);
v___x_766_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__12(v___x_764_, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___boxed(lean_object* v_s_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(v_s_767_);
lean_dec_ref(v_s_767_);
return v_res_768_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(lean_object* v_as_x27_769_, lean_object* v_b_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
if (lean_obj_tag(v_as_x27_769_) == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_b_770_);
return v___x_776_;
}
else
{
lean_object* v_head_777_; lean_object* v_tail_778_; lean_object* v___x_779_; 
v_head_777_ = lean_ctor_get(v_as_x27_769_, 0);
v_tail_778_ = lean_ctor_get(v_as_x27_769_, 1);
lean_inc(v_head_777_);
v___x_779_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_head_777_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_781_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_779_, 1);
v___x_781_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_770_, v_a_780_);
v_as_x27_769_ = v_tail_778_;
v_b_770_ = v___x_781_;
goto _start;
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v_b_770_);
v_a_783_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_779_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_769_ = stack[0].m_obj;
lean_object* v_b_770_ = stack[1].m_obj;
lean_object* v___y_771_ = stack[2].m_obj;
lean_object* v___y_772_ = stack[3].m_obj;
lean_object* v___y_773_ = stack[4].m_obj;
lean_object* v___y_774_ = stack[5].m_obj;
lean_object* v_res_791_;
v_res_791_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v_as_x27_769_, v_b_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg___boxed(lean_object* v_as_x27_792_, lean_object* v_b_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v_as_x27_792_, v_b_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v_as_x27_792_);
return v_res_799_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1(void){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_801_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__2(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__1, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__1_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__2, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__2_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__2);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__12(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = l_Lean_NameSet_empty;
v___x_824_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__3, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__3_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v___x_823_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__13(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__12, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__12_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__12);
v___x_827_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__3, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__3_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_826_);
return v___x_828_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymTheorems(lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___f_834_; lean_object* v___x_835_; 
v___f_834_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__0));
v___x_835_ = l_Lean_Meta_Grind_getNormTheorems(v_a_829_, v_a_830_, v_a_831_, v_a_832_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_837_; lean_object* v_pre_838_; lean_object* v_post_839_; lean_object* v_toUnfold_840_; lean_object* v___x_841_; lean_object* v___x_842_; size_t v_sz_843_; size_t v___x_844_; lean_object* v___x_845_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
v___x_837_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__3, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__3_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3);
v_pre_838_ = lean_ctor_get(v_a_836_, 0);
lean_inc_ref(v_pre_838_);
v_post_839_ = lean_ctor_get(v_a_836_, 1);
lean_inc_ref(v_post_839_);
v_toUnfold_840_ = lean_ctor_get(v_a_836_, 3);
lean_inc_ref(v_toUnfold_840_);
lean_dec(v_a_836_);
v___x_841_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__4));
v___x_842_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_834_, v_pre_838_, v___x_841_);
lean_dec_ref(v_pre_838_);
v_sz_843_ = lean_array_size(v___x_842_);
v___x_844_ = ((size_t)0ULL);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(v___x_842_, v_sz_843_, v___x_844_, v___x_837_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v___x_842_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
v___x_847_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__11));
v___x_848_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v___x_847_, v_a_846_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; lean_object* v___x_851_; size_t v_sz_852_; lean_object* v___x_853_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_850_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_834_, v_post_839_, v___x_841_);
lean_dec_ref(v_post_839_);
v___x_851_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__13, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__13_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__13);
v_sz_852_ = lean_array_size(v___x_850_);
v___x_853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(v___x_850_, v_sz_852_, v___x_844_, v___x_851_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v___x_850_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v_fst_855_; lean_object* v_snd_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_884_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v_fst_855_ = lean_ctor_get(v_a_854_, 0);
v_snd_856_ = lean_ctor_get(v_a_854_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_a_854_);
if (v_isSharedCheck_884_ == 0)
{
v___x_858_ = v_a_854_;
v_isShared_859_ = v_isSharedCheck_884_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_snd_856_);
lean_inc(v_fst_855_);
lean_dec(v_a_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_884_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_860_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(v_toUnfold_840_);
lean_dec_ref(v_toUnfold_840_);
if (v_isShared_859_ == 0)
{
v___x_862_ = v___x_858_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_fst_855_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_snd_856_);
v___x_862_ = v_reuseFailAlloc_883_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; 
v___x_863_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(v___x_860_, v___x_862_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v___x_860_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_874_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_874_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_fst_868_; lean_object* v_snd_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v_fst_868_ = lean_ctor_get(v_a_864_, 0);
lean_inc(v_fst_868_);
v_snd_869_ = lean_ctor_get(v_a_864_, 1);
lean_inc(v_snd_869_);
lean_dec(v_a_864_);
v___x_870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_870_, 0, v_a_849_);
lean_ctor_set(v___x_870_, 1, v_fst_868_);
lean_ctor_set(v___x_870_, 2, v_snd_869_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_870_);
v___x_872_ = v___x_866_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_a_849_);
v_a_875_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_863_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_863_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_a_849_);
lean_dec_ref(v_toUnfold_840_);
v_a_885_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_853_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_853_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v_toUnfold_840_);
lean_dec_ref(v_post_839_);
v_a_893_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_848_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_848_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_toUnfold_840_);
lean_dec_ref(v_post_839_);
v_a_901_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_845_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_845_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_909_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_835_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_835_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymTheorems_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_829_ = stack[0].m_obj;
lean_object* v_a_830_ = stack[1].m_obj;
lean_object* v_a_831_ = stack[2].m_obj;
lean_object* v_a_832_ = stack[3].m_obj;
lean_object* v_res_917_;
v_res_917_ = l_Lean_Meta_Grind_mkNormSymTheorems(v_a_829_, v_a_830_, v_a_831_, v_a_832_);
stack->m_obj
 = v_res_917_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___boxed(lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Meta_Grind_mkNormSymTheorems(v_a_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
return v_res_923_;
}
}
lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0(lean_object* v_declName_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_924_, v___y_928_);
return v___x_930_;
}
}
LEAN_EXPORT void l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_924_ = stack[0].m_obj;
lean_object* v___y_925_ = stack[1].m_obj;
lean_object* v___y_926_ = stack[2].m_obj;
lean_object* v___y_927_ = stack[3].m_obj;
lean_object* v___y_928_ = stack[4].m_obj;
lean_object* v_res_931_;
v_res_931_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0(v_declName_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
stack->m_obj
 = v_res_931_;
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___boxed(lean_object* v_declName_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0(v_declName_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_938_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1(lean_object* v_as_939_, size_t v_sz_940_, size_t v_i_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_as_939_, v_sz_940_, v_i_941_, v_b_942_);
return v___x_948_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_939_ = stack[0].m_obj;
size_t v_sz_940_ = stack[1].m_num;
size_t v_i_941_ = stack[2].m_num;
lean_object* v_b_942_ = stack[3].m_obj;
lean_object* v___y_943_ = stack[4].m_obj;
lean_object* v___y_944_ = stack[5].m_obj;
lean_object* v___y_945_ = stack[6].m_obj;
lean_object* v___y_946_ = stack[7].m_obj;
lean_object* v_res_949_;
v_res_949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1(v_as_939_, v_sz_940_, v_i_941_, v_b_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
stack->m_obj
 = v_res_949_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___boxed(lean_object* v_as_950_, lean_object* v_sz_951_, lean_object* v_i_952_, lean_object* v_b_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
size_t v_sz_boxed_959_; size_t v_i_boxed_960_; lean_object* v_res_961_; 
v_sz_boxed_959_ = lean_unbox_usize(v_sz_951_);
lean_dec(v_sz_951_);
v_i_boxed_960_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1(v_as_950_, v_sz_boxed_959_, v_i_boxed_960_, v_b_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec_ref(v_as_950_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg(lean_object* v_map_962_, lean_object* v_f_963_, lean_object* v_init_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_963_, v_map_962_, v_init_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg___boxed(lean_object* v_map_966_, lean_object* v_f_967_, lean_object* v_init_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg(v_map_966_, v_f_967_, v_init_968_);
lean_dec_ref(v_map_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3(lean_object* v_00_u03c3_970_, lean_object* v_00_u03b2_971_, lean_object* v_map_972_, lean_object* v_f_973_, lean_object* v_init_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_973_, v_map_972_, v_init_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___boxed(lean_object* v_00_u03c3_976_, lean_object* v_00_u03b2_977_, lean_object* v_map_978_, lean_object* v_f_979_, lean_object* v_init_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3(v_00_u03c3_976_, v_00_u03b2_977_, v_map_978_, v_f_979_, v_init_980_);
lean_dec_ref(v_map_978_);
return v_res_981_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5(lean_object* v_as_982_, lean_object* v_as_x27_983_, lean_object* v_b_984_, lean_object* v_a_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v_as_x27_983_, v_b_984_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
return v___x_991_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_982_ = stack[0].m_obj;
lean_object* v_as_x27_983_ = stack[1].m_obj;
lean_object* v_b_984_ = stack[2].m_obj;
lean_object* v___y_986_ = stack[4].m_obj;
lean_object* v___y_987_ = stack[5].m_obj;
lean_object* v___y_988_ = stack[6].m_obj;
lean_object* v___y_989_ = stack[7].m_obj;
lean_object* v_res_992_;
v_res_992_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5(v_as_982_, v_as_x27_983_, v_b_984_, lean_box(0), v___y_986_, v___y_987_, v___y_988_, v___y_989_);
stack->m_obj
 = v_res_992_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___boxed(lean_object* v_as_993_, lean_object* v_as_x27_994_, lean_object* v_b_995_, lean_object* v_a_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5(v_as_993_, v_as_x27_994_, v_b_995_, v_a_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v_as_x27_994_);
lean_dec(v_as_993_);
return v_res_1002_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8(lean_object* v_as_1003_, lean_object* v_as_x27_1004_, lean_object* v_b_1005_, lean_object* v_a_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(v_as_x27_1004_, v_b_1005_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1003_ = stack[0].m_obj;
lean_object* v_as_x27_1004_ = stack[1].m_obj;
lean_object* v_b_1005_ = stack[2].m_obj;
lean_object* v___y_1007_ = stack[4].m_obj;
lean_object* v___y_1008_ = stack[5].m_obj;
lean_object* v___y_1009_ = stack[6].m_obj;
lean_object* v___y_1010_ = stack[7].m_obj;
lean_object* v_res_1013_;
v_res_1013_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8(v_as_1003_, v_as_x27_1004_, v_b_1005_, lean_box(0), v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
stack->m_obj
 = v_res_1013_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___boxed(lean_object* v_as_1014_, lean_object* v_as_x27_1015_, lean_object* v_b_1016_, lean_object* v_a_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8(v_as_1014_, v_as_x27_1015_, v_b_1016_, v_a_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v_as_x27_1015_);
lean_dec(v_as_1014_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6(lean_object* v_00_u03c3_1024_, lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_f_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_1027_, v_x_1028_, v_x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1031_, lean_object* v_00_u03b1_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_f_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6(v_00_u03c3_1031_, v_00_u03b1_1032_, v_00_u03b2_1033_, v_f_1034_, v_x_1035_, v_x_1036_);
lean_dec_ref(v_x_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11(lean_object* v_00_u03b2_1038_, lean_object* v_m_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(v_m_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1041_, lean_object* v_m_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11(v_00_u03b2_1041_, v_m_1042_);
lean_dec_ref(v_m_1042_);
return v_res_1043_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7(lean_object* v_00_u03b1_1044_, lean_object* v_00_u03b2_1045_, lean_object* v_00_u03c3_1046_, lean_object* v_f_1047_, lean_object* v_as_1048_, size_t v_i_1049_, size_t v_stop_1050_, lean_object* v_b_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_1047_, v_as_1048_, v_i_1049_, v_stop_1050_, v_b_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1047_ = stack[3].m_obj;
lean_object* v_as_1048_ = stack[4].m_obj;
size_t v_i_1049_ = stack[5].m_num;
size_t v_stop_1050_ = stack[6].m_num;
lean_object* v_b_1051_ = stack[7].m_obj;
lean_object* v_res_1053_;
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7(lean_box(0), lean_box(0), lean_box(0), v_f_1047_, v_as_1048_, v_i_1049_, v_stop_1050_, v_b_1051_);
stack->m_obj
 = v_res_1053_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___boxed(lean_object* v_00_u03b1_1054_, lean_object* v_00_u03b2_1055_, lean_object* v_00_u03c3_1056_, lean_object* v_f_1057_, lean_object* v_as_1058_, lean_object* v_i_1059_, lean_object* v_stop_1060_, lean_object* v_b_1061_){
_start:
{
size_t v_i_boxed_1062_; size_t v_stop_boxed_1063_; lean_object* v_res_1064_; 
v_i_boxed_1062_ = lean_unbox_usize(v_i_1059_);
lean_dec(v_i_1059_);
v_stop_boxed_1063_ = lean_unbox_usize(v_stop_1060_);
lean_dec(v_stop_1060_);
v_res_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7(v_00_u03b1_1054_, v_00_u03b2_1055_, v_00_u03c3_1056_, v_f_1057_, v_as_1058_, v_i_boxed_1062_, v_stop_boxed_1063_, v_b_1061_);
lean_dec_ref(v_as_1058_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8(lean_object* v_00_u03c3_1065_, lean_object* v_00_u03b1_1066_, lean_object* v_00_u03b2_1067_, lean_object* v_f_1068_, lean_object* v_keys_1069_, lean_object* v_vals_1070_, lean_object* v_heq_1071_, lean_object* v_i_1072_, lean_object* v_acc_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_1068_, v_keys_1069_, v_vals_1070_, v_i_1072_, v_acc_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03c3_1075_, lean_object* v_00_u03b1_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_f_1078_, lean_object* v_keys_1079_, lean_object* v_vals_1080_, lean_object* v_heq_1081_, lean_object* v_i_1082_, lean_object* v_acc_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8(v_00_u03c3_1075_, v_00_u03b1_1076_, v_00_u03b2_1077_, v_f_1078_, v_keys_1079_, v_vals_1080_, v_heq_1081_, v_i_1082_, v_acc_1083_);
lean_dec_ref(v_vals_1080_);
lean_dec_ref(v_keys_1079_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14(lean_object* v_00_u03c3_1085_, lean_object* v_00_u03b2_1086_, lean_object* v_map_1087_, lean_object* v_f_1088_, lean_object* v_init_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(v_map_1087_, v_f_1088_, v_init_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___boxed(lean_object* v_00_u03c3_1091_, lean_object* v_00_u03b2_1092_, lean_object* v_map_1093_, lean_object* v_f_1094_, lean_object* v_init_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14(v_00_u03c3_1091_, v_00_u03b2_1092_, v_map_1093_, v_f_1094_, v_init_1095_);
lean_dec_ref(v_map_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___redArg(lean_object* v_map_1097_, lean_object* v_f_1098_, lean_object* v_init_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_1098_, v_map_1097_, v_init_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___redArg___boxed(lean_object* v_map_1101_, lean_object* v_f_1102_, lean_object* v_init_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___redArg(v_map_1101_, v_f_1102_, v_init_1103_);
lean_dec_ref(v_map_1101_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16(lean_object* v_00_u03c3_1105_, lean_object* v_00_u03b2_1106_, lean_object* v_map_1107_, lean_object* v_f_1108_, lean_object* v_init_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_1108_, v_map_1107_, v_init_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___boxed(lean_object* v_00_u03c3_1111_, lean_object* v_00_u03b2_1112_, lean_object* v_map_1113_, lean_object* v_f_1114_, lean_object* v_init_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16(v_00_u03c3_1111_, v_00_u03b2_1112_, v_map_1113_, v_f_1114_, v_init_1115_);
lean_dec_ref(v_map_1113_);
return v_res_1116_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0(lean_object* v_x_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; 
lean_inc_ref(v___y_1118_);
v___x_1129_ = l_Lean_Meta_Sym_Simp_reduceProj___redArg(v___y_1118_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
if (lean_obj_tag(v_a_1130_) == 0)
{
uint8_t v_done_1131_; 
v_done_1131_ = lean_ctor_get_uint8(v_a_1130_, 0);
if (v_done_1131_ == 0)
{
uint8_t v_contextDependent_1132_; lean_object* v___x_1133_; 
lean_dec_ref_known(v___x_1129_, 1);
v_contextDependent_1132_ = lean_ctor_get_uint8(v_a_1130_, 1);
lean_dec_ref_known(v_a_1130_, 0);
v___x_1133_ = l_Lean_Meta_Sym_Simp_reduceControl(v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; uint8_t v___y_1136_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
if (v_contextDependent_1132_ == 0)
{
return v___x_1133_;
}
else
{
if (lean_obj_tag(v_a_1134_) == 0)
{
uint8_t v_contextDependent_1146_; 
v_contextDependent_1146_ = lean_ctor_get_uint8(v_a_1134_, 1);
v___y_1136_ = v_contextDependent_1146_;
goto v___jp_1135_;
}
else
{
uint8_t v_contextDependent_1147_; 
v_contextDependent_1147_ = lean_ctor_get_uint8(v_a_1134_, sizeof(void*)*2 + 1);
v___y_1136_ = v_contextDependent_1147_;
goto v___jp_1135_;
}
}
v___jp_1135_:
{
if (v___y_1136_ == 0)
{
lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1144_; 
lean_inc(v_a_1134_);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1133_, 0);
lean_dec(v_unused_1145_);
v___x_1138_ = v___x_1133_;
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
else
{
lean_dec(v___x_1133_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1134_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
return v___x_1133_;
}
}
}
else
{
return v___x_1133_;
}
}
else
{
lean_dec_ref_known(v_a_1130_, 0);
lean_dec_ref(v___y_1118_);
return v___x_1129_;
}
}
else
{
uint8_t v_done_1148_; 
v_done_1148_ = lean_ctor_get_uint8(v_a_1130_, sizeof(void*)*2);
if (v_done_1148_ == 0)
{
lean_object* v_e_x27_1149_; lean_object* v_proof_1150_; uint8_t v_contextDependent_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref_known(v___x_1129_, 1);
v_e_x27_1149_ = lean_ctor_get(v_a_1130_, 0);
v_proof_1150_ = lean_ctor_get(v_a_1130_, 1);
v_contextDependent_1151_ = lean_ctor_get_uint8(v_a_1130_, sizeof(void*)*2 + 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_a_1130_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1153_ = v_a_1130_;
v_isShared_1154_ = v_isSharedCheck_1201_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_proof_1150_);
lean_inc(v_e_x27_1149_);
lean_dec(v_a_1130_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1201_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; 
lean_inc_ref(v_e_x27_1149_);
v___x_1155_ = l_Lean_Meta_Sym_Simp_reduceControl(v_e_x27_1149_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1200_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1200_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1200_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
if (lean_obj_tag(v_a_1156_) == 0)
{
uint8_t v_done_1160_; uint8_t v_contextDependent_1161_; uint8_t v___y_1163_; 
lean_dec_ref(v___y_1118_);
v_done_1160_ = lean_ctor_get_uint8(v_a_1156_, 0);
v_contextDependent_1161_ = lean_ctor_get_uint8(v_a_1156_, 1);
lean_dec_ref_known(v_a_1156_, 0);
if (v_contextDependent_1151_ == 0)
{
v___y_1163_ = v_contextDependent_1161_;
goto v___jp_1162_;
}
else
{
v___y_1163_ = v_contextDependent_1151_;
goto v___jp_1162_;
}
v___jp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1154_ == 0)
{
v___x_1165_ = v___x_1153_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_e_x27_1149_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_proof_1150_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
lean_ctor_set_uint8(v___x_1165_, sizeof(void*)*2, v_done_1160_);
lean_ctor_set_uint8(v___x_1165_, sizeof(void*)*2 + 1, v___y_1163_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1165_);
v___x_1167_ = v___x_1158_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
else
{
lean_object* v_e_x27_1170_; lean_object* v_proof_1171_; uint8_t v_done_1172_; uint8_t v_contextDependent_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1199_; 
lean_del_object(v___x_1158_);
lean_del_object(v___x_1153_);
v_e_x27_1170_ = lean_ctor_get(v_a_1156_, 0);
v_proof_1171_ = lean_ctor_get(v_a_1156_, 1);
v_done_1172_ = lean_ctor_get_uint8(v_a_1156_, sizeof(void*)*2);
v_contextDependent_1173_ = lean_ctor_get_uint8(v_a_1156_, sizeof(void*)*2 + 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_a_1156_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1175_ = v_a_1156_;
v_isShared_1176_ = v_isSharedCheck_1199_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_proof_1171_);
lean_inc(v_e_x27_1170_);
lean_dec(v_a_1156_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1199_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; 
lean_inc_ref(v_e_x27_1170_);
v___x_1177_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1118_, v_e_x27_1149_, v_proof_1150_, v_e_x27_1170_, v_proof_1171_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1190_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1190_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1190_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
uint8_t v___y_1183_; 
if (v_contextDependent_1151_ == 0)
{
v___y_1183_ = v_contextDependent_1173_;
goto v___jp_1182_;
}
else
{
v___y_1183_ = v_contextDependent_1151_;
goto v___jp_1182_;
}
v___jp_1182_:
{
lean_object* v___x_1185_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_a_1178_);
v___x_1185_ = v___x_1175_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_e_x27_1170_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_a_1178_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, sizeof(void*)*2, v_done_1172_);
v___x_1185_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*2 + 1, v___y_1183_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1185_);
v___x_1187_ = v___x_1180_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_del_object(v___x_1175_);
lean_dec_ref(v_e_x27_1170_);
v_a_1191_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1177_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1177_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1153_);
lean_dec_ref(v_proof_1150_);
lean_dec_ref(v_e_x27_1149_);
lean_dec_ref(v___y_1118_);
return v___x_1155_;
}
}
}
else
{
lean_dec_ref_known(v_a_1130_, 2);
lean_dec_ref(v___y_1118_);
return v___x_1129_;
}
}
}
else
{
lean_dec_ref(v___y_1118_);
return v___x_1129_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1117_ = stack[0].m_obj;
lean_object* v___y_1118_ = stack[1].m_obj;
lean_object* v___y_1119_ = stack[2].m_obj;
lean_object* v___y_1120_ = stack[3].m_obj;
lean_object* v___y_1121_ = stack[4].m_obj;
lean_object* v___y_1122_ = stack[5].m_obj;
lean_object* v___y_1123_ = stack[6].m_obj;
lean_object* v___y_1124_ = stack[7].m_obj;
lean_object* v___y_1125_ = stack[8].m_obj;
lean_object* v___y_1126_ = stack[9].m_obj;
lean_object* v___y_1127_ = stack[10].m_obj;
lean_object* v_res_1202_;
v_res_1202_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__0(v_x_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
stack->m_obj
 = v_res_1202_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0___boxed(lean_object* v_x_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__0(v_x_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
return v_res_1215_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1(lean_object* v___f_1216_, lean_object* v_x_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_box(0);
lean_inc_ref(v___y_1218_);
v___x_1230_ = l_Lean_Meta_Sym_Simp_beta___redArg(v___y_1218_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_a_1231_);
if (lean_obj_tag(v_a_1231_) == 0)
{
uint8_t v_done_1232_; 
v_done_1232_ = lean_ctor_get_uint8(v_a_1231_, 0);
if (v_done_1232_ == 0)
{
uint8_t v_contextDependent_1233_; lean_object* v___x_1234_; 
lean_dec_ref_known(v___x_1230_, 1);
v_contextDependent_1233_ = lean_ctor_get_uint8(v_a_1231_, 1);
lean_dec_ref_known(v_a_1231_, 0);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
lean_inc(v___y_1219_);
v___x_1234_ = lean_apply_12(v___f_1216_, v___x_1229_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, lean_box(0));
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; uint8_t v___y_1237_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
if (v_contextDependent_1233_ == 0)
{
lean_dec(v_a_1235_);
return v___x_1234_;
}
else
{
if (lean_obj_tag(v_a_1235_) == 0)
{
uint8_t v_contextDependent_1247_; 
v_contextDependent_1247_ = lean_ctor_get_uint8(v_a_1235_, 1);
v___y_1237_ = v_contextDependent_1247_;
goto v___jp_1236_;
}
else
{
uint8_t v_contextDependent_1248_; 
v_contextDependent_1248_ = lean_ctor_get_uint8(v_a_1235_, sizeof(void*)*2 + 1);
v___y_1237_ = v_contextDependent_1248_;
goto v___jp_1236_;
}
}
v___jp_1236_:
{
if (v___y_1237_ == 0)
{
lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v___x_1234_, 0);
lean_dec(v_unused_1246_);
v___x_1239_ = v___x_1234_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_dec(v___x_1234_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1235_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1241_);
v___x_1243_ = v___x_1239_;
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
else
{
lean_dec(v_a_1235_);
return v___x_1234_;
}
}
}
else
{
return v___x_1234_;
}
}
else
{
lean_dec_ref_known(v_a_1231_, 0);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___f_1216_);
return v___x_1230_;
}
}
else
{
uint8_t v_done_1249_; 
v_done_1249_ = lean_ctor_get_uint8(v_a_1231_, sizeof(void*)*2);
if (v_done_1249_ == 0)
{
lean_object* v_e_x27_1250_; lean_object* v_proof_1251_; uint8_t v_contextDependent_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref_known(v___x_1230_, 1);
v_e_x27_1250_ = lean_ctor_get(v_a_1231_, 0);
v_proof_1251_ = lean_ctor_get(v_a_1231_, 1);
v_contextDependent_1252_ = lean_ctor_get_uint8(v_a_1231_, sizeof(void*)*2 + 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_a_1231_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1254_ = v_a_1231_;
v_isShared_1255_ = v_isSharedCheck_1302_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_proof_1251_);
lean_inc(v_e_x27_1250_);
lean_dec(v_a_1231_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1302_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; 
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v___y_1220_);
lean_inc(v___y_1219_);
lean_inc_ref(v_e_x27_1250_);
v___x_1256_ = lean_apply_12(v___f_1216_, v___x_1229_, v_e_x27_1250_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, lean_box(0));
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1301_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1301_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1301_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
if (lean_obj_tag(v_a_1257_) == 0)
{
uint8_t v_done_1261_; uint8_t v_contextDependent_1262_; uint8_t v___y_1264_; 
lean_dec_ref(v___y_1218_);
v_done_1261_ = lean_ctor_get_uint8(v_a_1257_, 0);
v_contextDependent_1262_ = lean_ctor_get_uint8(v_a_1257_, 1);
lean_dec_ref_known(v_a_1257_, 0);
if (v_contextDependent_1252_ == 0)
{
v___y_1264_ = v_contextDependent_1262_;
goto v___jp_1263_;
}
else
{
v___y_1264_ = v_contextDependent_1252_;
goto v___jp_1263_;
}
v___jp_1263_:
{
lean_object* v___x_1266_; 
if (v_isShared_1255_ == 0)
{
v___x_1266_ = v___x_1254_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_e_x27_1250_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_proof_1251_);
v___x_1266_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1268_; 
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*2, v_done_1261_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*2 + 1, v___y_1264_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1266_);
v___x_1268_ = v___x_1259_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
else
{
lean_object* v_e_x27_1271_; lean_object* v_proof_1272_; uint8_t v_done_1273_; uint8_t v_contextDependent_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1300_; 
lean_del_object(v___x_1259_);
lean_del_object(v___x_1254_);
v_e_x27_1271_ = lean_ctor_get(v_a_1257_, 0);
v_proof_1272_ = lean_ctor_get(v_a_1257_, 1);
v_done_1273_ = lean_ctor_get_uint8(v_a_1257_, sizeof(void*)*2);
v_contextDependent_1274_ = lean_ctor_get_uint8(v_a_1257_, sizeof(void*)*2 + 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_a_1257_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1276_ = v_a_1257_;
v_isShared_1277_ = v_isSharedCheck_1300_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_proof_1272_);
lean_inc(v_e_x27_1271_);
lean_dec(v_a_1257_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1300_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; 
lean_inc_ref(v_e_x27_1271_);
v___x_1278_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1218_, v_e_x27_1250_, v_proof_1251_, v_e_x27_1271_, v_proof_1272_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1291_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1291_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1291_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
uint8_t v___y_1284_; 
if (v_contextDependent_1252_ == 0)
{
v___y_1284_ = v_contextDependent_1274_;
goto v___jp_1283_;
}
else
{
v___y_1284_ = v_contextDependent_1252_;
goto v___jp_1283_;
}
v___jp_1283_:
{
lean_object* v___x_1286_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v_a_1279_);
v___x_1286_ = v___x_1276_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_e_x27_1271_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_a_1279_);
lean_ctor_set_uint8(v_reuseFailAlloc_1290_, sizeof(void*)*2, v_done_1273_);
v___x_1286_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1288_; 
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*2 + 1, v___y_1284_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1286_);
v___x_1288_ = v___x_1281_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_del_object(v___x_1276_);
lean_dec_ref(v_e_x27_1271_);
v_a_1292_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1278_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1278_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1254_);
lean_dec_ref(v_proof_1251_);
lean_dec_ref(v_e_x27_1250_);
lean_dec_ref(v___y_1218_);
return v___x_1256_;
}
}
}
else
{
lean_dec_ref_known(v_a_1231_, 2);
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___f_1216_);
return v___x_1230_;
}
}
}
else
{
lean_dec_ref(v___y_1218_);
lean_dec_ref(v___f_1216_);
return v___x_1230_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1216_ = stack[0].m_obj;
lean_object* v_x_1217_ = stack[1].m_obj;
lean_object* v___y_1218_ = stack[2].m_obj;
lean_object* v___y_1219_ = stack[3].m_obj;
lean_object* v___y_1220_ = stack[4].m_obj;
lean_object* v___y_1221_ = stack[5].m_obj;
lean_object* v___y_1222_ = stack[6].m_obj;
lean_object* v___y_1223_ = stack[7].m_obj;
lean_object* v___y_1224_ = stack[8].m_obj;
lean_object* v___y_1225_ = stack[9].m_obj;
lean_object* v___y_1226_ = stack[10].m_obj;
lean_object* v___y_1227_ = stack[11].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__1(v___f_1216_, v_x_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1___boxed(lean_object* v___f_1304_, lean_object* v_x_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__1(v___f_1304_, v_x_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
return v_res_1317_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2(lean_object* v___f_1318_, lean_object* v_x_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_box(0);
lean_inc_ref(v___y_1320_);
v___x_1332_ = l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
if (lean_obj_tag(v_a_1333_) == 0)
{
uint8_t v_done_1334_; 
v_done_1334_ = lean_ctor_get_uint8(v_a_1333_, 0);
if (v_done_1334_ == 0)
{
uint8_t v_contextDependent_1335_; lean_object* v___x_1336_; 
lean_dec_ref_known(v___x_1332_, 1);
v_contextDependent_1335_ = lean_ctor_get_uint8(v_a_1333_, 1);
lean_dec_ref_known(v_a_1333_, 0);
lean_inc(v___y_1329_);
lean_inc_ref(v___y_1328_);
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
lean_inc(v___y_1321_);
v___x_1336_ = lean_apply_12(v___f_1318_, v___x_1331_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, lean_box(0));
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; uint8_t v___y_1339_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
if (v_contextDependent_1335_ == 0)
{
lean_dec(v_a_1337_);
return v___x_1336_;
}
else
{
if (lean_obj_tag(v_a_1337_) == 0)
{
uint8_t v_contextDependent_1349_; 
v_contextDependent_1349_ = lean_ctor_get_uint8(v_a_1337_, 1);
v___y_1339_ = v_contextDependent_1349_;
goto v___jp_1338_;
}
else
{
uint8_t v_contextDependent_1350_; 
v_contextDependent_1350_ = lean_ctor_get_uint8(v_a_1337_, sizeof(void*)*2 + 1);
v___y_1339_ = v_contextDependent_1350_;
goto v___jp_1338_;
}
}
v___jp_1338_:
{
if (v___y_1339_ == 0)
{
lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___x_1336_, 0);
lean_dec(v_unused_1348_);
v___x_1341_ = v___x_1336_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_dec(v___x_1336_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1337_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
else
{
lean_dec(v_a_1337_);
return v___x_1336_;
}
}
}
else
{
return v___x_1336_;
}
}
else
{
lean_dec_ref_known(v_a_1333_, 0);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___f_1318_);
return v___x_1332_;
}
}
else
{
uint8_t v_done_1351_; 
v_done_1351_ = lean_ctor_get_uint8(v_a_1333_, sizeof(void*)*2);
if (v_done_1351_ == 0)
{
lean_object* v_e_x27_1352_; lean_object* v_proof_1353_; uint8_t v_contextDependent_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1404_; 
lean_dec_ref_known(v___x_1332_, 1);
v_e_x27_1352_ = lean_ctor_get(v_a_1333_, 0);
v_proof_1353_ = lean_ctor_get(v_a_1333_, 1);
v_contextDependent_1354_ = lean_ctor_get_uint8(v_a_1333_, sizeof(void*)*2 + 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_a_1333_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1356_ = v_a_1333_;
v_isShared_1357_ = v_isSharedCheck_1404_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_proof_1353_);
lean_inc(v_e_x27_1352_);
lean_dec(v_a_1333_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1404_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; 
lean_inc(v___y_1329_);
lean_inc_ref(v___y_1328_);
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
lean_inc(v___y_1321_);
lean_inc_ref(v_e_x27_1352_);
v___x_1358_ = lean_apply_12(v___f_1318_, v___x_1331_, v_e_x27_1352_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, lean_box(0));
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1403_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1403_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1403_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
if (lean_obj_tag(v_a_1359_) == 0)
{
uint8_t v_done_1363_; uint8_t v_contextDependent_1364_; uint8_t v___y_1366_; 
lean_dec_ref(v___y_1320_);
v_done_1363_ = lean_ctor_get_uint8(v_a_1359_, 0);
v_contextDependent_1364_ = lean_ctor_get_uint8(v_a_1359_, 1);
lean_dec_ref_known(v_a_1359_, 0);
if (v_contextDependent_1354_ == 0)
{
v___y_1366_ = v_contextDependent_1364_;
goto v___jp_1365_;
}
else
{
v___y_1366_ = v_contextDependent_1354_;
goto v___jp_1365_;
}
v___jp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1357_ == 0)
{
v___x_1368_ = v___x_1356_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_e_x27_1352_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_proof_1353_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1370_; 
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*2, v_done_1363_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*2 + 1, v___y_1366_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1368_);
v___x_1370_ = v___x_1361_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_object* v_e_x27_1373_; lean_object* v_proof_1374_; uint8_t v_done_1375_; uint8_t v_contextDependent_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1402_; 
lean_del_object(v___x_1361_);
lean_del_object(v___x_1356_);
v_e_x27_1373_ = lean_ctor_get(v_a_1359_, 0);
v_proof_1374_ = lean_ctor_get(v_a_1359_, 1);
v_done_1375_ = lean_ctor_get_uint8(v_a_1359_, sizeof(void*)*2);
v_contextDependent_1376_ = lean_ctor_get_uint8(v_a_1359_, sizeof(void*)*2 + 1);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_a_1359_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1378_ = v_a_1359_;
v_isShared_1379_ = v_isSharedCheck_1402_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_proof_1374_);
lean_inc(v_e_x27_1373_);
lean_dec(v_a_1359_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1402_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; 
lean_inc_ref(v_e_x27_1373_);
v___x_1380_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1320_, v_e_x27_1352_, v_proof_1353_, v_e_x27_1373_, v_proof_1374_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1393_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1393_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1393_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
uint8_t v___y_1386_; 
if (v_contextDependent_1354_ == 0)
{
v___y_1386_ = v_contextDependent_1376_;
goto v___jp_1385_;
}
else
{
v___y_1386_ = v_contextDependent_1354_;
goto v___jp_1385_;
}
v___jp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 1, v_a_1381_);
v___x_1388_ = v___x_1378_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_e_x27_1373_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_a_1381_);
lean_ctor_set_uint8(v_reuseFailAlloc_1392_, sizeof(void*)*2, v_done_1375_);
v___x_1388_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1390_; 
lean_ctor_set_uint8(v___x_1388_, sizeof(void*)*2 + 1, v___y_1386_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1388_);
v___x_1390_ = v___x_1383_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_del_object(v___x_1378_);
lean_dec_ref(v_e_x27_1373_);
v_a_1394_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1380_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1380_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1356_);
lean_dec_ref(v_proof_1353_);
lean_dec_ref(v_e_x27_1352_);
lean_dec_ref(v___y_1320_);
return v___x_1358_;
}
}
}
else
{
lean_dec_ref_known(v_a_1333_, 2);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___f_1318_);
return v___x_1332_;
}
}
}
else
{
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___f_1318_);
return v___x_1332_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1318_ = stack[0].m_obj;
lean_object* v_x_1319_ = stack[1].m_obj;
lean_object* v___y_1320_ = stack[2].m_obj;
lean_object* v___y_1321_ = stack[3].m_obj;
lean_object* v___y_1322_ = stack[4].m_obj;
lean_object* v___y_1323_ = stack[5].m_obj;
lean_object* v___y_1324_ = stack[6].m_obj;
lean_object* v___y_1325_ = stack[7].m_obj;
lean_object* v___y_1326_ = stack[8].m_obj;
lean_object* v___y_1327_ = stack[9].m_obj;
lean_object* v___y_1328_ = stack[10].m_obj;
lean_object* v___y_1329_ = stack[11].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__2(v___f_1318_, v_x_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2___boxed(lean_object* v___f_1406_, lean_object* v_x_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__2(v___f_1406_, v_x_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
return v_res_1419_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3(lean_object* v___f_1420_, lean_object* v_x_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_box(0);
lean_inc_ref(v___y_1422_);
v___x_1434_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v___y_1422_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
if (lean_obj_tag(v_a_1435_) == 0)
{
uint8_t v_done_1436_; 
v_done_1436_ = lean_ctor_get_uint8(v_a_1435_, 0);
if (v_done_1436_ == 0)
{
uint8_t v_contextDependent_1437_; lean_object* v___x_1438_; 
lean_dec_ref_known(v___x_1434_, 1);
v_contextDependent_1437_ = lean_ctor_get_uint8(v_a_1435_, 1);
lean_dec_ref_known(v_a_1435_, 0);
lean_inc(v___y_1431_);
lean_inc_ref(v___y_1430_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
lean_inc(v___y_1423_);
v___x_1438_ = lean_apply_12(v___f_1420_, v___x_1433_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, lean_box(0));
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; uint8_t v___y_1441_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
if (v_contextDependent_1437_ == 0)
{
lean_dec(v_a_1439_);
return v___x_1438_;
}
else
{
if (lean_obj_tag(v_a_1439_) == 0)
{
uint8_t v_contextDependent_1451_; 
v_contextDependent_1451_ = lean_ctor_get_uint8(v_a_1439_, 1);
v___y_1441_ = v_contextDependent_1451_;
goto v___jp_1440_;
}
else
{
uint8_t v_contextDependent_1452_; 
v_contextDependent_1452_ = lean_ctor_get_uint8(v_a_1439_, sizeof(void*)*2 + 1);
v___y_1441_ = v_contextDependent_1452_;
goto v___jp_1440_;
}
}
v___jp_1440_:
{
if (v___y_1441_ == 0)
{
lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1449_; 
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; 
v_unused_1450_ = lean_ctor_get(v___x_1438_, 0);
lean_dec(v_unused_1450_);
v___x_1443_ = v___x_1438_;
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v___x_1438_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1439_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1445_);
v___x_1447_ = v___x_1443_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
else
{
lean_dec(v_a_1439_);
return v___x_1438_;
}
}
}
else
{
return v___x_1438_;
}
}
else
{
lean_dec_ref_known(v_a_1435_, 0);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v___f_1420_);
return v___x_1434_;
}
}
else
{
uint8_t v_done_1453_; 
v_done_1453_ = lean_ctor_get_uint8(v_a_1435_, sizeof(void*)*2);
if (v_done_1453_ == 0)
{
lean_object* v_e_x27_1454_; lean_object* v_proof_1455_; uint8_t v_contextDependent_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1506_; 
lean_dec_ref_known(v___x_1434_, 1);
v_e_x27_1454_ = lean_ctor_get(v_a_1435_, 0);
v_proof_1455_ = lean_ctor_get(v_a_1435_, 1);
v_contextDependent_1456_ = lean_ctor_get_uint8(v_a_1435_, sizeof(void*)*2 + 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_a_1435_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1458_ = v_a_1435_;
v_isShared_1459_ = v_isSharedCheck_1506_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_proof_1455_);
lean_inc(v_e_x27_1454_);
lean_dec(v_a_1435_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1506_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; 
lean_inc(v___y_1431_);
lean_inc_ref(v___y_1430_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
lean_inc(v___y_1423_);
lean_inc_ref(v_e_x27_1454_);
v___x_1460_ = lean_apply_12(v___f_1420_, v___x_1433_, v_e_x27_1454_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, lean_box(0));
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1505_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1505_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1505_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
if (lean_obj_tag(v_a_1461_) == 0)
{
uint8_t v_done_1465_; uint8_t v_contextDependent_1466_; uint8_t v___y_1468_; 
lean_dec_ref(v___y_1422_);
v_done_1465_ = lean_ctor_get_uint8(v_a_1461_, 0);
v_contextDependent_1466_ = lean_ctor_get_uint8(v_a_1461_, 1);
lean_dec_ref_known(v_a_1461_, 0);
if (v_contextDependent_1456_ == 0)
{
v___y_1468_ = v_contextDependent_1466_;
goto v___jp_1467_;
}
else
{
v___y_1468_ = v_contextDependent_1456_;
goto v___jp_1467_;
}
v___jp_1467_:
{
lean_object* v___x_1470_; 
if (v_isShared_1459_ == 0)
{
v___x_1470_ = v___x_1458_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_e_x27_1454_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_proof_1455_);
v___x_1470_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1472_; 
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*2, v_done_1465_);
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*2 + 1, v___y_1468_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1470_);
v___x_1472_ = v___x_1463_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v_e_x27_1475_; lean_object* v_proof_1476_; uint8_t v_done_1477_; uint8_t v_contextDependent_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1504_; 
lean_del_object(v___x_1463_);
lean_del_object(v___x_1458_);
v_e_x27_1475_ = lean_ctor_get(v_a_1461_, 0);
v_proof_1476_ = lean_ctor_get(v_a_1461_, 1);
v_done_1477_ = lean_ctor_get_uint8(v_a_1461_, sizeof(void*)*2);
v_contextDependent_1478_ = lean_ctor_get_uint8(v_a_1461_, sizeof(void*)*2 + 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_a_1461_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1480_ = v_a_1461_;
v_isShared_1481_ = v_isSharedCheck_1504_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_proof_1476_);
lean_inc(v_e_x27_1475_);
lean_dec(v_a_1461_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1504_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; 
lean_inc_ref(v_e_x27_1475_);
v___x_1482_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1422_, v_e_x27_1454_, v_proof_1455_, v_e_x27_1475_, v_proof_1476_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1495_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1495_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1495_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
uint8_t v___y_1488_; 
if (v_contextDependent_1456_ == 0)
{
v___y_1488_ = v_contextDependent_1478_;
goto v___jp_1487_;
}
else
{
v___y_1488_ = v_contextDependent_1456_;
goto v___jp_1487_;
}
v___jp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v_a_1483_);
v___x_1490_ = v___x_1480_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_e_x27_1475_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_a_1483_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*2, v_done_1477_);
v___x_1490_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1492_; 
lean_ctor_set_uint8(v___x_1490_, sizeof(void*)*2 + 1, v___y_1488_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1490_);
v___x_1492_ = v___x_1485_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_del_object(v___x_1480_);
lean_dec_ref(v_e_x27_1475_);
v_a_1496_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1482_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1482_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1458_);
lean_dec_ref(v_proof_1455_);
lean_dec_ref(v_e_x27_1454_);
lean_dec_ref(v___y_1422_);
return v___x_1460_;
}
}
}
else
{
lean_dec_ref_known(v_a_1435_, 2);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v___f_1420_);
return v___x_1434_;
}
}
}
else
{
lean_dec_ref(v___y_1422_);
lean_dec_ref(v___f_1420_);
return v___x_1434_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1420_ = stack[0].m_obj;
lean_object* v_x_1421_ = stack[1].m_obj;
lean_object* v___y_1422_ = stack[2].m_obj;
lean_object* v___y_1423_ = stack[3].m_obj;
lean_object* v___y_1424_ = stack[4].m_obj;
lean_object* v___y_1425_ = stack[5].m_obj;
lean_object* v___y_1426_ = stack[6].m_obj;
lean_object* v___y_1427_ = stack[7].m_obj;
lean_object* v___y_1428_ = stack[8].m_obj;
lean_object* v___y_1429_ = stack[9].m_obj;
lean_object* v___y_1430_ = stack[10].m_obj;
lean_object* v___y_1431_ = stack[11].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__3(v___f_1420_, v_x_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3___boxed(lean_object* v___f_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__3(v___f_1508_, v_x_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
return v_res_1521_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4(lean_object* v_x_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; 
lean_inc_ref(v___y_1523_);
v___x_1534_ = l_Lean_Meta_Grind_NormSym_simpForall(v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
if (lean_obj_tag(v_a_1535_) == 0)
{
uint8_t v_done_1536_; 
v_done_1536_ = lean_ctor_get_uint8(v_a_1535_, 0);
if (v_done_1536_ == 0)
{
uint8_t v_contextDependent_1537_; lean_object* v___x_1538_; 
lean_dec_ref_known(v___x_1534_, 1);
v_contextDependent_1537_ = lean_ctor_get_uint8(v_a_1535_, 1);
lean_dec_ref_known(v_a_1535_, 0);
v___x_1538_ = l_Lean_Meta_Grind_NormSym_simpExists(v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; uint8_t v___y_1541_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
if (v_contextDependent_1537_ == 0)
{
return v___x_1538_;
}
else
{
if (lean_obj_tag(v_a_1539_) == 0)
{
uint8_t v_contextDependent_1551_; 
v_contextDependent_1551_ = lean_ctor_get_uint8(v_a_1539_, 1);
v___y_1541_ = v_contextDependent_1551_;
goto v___jp_1540_;
}
else
{
uint8_t v_contextDependent_1552_; 
v_contextDependent_1552_ = lean_ctor_get_uint8(v_a_1539_, sizeof(void*)*2 + 1);
v___y_1541_ = v_contextDependent_1552_;
goto v___jp_1540_;
}
}
v___jp_1540_:
{
if (v___y_1541_ == 0)
{
lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1549_; 
lean_inc(v_a_1539_);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v___x_1538_, 0);
lean_dec(v_unused_1550_);
v___x_1543_ = v___x_1538_;
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
else
{
lean_dec(v___x_1538_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1549_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1545_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1539_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1545_);
v___x_1547_ = v___x_1543_;
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
else
{
return v___x_1538_;
}
}
}
else
{
return v___x_1538_;
}
}
else
{
lean_dec_ref_known(v_a_1535_, 0);
lean_dec_ref(v___y_1523_);
return v___x_1534_;
}
}
else
{
uint8_t v_done_1553_; 
v_done_1553_ = lean_ctor_get_uint8(v_a_1535_, sizeof(void*)*2);
if (v_done_1553_ == 0)
{
lean_object* v_e_x27_1554_; lean_object* v_proof_1555_; uint8_t v_contextDependent_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1606_; 
lean_dec_ref_known(v___x_1534_, 1);
v_e_x27_1554_ = lean_ctor_get(v_a_1535_, 0);
v_proof_1555_ = lean_ctor_get(v_a_1535_, 1);
v_contextDependent_1556_ = lean_ctor_get_uint8(v_a_1535_, sizeof(void*)*2 + 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_a_1535_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1558_ = v_a_1535_;
v_isShared_1559_ = v_isSharedCheck_1606_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_proof_1555_);
lean_inc(v_e_x27_1554_);
lean_dec(v_a_1535_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1606_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; 
lean_inc_ref(v_e_x27_1554_);
v___x_1560_ = l_Lean_Meta_Grind_NormSym_simpExists(v_e_x27_1554_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1605_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1605_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1605_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
if (lean_obj_tag(v_a_1561_) == 0)
{
uint8_t v_done_1565_; uint8_t v_contextDependent_1566_; uint8_t v___y_1568_; 
lean_dec_ref(v___y_1523_);
v_done_1565_ = lean_ctor_get_uint8(v_a_1561_, 0);
v_contextDependent_1566_ = lean_ctor_get_uint8(v_a_1561_, 1);
lean_dec_ref_known(v_a_1561_, 0);
if (v_contextDependent_1556_ == 0)
{
v___y_1568_ = v_contextDependent_1566_;
goto v___jp_1567_;
}
else
{
v___y_1568_ = v_contextDependent_1556_;
goto v___jp_1567_;
}
v___jp_1567_:
{
lean_object* v___x_1570_; 
if (v_isShared_1559_ == 0)
{
v___x_1570_ = v___x_1558_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_e_x27_1554_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_proof_1555_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; 
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*2, v_done_1565_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*2 + 1, v___y_1568_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1570_);
v___x_1572_ = v___x_1563_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_e_x27_1575_; lean_object* v_proof_1576_; uint8_t v_done_1577_; uint8_t v_contextDependent_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1604_; 
lean_del_object(v___x_1563_);
lean_del_object(v___x_1558_);
v_e_x27_1575_ = lean_ctor_get(v_a_1561_, 0);
v_proof_1576_ = lean_ctor_get(v_a_1561_, 1);
v_done_1577_ = lean_ctor_get_uint8(v_a_1561_, sizeof(void*)*2);
v_contextDependent_1578_ = lean_ctor_get_uint8(v_a_1561_, sizeof(void*)*2 + 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_a_1561_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1580_ = v_a_1561_;
v_isShared_1581_ = v_isSharedCheck_1604_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_proof_1576_);
lean_inc(v_e_x27_1575_);
lean_dec(v_a_1561_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1604_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; 
lean_inc_ref(v_e_x27_1575_);
v___x_1582_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1523_, v_e_x27_1554_, v_proof_1555_, v_e_x27_1575_, v_proof_1576_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1595_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1595_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1595_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
uint8_t v___y_1588_; 
if (v_contextDependent_1556_ == 0)
{
v___y_1588_ = v_contextDependent_1578_;
goto v___jp_1587_;
}
else
{
v___y_1588_ = v_contextDependent_1556_;
goto v___jp_1587_;
}
v___jp_1587_:
{
lean_object* v___x_1590_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v_a_1583_);
v___x_1590_ = v___x_1580_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_e_x27_1575_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_a_1583_);
lean_ctor_set_uint8(v_reuseFailAlloc_1594_, sizeof(void*)*2, v_done_1577_);
v___x_1590_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1592_; 
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*2 + 1, v___y_1588_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1590_);
v___x_1592_ = v___x_1585_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_del_object(v___x_1580_);
lean_dec_ref(v_e_x27_1575_);
v_a_1596_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1582_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1582_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1558_);
lean_dec_ref(v_proof_1555_);
lean_dec_ref(v_e_x27_1554_);
lean_dec_ref(v___y_1523_);
return v___x_1560_;
}
}
}
else
{
lean_dec_ref_known(v_a_1535_, 2);
lean_dec_ref(v___y_1523_);
return v___x_1534_;
}
}
}
else
{
lean_dec_ref(v___y_1523_);
return v___x_1534_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1522_ = stack[0].m_obj;
lean_object* v___y_1523_ = stack[1].m_obj;
lean_object* v___y_1524_ = stack[2].m_obj;
lean_object* v___y_1525_ = stack[3].m_obj;
lean_object* v___y_1526_ = stack[4].m_obj;
lean_object* v___y_1527_ = stack[5].m_obj;
lean_object* v___y_1528_ = stack[6].m_obj;
lean_object* v___y_1529_ = stack[7].m_obj;
lean_object* v___y_1530_ = stack[8].m_obj;
lean_object* v___y_1531_ = stack[9].m_obj;
lean_object* v___y_1532_ = stack[10].m_obj;
lean_object* v_res_1607_;
v_res_1607_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__4(v_x_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
stack->m_obj
 = v_res_1607_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4___boxed(lean_object* v_x_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__4(v_x_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
return v_res_1620_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5(lean_object* v___f_1621_, lean_object* v_x_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_box(0);
lean_inc_ref(v___y_1623_);
v___x_1635_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
if (lean_obj_tag(v_a_1636_) == 0)
{
uint8_t v_done_1637_; 
v_done_1637_ = lean_ctor_get_uint8(v_a_1636_, 0);
if (v_done_1637_ == 0)
{
uint8_t v_contextDependent_1638_; lean_object* v___x_1639_; 
lean_dec_ref_known(v___x_1635_, 1);
v_contextDependent_1638_ = lean_ctor_get_uint8(v_a_1636_, 1);
lean_dec_ref_known(v_a_1636_, 0);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
lean_inc(v___y_1626_);
lean_inc_ref(v___y_1625_);
lean_inc(v___y_1624_);
v___x_1639_ = lean_apply_12(v___f_1621_, v___x_1634_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, lean_box(0));
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; uint8_t v___y_1642_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
if (v_contextDependent_1638_ == 0)
{
lean_dec(v_a_1640_);
return v___x_1639_;
}
else
{
if (lean_obj_tag(v_a_1640_) == 0)
{
uint8_t v_contextDependent_1652_; 
v_contextDependent_1652_ = lean_ctor_get_uint8(v_a_1640_, 1);
v___y_1642_ = v_contextDependent_1652_;
goto v___jp_1641_;
}
else
{
uint8_t v_contextDependent_1653_; 
v_contextDependent_1653_ = lean_ctor_get_uint8(v_a_1640_, sizeof(void*)*2 + 1);
v___y_1642_ = v_contextDependent_1653_;
goto v___jp_1641_;
}
}
v___jp_1641_:
{
if (v___y_1642_ == 0)
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1650_; 
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v___x_1639_, 0);
lean_dec(v_unused_1651_);
v___x_1644_ = v___x_1639_;
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v___x_1639_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1640_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1646_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_dec(v_a_1640_);
return v___x_1639_;
}
}
}
else
{
return v___x_1639_;
}
}
else
{
lean_dec_ref_known(v_a_1636_, 0);
lean_dec_ref(v___y_1623_);
lean_dec_ref(v___f_1621_);
return v___x_1635_;
}
}
else
{
uint8_t v_done_1654_; 
v_done_1654_ = lean_ctor_get_uint8(v_a_1636_, sizeof(void*)*2);
if (v_done_1654_ == 0)
{
lean_object* v_e_x27_1655_; lean_object* v_proof_1656_; uint8_t v_contextDependent_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1707_; 
lean_dec_ref_known(v___x_1635_, 1);
v_e_x27_1655_ = lean_ctor_get(v_a_1636_, 0);
v_proof_1656_ = lean_ctor_get(v_a_1636_, 1);
v_contextDependent_1657_ = lean_ctor_get_uint8(v_a_1636_, sizeof(void*)*2 + 1);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_a_1636_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1659_ = v_a_1636_;
v_isShared_1660_ = v_isSharedCheck_1707_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_proof_1656_);
lean_inc(v_e_x27_1655_);
lean_dec(v_a_1636_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1707_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; 
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
lean_inc(v___y_1626_);
lean_inc_ref(v___y_1625_);
lean_inc(v___y_1624_);
lean_inc_ref(v_e_x27_1655_);
v___x_1661_ = lean_apply_12(v___f_1621_, v___x_1634_, v_e_x27_1655_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, lean_box(0));
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1706_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1706_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1706_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
if (lean_obj_tag(v_a_1662_) == 0)
{
uint8_t v_done_1666_; uint8_t v_contextDependent_1667_; uint8_t v___y_1669_; 
lean_dec_ref(v___y_1623_);
v_done_1666_ = lean_ctor_get_uint8(v_a_1662_, 0);
v_contextDependent_1667_ = lean_ctor_get_uint8(v_a_1662_, 1);
lean_dec_ref_known(v_a_1662_, 0);
if (v_contextDependent_1657_ == 0)
{
v___y_1669_ = v_contextDependent_1667_;
goto v___jp_1668_;
}
else
{
v___y_1669_ = v_contextDependent_1657_;
goto v___jp_1668_;
}
v___jp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1660_ == 0)
{
v___x_1671_ = v___x_1659_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_e_x27_1655_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_proof_1656_);
v___x_1671_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1673_; 
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*2, v_done_1666_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*2 + 1, v___y_1669_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1671_);
v___x_1673_ = v___x_1664_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v_e_x27_1676_; lean_object* v_proof_1677_; uint8_t v_done_1678_; uint8_t v_contextDependent_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1705_; 
lean_del_object(v___x_1664_);
lean_del_object(v___x_1659_);
v_e_x27_1676_ = lean_ctor_get(v_a_1662_, 0);
v_proof_1677_ = lean_ctor_get(v_a_1662_, 1);
v_done_1678_ = lean_ctor_get_uint8(v_a_1662_, sizeof(void*)*2);
v_contextDependent_1679_ = lean_ctor_get_uint8(v_a_1662_, sizeof(void*)*2 + 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_a_1662_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1681_ = v_a_1662_;
v_isShared_1682_ = v_isSharedCheck_1705_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_proof_1677_);
lean_inc(v_e_x27_1676_);
lean_dec(v_a_1662_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1705_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; 
lean_inc_ref(v_e_x27_1676_);
v___x_1683_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1623_, v_e_x27_1655_, v_proof_1656_, v_e_x27_1676_, v_proof_1677_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1696_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1696_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1696_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
uint8_t v___y_1689_; 
if (v_contextDependent_1657_ == 0)
{
v___y_1689_ = v_contextDependent_1679_;
goto v___jp_1688_;
}
else
{
v___y_1689_ = v_contextDependent_1657_;
goto v___jp_1688_;
}
v___jp_1688_:
{
lean_object* v___x_1691_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v_a_1684_);
v___x_1691_ = v___x_1681_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_e_x27_1676_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_a_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1695_, sizeof(void*)*2, v_done_1678_);
v___x_1691_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1693_; 
lean_ctor_set_uint8(v___x_1691_, sizeof(void*)*2 + 1, v___y_1689_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1691_);
v___x_1693_ = v___x_1686_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_del_object(v___x_1681_);
lean_dec_ref(v_e_x27_1676_);
v_a_1697_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1683_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1683_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1659_);
lean_dec_ref(v_proof_1656_);
lean_dec_ref(v_e_x27_1655_);
lean_dec_ref(v___y_1623_);
return v___x_1661_;
}
}
}
else
{
lean_dec_ref_known(v_a_1636_, 2);
lean_dec_ref(v___y_1623_);
lean_dec_ref(v___f_1621_);
return v___x_1635_;
}
}
}
else
{
lean_dec_ref(v___y_1623_);
lean_dec_ref(v___f_1621_);
return v___x_1635_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1621_ = stack[0].m_obj;
lean_object* v_x_1622_ = stack[1].m_obj;
lean_object* v___y_1623_ = stack[2].m_obj;
lean_object* v___y_1624_ = stack[3].m_obj;
lean_object* v___y_1625_ = stack[4].m_obj;
lean_object* v___y_1626_ = stack[5].m_obj;
lean_object* v___y_1627_ = stack[6].m_obj;
lean_object* v___y_1628_ = stack[7].m_obj;
lean_object* v___y_1629_ = stack[8].m_obj;
lean_object* v___y_1630_ = stack[9].m_obj;
lean_object* v___y_1631_ = stack[10].m_obj;
lean_object* v___y_1632_ = stack[11].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__5(v___f_1621_, v_x_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed(lean_object* v___f_1709_, lean_object* v_x_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__5(v___f_1709_, v_x_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
return v_res_1722_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6(lean_object* v___f_1723_, lean_object* v_x_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_box(0);
lean_inc_ref(v___y_1725_);
v___x_1737_ = l_Lean_Meta_Grind_NormSym_simpDIte(v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
if (lean_obj_tag(v_a_1738_) == 0)
{
uint8_t v_done_1739_; 
v_done_1739_ = lean_ctor_get_uint8(v_a_1738_, 0);
if (v_done_1739_ == 0)
{
uint8_t v_contextDependent_1740_; lean_object* v___x_1741_; 
lean_dec_ref_known(v___x_1737_, 1);
v_contextDependent_1740_ = lean_ctor_get_uint8(v_a_1738_, 1);
lean_dec_ref_known(v_a_1738_, 0);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1730_);
lean_inc_ref(v___y_1729_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1727_);
lean_inc(v___y_1726_);
v___x_1741_ = lean_apply_12(v___f_1723_, v___x_1736_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, lean_box(0));
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; uint8_t v___y_1744_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
if (v_contextDependent_1740_ == 0)
{
lean_dec(v_a_1742_);
return v___x_1741_;
}
else
{
if (lean_obj_tag(v_a_1742_) == 0)
{
uint8_t v_contextDependent_1754_; 
v_contextDependent_1754_ = lean_ctor_get_uint8(v_a_1742_, 1);
v___y_1744_ = v_contextDependent_1754_;
goto v___jp_1743_;
}
else
{
uint8_t v_contextDependent_1755_; 
v_contextDependent_1755_ = lean_ctor_get_uint8(v_a_1742_, sizeof(void*)*2 + 1);
v___y_1744_ = v_contextDependent_1755_;
goto v___jp_1743_;
}
}
v___jp_1743_:
{
if (v___y_1744_ == 0)
{
lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1752_; 
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; 
v_unused_1753_ = lean_ctor_get(v___x_1741_, 0);
lean_dec(v_unused_1753_);
v___x_1746_ = v___x_1741_;
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
else
{
lean_dec(v___x_1741_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1742_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1748_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
else
{
lean_dec(v_a_1742_);
return v___x_1741_;
}
}
}
else
{
return v___x_1741_;
}
}
else
{
lean_dec_ref_known(v_a_1738_, 0);
lean_dec_ref(v___y_1725_);
lean_dec_ref(v___f_1723_);
return v___x_1737_;
}
}
else
{
uint8_t v_done_1756_; 
v_done_1756_ = lean_ctor_get_uint8(v_a_1738_, sizeof(void*)*2);
if (v_done_1756_ == 0)
{
lean_object* v_e_x27_1757_; lean_object* v_proof_1758_; uint8_t v_contextDependent_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1809_; 
lean_dec_ref_known(v___x_1737_, 1);
v_e_x27_1757_ = lean_ctor_get(v_a_1738_, 0);
v_proof_1758_ = lean_ctor_get(v_a_1738_, 1);
v_contextDependent_1759_ = lean_ctor_get_uint8(v_a_1738_, sizeof(void*)*2 + 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_a_1738_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1761_ = v_a_1738_;
v_isShared_1762_ = v_isSharedCheck_1809_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_proof_1758_);
lean_inc(v_e_x27_1757_);
lean_dec(v_a_1738_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1809_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; 
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1730_);
lean_inc_ref(v___y_1729_);
lean_inc(v___y_1728_);
lean_inc_ref(v___y_1727_);
lean_inc(v___y_1726_);
lean_inc_ref(v_e_x27_1757_);
v___x_1763_ = lean_apply_12(v___f_1723_, v___x_1736_, v_e_x27_1757_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, lean_box(0));
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1808_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1808_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1808_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
if (lean_obj_tag(v_a_1764_) == 0)
{
uint8_t v_done_1768_; uint8_t v_contextDependent_1769_; uint8_t v___y_1771_; 
lean_dec_ref(v___y_1725_);
v_done_1768_ = lean_ctor_get_uint8(v_a_1764_, 0);
v_contextDependent_1769_ = lean_ctor_get_uint8(v_a_1764_, 1);
lean_dec_ref_known(v_a_1764_, 0);
if (v_contextDependent_1759_ == 0)
{
v___y_1771_ = v_contextDependent_1769_;
goto v___jp_1770_;
}
else
{
v___y_1771_ = v_contextDependent_1759_;
goto v___jp_1770_;
}
v___jp_1770_:
{
lean_object* v___x_1773_; 
if (v_isShared_1762_ == 0)
{
v___x_1773_ = v___x_1761_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_e_x27_1757_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_proof_1758_);
v___x_1773_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1775_; 
lean_ctor_set_uint8(v___x_1773_, sizeof(void*)*2, v_done_1768_);
lean_ctor_set_uint8(v___x_1773_, sizeof(void*)*2 + 1, v___y_1771_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1773_);
v___x_1775_ = v___x_1766_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v_e_x27_1778_; lean_object* v_proof_1779_; uint8_t v_done_1780_; uint8_t v_contextDependent_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1807_; 
lean_del_object(v___x_1766_);
lean_del_object(v___x_1761_);
v_e_x27_1778_ = lean_ctor_get(v_a_1764_, 0);
v_proof_1779_ = lean_ctor_get(v_a_1764_, 1);
v_done_1780_ = lean_ctor_get_uint8(v_a_1764_, sizeof(void*)*2);
v_contextDependent_1781_ = lean_ctor_get_uint8(v_a_1764_, sizeof(void*)*2 + 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_a_1764_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1783_ = v_a_1764_;
v_isShared_1784_ = v_isSharedCheck_1807_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_proof_1779_);
lean_inc(v_e_x27_1778_);
lean_dec(v_a_1764_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1807_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; 
lean_inc_ref(v_e_x27_1778_);
v___x_1785_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1725_, v_e_x27_1757_, v_proof_1758_, v_e_x27_1778_, v_proof_1779_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1798_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1798_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1798_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
uint8_t v___y_1791_; 
if (v_contextDependent_1759_ == 0)
{
v___y_1791_ = v_contextDependent_1781_;
goto v___jp_1790_;
}
else
{
v___y_1791_ = v_contextDependent_1759_;
goto v___jp_1790_;
}
v___jp_1790_:
{
lean_object* v___x_1793_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 1, v_a_1786_);
v___x_1793_ = v___x_1783_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_e_x27_1778_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_a_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1797_, sizeof(void*)*2, v_done_1780_);
v___x_1793_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
lean_ctor_set_uint8(v___x_1793_, sizeof(void*)*2 + 1, v___y_1791_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1793_);
v___x_1795_ = v___x_1788_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_del_object(v___x_1783_);
lean_dec_ref(v_e_x27_1778_);
v_a_1799_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1785_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1785_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1761_);
lean_dec_ref(v_proof_1758_);
lean_dec_ref(v_e_x27_1757_);
lean_dec_ref(v___y_1725_);
return v___x_1763_;
}
}
}
else
{
lean_dec_ref_known(v_a_1738_, 2);
lean_dec_ref(v___y_1725_);
lean_dec_ref(v___f_1723_);
return v___x_1737_;
}
}
}
else
{
lean_dec_ref(v___y_1725_);
lean_dec_ref(v___f_1723_);
return v___x_1737_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1723_ = stack[0].m_obj;
lean_object* v_x_1724_ = stack[1].m_obj;
lean_object* v___y_1725_ = stack[2].m_obj;
lean_object* v___y_1726_ = stack[3].m_obj;
lean_object* v___y_1727_ = stack[4].m_obj;
lean_object* v___y_1728_ = stack[5].m_obj;
lean_object* v___y_1729_ = stack[6].m_obj;
lean_object* v___y_1730_ = stack[7].m_obj;
lean_object* v___y_1731_ = stack[8].m_obj;
lean_object* v___y_1732_ = stack[9].m_obj;
lean_object* v___y_1733_ = stack[10].m_obj;
lean_object* v___y_1734_ = stack[11].m_obj;
lean_object* v_res_1810_;
v_res_1810_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__6(v___f_1723_, v_x_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
stack->m_obj
 = v_res_1810_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed(lean_object* v___f_1811_, lean_object* v_x_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__6(v___f_1811_, v_x_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
return v_res_1824_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7(lean_object* v___f_1825_, lean_object* v_x_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_box(0);
lean_inc_ref(v___y_1827_);
v___x_1839_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v___y_1827_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
if (lean_obj_tag(v_a_1840_) == 0)
{
uint8_t v_done_1841_; 
v_done_1841_ = lean_ctor_get_uint8(v_a_1840_, 0);
if (v_done_1841_ == 0)
{
uint8_t v_contextDependent_1842_; lean_object* v___x_1843_; 
lean_dec_ref_known(v___x_1839_, 1);
v_contextDependent_1842_ = lean_ctor_get_uint8(v_a_1840_, 1);
lean_dec_ref_known(v_a_1840_, 0);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
lean_inc(v___y_1828_);
v___x_1843_ = lean_apply_12(v___f_1825_, v___x_1838_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, lean_box(0));
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; uint8_t v___y_1846_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
if (v_contextDependent_1842_ == 0)
{
lean_dec(v_a_1844_);
return v___x_1843_;
}
else
{
if (lean_obj_tag(v_a_1844_) == 0)
{
uint8_t v_contextDependent_1856_; 
v_contextDependent_1856_ = lean_ctor_get_uint8(v_a_1844_, 1);
v___y_1846_ = v_contextDependent_1856_;
goto v___jp_1845_;
}
else
{
uint8_t v_contextDependent_1857_; 
v_contextDependent_1857_ = lean_ctor_get_uint8(v_a_1844_, sizeof(void*)*2 + 1);
v___y_1846_ = v_contextDependent_1857_;
goto v___jp_1845_;
}
}
v___jp_1845_:
{
if (v___y_1846_ == 0)
{
lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1854_; 
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v___x_1843_, 0);
lean_dec(v_unused_1855_);
v___x_1848_ = v___x_1843_;
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
else
{
lean_dec(v___x_1843_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1844_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1850_);
v___x_1852_ = v___x_1848_;
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
else
{
lean_dec(v_a_1844_);
return v___x_1843_;
}
}
}
else
{
return v___x_1843_;
}
}
else
{
lean_dec_ref_known(v_a_1840_, 0);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v___f_1825_);
return v___x_1839_;
}
}
else
{
uint8_t v_done_1858_; 
v_done_1858_ = lean_ctor_get_uint8(v_a_1840_, sizeof(void*)*2);
if (v_done_1858_ == 0)
{
lean_object* v_e_x27_1859_; lean_object* v_proof_1860_; uint8_t v_contextDependent_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1911_; 
lean_dec_ref_known(v___x_1839_, 1);
v_e_x27_1859_ = lean_ctor_get(v_a_1840_, 0);
v_proof_1860_ = lean_ctor_get(v_a_1840_, 1);
v_contextDependent_1861_ = lean_ctor_get_uint8(v_a_1840_, sizeof(void*)*2 + 1);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_a_1840_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1863_ = v_a_1840_;
v_isShared_1864_ = v_isSharedCheck_1911_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_proof_1860_);
lean_inc(v_e_x27_1859_);
lean_dec(v_a_1840_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1911_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; 
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
lean_inc(v___y_1828_);
lean_inc_ref(v_e_x27_1859_);
v___x_1865_ = lean_apply_12(v___f_1825_, v___x_1838_, v_e_x27_1859_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, lean_box(0));
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1910_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1910_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1910_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
if (lean_obj_tag(v_a_1866_) == 0)
{
uint8_t v_done_1870_; uint8_t v_contextDependent_1871_; uint8_t v___y_1873_; 
lean_dec_ref(v___y_1827_);
v_done_1870_ = lean_ctor_get_uint8(v_a_1866_, 0);
v_contextDependent_1871_ = lean_ctor_get_uint8(v_a_1866_, 1);
lean_dec_ref_known(v_a_1866_, 0);
if (v_contextDependent_1861_ == 0)
{
v___y_1873_ = v_contextDependent_1871_;
goto v___jp_1872_;
}
else
{
v___y_1873_ = v_contextDependent_1861_;
goto v___jp_1872_;
}
v___jp_1872_:
{
lean_object* v___x_1875_; 
if (v_isShared_1864_ == 0)
{
v___x_1875_ = v___x_1863_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_e_x27_1859_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_proof_1860_);
v___x_1875_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*2, v_done_1870_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*2 + 1, v___y_1873_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1875_);
v___x_1877_ = v___x_1868_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v_e_x27_1880_; lean_object* v_proof_1881_; uint8_t v_done_1882_; uint8_t v_contextDependent_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1909_; 
lean_del_object(v___x_1868_);
lean_del_object(v___x_1863_);
v_e_x27_1880_ = lean_ctor_get(v_a_1866_, 0);
v_proof_1881_ = lean_ctor_get(v_a_1866_, 1);
v_done_1882_ = lean_ctor_get_uint8(v_a_1866_, sizeof(void*)*2);
v_contextDependent_1883_ = lean_ctor_get_uint8(v_a_1866_, sizeof(void*)*2 + 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_a_1866_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1885_ = v_a_1866_;
v_isShared_1886_ = v_isSharedCheck_1909_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_proof_1881_);
lean_inc(v_e_x27_1880_);
lean_dec(v_a_1866_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1909_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; 
lean_inc_ref(v_e_x27_1880_);
v___x_1887_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1827_, v_e_x27_1859_, v_proof_1860_, v_e_x27_1880_, v_proof_1881_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1900_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1900_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1900_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
uint8_t v___y_1893_; 
if (v_contextDependent_1861_ == 0)
{
v___y_1893_ = v_contextDependent_1883_;
goto v___jp_1892_;
}
else
{
v___y_1893_ = v_contextDependent_1861_;
goto v___jp_1892_;
}
v___jp_1892_:
{
lean_object* v___x_1895_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v_a_1888_);
v___x_1895_ = v___x_1885_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_e_x27_1880_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_a_1888_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, sizeof(void*)*2, v_done_1882_);
v___x_1895_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1897_; 
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*2 + 1, v___y_1893_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1895_);
v___x_1897_ = v___x_1890_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_del_object(v___x_1885_);
lean_dec_ref(v_e_x27_1880_);
v_a_1901_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1887_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1887_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1863_);
lean_dec_ref(v_proof_1860_);
lean_dec_ref(v_e_x27_1859_);
lean_dec_ref(v___y_1827_);
return v___x_1865_;
}
}
}
else
{
lean_dec_ref_known(v_a_1840_, 2);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v___f_1825_);
return v___x_1839_;
}
}
}
else
{
lean_dec_ref(v___y_1827_);
lean_dec_ref(v___f_1825_);
return v___x_1839_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1825_ = stack[0].m_obj;
lean_object* v_x_1826_ = stack[1].m_obj;
lean_object* v___y_1827_ = stack[2].m_obj;
lean_object* v___y_1828_ = stack[3].m_obj;
lean_object* v___y_1829_ = stack[4].m_obj;
lean_object* v___y_1830_ = stack[5].m_obj;
lean_object* v___y_1831_ = stack[6].m_obj;
lean_object* v___y_1832_ = stack[7].m_obj;
lean_object* v___y_1833_ = stack[8].m_obj;
lean_object* v___y_1834_ = stack[9].m_obj;
lean_object* v___y_1835_ = stack[10].m_obj;
lean_object* v___y_1836_ = stack[11].m_obj;
lean_object* v_res_1912_;
v_res_1912_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__7(v___f_1825_, v_x_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
stack->m_obj
 = v_res_1912_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7___boxed(lean_object* v___f_1913_, lean_object* v_x_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__7(v___f_1913_, v_x_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
return v_res_1926_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8(lean_object* v___f_1927_, lean_object* v_x_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_box(0);
lean_inc_ref(v___y_1929_);
v___x_1941_ = l_Lean_Meta_Grind_NormSym_simpEq(v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
if (lean_obj_tag(v_a_1942_) == 0)
{
uint8_t v_done_1943_; 
v_done_1943_ = lean_ctor_get_uint8(v_a_1942_, 0);
if (v_done_1943_ == 0)
{
uint8_t v_contextDependent_1944_; lean_object* v___x_1945_; 
lean_dec_ref_known(v___x_1941_, 1);
v_contextDependent_1944_ = lean_ctor_get_uint8(v_a_1942_, 1);
lean_dec_ref_known(v_a_1942_, 0);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1937_);
lean_inc(v___y_1936_);
lean_inc_ref(v___y_1935_);
lean_inc(v___y_1934_);
lean_inc_ref(v___y_1933_);
lean_inc(v___y_1932_);
lean_inc_ref(v___y_1931_);
lean_inc(v___y_1930_);
v___x_1945_ = lean_apply_12(v___f_1927_, v___x_1940_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, lean_box(0));
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; uint8_t v___y_1948_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
if (v_contextDependent_1944_ == 0)
{
lean_dec(v_a_1946_);
return v___x_1945_;
}
else
{
if (lean_obj_tag(v_a_1946_) == 0)
{
uint8_t v_contextDependent_1958_; 
v_contextDependent_1958_ = lean_ctor_get_uint8(v_a_1946_, 1);
v___y_1948_ = v_contextDependent_1958_;
goto v___jp_1947_;
}
else
{
uint8_t v_contextDependent_1959_; 
v_contextDependent_1959_ = lean_ctor_get_uint8(v_a_1946_, sizeof(void*)*2 + 1);
v___y_1948_ = v_contextDependent_1959_;
goto v___jp_1947_;
}
}
v___jp_1947_:
{
if (v___y_1948_ == 0)
{
lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v___x_1945_, 0);
lean_dec(v_unused_1957_);
v___x_1950_ = v___x_1945_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_dec(v___x_1945_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1952_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1946_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1952_);
v___x_1954_ = v___x_1950_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
lean_dec(v_a_1946_);
return v___x_1945_;
}
}
}
else
{
return v___x_1945_;
}
}
else
{
lean_dec_ref_known(v_a_1942_, 0);
lean_dec_ref(v___y_1929_);
lean_dec_ref(v___f_1927_);
return v___x_1941_;
}
}
else
{
uint8_t v_done_1960_; 
v_done_1960_ = lean_ctor_get_uint8(v_a_1942_, sizeof(void*)*2);
if (v_done_1960_ == 0)
{
lean_object* v_e_x27_1961_; lean_object* v_proof_1962_; uint8_t v_contextDependent_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_2013_; 
lean_dec_ref_known(v___x_1941_, 1);
v_e_x27_1961_ = lean_ctor_get(v_a_1942_, 0);
v_proof_1962_ = lean_ctor_get(v_a_1942_, 1);
v_contextDependent_1963_ = lean_ctor_get_uint8(v_a_1942_, sizeof(void*)*2 + 1);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_a_1942_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1965_ = v_a_1942_;
v_isShared_1966_ = v_isSharedCheck_2013_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_proof_1962_);
lean_inc(v_e_x27_1961_);
lean_dec(v_a_1942_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_2013_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; 
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1937_);
lean_inc(v___y_1936_);
lean_inc_ref(v___y_1935_);
lean_inc(v___y_1934_);
lean_inc_ref(v___y_1933_);
lean_inc(v___y_1932_);
lean_inc_ref(v___y_1931_);
lean_inc(v___y_1930_);
lean_inc_ref(v_e_x27_1961_);
v___x_1967_ = lean_apply_12(v___f_1927_, v___x_1940_, v_e_x27_1961_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, lean_box(0));
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2012_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_2012_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2012_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
if (lean_obj_tag(v_a_1968_) == 0)
{
uint8_t v_done_1972_; uint8_t v_contextDependent_1973_; uint8_t v___y_1975_; 
lean_dec_ref(v___y_1929_);
v_done_1972_ = lean_ctor_get_uint8(v_a_1968_, 0);
v_contextDependent_1973_ = lean_ctor_get_uint8(v_a_1968_, 1);
lean_dec_ref_known(v_a_1968_, 0);
if (v_contextDependent_1963_ == 0)
{
v___y_1975_ = v_contextDependent_1973_;
goto v___jp_1974_;
}
else
{
v___y_1975_ = v_contextDependent_1963_;
goto v___jp_1974_;
}
v___jp_1974_:
{
lean_object* v___x_1977_; 
if (v_isShared_1966_ == 0)
{
v___x_1977_ = v___x_1965_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_e_x27_1961_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_proof_1962_);
v___x_1977_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1979_; 
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*2, v_done_1972_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*2 + 1, v___y_1975_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1977_);
v___x_1979_ = v___x_1970_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
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
else
{
lean_object* v_e_x27_1982_; lean_object* v_proof_1983_; uint8_t v_done_1984_; uint8_t v_contextDependent_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2011_; 
lean_del_object(v___x_1970_);
lean_del_object(v___x_1965_);
v_e_x27_1982_ = lean_ctor_get(v_a_1968_, 0);
v_proof_1983_ = lean_ctor_get(v_a_1968_, 1);
v_done_1984_ = lean_ctor_get_uint8(v_a_1968_, sizeof(void*)*2);
v_contextDependent_1985_ = lean_ctor_get_uint8(v_a_1968_, sizeof(void*)*2 + 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_a_1968_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1987_ = v_a_1968_;
v_isShared_1988_ = v_isSharedCheck_2011_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_proof_1983_);
lean_inc(v_e_x27_1982_);
lean_dec(v_a_1968_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2011_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; 
lean_inc_ref(v_e_x27_1982_);
v___x_1989_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1929_, v_e_x27_1961_, v_proof_1962_, v_e_x27_1982_, v_proof_1983_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2002_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2002_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2002_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
uint8_t v___y_1995_; 
if (v_contextDependent_1963_ == 0)
{
v___y_1995_ = v_contextDependent_1985_;
goto v___jp_1994_;
}
else
{
v___y_1995_ = v_contextDependent_1963_;
goto v___jp_1994_;
}
v___jp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v_a_1990_);
v___x_1997_ = v___x_1987_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_e_x27_1982_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_a_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2001_, sizeof(void*)*2, v_done_1984_);
v___x_1997_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1999_; 
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*2 + 1, v___y_1995_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1997_);
v___x_1999_ = v___x_1992_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_del_object(v___x_1987_);
lean_dec_ref(v_e_x27_1982_);
v_a_2003_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1989_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1989_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1965_);
lean_dec_ref(v_proof_1962_);
lean_dec_ref(v_e_x27_1961_);
lean_dec_ref(v___y_1929_);
return v___x_1967_;
}
}
}
else
{
lean_dec_ref_known(v_a_1942_, 2);
lean_dec_ref(v___y_1929_);
lean_dec_ref(v___f_1927_);
return v___x_1941_;
}
}
}
else
{
lean_dec_ref(v___y_1929_);
lean_dec_ref(v___f_1927_);
return v___x_1941_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1927_ = stack[0].m_obj;
lean_object* v_x_1928_ = stack[1].m_obj;
lean_object* v___y_1929_ = stack[2].m_obj;
lean_object* v___y_1930_ = stack[3].m_obj;
lean_object* v___y_1931_ = stack[4].m_obj;
lean_object* v___y_1932_ = stack[5].m_obj;
lean_object* v___y_1933_ = stack[6].m_obj;
lean_object* v___y_1934_ = stack[7].m_obj;
lean_object* v___y_1935_ = stack[8].m_obj;
lean_object* v___y_1936_ = stack[9].m_obj;
lean_object* v___y_1937_ = stack[10].m_obj;
lean_object* v___y_1938_ = stack[11].m_obj;
lean_object* v_res_2014_;
v_res_2014_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__8(v___f_1927_, v_x_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
stack->m_obj
 = v_res_2014_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8___boxed(lean_object* v___f_2015_, lean_object* v_x_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__8(v___f_2015_, v_x_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
return v_res_2028_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9(lean_object* v___f_2029_, lean_object* v_x_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_box(0);
lean_inc_ref(v___y_2031_);
v___x_2043_ = l_Lean_Meta_Sym_Simp_simpNatRel___redArg(v___y_2031_, v___y_2035_, v___y_2038_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
if (lean_obj_tag(v_a_2044_) == 0)
{
uint8_t v_done_2045_; 
v_done_2045_ = lean_ctor_get_uint8(v_a_2044_, 0);
if (v_done_2045_ == 0)
{
uint8_t v_contextDependent_2046_; lean_object* v___x_2047_; 
lean_dec_ref_known(v___x_2043_, 1);
v_contextDependent_2046_ = lean_ctor_get_uint8(v_a_2044_, 1);
lean_dec_ref_known(v_a_2044_, 0);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
lean_inc(v___y_2036_);
lean_inc_ref(v___y_2035_);
lean_inc(v___y_2034_);
lean_inc_ref(v___y_2033_);
lean_inc(v___y_2032_);
v___x_2047_ = lean_apply_12(v___f_2029_, v___x_2042_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, lean_box(0));
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; uint8_t v___y_2050_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
if (v_contextDependent_2046_ == 0)
{
lean_dec(v_a_2048_);
return v___x_2047_;
}
else
{
if (lean_obj_tag(v_a_2048_) == 0)
{
uint8_t v_contextDependent_2060_; 
v_contextDependent_2060_ = lean_ctor_get_uint8(v_a_2048_, 1);
v___y_2050_ = v_contextDependent_2060_;
goto v___jp_2049_;
}
else
{
uint8_t v_contextDependent_2061_; 
v_contextDependent_2061_ = lean_ctor_get_uint8(v_a_2048_, sizeof(void*)*2 + 1);
v___y_2050_ = v_contextDependent_2061_;
goto v___jp_2049_;
}
}
v___jp_2049_:
{
if (v___y_2050_ == 0)
{
lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2058_; 
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v___x_2047_, 0);
lean_dec(v_unused_2059_);
v___x_2052_ = v___x_2047_;
v_isShared_2053_ = v_isSharedCheck_2058_;
goto v_resetjp_2051_;
}
else
{
lean_dec(v___x_2047_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2058_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2054_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2048_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2054_);
v___x_2056_ = v___x_2052_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
else
{
lean_dec(v_a_2048_);
return v___x_2047_;
}
}
}
else
{
return v___x_2047_;
}
}
else
{
lean_dec_ref_known(v_a_2044_, 0);
lean_dec_ref(v___y_2031_);
lean_dec_ref(v___f_2029_);
return v___x_2043_;
}
}
else
{
uint8_t v_done_2062_; 
v_done_2062_ = lean_ctor_get_uint8(v_a_2044_, sizeof(void*)*2);
if (v_done_2062_ == 0)
{
lean_object* v_e_x27_2063_; lean_object* v_proof_2064_; uint8_t v_contextDependent_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref_known(v___x_2043_, 1);
v_e_x27_2063_ = lean_ctor_get(v_a_2044_, 0);
v_proof_2064_ = lean_ctor_get(v_a_2044_, 1);
v_contextDependent_2065_ = lean_ctor_get_uint8(v_a_2044_, sizeof(void*)*2 + 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_a_2044_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2067_ = v_a_2044_;
v_isShared_2068_ = v_isSharedCheck_2115_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_proof_2064_);
lean_inc(v_e_x27_2063_);
lean_dec(v_a_2044_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2115_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; 
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
lean_inc(v___y_2036_);
lean_inc_ref(v___y_2035_);
lean_inc(v___y_2034_);
lean_inc_ref(v___y_2033_);
lean_inc(v___y_2032_);
lean_inc_ref(v_e_x27_2063_);
v___x_2069_ = lean_apply_12(v___f_2029_, v___x_2042_, v_e_x27_2063_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, lean_box(0));
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2114_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2114_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2114_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
if (lean_obj_tag(v_a_2070_) == 0)
{
uint8_t v_done_2074_; uint8_t v_contextDependent_2075_; uint8_t v___y_2077_; 
lean_dec_ref(v___y_2031_);
v_done_2074_ = lean_ctor_get_uint8(v_a_2070_, 0);
v_contextDependent_2075_ = lean_ctor_get_uint8(v_a_2070_, 1);
lean_dec_ref_known(v_a_2070_, 0);
if (v_contextDependent_2065_ == 0)
{
v___y_2077_ = v_contextDependent_2075_;
goto v___jp_2076_;
}
else
{
v___y_2077_ = v_contextDependent_2065_;
goto v___jp_2076_;
}
v___jp_2076_:
{
lean_object* v___x_2079_; 
if (v_isShared_2068_ == 0)
{
v___x_2079_ = v___x_2067_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_e_x27_2063_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_proof_2064_);
v___x_2079_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2081_; 
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*2, v_done_2074_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*2 + 1, v___y_2077_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2079_);
v___x_2081_ = v___x_2072_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
else
{
lean_object* v_e_x27_2084_; lean_object* v_proof_2085_; uint8_t v_done_2086_; uint8_t v_contextDependent_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2113_; 
lean_del_object(v___x_2072_);
lean_del_object(v___x_2067_);
v_e_x27_2084_ = lean_ctor_get(v_a_2070_, 0);
v_proof_2085_ = lean_ctor_get(v_a_2070_, 1);
v_done_2086_ = lean_ctor_get_uint8(v_a_2070_, sizeof(void*)*2);
v_contextDependent_2087_ = lean_ctor_get_uint8(v_a_2070_, sizeof(void*)*2 + 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_a_2070_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2089_ = v_a_2070_;
v_isShared_2090_ = v_isSharedCheck_2113_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_proof_2085_);
lean_inc(v_e_x27_2084_);
lean_dec(v_a_2070_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2113_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; 
lean_inc_ref(v_e_x27_2084_);
v___x_2091_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2031_, v_e_x27_2063_, v_proof_2064_, v_e_x27_2084_, v_proof_2085_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2104_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2104_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2104_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
uint8_t v___y_2097_; 
if (v_contextDependent_2065_ == 0)
{
v___y_2097_ = v_contextDependent_2087_;
goto v___jp_2096_;
}
else
{
v___y_2097_ = v_contextDependent_2065_;
goto v___jp_2096_;
}
v___jp_2096_:
{
lean_object* v___x_2099_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v_a_2092_);
v___x_2099_ = v___x_2089_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_e_x27_2084_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_a_2092_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*2, v_done_2086_);
v___x_2099_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2101_; 
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*2 + 1, v___y_2097_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2099_);
v___x_2101_ = v___x_2094_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_del_object(v___x_2089_);
lean_dec_ref(v_e_x27_2084_);
v_a_2105_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2091_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2091_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2067_);
lean_dec_ref(v_proof_2064_);
lean_dec_ref(v_e_x27_2063_);
lean_dec_ref(v___y_2031_);
return v___x_2069_;
}
}
}
else
{
lean_dec_ref_known(v_a_2044_, 2);
lean_dec_ref(v___y_2031_);
lean_dec_ref(v___f_2029_);
return v___x_2043_;
}
}
}
else
{
lean_dec_ref(v___y_2031_);
lean_dec_ref(v___f_2029_);
return v___x_2043_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2029_ = stack[0].m_obj;
lean_object* v_x_2030_ = stack[1].m_obj;
lean_object* v___y_2031_ = stack[2].m_obj;
lean_object* v___y_2032_ = stack[3].m_obj;
lean_object* v___y_2033_ = stack[4].m_obj;
lean_object* v___y_2034_ = stack[5].m_obj;
lean_object* v___y_2035_ = stack[6].m_obj;
lean_object* v___y_2036_ = stack[7].m_obj;
lean_object* v___y_2037_ = stack[8].m_obj;
lean_object* v___y_2038_ = stack[9].m_obj;
lean_object* v___y_2039_ = stack[10].m_obj;
lean_object* v___y_2040_ = stack[11].m_obj;
lean_object* v_res_2116_;
v_res_2116_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__9(v___f_2029_, v_x_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
stack->m_obj
 = v_res_2116_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9___boxed(lean_object* v___f_2117_, lean_object* v_x_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__9(v___f_2117_, v_x_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
return v_res_2130_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10(lean_object* v___f_2134_, lean_object* v_x_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__10___closed__0));
v___x_2148_ = lean_box(0);
lean_inc_ref(v___y_2136_);
v___x_2149_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_2136_, v___x_2147_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
if (lean_obj_tag(v_a_2150_) == 0)
{
uint8_t v_done_2151_; 
v_done_2151_ = lean_ctor_get_uint8(v_a_2150_, 0);
if (v_done_2151_ == 0)
{
uint8_t v_contextDependent_2152_; lean_object* v___x_2153_; 
lean_dec_ref_known(v___x_2149_, 1);
v_contextDependent_2152_ = lean_ctor_get_uint8(v_a_2150_, 1);
lean_dec_ref_known(v_a_2150_, 0);
lean_inc(v___y_2145_);
lean_inc_ref(v___y_2144_);
lean_inc(v___y_2143_);
lean_inc_ref(v___y_2142_);
lean_inc(v___y_2141_);
lean_inc_ref(v___y_2140_);
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2138_);
lean_inc(v___y_2137_);
v___x_2153_ = lean_apply_12(v___f_2134_, v___x_2148_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, lean_box(0));
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; uint8_t v___y_2156_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
if (v_contextDependent_2152_ == 0)
{
lean_dec(v_a_2154_);
return v___x_2153_;
}
else
{
if (lean_obj_tag(v_a_2154_) == 0)
{
uint8_t v_contextDependent_2166_; 
v_contextDependent_2166_ = lean_ctor_get_uint8(v_a_2154_, 1);
v___y_2156_ = v_contextDependent_2166_;
goto v___jp_2155_;
}
else
{
uint8_t v_contextDependent_2167_; 
v_contextDependent_2167_ = lean_ctor_get_uint8(v_a_2154_, sizeof(void*)*2 + 1);
v___y_2156_ = v_contextDependent_2167_;
goto v___jp_2155_;
}
}
v___jp_2155_:
{
if (v___y_2156_ == 0)
{
lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2164_; 
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; 
v_unused_2165_ = lean_ctor_get(v___x_2153_, 0);
lean_dec(v_unused_2165_);
v___x_2158_ = v___x_2153_;
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
else
{
lean_dec(v___x_2153_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2154_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2160_);
v___x_2162_ = v___x_2158_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
else
{
lean_dec(v_a_2154_);
return v___x_2153_;
}
}
}
else
{
return v___x_2153_;
}
}
else
{
lean_dec_ref_known(v_a_2150_, 0);
lean_dec_ref(v___y_2136_);
lean_dec_ref(v___f_2134_);
return v___x_2149_;
}
}
else
{
uint8_t v_done_2168_; 
v_done_2168_ = lean_ctor_get_uint8(v_a_2150_, sizeof(void*)*2);
if (v_done_2168_ == 0)
{
lean_object* v_e_x27_2169_; lean_object* v_proof_2170_; uint8_t v_contextDependent_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref_known(v___x_2149_, 1);
v_e_x27_2169_ = lean_ctor_get(v_a_2150_, 0);
v_proof_2170_ = lean_ctor_get(v_a_2150_, 1);
v_contextDependent_2171_ = lean_ctor_get_uint8(v_a_2150_, sizeof(void*)*2 + 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_a_2150_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2173_ = v_a_2150_;
v_isShared_2174_ = v_isSharedCheck_2221_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_proof_2170_);
lean_inc(v_e_x27_2169_);
lean_dec(v_a_2150_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2221_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; 
lean_inc(v___y_2145_);
lean_inc_ref(v___y_2144_);
lean_inc(v___y_2143_);
lean_inc_ref(v___y_2142_);
lean_inc(v___y_2141_);
lean_inc_ref(v___y_2140_);
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2138_);
lean_inc(v___y_2137_);
lean_inc_ref(v_e_x27_2169_);
v___x_2175_ = lean_apply_12(v___f_2134_, v___x_2148_, v_e_x27_2169_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, lean_box(0));
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2220_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2220_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2220_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
if (lean_obj_tag(v_a_2176_) == 0)
{
uint8_t v_done_2180_; uint8_t v_contextDependent_2181_; uint8_t v___y_2183_; 
lean_dec_ref(v___y_2136_);
v_done_2180_ = lean_ctor_get_uint8(v_a_2176_, 0);
v_contextDependent_2181_ = lean_ctor_get_uint8(v_a_2176_, 1);
lean_dec_ref_known(v_a_2176_, 0);
if (v_contextDependent_2171_ == 0)
{
v___y_2183_ = v_contextDependent_2181_;
goto v___jp_2182_;
}
else
{
v___y_2183_ = v_contextDependent_2171_;
goto v___jp_2182_;
}
v___jp_2182_:
{
lean_object* v___x_2185_; 
if (v_isShared_2174_ == 0)
{
v___x_2185_ = v___x_2173_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_e_x27_2169_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_proof_2170_);
v___x_2185_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2187_; 
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*2, v_done_2180_);
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*2 + 1, v___y_2183_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2185_);
v___x_2187_ = v___x_2178_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v_e_x27_2190_; lean_object* v_proof_2191_; uint8_t v_done_2192_; uint8_t v_contextDependent_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2219_; 
lean_del_object(v___x_2178_);
lean_del_object(v___x_2173_);
v_e_x27_2190_ = lean_ctor_get(v_a_2176_, 0);
v_proof_2191_ = lean_ctor_get(v_a_2176_, 1);
v_done_2192_ = lean_ctor_get_uint8(v_a_2176_, sizeof(void*)*2);
v_contextDependent_2193_ = lean_ctor_get_uint8(v_a_2176_, sizeof(void*)*2 + 1);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_a_2176_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2195_ = v_a_2176_;
v_isShared_2196_ = v_isSharedCheck_2219_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_proof_2191_);
lean_inc(v_e_x27_2190_);
lean_dec(v_a_2176_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2219_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; 
lean_inc_ref(v_e_x27_2190_);
v___x_2197_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2136_, v_e_x27_2169_, v_proof_2170_, v_e_x27_2190_, v_proof_2191_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2210_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2210_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2210_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
uint8_t v___y_2203_; 
if (v_contextDependent_2171_ == 0)
{
v___y_2203_ = v_contextDependent_2193_;
goto v___jp_2202_;
}
else
{
v___y_2203_ = v_contextDependent_2171_;
goto v___jp_2202_;
}
v___jp_2202_:
{
lean_object* v___x_2205_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 1, v_a_2198_);
v___x_2205_ = v___x_2195_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_e_x27_2190_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_a_2198_);
lean_ctor_set_uint8(v_reuseFailAlloc_2209_, sizeof(void*)*2, v_done_2192_);
v___x_2205_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2207_; 
lean_ctor_set_uint8(v___x_2205_, sizeof(void*)*2 + 1, v___y_2203_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2205_);
v___x_2207_ = v___x_2200_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_del_object(v___x_2195_);
lean_dec_ref(v_e_x27_2190_);
v_a_2211_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2197_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2197_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2173_);
lean_dec_ref(v_proof_2170_);
lean_dec_ref(v_e_x27_2169_);
lean_dec_ref(v___y_2136_);
return v___x_2175_;
}
}
}
else
{
lean_dec_ref_known(v_a_2150_, 2);
lean_dec_ref(v___y_2136_);
lean_dec_ref(v___f_2134_);
return v___x_2149_;
}
}
}
else
{
lean_dec_ref(v___y_2136_);
lean_dec_ref(v___f_2134_);
return v___x_2149_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2134_ = stack[0].m_obj;
lean_object* v_x_2135_ = stack[1].m_obj;
lean_object* v___y_2136_ = stack[2].m_obj;
lean_object* v___y_2137_ = stack[3].m_obj;
lean_object* v___y_2138_ = stack[4].m_obj;
lean_object* v___y_2139_ = stack[5].m_obj;
lean_object* v___y_2140_ = stack[6].m_obj;
lean_object* v___y_2141_ = stack[7].m_obj;
lean_object* v___y_2142_ = stack[8].m_obj;
lean_object* v___y_2143_ = stack[9].m_obj;
lean_object* v___y_2144_ = stack[10].m_obj;
lean_object* v___y_2145_ = stack[11].m_obj;
lean_object* v_res_2222_;
v_res_2222_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__10(v___f_2134_, v_x_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
stack->m_obj
 = v_res_2222_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10___boxed(lean_object* v___f_2223_, lean_object* v_x_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__10(v___f_2223_, v_x_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
return v_res_2236_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11(lean_object* v_thms_2237_, lean_object* v_d_2238_, lean_object* v_x_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_pre_2251_; lean_object* v___x_2252_; 
v_pre_2251_ = lean_ctor_get(v_thms_2237_, 0);
v___x_2252_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_pre_2251_, v_d_2238_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
return v___x_2252_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_thms_2237_ = stack[0].m_obj;
lean_object* v_d_2238_ = stack[1].m_obj;
lean_object* v_x_2239_ = stack[2].m_obj;
lean_object* v___y_2240_ = stack[3].m_obj;
lean_object* v___y_2241_ = stack[4].m_obj;
lean_object* v___y_2242_ = stack[5].m_obj;
lean_object* v___y_2243_ = stack[6].m_obj;
lean_object* v___y_2244_ = stack[7].m_obj;
lean_object* v___y_2245_ = stack[8].m_obj;
lean_object* v___y_2246_ = stack[9].m_obj;
lean_object* v___y_2247_ = stack[10].m_obj;
lean_object* v___y_2248_ = stack[11].m_obj;
lean_object* v___y_2249_ = stack[12].m_obj;
lean_object* v_res_2253_;
v_res_2253_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__11(v_thms_2237_, v_d_2238_, v_x_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
stack->m_obj
 = v_res_2253_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed(lean_object* v_thms_2254_, lean_object* v_d_2255_, lean_object* v_x_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__11(v_thms_2254_, v_d_2255_, v_x_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v_thms_2254_);
return v_res_2268_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12(lean_object* v_d_2269_, lean_object* v___f_2270_, lean_object* v_x_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = 1;
v___x_2284_ = lean_box(0);
lean_inc_ref(v___y_2272_);
v___x_2285_ = l_Lean_Meta_Sym_Simp_simpArith(v_d_2269_, v___x_2283_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
if (lean_obj_tag(v_a_2286_) == 0)
{
uint8_t v_done_2287_; 
v_done_2287_ = lean_ctor_get_uint8(v_a_2286_, 0);
if (v_done_2287_ == 0)
{
uint8_t v_contextDependent_2288_; lean_object* v___x_2289_; 
lean_dec_ref_known(v___x_2285_, 1);
v_contextDependent_2288_ = lean_ctor_get_uint8(v_a_2286_, 1);
lean_dec_ref_known(v_a_2286_, 0);
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
lean_inc(v___y_2273_);
v___x_2289_ = lean_apply_12(v___f_2270_, v___x_2284_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, lean_box(0));
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; uint8_t v___y_2292_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
if (v_contextDependent_2288_ == 0)
{
lean_dec(v_a_2290_);
return v___x_2289_;
}
else
{
if (lean_obj_tag(v_a_2290_) == 0)
{
uint8_t v_contextDependent_2302_; 
v_contextDependent_2302_ = lean_ctor_get_uint8(v_a_2290_, 1);
v___y_2292_ = v_contextDependent_2302_;
goto v___jp_2291_;
}
else
{
uint8_t v_contextDependent_2303_; 
v_contextDependent_2303_ = lean_ctor_get_uint8(v_a_2290_, sizeof(void*)*2 + 1);
v___y_2292_ = v_contextDependent_2303_;
goto v___jp_2291_;
}
}
v___jp_2291_:
{
if (v___y_2292_ == 0)
{
lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2300_; 
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; 
v_unused_2301_ = lean_ctor_get(v___x_2289_, 0);
lean_dec(v_unused_2301_);
v___x_2294_ = v___x_2289_;
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
else
{
lean_dec(v___x_2289_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2296_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2290_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2296_);
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
else
{
lean_dec(v_a_2290_);
return v___x_2289_;
}
}
}
else
{
return v___x_2289_;
}
}
else
{
lean_dec_ref_known(v_a_2286_, 0);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v___f_2270_);
return v___x_2285_;
}
}
else
{
uint8_t v_done_2304_; 
v_done_2304_ = lean_ctor_get_uint8(v_a_2286_, sizeof(void*)*2);
if (v_done_2304_ == 0)
{
lean_object* v_e_x27_2305_; lean_object* v_proof_2306_; uint8_t v_contextDependent_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref_known(v___x_2285_, 1);
v_e_x27_2305_ = lean_ctor_get(v_a_2286_, 0);
v_proof_2306_ = lean_ctor_get(v_a_2286_, 1);
v_contextDependent_2307_ = lean_ctor_get_uint8(v_a_2286_, sizeof(void*)*2 + 1);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_a_2286_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2309_ = v_a_2286_;
v_isShared_2310_ = v_isSharedCheck_2357_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_proof_2306_);
lean_inc(v_e_x27_2305_);
lean_dec(v_a_2286_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2357_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; 
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
lean_inc(v___y_2273_);
lean_inc_ref(v_e_x27_2305_);
v___x_2311_ = lean_apply_12(v___f_2270_, v___x_2284_, v_e_x27_2305_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, lean_box(0));
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2356_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2356_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2356_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
if (lean_obj_tag(v_a_2312_) == 0)
{
uint8_t v_done_2316_; uint8_t v_contextDependent_2317_; uint8_t v___y_2319_; 
lean_dec_ref(v___y_2272_);
v_done_2316_ = lean_ctor_get_uint8(v_a_2312_, 0);
v_contextDependent_2317_ = lean_ctor_get_uint8(v_a_2312_, 1);
lean_dec_ref_known(v_a_2312_, 0);
if (v_contextDependent_2307_ == 0)
{
v___y_2319_ = v_contextDependent_2317_;
goto v___jp_2318_;
}
else
{
v___y_2319_ = v_contextDependent_2307_;
goto v___jp_2318_;
}
v___jp_2318_:
{
lean_object* v___x_2321_; 
if (v_isShared_2310_ == 0)
{
v___x_2321_ = v___x_2309_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_e_x27_2305_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_proof_2306_);
v___x_2321_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2323_; 
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*2, v_done_2316_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*2 + 1, v___y_2319_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v___x_2321_);
v___x_2323_ = v___x_2314_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
else
{
lean_object* v_e_x27_2326_; lean_object* v_proof_2327_; uint8_t v_done_2328_; uint8_t v_contextDependent_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2355_; 
lean_del_object(v___x_2314_);
lean_del_object(v___x_2309_);
v_e_x27_2326_ = lean_ctor_get(v_a_2312_, 0);
v_proof_2327_ = lean_ctor_get(v_a_2312_, 1);
v_done_2328_ = lean_ctor_get_uint8(v_a_2312_, sizeof(void*)*2);
v_contextDependent_2329_ = lean_ctor_get_uint8(v_a_2312_, sizeof(void*)*2 + 1);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_a_2312_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2331_ = v_a_2312_;
v_isShared_2332_ = v_isSharedCheck_2355_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_proof_2327_);
lean_inc(v_e_x27_2326_);
lean_dec(v_a_2312_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2355_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; 
lean_inc_ref(v_e_x27_2326_);
v___x_2333_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2272_, v_e_x27_2305_, v_proof_2306_, v_e_x27_2326_, v_proof_2327_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2346_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2346_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2346_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
uint8_t v___y_2339_; 
if (v_contextDependent_2307_ == 0)
{
v___y_2339_ = v_contextDependent_2329_;
goto v___jp_2338_;
}
else
{
v___y_2339_ = v_contextDependent_2307_;
goto v___jp_2338_;
}
v___jp_2338_:
{
lean_object* v___x_2341_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v_a_2334_);
v___x_2341_ = v___x_2331_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_e_x27_2326_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_a_2334_);
lean_ctor_set_uint8(v_reuseFailAlloc_2345_, sizeof(void*)*2, v_done_2328_);
v___x_2341_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2343_; 
lean_ctor_set_uint8(v___x_2341_, sizeof(void*)*2 + 1, v___y_2339_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2341_);
v___x_2343_ = v___x_2336_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_del_object(v___x_2331_);
lean_dec_ref(v_e_x27_2326_);
v_a_2347_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2333_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2333_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2309_);
lean_dec_ref(v_proof_2306_);
lean_dec_ref(v_e_x27_2305_);
lean_dec_ref(v___y_2272_);
return v___x_2311_;
}
}
}
else
{
lean_dec_ref_known(v_a_2286_, 2);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v___f_2270_);
return v___x_2285_;
}
}
}
else
{
lean_dec_ref(v___y_2272_);
lean_dec_ref(v___f_2270_);
return v___x_2285_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_2269_ = stack[0].m_obj;
lean_object* v___f_2270_ = stack[1].m_obj;
lean_object* v_x_2271_ = stack[2].m_obj;
lean_object* v___y_2272_ = stack[3].m_obj;
lean_object* v___y_2273_ = stack[4].m_obj;
lean_object* v___y_2274_ = stack[5].m_obj;
lean_object* v___y_2275_ = stack[6].m_obj;
lean_object* v___y_2276_ = stack[7].m_obj;
lean_object* v___y_2277_ = stack[8].m_obj;
lean_object* v___y_2278_ = stack[9].m_obj;
lean_object* v___y_2279_ = stack[10].m_obj;
lean_object* v___y_2280_ = stack[11].m_obj;
lean_object* v___y_2281_ = stack[12].m_obj;
lean_object* v_res_2358_;
v_res_2358_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__12(v_d_2269_, v___f_2270_, v_x_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
stack->m_obj
 = v_res_2358_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed(lean_object* v_d_2359_, lean_object* v___f_2360_, lean_object* v_x_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__12(v_d_2359_, v___f_2360_, v_x_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
return v_res_2373_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13(lean_object* v___f_2374_, lean_object* v_x_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_box(0);
lean_inc_ref(v___y_2376_);
v___x_2388_ = l_Lean_Meta_Grind_NormSym_pushNot(v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
if (lean_obj_tag(v_a_2389_) == 0)
{
uint8_t v_done_2390_; 
v_done_2390_ = lean_ctor_get_uint8(v_a_2389_, 0);
if (v_done_2390_ == 0)
{
uint8_t v_contextDependent_2391_; lean_object* v___x_2392_; 
lean_dec_ref_known(v___x_2388_, 1);
v_contextDependent_2391_ = lean_ctor_get_uint8(v_a_2389_, 1);
lean_dec_ref_known(v_a_2389_, 0);
lean_inc(v___y_2385_);
lean_inc_ref(v___y_2384_);
lean_inc(v___y_2383_);
lean_inc_ref(v___y_2382_);
lean_inc(v___y_2381_);
lean_inc_ref(v___y_2380_);
lean_inc(v___y_2379_);
lean_inc_ref(v___y_2378_);
lean_inc(v___y_2377_);
v___x_2392_ = lean_apply_12(v___f_2374_, v___x_2387_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, lean_box(0));
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; uint8_t v___y_2395_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
if (v_contextDependent_2391_ == 0)
{
lean_dec(v_a_2393_);
return v___x_2392_;
}
else
{
if (lean_obj_tag(v_a_2393_) == 0)
{
uint8_t v_contextDependent_2405_; 
v_contextDependent_2405_ = lean_ctor_get_uint8(v_a_2393_, 1);
v___y_2395_ = v_contextDependent_2405_;
goto v___jp_2394_;
}
else
{
uint8_t v_contextDependent_2406_; 
v_contextDependent_2406_ = lean_ctor_get_uint8(v_a_2393_, sizeof(void*)*2 + 1);
v___y_2395_ = v_contextDependent_2406_;
goto v___jp_2394_;
}
}
v___jp_2394_:
{
if (v___y_2395_ == 0)
{
lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2403_; 
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v___x_2392_, 0);
lean_dec(v_unused_2404_);
v___x_2397_ = v___x_2392_;
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
else
{
lean_dec(v___x_2392_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2403_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2401_; 
v___x_2399_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2393_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2399_);
v___x_2401_ = v___x_2397_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
else
{
lean_dec(v_a_2393_);
return v___x_2392_;
}
}
}
else
{
return v___x_2392_;
}
}
else
{
lean_dec_ref_known(v_a_2389_, 0);
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___f_2374_);
return v___x_2388_;
}
}
else
{
uint8_t v_done_2407_; 
v_done_2407_ = lean_ctor_get_uint8(v_a_2389_, sizeof(void*)*2);
if (v_done_2407_ == 0)
{
lean_object* v_e_x27_2408_; lean_object* v_proof_2409_; uint8_t v_contextDependent_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2460_; 
lean_dec_ref_known(v___x_2388_, 1);
v_e_x27_2408_ = lean_ctor_get(v_a_2389_, 0);
v_proof_2409_ = lean_ctor_get(v_a_2389_, 1);
v_contextDependent_2410_ = lean_ctor_get_uint8(v_a_2389_, sizeof(void*)*2 + 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_a_2389_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2412_ = v_a_2389_;
v_isShared_2413_ = v_isSharedCheck_2460_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_proof_2409_);
lean_inc(v_e_x27_2408_);
lean_dec(v_a_2389_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2460_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; 
lean_inc(v___y_2385_);
lean_inc_ref(v___y_2384_);
lean_inc(v___y_2383_);
lean_inc_ref(v___y_2382_);
lean_inc(v___y_2381_);
lean_inc_ref(v___y_2380_);
lean_inc(v___y_2379_);
lean_inc_ref(v___y_2378_);
lean_inc(v___y_2377_);
lean_inc_ref(v_e_x27_2408_);
v___x_2414_ = lean_apply_12(v___f_2374_, v___x_2387_, v_e_x27_2408_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, lean_box(0));
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2459_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2459_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2459_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
if (lean_obj_tag(v_a_2415_) == 0)
{
uint8_t v_done_2419_; uint8_t v_contextDependent_2420_; uint8_t v___y_2422_; 
lean_dec_ref(v___y_2376_);
v_done_2419_ = lean_ctor_get_uint8(v_a_2415_, 0);
v_contextDependent_2420_ = lean_ctor_get_uint8(v_a_2415_, 1);
lean_dec_ref_known(v_a_2415_, 0);
if (v_contextDependent_2410_ == 0)
{
v___y_2422_ = v_contextDependent_2420_;
goto v___jp_2421_;
}
else
{
v___y_2422_ = v_contextDependent_2410_;
goto v___jp_2421_;
}
v___jp_2421_:
{
lean_object* v___x_2424_; 
if (v_isShared_2413_ == 0)
{
v___x_2424_ = v___x_2412_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_e_x27_2408_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_proof_2409_);
v___x_2424_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2426_; 
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*2, v_done_2419_);
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*2 + 1, v___y_2422_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2424_);
v___x_2426_ = v___x_2417_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_object* v_e_x27_2429_; lean_object* v_proof_2430_; uint8_t v_done_2431_; uint8_t v_contextDependent_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2458_; 
lean_del_object(v___x_2417_);
lean_del_object(v___x_2412_);
v_e_x27_2429_ = lean_ctor_get(v_a_2415_, 0);
v_proof_2430_ = lean_ctor_get(v_a_2415_, 1);
v_done_2431_ = lean_ctor_get_uint8(v_a_2415_, sizeof(void*)*2);
v_contextDependent_2432_ = lean_ctor_get_uint8(v_a_2415_, sizeof(void*)*2 + 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_a_2415_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2434_ = v_a_2415_;
v_isShared_2435_ = v_isSharedCheck_2458_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_proof_2430_);
lean_inc(v_e_x27_2429_);
lean_dec(v_a_2415_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2458_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; 
lean_inc_ref(v_e_x27_2429_);
v___x_2436_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2376_, v_e_x27_2408_, v_proof_2409_, v_e_x27_2429_, v_proof_2430_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2449_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2449_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2449_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
uint8_t v___y_2442_; 
if (v_contextDependent_2410_ == 0)
{
v___y_2442_ = v_contextDependent_2432_;
goto v___jp_2441_;
}
else
{
v___y_2442_ = v_contextDependent_2410_;
goto v___jp_2441_;
}
v___jp_2441_:
{
lean_object* v___x_2444_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 1, v_a_2437_);
v___x_2444_ = v___x_2434_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_e_x27_2429_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_a_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2448_, sizeof(void*)*2, v_done_2431_);
v___x_2444_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2446_; 
lean_ctor_set_uint8(v___x_2444_, sizeof(void*)*2 + 1, v___y_2442_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2444_);
v___x_2446_ = v___x_2439_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_del_object(v___x_2434_);
lean_dec_ref(v_e_x27_2429_);
v_a_2450_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2436_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2436_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2412_);
lean_dec_ref(v_proof_2409_);
lean_dec_ref(v_e_x27_2408_);
lean_dec_ref(v___y_2376_);
return v___x_2414_;
}
}
}
else
{
lean_dec_ref_known(v_a_2389_, 2);
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___f_2374_);
return v___x_2388_;
}
}
}
else
{
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___f_2374_);
return v___x_2388_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2374_ = stack[0].m_obj;
lean_object* v_x_2375_ = stack[1].m_obj;
lean_object* v___y_2376_ = stack[2].m_obj;
lean_object* v___y_2377_ = stack[3].m_obj;
lean_object* v___y_2378_ = stack[4].m_obj;
lean_object* v___y_2379_ = stack[5].m_obj;
lean_object* v___y_2380_ = stack[6].m_obj;
lean_object* v___y_2381_ = stack[7].m_obj;
lean_object* v___y_2382_ = stack[8].m_obj;
lean_object* v___y_2383_ = stack[9].m_obj;
lean_object* v___y_2384_ = stack[10].m_obj;
lean_object* v___y_2385_ = stack[11].m_obj;
lean_object* v_res_2461_;
v_res_2461_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__13(v___f_2374_, v_x_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
stack->m_obj
 = v_res_2461_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed(lean_object* v___f_2462_, lean_object* v_x_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__13(v___f_2462_, v_x_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
return v_res_2475_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14(lean_object* v_pre_2476_, lean_object* v___f_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_box(0);
lean_inc(v___y_2487_);
lean_inc_ref(v___y_2486_);
lean_inc(v___y_2485_);
lean_inc_ref(v___y_2484_);
lean_inc(v___y_2483_);
lean_inc_ref(v___y_2482_);
lean_inc(v___y_2481_);
lean_inc_ref(v___y_2480_);
lean_inc(v___y_2479_);
lean_inc_ref(v___y_2478_);
v___x_2490_ = lean_apply_11(v_pre_2476_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, lean_box(0));
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2491_);
if (lean_obj_tag(v_a_2491_) == 0)
{
uint8_t v_done_2492_; 
v_done_2492_ = lean_ctor_get_uint8(v_a_2491_, 0);
if (v_done_2492_ == 0)
{
uint8_t v_contextDependent_2493_; lean_object* v___x_2494_; 
lean_dec_ref_known(v___x_2490_, 1);
v_contextDependent_2493_ = lean_ctor_get_uint8(v_a_2491_, 1);
lean_dec_ref_known(v_a_2491_, 0);
v___x_2494_ = lean_apply_12(v___f_2477_, v___x_2489_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, lean_box(0));
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; uint8_t v___y_2497_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
if (v_contextDependent_2493_ == 0)
{
lean_dec(v_a_2495_);
return v___x_2494_;
}
else
{
if (lean_obj_tag(v_a_2495_) == 0)
{
uint8_t v_contextDependent_2507_; 
v_contextDependent_2507_ = lean_ctor_get_uint8(v_a_2495_, 1);
v___y_2497_ = v_contextDependent_2507_;
goto v___jp_2496_;
}
else
{
uint8_t v_contextDependent_2508_; 
v_contextDependent_2508_ = lean_ctor_get_uint8(v_a_2495_, sizeof(void*)*2 + 1);
v___y_2497_ = v_contextDependent_2508_;
goto v___jp_2496_;
}
}
v___jp_2496_:
{
if (v___y_2497_ == 0)
{
lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2505_; 
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v___x_2494_, 0);
lean_dec(v_unused_2506_);
v___x_2499_ = v___x_2494_;
v_isShared_2500_ = v_isSharedCheck_2505_;
goto v_resetjp_2498_;
}
else
{
lean_dec(v___x_2494_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2505_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2501_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2495_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2501_);
v___x_2503_ = v___x_2499_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
else
{
lean_dec(v_a_2495_);
return v___x_2494_;
}
}
}
else
{
return v___x_2494_;
}
}
else
{
lean_dec_ref_known(v_a_2491_, 0);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec_ref(v___f_2477_);
return v___x_2490_;
}
}
else
{
uint8_t v_done_2509_; 
v_done_2509_ = lean_ctor_get_uint8(v_a_2491_, sizeof(void*)*2);
if (v_done_2509_ == 0)
{
lean_object* v_e_x27_2510_; lean_object* v_proof_2511_; uint8_t v_contextDependent_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref_known(v___x_2490_, 1);
v_e_x27_2510_ = lean_ctor_get(v_a_2491_, 0);
v_proof_2511_ = lean_ctor_get(v_a_2491_, 1);
v_contextDependent_2512_ = lean_ctor_get_uint8(v_a_2491_, sizeof(void*)*2 + 1);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_a_2491_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2514_ = v_a_2491_;
v_isShared_2515_ = v_isSharedCheck_2562_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_proof_2511_);
lean_inc(v_e_x27_2510_);
lean_dec(v_a_2491_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2562_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; 
lean_inc(v___y_2487_);
lean_inc_ref(v___y_2486_);
lean_inc(v___y_2485_);
lean_inc_ref(v___y_2484_);
lean_inc(v___y_2483_);
lean_inc_ref(v___y_2482_);
lean_inc_ref(v_e_x27_2510_);
v___x_2516_ = lean_apply_12(v___f_2477_, v___x_2489_, v_e_x27_2510_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, lean_box(0));
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2561_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2519_ = v___x_2516_;
v_isShared_2520_ = v_isSharedCheck_2561_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2516_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2561_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
if (lean_obj_tag(v_a_2517_) == 0)
{
uint8_t v_done_2521_; uint8_t v_contextDependent_2522_; uint8_t v___y_2524_; 
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v___y_2478_);
v_done_2521_ = lean_ctor_get_uint8(v_a_2517_, 0);
v_contextDependent_2522_ = lean_ctor_get_uint8(v_a_2517_, 1);
lean_dec_ref_known(v_a_2517_, 0);
if (v_contextDependent_2512_ == 0)
{
v___y_2524_ = v_contextDependent_2522_;
goto v___jp_2523_;
}
else
{
v___y_2524_ = v_contextDependent_2512_;
goto v___jp_2523_;
}
v___jp_2523_:
{
lean_object* v___x_2526_; 
if (v_isShared_2515_ == 0)
{
v___x_2526_ = v___x_2514_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_e_x27_2510_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_proof_2511_);
v___x_2526_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2528_; 
lean_ctor_set_uint8(v___x_2526_, sizeof(void*)*2, v_done_2521_);
lean_ctor_set_uint8(v___x_2526_, sizeof(void*)*2 + 1, v___y_2524_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 0, v___x_2526_);
v___x_2528_ = v___x_2519_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_object* v_e_x27_2531_; lean_object* v_proof_2532_; uint8_t v_done_2533_; uint8_t v_contextDependent_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2560_; 
lean_del_object(v___x_2519_);
lean_del_object(v___x_2514_);
v_e_x27_2531_ = lean_ctor_get(v_a_2517_, 0);
v_proof_2532_ = lean_ctor_get(v_a_2517_, 1);
v_done_2533_ = lean_ctor_get_uint8(v_a_2517_, sizeof(void*)*2);
v_contextDependent_2534_ = lean_ctor_get_uint8(v_a_2517_, sizeof(void*)*2 + 1);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_a_2517_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2536_ = v_a_2517_;
v_isShared_2537_ = v_isSharedCheck_2560_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_proof_2532_);
lean_inc(v_e_x27_2531_);
lean_dec(v_a_2517_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2560_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; 
lean_inc_ref(v_e_x27_2531_);
v___x_2538_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2478_, v_e_x27_2510_, v_proof_2511_, v_e_x27_2531_, v_proof_2532_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2551_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2551_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2551_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
uint8_t v___y_2544_; 
if (v_contextDependent_2512_ == 0)
{
v___y_2544_ = v_contextDependent_2534_;
goto v___jp_2543_;
}
else
{
v___y_2544_ = v_contextDependent_2512_;
goto v___jp_2543_;
}
v___jp_2543_:
{
lean_object* v___x_2546_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 1, v_a_2539_);
v___x_2546_ = v___x_2536_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_e_x27_2531_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_a_2539_);
lean_ctor_set_uint8(v_reuseFailAlloc_2550_, sizeof(void*)*2, v_done_2533_);
v___x_2546_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2548_; 
lean_ctor_set_uint8(v___x_2546_, sizeof(void*)*2 + 1, v___y_2544_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 0, v___x_2546_);
v___x_2548_ = v___x_2541_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_del_object(v___x_2536_);
lean_dec_ref(v_e_x27_2531_);
v_a_2552_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2538_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2538_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2514_);
lean_dec_ref(v_proof_2511_);
lean_dec_ref(v_e_x27_2510_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v___y_2478_);
return v___x_2516_;
}
}
}
else
{
lean_dec_ref_known(v_a_2491_, 2);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec_ref(v___f_2477_);
return v___x_2490_;
}
}
}
else
{
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec_ref(v___f_2477_);
return v___x_2490_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2476_ = stack[0].m_obj;
lean_object* v___f_2477_ = stack[1].m_obj;
lean_object* v___y_2478_ = stack[2].m_obj;
lean_object* v___y_2479_ = stack[3].m_obj;
lean_object* v___y_2480_ = stack[4].m_obj;
lean_object* v___y_2481_ = stack[5].m_obj;
lean_object* v___y_2482_ = stack[6].m_obj;
lean_object* v___y_2483_ = stack[7].m_obj;
lean_object* v___y_2484_ = stack[8].m_obj;
lean_object* v___y_2485_ = stack[9].m_obj;
lean_object* v___y_2486_ = stack[10].m_obj;
lean_object* v___y_2487_ = stack[11].m_obj;
lean_object* v_res_2563_;
v_res_2563_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__14(v_pre_2476_, v___f_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
stack->m_obj
 = v_res_2563_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed(lean_object* v_pre_2564_, lean_object* v___f_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__14(v_pre_2564_, v___f_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
return v_res_2577_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15(lean_object* v_post_2578_, lean_object* v_d_2579_, lean_object* v___f_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_box(0);
lean_inc_ref(v___y_2581_);
v___x_2593_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_post_2578_, v_d_2579_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
if (lean_obj_tag(v_a_2594_) == 0)
{
uint8_t v_done_2595_; 
v_done_2595_ = lean_ctor_get_uint8(v_a_2594_, 0);
if (v_done_2595_ == 0)
{
uint8_t v_contextDependent_2596_; lean_object* v___x_2597_; 
lean_dec_ref_known(v___x_2593_, 1);
v_contextDependent_2596_ = lean_ctor_get_uint8(v_a_2594_, 1);
lean_dec_ref_known(v_a_2594_, 0);
v___x_2597_ = lean_apply_12(v___f_2580_, v___x_2592_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, lean_box(0));
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; uint8_t v___y_2600_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
if (v_contextDependent_2596_ == 0)
{
lean_dec(v_a_2598_);
return v___x_2597_;
}
else
{
if (lean_obj_tag(v_a_2598_) == 0)
{
uint8_t v_contextDependent_2610_; 
v_contextDependent_2610_ = lean_ctor_get_uint8(v_a_2598_, 1);
v___y_2600_ = v_contextDependent_2610_;
goto v___jp_2599_;
}
else
{
uint8_t v_contextDependent_2611_; 
v_contextDependent_2611_ = lean_ctor_get_uint8(v_a_2598_, sizeof(void*)*2 + 1);
v___y_2600_ = v_contextDependent_2611_;
goto v___jp_2599_;
}
}
v___jp_2599_:
{
if (v___y_2600_ == 0)
{
lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2608_; 
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; 
v_unused_2609_ = lean_ctor_get(v___x_2597_, 0);
lean_dec(v_unused_2609_);
v___x_2602_ = v___x_2597_;
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
else
{
lean_dec(v___x_2597_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2604_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2598_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2604_);
v___x_2606_ = v___x_2602_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
else
{
lean_dec(v_a_2598_);
return v___x_2597_;
}
}
}
else
{
return v___x_2597_;
}
}
else
{
lean_dec_ref_known(v_a_2594_, 0);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___f_2580_);
return v___x_2593_;
}
}
else
{
uint8_t v_done_2612_; 
v_done_2612_ = lean_ctor_get_uint8(v_a_2594_, sizeof(void*)*2);
if (v_done_2612_ == 0)
{
lean_object* v_e_x27_2613_; lean_object* v_proof_2614_; uint8_t v_contextDependent_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2665_; 
lean_dec_ref_known(v___x_2593_, 1);
v_e_x27_2613_ = lean_ctor_get(v_a_2594_, 0);
v_proof_2614_ = lean_ctor_get(v_a_2594_, 1);
v_contextDependent_2615_ = lean_ctor_get_uint8(v_a_2594_, sizeof(void*)*2 + 1);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_a_2594_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2617_ = v_a_2594_;
v_isShared_2618_ = v_isSharedCheck_2665_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_proof_2614_);
lean_inc(v_e_x27_2613_);
lean_dec(v_a_2594_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2665_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; 
lean_inc(v___y_2590_);
lean_inc_ref(v___y_2589_);
lean_inc(v___y_2588_);
lean_inc_ref(v___y_2587_);
lean_inc(v___y_2586_);
lean_inc_ref(v___y_2585_);
lean_inc_ref(v_e_x27_2613_);
v___x_2619_ = lean_apply_12(v___f_2580_, v___x_2592_, v_e_x27_2613_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, lean_box(0));
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2664_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2664_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2664_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
if (lean_obj_tag(v_a_2620_) == 0)
{
uint8_t v_done_2624_; uint8_t v_contextDependent_2625_; uint8_t v___y_2627_; 
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2581_);
v_done_2624_ = lean_ctor_get_uint8(v_a_2620_, 0);
v_contextDependent_2625_ = lean_ctor_get_uint8(v_a_2620_, 1);
lean_dec_ref_known(v_a_2620_, 0);
if (v_contextDependent_2615_ == 0)
{
v___y_2627_ = v_contextDependent_2625_;
goto v___jp_2626_;
}
else
{
v___y_2627_ = v_contextDependent_2615_;
goto v___jp_2626_;
}
v___jp_2626_:
{
lean_object* v___x_2629_; 
if (v_isShared_2618_ == 0)
{
v___x_2629_ = v___x_2617_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_e_x27_2613_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_proof_2614_);
v___x_2629_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2631_; 
lean_ctor_set_uint8(v___x_2629_, sizeof(void*)*2, v_done_2624_);
lean_ctor_set_uint8(v___x_2629_, sizeof(void*)*2 + 1, v___y_2627_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2629_);
v___x_2631_ = v___x_2622_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
else
{
lean_object* v_e_x27_2634_; lean_object* v_proof_2635_; uint8_t v_done_2636_; uint8_t v_contextDependent_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2663_; 
lean_del_object(v___x_2622_);
lean_del_object(v___x_2617_);
v_e_x27_2634_ = lean_ctor_get(v_a_2620_, 0);
v_proof_2635_ = lean_ctor_get(v_a_2620_, 1);
v_done_2636_ = lean_ctor_get_uint8(v_a_2620_, sizeof(void*)*2);
v_contextDependent_2637_ = lean_ctor_get_uint8(v_a_2620_, sizeof(void*)*2 + 1);
v_isSharedCheck_2663_ = !lean_is_exclusive(v_a_2620_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2639_ = v_a_2620_;
v_isShared_2640_ = v_isSharedCheck_2663_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_proof_2635_);
lean_inc(v_e_x27_2634_);
lean_dec(v_a_2620_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2663_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2641_; 
lean_inc_ref(v_e_x27_2634_);
v___x_2641_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2581_, v_e_x27_2613_, v_proof_2614_, v_e_x27_2634_, v_proof_2635_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2654_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2654_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2654_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
uint8_t v___y_2647_; 
if (v_contextDependent_2615_ == 0)
{
v___y_2647_ = v_contextDependent_2637_;
goto v___jp_2646_;
}
else
{
v___y_2647_ = v_contextDependent_2615_;
goto v___jp_2646_;
}
v___jp_2646_:
{
lean_object* v___x_2649_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 1, v_a_2642_);
v___x_2649_ = v___x_2639_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_e_x27_2634_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_a_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2653_, sizeof(void*)*2, v_done_2636_);
v___x_2649_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2651_; 
lean_ctor_set_uint8(v___x_2649_, sizeof(void*)*2 + 1, v___y_2647_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2649_);
v___x_2651_ = v___x_2644_;
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
return v___x_2651_;
}
}
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_del_object(v___x_2639_);
lean_dec_ref(v_e_x27_2634_);
v_a_2655_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2641_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2641_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2617_);
lean_dec_ref(v_proof_2614_);
lean_dec_ref(v_e_x27_2613_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec_ref(v___y_2581_);
return v___x_2619_;
}
}
}
else
{
lean_dec_ref_known(v_a_2594_, 2);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___f_2580_);
return v___x_2593_;
}
}
}
else
{
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec_ref(v___f_2580_);
return v___x_2593_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_post_2578_ = stack[0].m_obj;
lean_object* v_d_2579_ = stack[1].m_obj;
lean_object* v___f_2580_ = stack[2].m_obj;
lean_object* v___y_2581_ = stack[3].m_obj;
lean_object* v___y_2582_ = stack[4].m_obj;
lean_object* v___y_2583_ = stack[5].m_obj;
lean_object* v___y_2584_ = stack[6].m_obj;
lean_object* v___y_2585_ = stack[7].m_obj;
lean_object* v___y_2586_ = stack[8].m_obj;
lean_object* v___y_2587_ = stack[9].m_obj;
lean_object* v___y_2588_ = stack[10].m_obj;
lean_object* v___y_2589_ = stack[11].m_obj;
lean_object* v___y_2590_ = stack[12].m_obj;
lean_object* v_res_2666_;
v_res_2666_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__15(v_post_2578_, v_d_2579_, v___f_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
stack->m_obj
 = v_res_2666_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed(lean_object* v_post_2667_, lean_object* v_d_2668_, lean_object* v___f_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__15(v_post_2667_, v_d_2668_, v___f_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec_ref(v_post_2667_);
return v_res_2681_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16(lean_object* v_pre_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v___x_2694_; 
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc(v___y_2690_);
lean_inc_ref(v___y_2689_);
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2687_);
lean_inc_ref(v___y_2683_);
v___x_2694_ = lean_apply_11(v_pre_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, lean_box(0));
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
if (lean_obj_tag(v_a_2695_) == 0)
{
uint8_t v_done_2696_; 
v_done_2696_ = lean_ctor_get_uint8(v_a_2695_, 0);
if (v_done_2696_ == 0)
{
uint8_t v_contextDependent_2697_; lean_object* v___x_2698_; 
lean_dec_ref_known(v___x_2694_, 1);
v_contextDependent_2697_ = lean_ctor_get_uint8(v_a_2695_, 1);
lean_dec_ref_known(v_a_2695_, 0);
v___x_2698_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v___y_2683_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; uint8_t v___y_2701_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
if (v_contextDependent_2697_ == 0)
{
return v___x_2698_;
}
else
{
if (lean_obj_tag(v_a_2699_) == 0)
{
uint8_t v_contextDependent_2711_; 
v_contextDependent_2711_ = lean_ctor_get_uint8(v_a_2699_, 1);
v___y_2701_ = v_contextDependent_2711_;
goto v___jp_2700_;
}
else
{
uint8_t v_contextDependent_2712_; 
v_contextDependent_2712_ = lean_ctor_get_uint8(v_a_2699_, sizeof(void*)*2 + 1);
v___y_2701_ = v_contextDependent_2712_;
goto v___jp_2700_;
}
}
v___jp_2700_:
{
if (v___y_2701_ == 0)
{
lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2709_; 
lean_inc(v_a_2699_);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2709_ == 0)
{
lean_object* v_unused_2710_; 
v_unused_2710_ = lean_ctor_get(v___x_2698_, 0);
lean_dec(v_unused_2710_);
v___x_2703_ = v___x_2698_;
v_isShared_2704_ = v_isSharedCheck_2709_;
goto v_resetjp_2702_;
}
else
{
lean_dec(v___x_2698_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2709_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2705_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2699_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___x_2705_);
v___x_2707_ = v___x_2703_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
else
{
return v___x_2698_;
}
}
}
else
{
return v___x_2698_;
}
}
else
{
lean_dec_ref_known(v_a_2695_, 0);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec_ref(v___y_2683_);
return v___x_2694_;
}
}
else
{
uint8_t v_done_2713_; 
v_done_2713_ = lean_ctor_get_uint8(v_a_2695_, sizeof(void*)*2);
if (v_done_2713_ == 0)
{
lean_object* v_e_x27_2714_; lean_object* v_proof_2715_; uint8_t v_contextDependent_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2766_; 
lean_dec_ref_known(v___x_2694_, 1);
v_e_x27_2714_ = lean_ctor_get(v_a_2695_, 0);
v_proof_2715_ = lean_ctor_get(v_a_2695_, 1);
v_contextDependent_2716_ = lean_ctor_get_uint8(v_a_2695_, sizeof(void*)*2 + 1);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_a_2695_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2718_ = v_a_2695_;
v_isShared_2719_ = v_isSharedCheck_2766_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_proof_2715_);
lean_inc(v_e_x27_2714_);
lean_dec(v_a_2695_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2766_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; 
lean_inc_ref(v_e_x27_2714_);
v___x_2720_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v_e_x27_2714_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2765_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2723_ = v___x_2720_;
v_isShared_2724_ = v_isSharedCheck_2765_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2765_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
if (lean_obj_tag(v_a_2721_) == 0)
{
uint8_t v_done_2725_; uint8_t v_contextDependent_2726_; uint8_t v___y_2728_; 
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec_ref(v___y_2683_);
v_done_2725_ = lean_ctor_get_uint8(v_a_2721_, 0);
v_contextDependent_2726_ = lean_ctor_get_uint8(v_a_2721_, 1);
lean_dec_ref_known(v_a_2721_, 0);
if (v_contextDependent_2716_ == 0)
{
v___y_2728_ = v_contextDependent_2726_;
goto v___jp_2727_;
}
else
{
v___y_2728_ = v_contextDependent_2716_;
goto v___jp_2727_;
}
v___jp_2727_:
{
lean_object* v___x_2730_; 
if (v_isShared_2719_ == 0)
{
v___x_2730_ = v___x_2718_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_e_x27_2714_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_proof_2715_);
v___x_2730_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2732_; 
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*2, v_done_2725_);
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*2 + 1, v___y_2728_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2730_);
v___x_2732_ = v___x_2723_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
else
{
lean_object* v_e_x27_2735_; lean_object* v_proof_2736_; uint8_t v_done_2737_; uint8_t v_contextDependent_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2764_; 
lean_del_object(v___x_2723_);
lean_del_object(v___x_2718_);
v_e_x27_2735_ = lean_ctor_get(v_a_2721_, 0);
v_proof_2736_ = lean_ctor_get(v_a_2721_, 1);
v_done_2737_ = lean_ctor_get_uint8(v_a_2721_, sizeof(void*)*2);
v_contextDependent_2738_ = lean_ctor_get_uint8(v_a_2721_, sizeof(void*)*2 + 1);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_a_2721_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2740_ = v_a_2721_;
v_isShared_2741_ = v_isSharedCheck_2764_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_proof_2736_);
lean_inc(v_e_x27_2735_);
lean_dec(v_a_2721_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2764_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; 
lean_inc_ref(v_e_x27_2735_);
v___x_2742_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2683_, v_e_x27_2714_, v_proof_2715_, v_e_x27_2735_, v_proof_2736_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2755_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2755_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2755_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
uint8_t v___y_2748_; 
if (v_contextDependent_2716_ == 0)
{
v___y_2748_ = v_contextDependent_2738_;
goto v___jp_2747_;
}
else
{
v___y_2748_ = v_contextDependent_2716_;
goto v___jp_2747_;
}
v___jp_2747_:
{
lean_object* v___x_2750_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 1, v_a_2743_);
v___x_2750_ = v___x_2740_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_e_x27_2735_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_a_2743_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, sizeof(void*)*2, v_done_2737_);
v___x_2750_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2752_; 
lean_ctor_set_uint8(v___x_2750_, sizeof(void*)*2 + 1, v___y_2748_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2750_);
v___x_2752_ = v___x_2745_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_del_object(v___x_2740_);
lean_dec_ref(v_e_x27_2735_);
v_a_2756_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2742_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2742_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2718_);
lean_dec_ref(v_proof_2715_);
lean_dec_ref(v_e_x27_2714_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec_ref(v___y_2683_);
return v___x_2720_;
}
}
}
else
{
lean_dec_ref_known(v_a_2695_, 2);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec_ref(v___y_2683_);
return v___x_2694_;
}
}
}
else
{
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec_ref(v___y_2683_);
return v___x_2694_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2682_ = stack[0].m_obj;
lean_object* v___y_2683_ = stack[1].m_obj;
lean_object* v___y_2684_ = stack[2].m_obj;
lean_object* v___y_2685_ = stack[3].m_obj;
lean_object* v___y_2686_ = stack[4].m_obj;
lean_object* v___y_2687_ = stack[5].m_obj;
lean_object* v___y_2688_ = stack[6].m_obj;
lean_object* v___y_2689_ = stack[7].m_obj;
lean_object* v___y_2690_ = stack[8].m_obj;
lean_object* v___y_2691_ = stack[9].m_obj;
lean_object* v___y_2692_ = stack[10].m_obj;
lean_object* v_res_2767_;
v_res_2767_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__16(v_pre_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
stack->m_obj
 = v_res_2767_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed(lean_object* v_pre_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__16(v_pre_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v_res_2780_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17(lean_object* v___f_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_box(0);
lean_inc_ref(v___y_2782_);
v___x_2794_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_2782_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
if (lean_obj_tag(v_a_2795_) == 0)
{
uint8_t v_done_2796_; 
v_done_2796_ = lean_ctor_get_uint8(v_a_2795_, 0);
if (v_done_2796_ == 0)
{
uint8_t v_contextDependent_2797_; lean_object* v___x_2798_; 
lean_dec_ref_known(v___x_2794_, 1);
v_contextDependent_2797_ = lean_ctor_get_uint8(v_a_2795_, 1);
lean_dec_ref_known(v_a_2795_, 0);
v___x_2798_ = lean_apply_12(v___f_2781_, v___x_2793_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, lean_box(0));
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; uint8_t v___y_2801_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
if (v_contextDependent_2797_ == 0)
{
lean_dec(v_a_2799_);
return v___x_2798_;
}
else
{
if (lean_obj_tag(v_a_2799_) == 0)
{
uint8_t v_contextDependent_2811_; 
v_contextDependent_2811_ = lean_ctor_get_uint8(v_a_2799_, 1);
v___y_2801_ = v_contextDependent_2811_;
goto v___jp_2800_;
}
else
{
uint8_t v_contextDependent_2812_; 
v_contextDependent_2812_ = lean_ctor_get_uint8(v_a_2799_, sizeof(void*)*2 + 1);
v___y_2801_ = v_contextDependent_2812_;
goto v___jp_2800_;
}
}
v___jp_2800_:
{
if (v___y_2801_ == 0)
{
lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2809_; 
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; 
v_unused_2810_ = lean_ctor_get(v___x_2798_, 0);
lean_dec(v_unused_2810_);
v___x_2803_ = v___x_2798_;
v_isShared_2804_ = v_isSharedCheck_2809_;
goto v_resetjp_2802_;
}
else
{
lean_dec(v___x_2798_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2809_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2805_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2799_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2805_);
v___x_2807_ = v___x_2803_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
else
{
lean_dec(v_a_2799_);
return v___x_2798_;
}
}
}
else
{
return v___x_2798_;
}
}
else
{
lean_dec_ref_known(v_a_2795_, 0);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___f_2781_);
return v___x_2794_;
}
}
else
{
uint8_t v_done_2813_; 
v_done_2813_ = lean_ctor_get_uint8(v_a_2795_, sizeof(void*)*2);
if (v_done_2813_ == 0)
{
lean_object* v_e_x27_2814_; lean_object* v_proof_2815_; uint8_t v_contextDependent_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2866_; 
lean_dec_ref_known(v___x_2794_, 1);
v_e_x27_2814_ = lean_ctor_get(v_a_2795_, 0);
v_proof_2815_ = lean_ctor_get(v_a_2795_, 1);
v_contextDependent_2816_ = lean_ctor_get_uint8(v_a_2795_, sizeof(void*)*2 + 1);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_a_2795_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2818_ = v_a_2795_;
v_isShared_2819_ = v_isSharedCheck_2866_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_proof_2815_);
lean_inc(v_e_x27_2814_);
lean_dec(v_a_2795_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2866_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; 
lean_inc(v___y_2791_);
lean_inc_ref(v___y_2790_);
lean_inc(v___y_2789_);
lean_inc_ref(v___y_2788_);
lean_inc(v___y_2787_);
lean_inc_ref(v___y_2786_);
lean_inc_ref(v_e_x27_2814_);
v___x_2820_ = lean_apply_12(v___f_2781_, v___x_2793_, v_e_x27_2814_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, lean_box(0));
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2865_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2823_ = v___x_2820_;
v_isShared_2824_ = v_isSharedCheck_2865_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2820_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2865_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
if (lean_obj_tag(v_a_2821_) == 0)
{
uint8_t v_done_2825_; uint8_t v_contextDependent_2826_; uint8_t v___y_2828_; 
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec_ref(v___y_2782_);
v_done_2825_ = lean_ctor_get_uint8(v_a_2821_, 0);
v_contextDependent_2826_ = lean_ctor_get_uint8(v_a_2821_, 1);
lean_dec_ref_known(v_a_2821_, 0);
if (v_contextDependent_2816_ == 0)
{
v___y_2828_ = v_contextDependent_2826_;
goto v___jp_2827_;
}
else
{
v___y_2828_ = v_contextDependent_2816_;
goto v___jp_2827_;
}
v___jp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2819_ == 0)
{
v___x_2830_ = v___x_2818_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_e_x27_2814_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_proof_2815_);
v___x_2830_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2832_; 
lean_ctor_set_uint8(v___x_2830_, sizeof(void*)*2, v_done_2825_);
lean_ctor_set_uint8(v___x_2830_, sizeof(void*)*2 + 1, v___y_2828_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2830_);
v___x_2832_ = v___x_2823_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
lean_object* v_e_x27_2835_; lean_object* v_proof_2836_; uint8_t v_done_2837_; uint8_t v_contextDependent_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2864_; 
lean_del_object(v___x_2823_);
lean_del_object(v___x_2818_);
v_e_x27_2835_ = lean_ctor_get(v_a_2821_, 0);
v_proof_2836_ = lean_ctor_get(v_a_2821_, 1);
v_done_2837_ = lean_ctor_get_uint8(v_a_2821_, sizeof(void*)*2);
v_contextDependent_2838_ = lean_ctor_get_uint8(v_a_2821_, sizeof(void*)*2 + 1);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_a_2821_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2840_ = v_a_2821_;
v_isShared_2841_ = v_isSharedCheck_2864_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_proof_2836_);
lean_inc(v_e_x27_2835_);
lean_dec(v_a_2821_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2864_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; 
lean_inc_ref(v_e_x27_2835_);
v___x_2842_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2782_, v_e_x27_2814_, v_proof_2815_, v_e_x27_2835_, v_proof_2836_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2855_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2855_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2855_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
uint8_t v___y_2848_; 
if (v_contextDependent_2816_ == 0)
{
v___y_2848_ = v_contextDependent_2838_;
goto v___jp_2847_;
}
else
{
v___y_2848_ = v_contextDependent_2816_;
goto v___jp_2847_;
}
v___jp_2847_:
{
lean_object* v___x_2850_; 
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 1, v_a_2843_);
v___x_2850_ = v___x_2840_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_e_x27_2835_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_a_2843_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, sizeof(void*)*2, v_done_2837_);
v___x_2850_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2852_; 
lean_ctor_set_uint8(v___x_2850_, sizeof(void*)*2 + 1, v___y_2848_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2850_);
v___x_2852_ = v___x_2845_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_del_object(v___x_2840_);
lean_dec_ref(v_e_x27_2835_);
v_a_2856_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2842_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2842_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2818_);
lean_dec_ref(v_proof_2815_);
lean_dec_ref(v_e_x27_2814_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec_ref(v___y_2782_);
return v___x_2820_;
}
}
}
else
{
lean_dec_ref_known(v_a_2795_, 2);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___f_2781_);
return v___x_2794_;
}
}
}
else
{
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec_ref(v___f_2781_);
return v___x_2794_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__17_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2781_ = stack[0].m_obj;
lean_object* v___y_2782_ = stack[1].m_obj;
lean_object* v___y_2783_ = stack[2].m_obj;
lean_object* v___y_2784_ = stack[3].m_obj;
lean_object* v___y_2785_ = stack[4].m_obj;
lean_object* v___y_2786_ = stack[5].m_obj;
lean_object* v___y_2787_ = stack[6].m_obj;
lean_object* v___y_2788_ = stack[7].m_obj;
lean_object* v___y_2789_ = stack[8].m_obj;
lean_object* v___y_2790_ = stack[9].m_obj;
lean_object* v___y_2791_ = stack[10].m_obj;
lean_object* v_res_2867_;
v_res_2867_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__17(v___f_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
stack->m_obj
 = v_res_2867_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed(lean_object* v___f_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__17(v___f_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
return v_res_2880_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18(lean_object* v___f_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v___y_2894_; lean_object* v___y_2895_; uint8_t v___y_2896_; uint8_t v___y_2897_; lean_object* v___y_2901_; uint8_t v___y_2902_; lean_object* v___y_2903_; uint8_t v___y_2904_; lean_object* v___y_2908_; lean_object* v_e_x27_2909_; lean_object* v_proof_2910_; uint8_t v_done_2911_; uint8_t v_contextDependent_2912_; lean_object* v___y_2934_; lean_object* v___y_2935_; uint8_t v___y_2936_; lean_object* v___y_2940_; lean_object* v_a_2941_; lean_object* v___y_2953_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_box(0);
lean_inc_ref(v___y_2882_);
v___x_2956_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_2882_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
if (lean_obj_tag(v_a_2957_) == 0)
{
uint8_t v_done_2958_; 
v_done_2958_ = lean_ctor_get_uint8(v_a_2957_, 0);
if (v_done_2958_ == 0)
{
uint8_t v_contextDependent_2959_; lean_object* v___x_2960_; 
lean_dec_ref_known(v___x_2956_, 1);
v_contextDependent_2959_ = lean_ctor_get_uint8(v_a_2957_, 1);
lean_dec_ref_known(v_a_2957_, 0);
lean_inc(v___y_2891_);
lean_inc_ref(v___y_2890_);
lean_inc(v___y_2889_);
lean_inc_ref(v___y_2888_);
lean_inc(v___y_2887_);
lean_inc_ref(v___y_2886_);
lean_inc_ref(v___y_2882_);
v___x_2960_ = lean_apply_12(v___f_2881_, v___x_2955_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, lean_box(0));
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; uint8_t v___y_2963_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
if (v_contextDependent_2959_ == 0)
{
v___y_2940_ = v___x_2960_;
v_a_2941_ = v_a_2961_;
goto v___jp_2939_;
}
else
{
if (lean_obj_tag(v_a_2961_) == 0)
{
uint8_t v_contextDependent_2973_; 
v_contextDependent_2973_ = lean_ctor_get_uint8(v_a_2961_, 1);
v___y_2963_ = v_contextDependent_2973_;
goto v___jp_2962_;
}
else
{
uint8_t v_contextDependent_2974_; 
v_contextDependent_2974_ = lean_ctor_get_uint8(v_a_2961_, sizeof(void*)*2 + 1);
v___y_2963_ = v_contextDependent_2974_;
goto v___jp_2962_;
}
}
v___jp_2962_:
{
if (v___y_2963_ == 0)
{
lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2971_; 
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; 
v_unused_2972_ = lean_ctor_get(v___x_2960_, 0);
lean_dec(v_unused_2972_);
v___x_2965_ = v___x_2960_;
v_isShared_2966_ = v_isSharedCheck_2971_;
goto v_resetjp_2964_;
}
else
{
lean_dec(v___x_2960_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2971_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2967_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2961_);
lean_inc_ref(v___x_2967_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 0, v___x_2967_);
v___x_2969_ = v___x_2965_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
v___y_2940_ = v___x_2969_;
v_a_2941_ = v___x_2967_;
goto v___jp_2939_;
}
}
}
else
{
v___y_2940_ = v___x_2960_;
v_a_2941_ = v_a_2961_;
goto v___jp_2939_;
}
}
}
else
{
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2882_);
return v___x_2960_;
}
}
else
{
lean_dec_ref_known(v_a_2957_, 0);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___f_2881_);
v___y_2953_ = v___x_2956_;
goto v___jp_2952_;
}
}
else
{
uint8_t v_done_2975_; 
v_done_2975_ = lean_ctor_get_uint8(v_a_2957_, sizeof(void*)*2);
if (v_done_2975_ == 0)
{
lean_object* v_e_x27_2976_; lean_object* v_proof_2977_; uint8_t v_contextDependent_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref_known(v___x_2956_, 1);
v_e_x27_2976_ = lean_ctor_get(v_a_2957_, 0);
v_proof_2977_ = lean_ctor_get(v_a_2957_, 1);
v_contextDependent_2978_ = lean_ctor_get_uint8(v_a_2957_, sizeof(void*)*2 + 1);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_a_2957_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_2980_ = v_a_2957_;
v_isShared_2981_ = v_isSharedCheck_3028_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_proof_2977_);
lean_inc(v_e_x27_2976_);
lean_dec(v_a_2957_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3028_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; 
lean_inc(v___y_2891_);
lean_inc_ref(v___y_2890_);
lean_inc(v___y_2889_);
lean_inc_ref(v___y_2888_);
lean_inc(v___y_2887_);
lean_inc_ref(v___y_2886_);
lean_inc_ref(v_e_x27_2976_);
v___x_2982_ = lean_apply_12(v___f_2881_, v___x_2955_, v_e_x27_2976_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, lean_box(0));
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3027_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_3027_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3027_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
if (lean_obj_tag(v_a_2983_) == 0)
{
uint8_t v_done_2987_; uint8_t v_contextDependent_2988_; uint8_t v___y_2990_; 
v_done_2987_ = lean_ctor_get_uint8(v_a_2983_, 0);
v_contextDependent_2988_ = lean_ctor_get_uint8(v_a_2983_, 1);
lean_dec_ref_known(v_a_2983_, 0);
if (v_contextDependent_2978_ == 0)
{
v___y_2990_ = v_contextDependent_2988_;
goto v___jp_2989_;
}
else
{
v___y_2990_ = v_contextDependent_2978_;
goto v___jp_2989_;
}
v___jp_2989_:
{
lean_object* v___x_2992_; 
lean_inc_ref(v_proof_2977_);
lean_inc_ref(v_e_x27_2976_);
if (v_isShared_2981_ == 0)
{
v___x_2992_ = v___x_2980_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_e_x27_2976_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_proof_2977_);
v___x_2992_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2994_; 
lean_ctor_set_uint8(v___x_2992_, sizeof(void*)*2, v_done_2987_);
lean_ctor_set_uint8(v___x_2992_, sizeof(void*)*2 + 1, v___y_2990_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2992_);
v___x_2994_ = v___x_2985_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
v___y_2908_ = v___x_2994_;
v_e_x27_2909_ = v_e_x27_2976_;
v_proof_2910_ = v_proof_2977_;
v_done_2911_ = v_done_2987_;
v_contextDependent_2912_ = v___y_2990_;
goto v___jp_2907_;
}
}
}
}
else
{
lean_object* v_e_x27_2997_; lean_object* v_proof_2998_; uint8_t v_done_2999_; uint8_t v_contextDependent_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3026_; 
lean_del_object(v___x_2985_);
lean_del_object(v___x_2980_);
v_e_x27_2997_ = lean_ctor_get(v_a_2983_, 0);
v_proof_2998_ = lean_ctor_get(v_a_2983_, 1);
v_done_2999_ = lean_ctor_get_uint8(v_a_2983_, sizeof(void*)*2);
v_contextDependent_3000_ = lean_ctor_get_uint8(v_a_2983_, sizeof(void*)*2 + 1);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_a_2983_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3002_ = v_a_2983_;
v_isShared_3003_ = v_isSharedCheck_3026_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_proof_2998_);
lean_inc(v_e_x27_2997_);
lean_dec(v_a_2983_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3026_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; 
lean_inc_ref(v_e_x27_2997_);
lean_inc_ref(v___y_2882_);
v___x_3004_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2882_, v_e_x27_2976_, v_proof_2977_, v_e_x27_2997_, v_proof_2998_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3017_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3017_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3017_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
uint8_t v___y_3010_; 
if (v_contextDependent_2978_ == 0)
{
v___y_3010_ = v_contextDependent_3000_;
goto v___jp_3009_;
}
else
{
v___y_3010_ = v_contextDependent_2978_;
goto v___jp_3009_;
}
v___jp_3009_:
{
lean_object* v___x_3012_; 
lean_inc(v_a_3005_);
lean_inc_ref(v_e_x27_2997_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 1, v_a_3005_);
v___x_3012_ = v___x_3002_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_e_x27_2997_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_a_3005_);
lean_ctor_set_uint8(v_reuseFailAlloc_3016_, sizeof(void*)*2, v_done_2999_);
v___x_3012_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3014_; 
lean_ctor_set_uint8(v___x_3012_, sizeof(void*)*2 + 1, v___y_3010_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3012_);
v___x_3014_ = v___x_3007_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
v___y_2908_ = v___x_3014_;
v_e_x27_2909_ = v_e_x27_2997_;
v_proof_2910_ = v_a_3005_;
v_done_2911_ = v_done_2999_;
v_contextDependent_2912_ = v___y_3010_;
goto v___jp_2907_;
}
}
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_del_object(v___x_3002_);
lean_dec_ref(v_e_x27_2997_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2882_);
v_a_3018_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3004_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3004_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2980_);
lean_dec_ref(v_proof_2977_);
lean_dec_ref(v_e_x27_2976_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2882_);
return v___x_2982_;
}
}
}
else
{
lean_dec_ref_known(v_a_2957_, 2);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___f_2881_);
v___y_2953_ = v___x_2956_;
goto v___jp_2952_;
}
}
}
else
{
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___f_2881_);
v___y_2953_ = v___x_2956_;
goto v___jp_2952_;
}
v___jp_2893_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2898_, 0, v___y_2894_);
lean_ctor_set(v___x_2898_, 1, v___y_2895_);
lean_ctor_set_uint8(v___x_2898_, sizeof(void*)*2, v___y_2896_);
lean_ctor_set_uint8(v___x_2898_, sizeof(void*)*2 + 1, v___y_2897_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
v___jp_2900_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2905_, 0, v___y_2901_);
lean_ctor_set(v___x_2905_, 1, v___y_2903_);
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*2, v___y_2902_);
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*2 + 1, v___y_2904_);
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
return v___x_2906_;
}
v___jp_2907_:
{
if (v_done_2911_ == 0)
{
lean_object* v___x_2913_; 
lean_dec_ref(v___y_2908_);
lean_inc_ref(v_e_x27_2909_);
v___x_2913_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v_e_x27_2909_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2913_, 1);
if (lean_obj_tag(v_a_2914_) == 0)
{
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2882_);
if (v_contextDependent_2912_ == 0)
{
uint8_t v_done_2915_; uint8_t v_contextDependent_2916_; 
v_done_2915_ = lean_ctor_get_uint8(v_a_2914_, 0);
v_contextDependent_2916_ = lean_ctor_get_uint8(v_a_2914_, 1);
lean_dec_ref_known(v_a_2914_, 0);
v___y_2894_ = v_e_x27_2909_;
v___y_2895_ = v_proof_2910_;
v___y_2896_ = v_done_2915_;
v___y_2897_ = v_contextDependent_2916_;
goto v___jp_2893_;
}
else
{
uint8_t v_done_2917_; 
v_done_2917_ = lean_ctor_get_uint8(v_a_2914_, 0);
lean_dec_ref_known(v_a_2914_, 0);
v___y_2894_ = v_e_x27_2909_;
v___y_2895_ = v_proof_2910_;
v___y_2896_ = v_done_2917_;
v___y_2897_ = v_contextDependent_2912_;
goto v___jp_2893_;
}
}
else
{
lean_object* v_e_x27_2918_; lean_object* v_proof_2919_; uint8_t v_done_2920_; uint8_t v_contextDependent_2921_; lean_object* v___x_2922_; 
v_e_x27_2918_ = lean_ctor_get(v_a_2914_, 0);
lean_inc_ref_n(v_e_x27_2918_, 2);
v_proof_2919_ = lean_ctor_get(v_a_2914_, 1);
lean_inc_ref(v_proof_2919_);
v_done_2920_ = lean_ctor_get_uint8(v_a_2914_, sizeof(void*)*2);
v_contextDependent_2921_ = lean_ctor_get_uint8(v_a_2914_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2914_, 2);
v___x_2922_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2882_, v_e_x27_2909_, v_proof_2910_, v_e_x27_2918_, v_proof_2919_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
if (lean_obj_tag(v___x_2922_) == 0)
{
if (v_contextDependent_2912_ == 0)
{
lean_object* v_a_2923_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v___y_2901_ = v_e_x27_2918_;
v___y_2902_ = v_done_2920_;
v___y_2903_ = v_a_2923_;
v___y_2904_ = v_contextDependent_2921_;
goto v___jp_2900_;
}
else
{
lean_object* v_a_2924_; 
v_a_2924_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2922_, 1);
v___y_2901_ = v_e_x27_2918_;
v___y_2902_ = v_done_2920_;
v___y_2903_ = v_a_2924_;
v___y_2904_ = v_contextDependent_2912_;
goto v___jp_2900_;
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec_ref(v_e_x27_2918_);
v_a_2925_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2922_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2922_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_2910_);
lean_dec_ref(v_e_x27_2909_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2882_);
return v___x_2913_;
}
}
else
{
lean_dec_ref(v_proof_2910_);
lean_dec_ref(v_e_x27_2909_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2882_);
return v___y_2908_;
}
}
v___jp_2933_:
{
if (v___y_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
lean_dec_ref(v___y_2935_);
v___x_2937_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_2934_);
v___x_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
return v___x_2938_;
}
else
{
lean_dec_ref(v___y_2934_);
return v___y_2935_;
}
}
v___jp_2939_:
{
if (lean_obj_tag(v_a_2941_) == 0)
{
uint8_t v_done_2942_; 
v_done_2942_ = lean_ctor_get_uint8(v_a_2941_, 0);
if (v_done_2942_ == 0)
{
uint8_t v_contextDependent_2943_; lean_object* v___x_2944_; 
lean_dec_ref(v___y_2940_);
v_contextDependent_2943_ = lean_ctor_get_uint8(v_a_2941_, 1);
lean_dec_ref_known(v_a_2941_, 0);
v___x_2944_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v___y_2882_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
if (lean_obj_tag(v___x_2944_) == 0)
{
if (v_contextDependent_2943_ == 0)
{
return v___x_2944_;
}
else
{
lean_object* v_a_2945_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
if (lean_obj_tag(v_a_2945_) == 0)
{
uint8_t v_contextDependent_2946_; 
v_contextDependent_2946_ = lean_ctor_get_uint8(v_a_2945_, 1);
v___y_2934_ = v_a_2945_;
v___y_2935_ = v___x_2944_;
v___y_2936_ = v_contextDependent_2946_;
goto v___jp_2933_;
}
else
{
uint8_t v_contextDependent_2947_; 
v_contextDependent_2947_ = lean_ctor_get_uint8(v_a_2945_, sizeof(void*)*2 + 1);
v___y_2934_ = v_a_2945_;
v___y_2935_ = v___x_2944_;
v___y_2936_ = v_contextDependent_2947_;
goto v___jp_2933_;
}
}
}
else
{
return v___x_2944_;
}
}
else
{
lean_dec_ref_known(v_a_2941_, 0);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2882_);
return v___y_2940_;
}
}
else
{
lean_object* v_e_x27_2948_; lean_object* v_proof_2949_; uint8_t v_done_2950_; uint8_t v_contextDependent_2951_; 
v_e_x27_2948_ = lean_ctor_get(v_a_2941_, 0);
lean_inc_ref(v_e_x27_2948_);
v_proof_2949_ = lean_ctor_get(v_a_2941_, 1);
lean_inc_ref(v_proof_2949_);
v_done_2950_ = lean_ctor_get_uint8(v_a_2941_, sizeof(void*)*2);
v_contextDependent_2951_ = lean_ctor_get_uint8(v_a_2941_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2941_, 2);
v___y_2908_ = v___y_2940_;
v_e_x27_2909_ = v_e_x27_2948_;
v_proof_2910_ = v_proof_2949_;
v_done_2911_ = v_done_2950_;
v_contextDependent_2912_ = v_contextDependent_2951_;
goto v___jp_2907_;
}
}
v___jp_2952_:
{
if (lean_obj_tag(v___y_2953_) == 0)
{
lean_object* v_a_2954_; 
v_a_2954_ = lean_ctor_get(v___y_2953_, 0);
lean_inc(v_a_2954_);
v___y_2940_ = v___y_2953_;
v_a_2941_ = v_a_2954_;
goto v___jp_2939_;
}
else
{
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2882_);
return v___y_2953_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymMethods___lam__18_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2881_ = stack[0].m_obj;
lean_object* v___y_2882_ = stack[1].m_obj;
lean_object* v___y_2883_ = stack[2].m_obj;
lean_object* v___y_2884_ = stack[3].m_obj;
lean_object* v___y_2885_ = stack[4].m_obj;
lean_object* v___y_2886_ = stack[5].m_obj;
lean_object* v___y_2887_ = stack[6].m_obj;
lean_object* v___y_2888_ = stack[7].m_obj;
lean_object* v___y_2889_ = stack[8].m_obj;
lean_object* v___y_2890_ = stack[9].m_obj;
lean_object* v___y_2891_ = stack[10].m_obj;
lean_object* v_res_3029_;
v_res_3029_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__18(v___f_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
stack->m_obj
 = v_res_3029_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18___boxed(lean_object* v___f_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__18(v___f_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object* v_config_3068_, lean_object* v_thms_3069_){
_start:
{
uint8_t v_zetaDelta_3070_; uint8_t v_zeta_3071_; lean_object* v___f_3072_; lean_object* v_d_3073_; lean_object* v___f_3074_; lean_object* v___f_3075_; lean_object* v___f_3076_; lean_object* v_pre_3078_; lean_object* v_pre_3084_; 
v_zetaDelta_3070_ = lean_ctor_get_uint8(v_config_3068_, sizeof(void*)*14 + 19);
v_zeta_3071_ = lean_ctor_get_uint8(v_config_3068_, sizeof(void*)*14 + 20);
v___f_3072_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__10));
v_d_3073_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__11));
lean_inc_ref(v_thms_3069_);
v___f_3074_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed), 14, 2);
lean_closure_set(v___f_3074_, 0, v_thms_3069_);
lean_closure_set(v___f_3074_, 1, v_d_3073_);
v___f_3075_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed), 14, 2);
lean_closure_set(v___f_3075_, 0, v_d_3073_);
lean_closure_set(v___f_3075_, 1, v___f_3074_);
v___f_3076_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed), 13, 1);
lean_closure_set(v___f_3076_, 0, v___f_3075_);
if (v_zeta_3071_ == 0)
{
lean_object* v_pre_3086_; 
v_pre_3086_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__12));
v_pre_3084_ = v_pre_3086_;
goto v___jp_3083_;
}
else
{
lean_object* v_pre_3087_; 
v_pre_3087_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__13));
v_pre_3084_ = v_pre_3087_;
goto v___jp_3083_;
}
v___jp_3077_:
{
lean_object* v_post_3079_; lean_object* v_pre_3080_; lean_object* v_post_3081_; lean_object* v___x_3082_; 
v_post_3079_ = lean_ctor_get(v_thms_3069_, 1);
lean_inc_ref(v_post_3079_);
lean_dec_ref(v_thms_3069_);
v_pre_3080_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed), 13, 2);
lean_closure_set(v_pre_3080_, 0, v_pre_3078_);
lean_closure_set(v_pre_3080_, 1, v___f_3076_);
v_post_3081_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed), 14, 3);
lean_closure_set(v_post_3081_, 0, v_post_3079_);
lean_closure_set(v_post_3081_, 1, v_d_3073_);
lean_closure_set(v_post_3081_, 2, v___f_3072_);
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v_pre_3080_);
lean_ctor_set(v___x_3082_, 1, v_post_3081_);
return v___x_3082_;
}
v___jp_3083_:
{
if (v_zetaDelta_3070_ == 0)
{
lean_inc_ref(v_pre_3084_);
v_pre_3078_ = v_pre_3084_;
goto v___jp_3077_;
}
else
{
lean_object* v_pre_3085_; 
lean_inc_ref(v_pre_3084_);
v_pre_3085_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed), 12, 1);
lean_closure_set(v_pre_3085_, 0, v_pre_3084_);
v_pre_3078_ = v_pre_3085_;
goto v___jp_3077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___boxed(lean_object* v_config_3088_, lean_object* v_thms_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_Meta_Grind_mkNormSymMethods(v_config_3088_, v_thms_3089_);
lean_dec_ref(v_config_3088_);
return v_res_3090_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(lean_object* v_x_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; 
lean_inc_ref(v___y_3092_);
v___x_3103_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v___y_3092_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
if (lean_obj_tag(v_a_3104_) == 0)
{
uint8_t v_done_3105_; 
v_done_3105_ = lean_ctor_get_uint8(v_a_3104_, 0);
lean_dec_ref_known(v_a_3104_, 0);
if (v_done_3105_ == 0)
{
lean_object* v___x_3106_; 
lean_dec_ref_known(v___x_3103_, 1);
v___x_3106_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_3092_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
lean_dec_ref(v___y_3092_);
return v___x_3106_;
}
else
{
lean_dec_ref(v___y_3092_);
return v___x_3103_;
}
}
else
{
uint8_t v_done_3107_; 
lean_dec_ref(v___y_3092_);
v_done_3107_ = lean_ctor_get_uint8(v_a_3104_, sizeof(void*)*1);
if (v_done_3107_ == 0)
{
lean_object* v_e_x27_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref_known(v___x_3103_, 1);
v_e_x27_3108_ = lean_ctor_get(v_a_3104_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_a_3104_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3110_ = v_a_3104_;
v_isShared_3111_ = v_isSharedCheck_3126_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_e_x27_3108_);
lean_dec(v_a_3104_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3126_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; 
v___x_3112_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_x27_3108_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
if (lean_obj_tag(v_a_3113_) == 0)
{
lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3124_; 
lean_inc_ref(v_a_3113_);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v___x_3112_, 0);
lean_dec(v_unused_3125_);
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3124_;
goto v_resetjp_3114_;
}
else
{
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3124_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
uint8_t v_done_3117_; lean_object* v___x_3119_; 
v_done_3117_ = lean_ctor_get_uint8(v_a_3113_, 0);
lean_dec_ref_known(v_a_3113_, 0);
if (v_isShared_3111_ == 0)
{
v___x_3119_ = v___x_3110_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_e_x27_3108_);
v___x_3119_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3121_; 
lean_ctor_set_uint8(v___x_3119_, sizeof(void*)*1, v_done_3117_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3119_);
v___x_3121_ = v___x_3115_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
else
{
lean_del_object(v___x_3110_);
lean_dec_ref(v_e_x27_3108_);
return v___x_3112_;
}
}
else
{
lean_del_object(v___x_3110_);
lean_dec_ref(v_e_x27_3108_);
return v___x_3112_;
}
}
}
else
{
lean_dec_ref_known(v_a_3104_, 1);
return v___x_3103_;
}
}
}
else
{
lean_dec_ref(v___y_3092_);
return v___x_3103_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3091_ = stack[0].m_obj;
lean_object* v___y_3092_ = stack[1].m_obj;
lean_object* v___y_3093_ = stack[2].m_obj;
lean_object* v___y_3094_ = stack[3].m_obj;
lean_object* v___y_3095_ = stack[4].m_obj;
lean_object* v___y_3096_ = stack[5].m_obj;
lean_object* v___y_3097_ = stack[6].m_obj;
lean_object* v___y_3098_ = stack[7].m_obj;
lean_object* v___y_3099_ = stack[8].m_obj;
lean_object* v___y_3100_ = stack[9].m_obj;
lean_object* v___y_3101_ = stack[10].m_obj;
lean_object* v_res_3127_;
v_res_3127_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(v_x_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
stack->m_obj
 = v_res_3127_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0___boxed(lean_object* v_x_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v_res_3140_; 
v_res_3140_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(v_x_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
return v_res_3140_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(lean_object* v_x_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_unsigned_to_nat(255u);
v___x_3154_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_3153_, v___y_3142_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
return v___x_3154_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3141_ = stack[0].m_obj;
lean_object* v___y_3142_ = stack[1].m_obj;
lean_object* v___y_3143_ = stack[2].m_obj;
lean_object* v___y_3144_ = stack[3].m_obj;
lean_object* v___y_3145_ = stack[4].m_obj;
lean_object* v___y_3146_ = stack[5].m_obj;
lean_object* v___y_3147_ = stack[6].m_obj;
lean_object* v___y_3148_ = stack[7].m_obj;
lean_object* v___y_3149_ = stack[8].m_obj;
lean_object* v___y_3150_ = stack[9].m_obj;
lean_object* v___y_3151_ = stack[10].m_obj;
lean_object* v_res_3155_;
v_res_3155_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(v_x_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
stack->m_obj
 = v_res_3155_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___boxed(lean_object* v_x_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(v_x_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
return v_res_3168_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(lean_object* v_dsimp_3169_, lean_object* v___f_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_box(0);
lean_inc_ref(v___y_3171_);
v___x_3183_ = l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(v_dsimp_3169_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
if (lean_obj_tag(v_a_3184_) == 0)
{
uint8_t v_done_3185_; 
v_done_3185_ = lean_ctor_get_uint8(v_a_3184_, 0);
lean_dec_ref_known(v_a_3184_, 0);
if (v_done_3185_ == 0)
{
lean_object* v___x_3186_; 
lean_dec_ref_known(v___x_3183_, 1);
v___x_3186_ = lean_apply_12(v___f_3170_, v___x_3182_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, lean_box(0));
return v___x_3186_;
}
else
{
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v___f_3170_);
return v___x_3183_;
}
}
else
{
uint8_t v_done_3187_; 
lean_dec_ref(v___y_3171_);
v_done_3187_ = lean_ctor_get_uint8(v_a_3184_, sizeof(void*)*1);
if (v_done_3187_ == 0)
{
lean_object* v_e_x27_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3206_; 
lean_dec_ref_known(v___x_3183_, 1);
v_e_x27_3188_ = lean_ctor_get(v_a_3184_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_a_3184_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3190_ = v_a_3184_;
v_isShared_3191_ = v_isSharedCheck_3206_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_e_x27_3188_);
lean_dec(v_a_3184_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3206_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3192_; 
lean_inc_ref(v_e_x27_3188_);
v___x_3192_ = lean_apply_12(v___f_3170_, v___x_3182_, v_e_x27_3188_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, lean_box(0));
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
if (lean_obj_tag(v_a_3193_) == 0)
{
lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3204_; 
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; 
v_unused_3205_ = lean_ctor_get(v___x_3192_, 0);
lean_dec(v_unused_3205_);
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3204_;
goto v_resetjp_3194_;
}
else
{
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3204_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
uint8_t v_done_3197_; lean_object* v___x_3199_; 
v_done_3197_ = lean_ctor_get_uint8(v_a_3193_, 0);
lean_dec_ref_known(v_a_3193_, 0);
if (v_isShared_3191_ == 0)
{
v___x_3199_ = v___x_3190_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_e_x27_3188_);
v___x_3199_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3201_; 
lean_ctor_set_uint8(v___x_3199_, sizeof(void*)*1, v_done_3197_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3199_);
v___x_3201_ = v___x_3195_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3193_, 1);
lean_del_object(v___x_3190_);
lean_dec_ref(v_e_x27_3188_);
return v___x_3192_;
}
}
else
{
lean_del_object(v___x_3190_);
lean_dec_ref(v_e_x27_3188_);
return v___x_3192_;
}
}
}
else
{
lean_dec_ref_known(v_a_3184_, 1);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___f_3170_);
return v___x_3183_;
}
}
}
else
{
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v___f_3170_);
return v___x_3183_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_dsimp_3169_ = stack[0].m_obj;
lean_object* v___f_3170_ = stack[1].m_obj;
lean_object* v___y_3171_ = stack[2].m_obj;
lean_object* v___y_3172_ = stack[3].m_obj;
lean_object* v___y_3173_ = stack[4].m_obj;
lean_object* v___y_3174_ = stack[5].m_obj;
lean_object* v___y_3175_ = stack[6].m_obj;
lean_object* v___y_3176_ = stack[7].m_obj;
lean_object* v___y_3177_ = stack[8].m_obj;
lean_object* v___y_3178_ = stack[9].m_obj;
lean_object* v___y_3179_ = stack[10].m_obj;
lean_object* v___y_3180_ = stack[11].m_obj;
lean_object* v_res_3207_;
v_res_3207_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(v_dsimp_3169_, v___f_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
stack->m_obj
 = v_res_3207_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed(lean_object* v_dsimp_3208_, lean_object* v___f_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(v_dsimp_3208_, v___f_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
lean_dec_ref(v_dsimp_3208_);
return v_res_3221_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(lean_object* v_pre_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___x_3234_; 
lean_inc(v___y_3232_);
lean_inc_ref(v___y_3231_);
lean_inc(v___y_3230_);
lean_inc_ref(v___y_3229_);
lean_inc(v___y_3228_);
lean_inc_ref(v___y_3227_);
lean_inc_ref(v___y_3223_);
v___x_3234_ = lean_apply_11(v_pre_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, lean_box(0));
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
if (lean_obj_tag(v_a_3235_) == 0)
{
uint8_t v_done_3236_; 
v_done_3236_ = lean_ctor_get_uint8(v_a_3235_, 0);
lean_dec_ref_known(v_a_3235_, 0);
if (v_done_3236_ == 0)
{
lean_object* v___x_3237_; 
lean_dec_ref_known(v___x_3234_, 1);
v___x_3237_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_3223_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
return v___x_3237_;
}
else
{
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec_ref(v___y_3223_);
return v___x_3234_;
}
}
else
{
uint8_t v_done_3238_; 
lean_dec_ref(v___y_3223_);
v_done_3238_ = lean_ctor_get_uint8(v_a_3235_, sizeof(void*)*1);
if (v_done_3238_ == 0)
{
lean_object* v_e_x27_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3257_; 
lean_dec_ref_known(v___x_3234_, 1);
v_e_x27_3239_ = lean_ctor_get(v_a_3235_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_a_3235_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3241_ = v_a_3235_;
v_isShared_3242_ = v_isSharedCheck_3257_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_e_x27_3239_);
lean_dec(v_a_3235_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3257_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; 
lean_inc_ref(v_e_x27_3239_);
v___x_3243_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_x27_3239_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
if (lean_obj_tag(v_a_3244_) == 0)
{
lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3255_; 
lean_inc_ref(v_a_3244_);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3255_ == 0)
{
lean_object* v_unused_3256_; 
v_unused_3256_ = lean_ctor_get(v___x_3243_, 0);
lean_dec(v_unused_3256_);
v___x_3246_ = v___x_3243_;
v_isShared_3247_ = v_isSharedCheck_3255_;
goto v_resetjp_3245_;
}
else
{
lean_dec(v___x_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3255_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
uint8_t v_done_3248_; lean_object* v___x_3250_; 
v_done_3248_ = lean_ctor_get_uint8(v_a_3244_, 0);
lean_dec_ref_known(v_a_3244_, 0);
if (v_isShared_3242_ == 0)
{
v___x_3250_ = v___x_3241_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_e_x27_3239_);
v___x_3250_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
lean_object* v___x_3252_; 
lean_ctor_set_uint8(v___x_3250_, sizeof(void*)*1, v_done_3248_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v___x_3250_);
v___x_3252_ = v___x_3246_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3250_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
else
{
lean_del_object(v___x_3241_);
lean_dec_ref(v_e_x27_3239_);
return v___x_3243_;
}
}
else
{
lean_del_object(v___x_3241_);
lean_dec_ref(v_e_x27_3239_);
return v___x_3243_;
}
}
}
else
{
lean_dec_ref_known(v_a_3235_, 1);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
return v___x_3234_;
}
}
}
else
{
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec_ref(v___y_3223_);
return v___x_3234_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3222_ = stack[0].m_obj;
lean_object* v___y_3223_ = stack[1].m_obj;
lean_object* v___y_3224_ = stack[2].m_obj;
lean_object* v___y_3225_ = stack[3].m_obj;
lean_object* v___y_3226_ = stack[4].m_obj;
lean_object* v___y_3227_ = stack[5].m_obj;
lean_object* v___y_3228_ = stack[6].m_obj;
lean_object* v___y_3229_ = stack[7].m_obj;
lean_object* v___y_3230_ = stack[8].m_obj;
lean_object* v___y_3231_ = stack[9].m_obj;
lean_object* v___y_3232_ = stack[10].m_obj;
lean_object* v_res_3258_;
v_res_3258_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(v_pre_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
stack->m_obj
 = v_res_3258_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed(lean_object* v_pre_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(v_pre_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
return v_res_3271_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(lean_object* v___f_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3284_ = lean_box(0);
lean_inc_ref(v___y_3273_);
v___x_3285_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_3273_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
if (lean_obj_tag(v_a_3286_) == 0)
{
uint8_t v_done_3287_; 
v_done_3287_ = lean_ctor_get_uint8(v_a_3286_, 0);
lean_dec_ref_known(v_a_3286_, 0);
if (v_done_3287_ == 0)
{
lean_object* v___x_3288_; 
lean_dec_ref_known(v___x_3285_, 1);
v___x_3288_ = lean_apply_12(v___f_3272_, v___x_3284_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, lean_box(0));
return v___x_3288_;
}
else
{
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec_ref(v___f_3272_);
return v___x_3285_;
}
}
else
{
uint8_t v_done_3289_; 
lean_dec_ref(v___y_3273_);
v_done_3289_ = lean_ctor_get_uint8(v_a_3286_, sizeof(void*)*1);
if (v_done_3289_ == 0)
{
lean_object* v_e_x27_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref_known(v___x_3285_, 1);
v_e_x27_3290_ = lean_ctor_get(v_a_3286_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v_a_3286_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3292_ = v_a_3286_;
v_isShared_3293_ = v_isSharedCheck_3308_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_e_x27_3290_);
lean_dec(v_a_3286_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3308_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; 
lean_inc_ref(v_e_x27_3290_);
v___x_3294_ = lean_apply_12(v___f_3272_, v___x_3284_, v_e_x27_3290_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, lean_box(0));
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc(v_a_3295_);
if (lean_obj_tag(v_a_3295_) == 0)
{
lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3306_; 
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; 
v_unused_3307_ = lean_ctor_get(v___x_3294_, 0);
lean_dec(v_unused_3307_);
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3306_;
goto v_resetjp_3296_;
}
else
{
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3306_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
uint8_t v_done_3299_; lean_object* v___x_3301_; 
v_done_3299_ = lean_ctor_get_uint8(v_a_3295_, 0);
lean_dec_ref_known(v_a_3295_, 0);
if (v_isShared_3293_ == 0)
{
v___x_3301_ = v___x_3292_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_e_x27_3290_);
v___x_3301_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
lean_object* v___x_3303_; 
lean_ctor_set_uint8(v___x_3301_, sizeof(void*)*1, v_done_3299_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3301_);
v___x_3303_ = v___x_3297_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3301_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3295_, 1);
lean_del_object(v___x_3292_);
lean_dec_ref(v_e_x27_3290_);
return v___x_3294_;
}
}
else
{
lean_del_object(v___x_3292_);
lean_dec_ref(v_e_x27_3290_);
return v___x_3294_;
}
}
}
else
{
lean_dec_ref_known(v_a_3286_, 1);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___f_3272_);
return v___x_3285_;
}
}
}
else
{
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec_ref(v___f_3272_);
return v___x_3285_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3272_ = stack[0].m_obj;
lean_object* v___y_3273_ = stack[1].m_obj;
lean_object* v___y_3274_ = stack[2].m_obj;
lean_object* v___y_3275_ = stack[3].m_obj;
lean_object* v___y_3276_ = stack[4].m_obj;
lean_object* v___y_3277_ = stack[5].m_obj;
lean_object* v___y_3278_ = stack[6].m_obj;
lean_object* v___y_3279_ = stack[7].m_obj;
lean_object* v___y_3280_ = stack[8].m_obj;
lean_object* v___y_3281_ = stack[9].m_obj;
lean_object* v___y_3282_ = stack[10].m_obj;
lean_object* v_res_3309_;
v_res_3309_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(v___f_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
stack->m_obj
 = v_res_3309_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4___boxed(lean_object* v___f_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(v___f_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
return v_res_3322_;
}
}
lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(lean_object* v___f_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___y_3336_; lean_object* v_e_x27_3337_; uint8_t v_done_3338_; lean_object* v___y_3352_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = lean_box(0);
lean_inc_ref(v___y_3324_);
v___x_3359_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_3324_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
if (lean_obj_tag(v_a_3360_) == 0)
{
uint8_t v_done_3361_; 
v_done_3361_ = lean_ctor_get_uint8(v_a_3360_, 0);
lean_dec_ref_known(v_a_3360_, 0);
if (v_done_3361_ == 0)
{
lean_object* v___x_3362_; 
lean_dec_ref_known(v___x_3359_, 1);
lean_inc(v___y_3333_);
lean_inc_ref(v___y_3332_);
lean_inc(v___y_3331_);
lean_inc_ref(v___y_3330_);
lean_inc(v___y_3329_);
lean_inc_ref(v___y_3328_);
lean_inc_ref(v___y_3324_);
v___x_3362_ = lean_apply_12(v___f_3323_, v___x_3358_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, lean_box(0));
v___y_3352_ = v___x_3362_;
goto v___jp_3351_;
}
else
{
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___f_3323_);
v___y_3352_ = v___x_3359_;
goto v___jp_3351_;
}
}
else
{
uint8_t v_done_3363_; 
v_done_3363_ = lean_ctor_get_uint8(v_a_3360_, sizeof(void*)*1);
if (v_done_3363_ == 0)
{
lean_object* v_e_x27_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref_known(v___x_3359_, 1);
lean_dec_ref(v___y_3324_);
v_e_x27_3364_ = lean_ctor_get(v_a_3360_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_a_3360_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3366_ = v_a_3360_;
v_isShared_3367_ = v_isSharedCheck_3384_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_e_x27_3364_);
lean_dec(v_a_3360_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3384_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; 
lean_inc(v___y_3333_);
lean_inc_ref(v___y_3332_);
lean_inc(v___y_3331_);
lean_inc_ref(v___y_3330_);
lean_inc(v___y_3329_);
lean_inc_ref(v___y_3328_);
lean_inc_ref(v_e_x27_3364_);
v___x_3368_ = lean_apply_12(v___f_3323_, v___x_3358_, v_e_x27_3364_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, lean_box(0));
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
if (lean_obj_tag(v_a_3369_) == 0)
{
lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3380_; 
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v___x_3368_, 0);
lean_dec(v_unused_3381_);
v___x_3371_ = v___x_3368_;
v_isShared_3372_ = v_isSharedCheck_3380_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3380_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
uint8_t v_done_3373_; lean_object* v___x_3375_; 
v_done_3373_ = lean_ctor_get_uint8(v_a_3369_, 0);
lean_dec_ref_known(v_a_3369_, 0);
lean_inc_ref(v_e_x27_3364_);
if (v_isShared_3367_ == 0)
{
v___x_3375_ = v___x_3366_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_e_x27_3364_);
v___x_3375_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*1, v_done_3373_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3375_);
v___x_3377_ = v___x_3371_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
v___y_3336_ = v___x_3377_;
v_e_x27_3337_ = v_e_x27_3364_;
v_done_3338_ = v_done_3373_;
goto v___jp_3335_;
}
}
}
}
else
{
lean_object* v_e_x27_3382_; uint8_t v_done_3383_; 
lean_del_object(v___x_3366_);
lean_dec_ref(v_e_x27_3364_);
v_e_x27_3382_ = lean_ctor_get(v_a_3369_, 0);
lean_inc_ref(v_e_x27_3382_);
v_done_3383_ = lean_ctor_get_uint8(v_a_3369_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3369_, 1);
v___y_3336_ = v___x_3368_;
v_e_x27_3337_ = v_e_x27_3382_;
v_done_3338_ = v_done_3383_;
goto v___jp_3335_;
}
}
else
{
lean_del_object(v___x_3366_);
lean_dec_ref(v_e_x27_3364_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
return v___x_3368_;
}
}
}
else
{
lean_dec_ref_known(v_a_3360_, 1);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___f_3323_);
v___y_3352_ = v___x_3359_;
goto v___jp_3351_;
}
}
}
else
{
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___f_3323_);
v___y_3352_ = v___x_3359_;
goto v___jp_3351_;
}
v___jp_3335_:
{
if (v_done_3338_ == 0)
{
lean_object* v___x_3339_; 
lean_dec_ref(v___y_3336_);
lean_inc_ref(v_e_x27_3337_);
v___x_3339_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_x27_3337_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
if (lean_obj_tag(v_a_3340_) == 0)
{
lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3349_; 
lean_inc_ref(v_a_3340_);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3349_ == 0)
{
lean_object* v_unused_3350_; 
v_unused_3350_ = lean_ctor_get(v___x_3339_, 0);
lean_dec(v_unused_3350_);
v___x_3342_ = v___x_3339_;
v_isShared_3343_ = v_isSharedCheck_3349_;
goto v_resetjp_3341_;
}
else
{
lean_dec(v___x_3339_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3349_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
uint8_t v_done_3344_; lean_object* v___x_3345_; lean_object* v___x_3347_; 
v_done_3344_ = lean_ctor_get_uint8(v_a_3340_, 0);
lean_dec_ref_known(v_a_3340_, 0);
v___x_3345_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3345_, 0, v_e_x27_3337_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*1, v_done_3344_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 0, v___x_3345_);
v___x_3347_ = v___x_3342_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
else
{
lean_dec_ref(v_e_x27_3337_);
return v___x_3339_;
}
}
else
{
lean_dec_ref(v_e_x27_3337_);
return v___x_3339_;
}
}
else
{
lean_dec_ref(v_e_x27_3337_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
return v___y_3336_;
}
}
v___jp_3351_:
{
if (lean_obj_tag(v___y_3352_) == 0)
{
lean_object* v_a_3353_; 
v_a_3353_ = lean_ctor_get(v___y_3352_, 0);
if (lean_obj_tag(v_a_3353_) == 0)
{
uint8_t v_done_3354_; 
v_done_3354_ = lean_ctor_get_uint8(v_a_3353_, 0);
if (v_done_3354_ == 0)
{
lean_object* v___x_3355_; 
lean_dec_ref_known(v___y_3352_, 1);
v___x_3355_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_3324_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
return v___x_3355_;
}
else
{
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec_ref(v___y_3324_);
return v___y_3352_;
}
}
else
{
lean_object* v_e_x27_3356_; uint8_t v_done_3357_; 
lean_dec_ref(v___y_3324_);
v_e_x27_3356_ = lean_ctor_get(v_a_3353_, 0);
lean_inc_ref(v_e_x27_3356_);
v_done_3357_ = lean_ctor_get_uint8(v_a_3353_, sizeof(void*)*1);
v___y_3336_ = v___y_3352_;
v_e_x27_3337_ = v_e_x27_3356_;
v_done_3338_ = v_done_3357_;
goto v___jp_3335_;
}
}
else
{
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec_ref(v___y_3324_);
return v___y_3352_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3323_ = stack[0].m_obj;
lean_object* v___y_3324_ = stack[1].m_obj;
lean_object* v___y_3325_ = stack[2].m_obj;
lean_object* v___y_3326_ = stack[3].m_obj;
lean_object* v___y_3327_ = stack[4].m_obj;
lean_object* v___y_3328_ = stack[5].m_obj;
lean_object* v___y_3329_ = stack[6].m_obj;
lean_object* v___y_3330_ = stack[7].m_obj;
lean_object* v___y_3331_ = stack[8].m_obj;
lean_object* v___y_3332_ = stack[9].m_obj;
lean_object* v___y_3333_ = stack[10].m_obj;
lean_object* v_res_3385_;
v_res_3385_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(v___f_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
stack->m_obj
 = v_res_3385_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5___boxed(lean_object* v___f_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(v___f_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods(lean_object* v_config_3405_, lean_object* v_thms_3406_){
_start:
{
uint8_t v_zetaDelta_3407_; uint8_t v_zeta_3408_; lean_object* v___f_3409_; lean_object* v_pre_3411_; lean_object* v_pre_3416_; 
v_zetaDelta_3407_ = lean_ctor_get_uint8(v_config_3405_, sizeof(void*)*14 + 19);
v_zeta_3408_ = lean_ctor_get_uint8(v_config_3405_, sizeof(void*)*14 + 20);
v___f_3409_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__1));
if (v_zeta_3408_ == 0)
{
lean_object* v_pre_3418_; 
v_pre_3418_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__2));
v_pre_3416_ = v_pre_3418_;
goto v___jp_3415_;
}
else
{
lean_object* v_pre_3419_; 
v_pre_3419_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__3));
v_pre_3416_ = v_pre_3419_;
goto v___jp_3415_;
}
v___jp_3410_:
{
lean_object* v_dsimp_3412_; lean_object* v_post_3413_; lean_object* v___x_3414_; 
v_dsimp_3412_ = lean_ctor_get(v_thms_3406_, 2);
lean_inc_ref(v_dsimp_3412_);
lean_dec_ref(v_thms_3406_);
v_post_3413_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed), 13, 2);
lean_closure_set(v_post_3413_, 0, v_dsimp_3412_);
lean_closure_set(v_post_3413_, 1, v___f_3409_);
v___x_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3414_, 0, v_pre_3411_);
lean_ctor_set(v___x_3414_, 1, v_post_3413_);
return v___x_3414_;
}
v___jp_3415_:
{
if (v_zetaDelta_3407_ == 0)
{
lean_inc_ref(v_pre_3416_);
v_pre_3411_ = v_pre_3416_;
goto v___jp_3410_;
}
else
{
lean_object* v_pre_3417_; 
lean_inc_ref(v_pre_3416_);
v_pre_3417_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed), 12, 1);
lean_closure_set(v_pre_3417_, 0, v_pre_3416_);
v_pre_3411_ = v_pre_3417_;
goto v___jp_3410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___boxed(lean_object* v_config_3420_, lean_object* v_thms_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_config_3420_, v_thms_3421_);
lean_dec_ref(v_config_3420_);
return v_res_3422_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(lean_object* v_e_3423_, lean_object* v___y_3424_){
_start:
{
uint8_t v___x_3426_; 
v___x_3426_ = l_Lean_Expr_hasMVar(v_e_3423_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v_e_3423_);
return v___x_3427_;
}
else
{
lean_object* v___x_3428_; lean_object* v_mctx_3429_; lean_object* v___x_3430_; lean_object* v_fst_3431_; lean_object* v_snd_3432_; lean_object* v___x_3433_; lean_object* v_cache_3434_; lean_object* v_zetaDeltaFVarIds_3435_; lean_object* v_postponed_3436_; lean_object* v_diag_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3446_; 
v___x_3428_ = lean_st_ref_get(v___y_3424_);
v_mctx_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc_ref(v_mctx_3429_);
lean_dec(v___x_3428_);
v___x_3430_ = l_Lean_instantiateMVarsCore(v_mctx_3429_, v_e_3423_);
v_fst_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_fst_3431_);
v_snd_3432_ = lean_ctor_get(v___x_3430_, 1);
lean_inc(v_snd_3432_);
lean_dec_ref(v___x_3430_);
v___x_3433_ = lean_st_ref_take(v___y_3424_);
v_cache_3434_ = lean_ctor_get(v___x_3433_, 1);
v_zetaDeltaFVarIds_3435_ = lean_ctor_get(v___x_3433_, 2);
v_postponed_3436_ = lean_ctor_get(v___x_3433_, 3);
v_diag_3437_ = lean_ctor_get(v___x_3433_, 4);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3446_ == 0)
{
lean_object* v_unused_3447_; 
v_unused_3447_ = lean_ctor_get(v___x_3433_, 0);
lean_dec(v_unused_3447_);
v___x_3439_ = v___x_3433_;
v_isShared_3440_ = v_isSharedCheck_3446_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_diag_3437_);
lean_inc(v_postponed_3436_);
lean_inc(v_zetaDeltaFVarIds_3435_);
lean_inc(v_cache_3434_);
lean_dec(v___x_3433_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3446_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v_snd_3432_);
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_snd_3432_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v_cache_3434_);
lean_ctor_set(v_reuseFailAlloc_3445_, 2, v_zetaDeltaFVarIds_3435_);
lean_ctor_set(v_reuseFailAlloc_3445_, 3, v_postponed_3436_);
lean_ctor_set(v_reuseFailAlloc_3445_, 4, v_diag_3437_);
v___x_3442_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = lean_st_ref_put(v___y_3424_, v___x_3442_);
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v_fst_3431_);
return v___x_3444_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3423_ = stack[0].m_obj;
lean_object* v___y_3424_ = stack[1].m_obj;
lean_object* v_res_3448_;
v_res_3448_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_3423_, v___y_3424_);
stack->m_obj
 = v_res_3448_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg___boxed(lean_object* v_e_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_3449_, v___y_3450_);
lean_dec(v___y_3450_);
return v_res_3452_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(lean_object* v_e_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_3453_, v___y_3460_);
return v___x_3464_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3453_ = stack[0].m_obj;
lean_object* v___y_3454_ = stack[1].m_obj;
lean_object* v___y_3455_ = stack[2].m_obj;
lean_object* v___y_3456_ = stack[3].m_obj;
lean_object* v___y_3457_ = stack[4].m_obj;
lean_object* v___y_3458_ = stack[5].m_obj;
lean_object* v___y_3459_ = stack[6].m_obj;
lean_object* v___y_3460_ = stack[7].m_obj;
lean_object* v___y_3461_ = stack[8].m_obj;
lean_object* v___y_3462_ = stack[9].m_obj;
lean_object* v_res_3465_;
v_res_3465_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(v_e_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
stack->m_obj
 = v_res_3465_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___boxed(lean_object* v_e_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(v_e_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
return v_res_3477_;
}
}
lean_object* l_Lean_Meta_Grind_normLegacy(lean_object* v_e_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v___x_3489_; lean_object* v_a_3490_; lean_object* v___x_3491_; 
v___x_3489_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_3478_, v_a_3485_);
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref(v___x_3489_);
v___x_3491_ = l_Lean_Meta_Grind_simpCore(v_a_3490_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v_expr_3493_; lean_object* v_proof_x3f_3494_; uint8_t v_cache_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3519_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
v_expr_3493_ = lean_ctor_get(v_a_3492_, 0);
v_proof_x3f_3494_ = lean_ctor_get(v_a_3492_, 1);
v_cache_3495_ = lean_ctor_get_uint8(v_a_3492_, sizeof(void*)*2);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_a_3492_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3497_ = v_a_3492_;
v_isShared_3498_ = v_isSharedCheck_3519_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_proof_x3f_3494_);
lean_inc(v_expr_3493_);
lean_dec(v_a_3492_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3519_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_expr_3493_, v_a_3486_, v_a_3487_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3510_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3502_ = v___x_3499_;
v_isShared_3503_ = v_isSharedCheck_3510_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3499_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3510_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v_a_3500_);
v___x_3505_ = v___x_3497_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3500_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v_proof_x3f_3494_);
lean_ctor_set_uint8(v_reuseFailAlloc_3509_, sizeof(void*)*2, v_cache_3495_);
v___x_3505_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
lean_object* v___x_3507_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3505_);
v___x_3507_ = v___x_3502_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_del_object(v___x_3497_);
lean_dec(v_proof_x3f_3494_);
v_a_3511_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3499_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3499_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
else
{
return v___x_3491_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_normLegacy_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3478_ = stack[0].m_obj;
lean_object* v_a_3479_ = stack[1].m_obj;
lean_object* v_a_3480_ = stack[2].m_obj;
lean_object* v_a_3481_ = stack[3].m_obj;
lean_object* v_a_3482_ = stack[4].m_obj;
lean_object* v_a_3483_ = stack[5].m_obj;
lean_object* v_a_3484_ = stack[6].m_obj;
lean_object* v_a_3485_ = stack[7].m_obj;
lean_object* v_a_3486_ = stack[8].m_obj;
lean_object* v_a_3487_ = stack[9].m_obj;
lean_object* v_res_3520_;
v_res_3520_ = l_Lean_Meta_Grind_normLegacy(v_e_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
stack->m_obj
 = v_res_3520_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy___boxed(lean_object* v_e_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_Meta_Grind_normLegacy(v_e_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
return v_res_3532_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__0(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__1, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__1_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1);
v___x_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
return v___x_3534_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__1(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3535_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__0, &l_Lean_Meta_Grind_normSym___redArg___closed__0_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__0);
v___x_3536_ = lean_unsigned_to_nat(0u);
v___x_3537_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
lean_ctor_set(v___x_3537_, 1, v___x_3535_);
lean_ctor_set(v___x_3537_, 2, v___x_3535_);
lean_ctor_set(v___x_3537_, 3, v___x_3535_);
return v___x_3537_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__2(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__0, &l_Lean_Meta_Grind_normSym___redArg___closed__0_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__0);
v___x_3539_ = lean_unsigned_to_nat(0u);
v___x_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
lean_ctor_set(v___x_3540_, 1, v___x_3538_);
return v___x_3540_;
}
}
lean_object* l_Lean_Meta_Grind_normSym___redArg(lean_object* v_e_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_Meta_Grind_mkNormSymTheorems(v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3552_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
v___x_3552_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3542_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3552_, 1);
lean_inc(v_a_3551_);
v___x_3554_ = l_Lean_Meta_Grind_mkNormSymMethods(v_a_3553_, v_a_3551_);
v___x_3555_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_a_3553_, v_a_3551_);
lean_dec(v_a_3553_);
v___x_3556_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__1, &l_Lean_Meta_Grind_normSym___redArg___closed__1_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__1);
v___x_3557_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__2, &l_Lean_Meta_Grind_normSym___redArg___closed__2_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__2);
v___x_3558_ = l_Lean_Meta_Grind_symNorm(v_e_3541_, v___x_3554_, v___x_3555_, v___x_3556_, v___x_3557_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3567_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3567_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3567_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_fst_3563_; lean_object* v___x_3565_; 
v_fst_3563_ = lean_ctor_get(v_a_3559_, 0);
lean_inc(v_fst_3563_);
lean_dec(v_a_3559_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v_fst_3563_);
v___x_3565_ = v___x_3561_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_fst_3563_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
v_a_3568_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3558_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3558_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_dec(v_a_3551_);
lean_dec_ref(v_e_3541_);
v_a_3576_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3552_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3552_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec_ref(v_e_3541_);
v_a_3584_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3550_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3550_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_normSym___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3541_ = stack[0].m_obj;
lean_object* v_a_3542_ = stack[1].m_obj;
lean_object* v_a_3543_ = stack[2].m_obj;
lean_object* v_a_3544_ = stack[3].m_obj;
lean_object* v_a_3545_ = stack[4].m_obj;
lean_object* v_a_3546_ = stack[5].m_obj;
lean_object* v_a_3547_ = stack[6].m_obj;
lean_object* v_a_3548_ = stack[7].m_obj;
lean_object* v_res_3592_;
v_res_3592_ = l_Lean_Meta_Grind_normSym___redArg(v_e_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
stack->m_obj
 = v_res_3592_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg___boxed(lean_object* v_e_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_Meta_Grind_normSym___redArg(v_e_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec_ref(v_a_3594_);
return v_res_3602_;
}
}
lean_object* l_Lean_Meta_Grind_normSym(lean_object* v_e_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l_Lean_Meta_Grind_normSym___redArg(v_e_3603_, v_a_3605_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_);
return v___x_3614_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_normSym_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3603_ = stack[0].m_obj;
lean_object* v_a_3604_ = stack[1].m_obj;
lean_object* v_a_3605_ = stack[2].m_obj;
lean_object* v_a_3606_ = stack[3].m_obj;
lean_object* v_a_3607_ = stack[4].m_obj;
lean_object* v_a_3608_ = stack[5].m_obj;
lean_object* v_a_3609_ = stack[6].m_obj;
lean_object* v_a_3610_ = stack[7].m_obj;
lean_object* v_a_3611_ = stack[8].m_obj;
lean_object* v_a_3612_ = stack[9].m_obj;
lean_object* v_res_3615_;
v_res_3615_ = l_Lean_Meta_Grind_normSym(v_e_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_);
stack->m_obj
 = v_res_3615_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___boxed(lean_object* v_e_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_Meta_Grind_normSym(v_e_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
lean_dec(v_a_3625_);
lean_dec_ref(v_a_3624_);
lean_dec(v_a_3623_);
lean_dec_ref(v_a_3622_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
return v_res_3627_;
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
