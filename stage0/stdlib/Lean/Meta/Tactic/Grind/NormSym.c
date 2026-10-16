// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.NormSym
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Sym.Simp.Theorems import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.SimpUtil import Lean.Meta.Tactic.Grind.Util import Lean.Meta.Sym.Simp.Main import Lean.Meta.Sym.Simp.Simproc import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.EvalGround import Lean.Meta.Sym.Simp.Forall import Lean.Meta.Sym.Simp.Arith import Lean.Meta.Sym.Simp.Discharger import Lean.Meta.Tactic.Grind.NormSymProcs import Lean.Meta.Sym.Simp.Reduce public import Lean.Meta.Sym.DSimp import Lean.Meta.Sym.Simp.ControlFlow import Lean.Meta.Sym.Util import Lean.Meta.DiscrTree
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
lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
lean_object* l_Lean_Meta_Sym_Simp_simpArith(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_pushNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_reduceControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_reduceProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymMethods___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___lam__11___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__0_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__2___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__1_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__3___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__2_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__4___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__3_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__10_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__11_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__12_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__18___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__4_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__13_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__19___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__4_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__14_value;
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
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_283_; 
v_a_246_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_283_ == 0)
{
v___x_248_ = v___x_236_;
v_isShared_249_ = v_isSharedCheck_283_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_236_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_283_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
uint8_t v___x_250_; 
v___x_250_ = l_Lean_Exception_isInterrupt(v_a_246_);
if (v___x_250_ == 0)
{
uint8_t v___x_251_; 
lean_inc(v_a_246_);
v___x_251_ = l_Lean_Exception_isRuntime(v_a_246_);
if (v___x_251_ == 0)
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
v___x_260_ = l_Lean_MessageData_ofConstName(v_declName_232_, v___x_251_);
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
else
{
lean_object* v___x_281_; 
lean_dec(v_declName_232_);
lean_dec_ref(v_thms_213_);
if (v_isShared_249_ == 0)
{
v___x_281_ = v___x_248_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_246_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
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
lean_object* v_toCold_284_; lean_object* v_options_285_; uint8_t v_hasTrace_286_; 
v_toCold_284_ = lean_ctor_get(v_a_217_, 0);
v_options_285_ = lean_ctor_get(v_toCold_284_, 2);
v_hasTrace_286_ = lean_ctor_get_uint8(v_options_285_, sizeof(void*)*1);
if (v_hasTrace_286_ == 0)
{
lean_object* v___x_287_; 
lean_dec_ref(v_thm_214_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v_thms_213_);
return v___x_287_;
}
else
{
lean_object* v_origin_288_; lean_object* v_inheritedTraceOptions_289_; lean_object* v_cls_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v_origin_288_ = lean_ctor_get(v_thm_214_, 4);
lean_inc_ref(v_origin_288_);
lean_dec_ref(v_thm_214_);
v_inheritedTraceOptions_289_ = lean_ctor_get(v_toCold_284_, 11);
v_cls_290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_291_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2);
v___x_292_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_289_, v_options_285_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec_ref(v_origin_288_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v_thms_213_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_294_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__4);
v___x_295_ = l_Lean_Meta_Origin_key(v_origin_288_);
lean_dec_ref(v_origin_288_);
v___x_296_ = l_Lean_MessageData_ofName(v___x_295_);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_294_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__8);
v___x_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v_cls_290_, v___x_299_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v___x_300_, 0);
lean_dec(v_unused_308_);
v___x_302_ = v___x_300_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_dec(v___x_300_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v_thms_213_);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_thms_213_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref(v_thms_213_);
v_a_309_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_300_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_300_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___boxed(lean_object* v_thms_317_, lean_object* v_thm_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_thms_317_, v_thm_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(lean_object* v_as_325_, size_t v_i_326_, size_t v_stop_327_, lean_object* v_b_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_eq(v_i_326_, v_stop_327_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; size_t v___x_332_; size_t v___x_333_; 
v___x_330_ = lean_array_uget_borrowed(v_as_325_, v_i_326_);
lean_inc(v___x_330_);
v___x_331_ = lean_array_push(v_b_328_, v___x_330_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_326_, v___x_332_);
v_i_326_ = v___x_333_;
v_b_328_ = v___x_331_;
goto _start;
}
else
{
return v_b_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4___boxed(lean_object* v_as_335_, lean_object* v_i_336_, lean_object* v_stop_337_, lean_object* v_b_338_){
_start:
{
size_t v_i_boxed_339_; size_t v_stop_boxed_340_; lean_object* v_res_341_; 
v_i_boxed_339_ = lean_unbox_usize(v_i_336_);
lean_dec(v_i_336_);
v_stop_boxed_340_ = lean_unbox_usize(v_stop_337_);
lean_dec(v_stop_337_);
v_res_341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(v_as_335_, v_i_boxed_339_, v_stop_boxed_340_, v_b_338_);
lean_dec_ref(v_as_335_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
lean_object* v_child_344_; 
v_child_344_ = lean_ctor_get(v_x_343_, 1);
v_x_343_ = v_child_344_;
goto _start;
}
else
{
lean_object* v_vs_346_; lean_object* v_children_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_vs_346_ = lean_ctor_get(v_x_343_, 0);
v_children_347_ = lean_ctor_get(v_x_343_, 1);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_array_get_size(v_vs_346_);
v___x_350_ = lean_nat_dec_lt(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = lean_array_get_size(v_children_347_);
v___x_352_ = lean_nat_dec_lt(v___x_348_, v___x_351_);
if (v___x_352_ == 0)
{
return v_x_342_;
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((size_t)0ULL);
v___x_354_ = lean_usize_of_nat(v___x_351_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_children_347_, v___x_353_, v___x_354_, v_x_342_);
return v___x_355_;
}
}
else
{
size_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_356_ = ((size_t)0ULL);
v___x_357_ = lean_usize_of_nat(v___x_349_);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__4(v_vs_346_, v___x_356_, v___x_357_, v_x_342_);
v___x_359_ = lean_array_get_size(v_children_347_);
v___x_360_ = lean_nat_dec_lt(v___x_348_, v___x_359_);
if (v___x_360_ == 0)
{
return v___x_358_;
}
else
{
size_t v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_usize_of_nat(v___x_359_);
v___x_362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_children_347_, v___x_356_, v___x_361_, v___x_358_);
return v___x_362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(lean_object* v_as_363_, size_t v_i_364_, size_t v_stop_365_, lean_object* v_b_366_){
_start:
{
uint8_t v___x_367_; 
v___x_367_ = lean_usize_dec_eq(v_i_364_, v_stop_365_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v_snd_369_; lean_object* v___x_370_; size_t v___x_371_; size_t v___x_372_; 
v___x_368_ = lean_array_uget_borrowed(v_as_363_, v_i_364_);
v_snd_369_ = lean_ctor_get(v___x_368_, 1);
v___x_370_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_b_366_, v_snd_369_);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_add(v_i_364_, v___x_371_);
v_i_364_ = v___x_372_;
v_b_366_ = v___x_370_;
goto _start;
}
else
{
return v_b_366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3___boxed(lean_object* v_as_374_, lean_object* v_i_375_, lean_object* v_stop_376_, lean_object* v_b_377_){
_start:
{
size_t v_i_boxed_378_; size_t v_stop_boxed_379_; lean_object* v_res_380_; 
v_i_boxed_378_ = lean_unbox_usize(v_i_375_);
lean_dec(v_i_375_);
v_stop_boxed_379_ = lean_unbox_usize(v_stop_376_);
lean_dec(v_stop_376_);
v_res_380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2_spec__3(v_as_374_, v_i_boxed_378_, v_stop_boxed_379_, v_b_377_);
lean_dec_ref(v_as_374_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2___boxed(lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_x_381_, v_x_382_);
lean_dec_ref(v_x_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___lam__0(lean_object* v_s_384_, lean_object* v_x_385_, lean_object* v_t_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__2(v_s_384_, v_t_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___lam__0___boxed(lean_object* v_s_388_, lean_object* v_x_389_, lean_object* v_t_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Meta_Grind_mkNormSymTheorems___lam__0(v_s_388_, v_x_389_, v_t_390_);
lean_dec_ref(v_t_390_);
lean_dec(v_x_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(lean_object* v_as_392_, size_t v_sz_393_, size_t v_i_394_, lean_object* v_b_395_){
_start:
{
uint8_t v___x_397_; 
v___x_397_ = lean_usize_dec_lt(v_i_394_, v_sz_393_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_b_395_);
return v___x_398_;
}
else
{
lean_object* v_a_399_; lean_object* v___x_400_; size_t v___x_401_; size_t v___x_402_; 
v_a_399_ = lean_array_uget_borrowed(v_as_392_, v_i_394_);
lean_inc(v_a_399_);
v___x_400_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_395_, v_a_399_);
v___x_401_ = ((size_t)1ULL);
v___x_402_ = lean_usize_add(v_i_394_, v___x_401_);
v_i_394_ = v___x_402_;
v_b_395_ = v___x_400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg___boxed(lean_object* v_as_404_, lean_object* v_sz_405_, lean_object* v_i_406_, lean_object* v_b_407_, lean_object* v___y_408_){
_start:
{
size_t v_sz_boxed_409_; size_t v_i_boxed_410_; lean_object* v_res_411_; 
v_sz_boxed_409_ = lean_unbox_usize(v_sz_405_);
lean_dec(v_sz_405_);
v_i_boxed_410_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_as_404_, v_sz_boxed_409_, v_i_boxed_410_, v_b_407_);
lean_dec_ref(v_as_404_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(lean_object* v_declName_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; lean_object* v_env_416_; uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_415_ = lean_st_ref_get(v___y_413_);
v_env_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_ref(v_env_416_);
lean_dec(v___x_415_);
v___x_417_ = l_Lean_getReducibilityStatusCore(v_env_416_, v_declName_412_);
v___x_418_ = lean_box(v___x_417_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg___boxed(lean_object* v_declName_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_420_, v___y_421_);
lean_dec(v___y_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(lean_object* v_declName_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_446_; 
v___x_430_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_424_, v___y_428_);
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_446_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_446_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_446_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
uint8_t v___x_435_; 
v___x_435_ = lean_unbox(v_a_431_);
lean_dec(v_a_431_);
if (v___x_435_ == 0)
{
uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = 1;
v___x_437_ = lean_box(v___x_436_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_437_);
v___x_439_ = v___x_433_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
else
{
uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_441_ = 0;
v___x_442_ = lean_box(v___x_441_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_442_);
v___x_444_ = v___x_433_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0___boxed(lean_object* v_declName_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(v_declName_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_453_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__0));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(lean_object* v_as_x27_457_, lean_object* v_b_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
if (lean_obj_tag(v_as_x27_457_) == 0)
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_b_458_);
return v___x_464_;
}
else
{
lean_object* v_head_465_; lean_object* v_tail_466_; lean_object* v_fst_468_; lean_object* v_snd_469_; lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_541_; 
v_head_465_ = lean_ctor_get(v_as_x27_457_, 0);
v_tail_466_ = lean_ctor_get(v_as_x27_457_, 1);
v_fst_472_ = lean_ctor_get(v_b_458_, 0);
v_snd_473_ = lean_ctor_get(v_b_458_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_b_458_);
if (v_isSharedCheck_541_ == 0)
{
v___x_475_ = v_b_458_;
v_isShared_476_ = v_isSharedCheck_541_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snd_473_);
lean_inc(v_fst_472_);
lean_dec(v_b_458_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_541_;
goto v_resetjp_474_;
}
v___jp_467_:
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v_fst_468_);
lean_ctor_set(v___x_470_, 1, v_snd_469_);
v_as_x27_457_ = v_tail_466_;
v_b_458_ = v___x_470_;
goto _start;
}
v_resetjp_474_:
{
lean_object* v___x_477_; 
lean_inc(v_head_465_);
v___x_477_ = l_Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0(v_head_465_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_532_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_532_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_532_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_532_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v_a_483_; uint8_t v___x_516_; 
v___x_516_ = lean_unbox(v_a_478_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_del_object(v___x_475_);
lean_inc(v_head_465_);
v___x_517_ = l_Lean_Meta_Sym_Simp_mkTheoremsFromDecl(v_head_465_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; size_t v_sz_519_; size_t v___x_520_; lean_object* v___x_521_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v_sz_519_ = lean_array_size(v_a_518_);
v___x_520_ = ((size_t)0ULL);
lean_inc(v_fst_472_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_a_518_, v_sz_519_, v___x_520_, v_fst_472_);
lean_dec(v_a_518_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
lean_inc(v_head_465_);
lean_inc(v_snd_473_);
v___x_523_ = l_Lean_Meta_Sym_DSimp_Decls_add(v_snd_473_, v_head_465_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; 
lean_del_object(v___x_480_);
lean_dec(v_a_478_);
lean_dec(v_snd_473_);
lean_dec(v_fst_472_);
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v_fst_468_ = v_a_522_;
v_snd_469_ = v_a_524_;
goto v___jp_467_;
}
else
{
lean_object* v_a_525_; 
lean_dec(v_a_522_);
v_a_525_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_523_, 1);
v_a_483_ = v_a_525_;
goto v___jp_482_;
}
}
else
{
lean_object* v_a_526_; 
v_a_526_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_521_, 1);
v_a_483_ = v_a_526_;
goto v___jp_482_;
}
}
else
{
lean_object* v_a_527_; 
v_a_527_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_517_, 1);
v_a_483_ = v_a_527_;
goto v___jp_482_;
}
}
else
{
lean_object* v___x_529_; 
lean_del_object(v___x_480_);
lean_dec(v_a_478_);
if (v_isShared_476_ == 0)
{
v___x_529_ = v___x_475_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_fst_472_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_snd_473_);
v___x_529_ = v_reuseFailAlloc_531_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
v_as_x27_457_ = v_tail_466_;
v_b_458_ = v___x_529_;
goto _start;
}
}
v___jp_482_:
{
uint8_t v___x_484_; 
v___x_484_ = l_Lean_Exception_isInterrupt(v_a_483_);
if (v___x_484_ == 0)
{
uint8_t v___x_485_; 
lean_inc_ref(v_a_483_);
v___x_485_ = l_Lean_Exception_isRuntime(v_a_483_);
if (v___x_485_ == 0)
{
lean_object* v_toCold_486_; lean_object* v_options_487_; uint8_t v_hasTrace_488_; 
lean_del_object(v___x_480_);
v_toCold_486_ = lean_ctor_get(v___y_461_, 0);
v_options_487_ = lean_ctor_get(v_toCold_486_, 2);
v_hasTrace_488_ = lean_ctor_get_uint8(v_options_487_, sizeof(void*)*1);
if (v_hasTrace_488_ == 0)
{
lean_dec_ref(v_a_483_);
lean_dec(v_a_478_);
v_fst_468_ = v_fst_472_;
v_snd_469_ = v_snd_473_;
goto v___jp_467_;
}
else
{
lean_object* v_inheritedTraceOptions_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_inheritedTraceOptions_489_ = lean_ctor_get(v_toCold_486_, 11);
v___x_490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_NormSym_448808965____hygCtx___hyg_2_));
v___x_491_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__2);
v___x_492_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_489_, v_options_487_, v___x_491_);
if (v___x_492_ == 0)
{
lean_dec_ref(v_a_483_);
lean_dec(v_a_478_);
v_fst_468_ = v_fst_472_;
v_snd_469_ = v_snd_473_;
goto v___jp_467_;
}
else
{
lean_object* v___x_493_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_493_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___closed__1);
v___x_494_ = lean_unbox(v_a_478_);
lean_dec(v_a_478_);
lean_inc(v_head_465_);
v___x_495_ = l_Lean_MessageData_ofConstName(v_head_465_, v___x_494_);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_493_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6, &l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem___closed__6);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_Exception_toMessageData(v_a_483_);
v___x_500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem_spec__0(v___x_490_, v___x_500_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_dec_ref_known(v___x_501_, 1);
v_fst_468_ = v_fst_472_;
v_snd_469_ = v_snd_473_;
goto v___jp_467_;
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec(v_snd_473_);
lean_dec(v_fst_472_);
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
else
{
lean_object* v___x_511_; 
lean_dec(v_a_478_);
lean_dec(v_snd_473_);
lean_dec(v_fst_472_);
if (v_isShared_481_ == 0)
{
lean_ctor_set_tag(v___x_480_, 1);
lean_ctor_set(v___x_480_, 0, v_a_483_);
v___x_511_ = v___x_480_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_483_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
else
{
lean_object* v___x_514_; 
lean_dec(v_a_478_);
lean_dec(v_snd_473_);
lean_dec(v_fst_472_);
if (v_isShared_481_ == 0)
{
lean_ctor_set_tag(v___x_480_, 1);
lean_ctor_set(v___x_480_, 0, v_a_483_);
v___x_514_ = v___x_480_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_483_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_del_object(v___x_475_);
lean_dec(v_snd_473_);
lean_dec(v_fst_472_);
v_a_533_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_477_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_477_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg___boxed(lean_object* v_as_x27_542_, lean_object* v_b_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(v_as_x27_542_, v_b_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v_as_x27_542_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(lean_object* v_as_550_, size_t v_sz_551_, size_t v_i_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_a_560_; uint8_t v___x_564_; 
v___x_564_ = lean_usize_dec_lt(v_i_552_, v_sz_551_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v_b_553_);
return v___x_565_;
}
else
{
lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_606_; 
v_fst_566_ = lean_ctor_get(v_b_553_, 0);
v_snd_567_ = lean_ctor_get(v_b_553_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v_b_553_);
if (v_isSharedCheck_606_ == 0)
{
v___x_569_ = v_b_553_;
v_isShared_570_ = v_isSharedCheck_606_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_snd_567_);
lean_inc(v_fst_566_);
lean_dec(v_b_553_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_606_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v_a_571_; lean_object* v___x_572_; 
v_a_571_ = lean_array_uget_borrowed(v_as_550_, v_i_552_);
lean_inc(v_a_571_);
v___x_572_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_fst_566_, v_a_571_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_572_) == 0)
{
uint8_t v_rfl_573_; 
v_rfl_573_ = lean_ctor_get_uint8(v_a_571_, sizeof(void*)*5 + 2);
if (v_rfl_573_ == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; 
v_a_574_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_572_, 1);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v_a_574_);
v___x_576_ = v___x_569_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_574_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_snd_567_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
v_a_560_ = v___x_576_;
goto v___jp_559_;
}
}
else
{
lean_object* v_proof_578_; 
v_proof_578_ = lean_ctor_get(v_a_571_, 2);
if (lean_obj_tag(v_proof_578_) == 4)
{
lean_object* v_a_579_; lean_object* v_declName_580_; lean_object* v___x_581_; 
v_a_579_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_572_, 1);
v_declName_580_ = lean_ctor_get(v_proof_578_, 0);
lean_inc(v_declName_580_);
v___x_581_ = l_Lean_Meta_Sym_DSimp_Decls_add(v_snd_567_, v_declName_580_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 1);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 1, v_a_582_);
lean_ctor_set(v___x_569_, 0, v_a_579_);
v___x_584_ = v___x_569_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_a_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v_a_560_ = v___x_584_;
goto v___jp_559_;
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v_a_579_);
lean_del_object(v___x_569_);
v_a_586_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_581_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_581_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; 
v_a_594_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_572_, 1);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v_a_594_);
v___x_596_ = v___x_569_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_snd_567_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
v_a_560_ = v___x_596_;
goto v___jp_559_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_del_object(v___x_569_);
lean_dec(v_snd_567_);
v_a_598_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_572_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_572_);
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
}
v___jp_559_:
{
size_t v___x_561_; size_t v___x_562_; 
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_add(v_i_552_, v___x_561_);
v_i_552_ = v___x_562_;
v_b_553_ = v_a_560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6___boxed(lean_object* v_as_607_, lean_object* v_sz_608_, lean_object* v_i_609_, lean_object* v_b_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
size_t v_sz_boxed_616_; size_t v_i_boxed_617_; lean_object* v_res_618_; 
v_sz_boxed_616_ = lean_unbox_usize(v_sz_608_);
lean_dec(v_sz_608_);
v_i_boxed_617_ = lean_unbox_usize(v_i_609_);
lean_dec(v_i_609_);
v_res_618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(v_as_607_, v_sz_boxed_616_, v_i_boxed_617_, v_b_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec_ref(v_as_607_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(lean_object* v_as_619_, size_t v_sz_620_, size_t v_i_621_, lean_object* v_b_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
uint8_t v___x_628_; 
v___x_628_ = lean_usize_dec_lt(v_i_621_, v_sz_620_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_b_622_);
return v___x_629_;
}
else
{
lean_object* v_a_630_; lean_object* v___x_631_; 
v_a_630_ = lean_array_uget_borrowed(v_as_619_, v_i_621_);
lean_inc(v_a_630_);
v___x_631_ = l___private_Lean_Meta_Tactic_Grind_NormSym_0__Lean_Meta_Grind_addNormSymTheorem(v_b_622_, v_a_630_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; size_t v___x_633_; size_t v___x_634_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_633_ = ((size_t)1ULL);
v___x_634_ = lean_usize_add(v_i_621_, v___x_633_);
v_i_621_ = v___x_634_;
v_b_622_ = v_a_632_;
goto _start;
}
else
{
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4___boxed(lean_object* v_as_636_, lean_object* v_sz_637_, lean_object* v_i_638_, lean_object* v_b_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
size_t v_sz_boxed_645_; size_t v_i_boxed_646_; lean_object* v_res_647_; 
v_sz_boxed_645_ = lean_unbox_usize(v_sz_637_);
lean_dec(v_sz_637_);
v_i_boxed_646_ = lean_unbox_usize(v_i_638_);
lean_dec(v_i_638_);
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(v_as_636_, v_sz_boxed_645_, v_i_boxed_646_, v_b_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec_ref(v_as_636_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__12(lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
if (lean_obj_tag(v_a_648_) == 0)
{
lean_object* v___x_650_; 
v___x_650_ = l_List_reverse___redArg(v_a_649_);
return v___x_650_;
}
else
{
lean_object* v_head_651_; lean_object* v_tail_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_661_; 
v_head_651_ = lean_ctor_get(v_a_648_, 0);
v_tail_652_ = lean_ctor_get(v_a_648_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_a_648_);
if (v_isSharedCheck_661_ == 0)
{
v___x_654_ = v_a_648_;
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_tail_652_);
lean_inc(v_head_651_);
lean_dec(v_a_648_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_fst_656_; lean_object* v___x_658_; 
v_fst_656_ = lean_ctor_get(v_head_651_, 0);
lean_inc(v_fst_656_);
lean_dec(v_head_651_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 1, v_a_649_);
lean_ctor_set(v___x_654_, 0, v_fst_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_fst_656_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_a_649_);
v___x_658_ = v_reuseFailAlloc_660_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
v_a_648_ = v_tail_652_;
v_a_649_ = v___x_658_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg___lam__0(lean_object* v_f_662_, lean_object* v_x1_663_, lean_object* v_x2_664_, lean_object* v_x3_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_apply_3(v_f_662_, v_x1_663_, v_x2_664_, v_x3_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(lean_object* v_f_667_, lean_object* v_keys_668_, lean_object* v_vals_669_, lean_object* v_i_670_, lean_object* v_acc_671_){
_start:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = lean_array_get_size(v_keys_668_);
v___x_673_ = lean_nat_dec_lt(v_i_670_, v___x_672_);
if (v___x_673_ == 0)
{
lean_dec(v_i_670_);
lean_dec(v_f_667_);
return v_acc_671_;
}
else
{
lean_object* v_k_674_; lean_object* v_v_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_k_674_ = lean_array_fget_borrowed(v_keys_668_, v_i_670_);
v_v_675_ = lean_array_fget_borrowed(v_vals_669_, v_i_670_);
lean_inc(v_f_667_);
lean_inc(v_v_675_);
lean_inc(v_k_674_);
v___x_676_ = lean_apply_3(v_f_667_, v_acc_671_, v_k_674_, v_v_675_);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_add(v_i_670_, v___x_677_);
lean_dec(v_i_670_);
v_i_670_ = v___x_678_;
v_acc_671_ = v___x_676_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_f_680_, lean_object* v_keys_681_, lean_object* v_vals_682_, lean_object* v_i_683_, lean_object* v_acc_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_680_, v_keys_681_, v_vals_682_, v_i_683_, v_acc_684_);
lean_dec_ref(v_vals_682_);
lean_dec_ref(v_keys_681_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(lean_object* v_f_686_, lean_object* v_as_687_, size_t v_i_688_, size_t v_stop_689_, lean_object* v_b_690_){
_start:
{
lean_object* v___y_692_; uint8_t v___x_696_; 
v___x_696_ = lean_usize_dec_eq(v_i_688_, v_stop_689_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_array_uget_borrowed(v_as_687_, v_i_688_);
switch(lean_obj_tag(v___x_697_))
{
case 0:
{
lean_object* v_key_698_; lean_object* v_val_699_; lean_object* v___x_700_; 
v_key_698_ = lean_ctor_get(v___x_697_, 0);
v_val_699_ = lean_ctor_get(v___x_697_, 1);
lean_inc(v_f_686_);
lean_inc(v_val_699_);
lean_inc(v_key_698_);
v___x_700_ = lean_apply_3(v_f_686_, v_b_690_, v_key_698_, v_val_699_);
v___y_692_ = v___x_700_;
goto v___jp_691_;
}
case 1:
{
lean_object* v_node_701_; lean_object* v___x_702_; 
v_node_701_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_f_686_);
v___x_702_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_686_, v_node_701_, v_b_690_);
v___y_692_ = v___x_702_;
goto v___jp_691_;
}
default: 
{
v___y_692_ = v_b_690_;
goto v___jp_691_;
}
}
}
else
{
lean_dec(v_f_686_);
return v_b_690_;
}
v___jp_691_:
{
size_t v___x_693_; size_t v___x_694_; 
v___x_693_ = ((size_t)1ULL);
v___x_694_ = lean_usize_add(v_i_688_, v___x_693_);
v_i_688_ = v___x_694_;
v_b_690_ = v___y_692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(lean_object* v_f_703_, lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
if (lean_obj_tag(v_x_704_) == 0)
{
lean_object* v_es_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_es_706_ = lean_ctor_get(v_x_704_, 0);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = lean_array_get_size(v_es_706_);
v___x_709_ = lean_nat_dec_lt(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
lean_dec(v_f_703_);
return v_x_705_;
}
else
{
size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; 
v___x_710_ = ((size_t)0ULL);
v___x_711_ = lean_usize_of_nat(v___x_708_);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_703_, v_es_706_, v___x_710_, v___x_711_, v_x_705_);
return v___x_712_;
}
}
else
{
lean_object* v_ks_713_; lean_object* v_vs_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_ks_713_ = lean_ctor_get(v_x_704_, 0);
v_vs_714_ = lean_ctor_get(v_x_704_, 1);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_703_, v_ks_713_, v_vs_714_, v___x_715_, v_x_705_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg___boxed(lean_object* v_f_717_, lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_717_, v_x_718_, v_x_719_);
lean_dec_ref(v_x_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v_f_721_, lean_object* v_as_722_, lean_object* v_i_723_, lean_object* v_stop_724_, lean_object* v_b_725_){
_start:
{
size_t v_i_boxed_726_; size_t v_stop_boxed_727_; lean_object* v_res_728_; 
v_i_boxed_726_ = lean_unbox_usize(v_i_723_);
lean_dec(v_i_723_);
v_stop_boxed_727_ = lean_unbox_usize(v_stop_724_);
lean_dec(v_stop_724_);
v_res_728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_721_, v_as_722_, v_i_boxed_726_, v_stop_boxed_727_, v_b_725_);
lean_dec_ref(v_as_722_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(lean_object* v_map_729_, lean_object* v_f_730_, lean_object* v_init_731_){
_start:
{
lean_object* v___f_732_; lean_object* v___x_733_; 
v___f_732_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg___lam__0), 4, 1);
lean_closure_set(v___f_732_, 0, v_f_730_);
v___x_733_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_732_, v_map_729_, v_init_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg___boxed(lean_object* v_map_734_, lean_object* v_f_735_, lean_object* v_init_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(v_map_734_, v_f_735_, v_init_736_);
lean_dec_ref(v_map_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___lam__0(lean_object* v_ps_738_, lean_object* v_k_739_, lean_object* v_v_740_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_k_739_);
lean_ctor_set(v___x_741_, 1, v_v_740_);
v___x_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v_ps_738_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(lean_object* v_m_744_){
_start:
{
lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___f_745_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___closed__0));
v___x_746_ = lean_box(0);
v___x_747_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(v_m_744_, v___f_745_, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg___boxed(lean_object* v_m_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(v_m_748_);
lean_dec_ref(v_m_748_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(lean_object* v_s_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(v_s_750_);
v___x_752_ = lean_box(0);
v___x_753_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__12(v___x_751_, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7___boxed(lean_object* v_s_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(v_s_754_);
lean_dec_ref(v_s_754_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(lean_object* v_as_x27_756_, lean_object* v_b_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
if (lean_obj_tag(v_as_x27_756_) == 0)
{
lean_object* v___x_763_; 
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v_b_757_);
return v___x_763_;
}
else
{
lean_object* v_head_764_; lean_object* v_tail_765_; lean_object* v___x_766_; 
v_head_764_ = lean_ctor_get(v_as_x27_756_, 0);
v_tail_765_ = lean_ctor_get(v_as_x27_756_, 1);
lean_inc(v_head_764_);
v___x_766_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_head_764_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_757_, v_a_767_);
v_as_x27_756_ = v_tail_765_;
v_b_757_ = v___x_768_;
goto _start;
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_b_757_);
v_a_770_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_766_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_766_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg___boxed(lean_object* v_as_x27_778_, lean_object* v_b_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v_as_x27_778_, v_b_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v_as_x27_778_);
return v_res_785_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1(void){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_787_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__2(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__1, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__1_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__2, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__2_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__2);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
return v___x_791_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__12(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = l_Lean_NameSet_empty;
v___x_810_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__3, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__3_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__13(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__12, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__12_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__12);
v___x_813_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__3, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__3_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___x_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems(lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___f_820_; lean_object* v___x_821_; 
v___f_820_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__0));
v___x_821_ = l_Lean_Meta_Grind_getNormTheorems(v_a_815_, v_a_816_, v_a_817_, v_a_818_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; lean_object* v_pre_824_; lean_object* v_post_825_; lean_object* v_toUnfold_826_; lean_object* v___x_827_; lean_object* v___x_828_; size_t v_sz_829_; size_t v___x_830_; lean_object* v___x_831_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
v___x_823_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__3, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__3_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__3);
v_pre_824_ = lean_ctor_get(v_a_822_, 0);
lean_inc_ref(v_pre_824_);
v_post_825_ = lean_ctor_get(v_a_822_, 1);
lean_inc_ref(v_post_825_);
v_toUnfold_826_ = lean_ctor_get(v_a_822_, 3);
lean_inc_ref(v_toUnfold_826_);
lean_dec(v_a_822_);
v___x_827_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__4));
v___x_828_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_820_, v_pre_824_, v___x_827_);
lean_dec_ref(v_pre_824_);
v_sz_829_ = lean_array_size(v___x_828_);
v___x_830_ = ((size_t)0ULL);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__4(v___x_828_, v_sz_829_, v___x_830_, v___x_823_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v___x_828_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
v___x_833_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymTheorems___closed__11));
v___x_834_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v___x_833_, v_a_832_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_836_; lean_object* v___x_837_; size_t v_sz_838_; lean_object* v___x_839_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_834_, 1);
v___x_836_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v___f_820_, v_post_825_, v___x_827_);
lean_dec_ref(v_post_825_);
v___x_837_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__13, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__13_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__13);
v_sz_838_ = lean_array_size(v___x_836_);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__6(v___x_836_, v_sz_838_, v___x_830_, v___x_837_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v___x_836_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v_fst_841_; lean_object* v_snd_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_870_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v_fst_841_ = lean_ctor_get(v_a_840_, 0);
v_snd_842_ = lean_ctor_get(v_a_840_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_a_840_);
if (v_isSharedCheck_870_ == 0)
{
v___x_844_ = v_a_840_;
v_isShared_845_ = v_isSharedCheck_870_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_snd_842_);
lean_inc(v_fst_841_);
lean_dec(v_a_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_870_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = l_Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7(v_toUnfold_826_);
lean_dec_ref(v_toUnfold_826_);
if (v_isShared_845_ == 0)
{
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_fst_841_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_snd_842_);
v___x_848_ = v_reuseFailAlloc_869_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; 
v___x_849_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(v___x_846_, v___x_848_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v___x_846_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_860_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_860_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_fst_854_; lean_object* v_snd_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v_fst_854_ = lean_ctor_get(v_a_850_, 0);
lean_inc(v_fst_854_);
v_snd_855_ = lean_ctor_get(v_a_850_, 1);
lean_inc(v_snd_855_);
lean_dec(v_a_850_);
v___x_856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_856_, 0, v_a_835_);
lean_ctor_set(v___x_856_, 1, v_fst_854_);
lean_ctor_set(v___x_856_, 2, v_snd_855_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_856_);
v___x_858_ = v___x_852_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_a_835_);
v_a_861_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_849_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_849_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_a_835_);
lean_dec_ref(v_toUnfold_826_);
v_a_871_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_839_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_839_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec_ref(v_toUnfold_826_);
lean_dec_ref(v_post_825_);
v_a_879_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_834_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_834_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref(v_toUnfold_826_);
lean_dec_ref(v_post_825_);
v_a_887_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_831_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_831_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_821_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_821_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymTheorems___boxed(lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Meta_Grind_mkNormSymTheorems(v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0(lean_object* v_declName_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___redArg(v_declName_909_, v___y_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0___boxed(lean_object* v_declName_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__0_spec__0(v_declName_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1(lean_object* v_as_923_, size_t v_sz_924_, size_t v_i_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___redArg(v_as_923_, v_sz_924_, v_i_925_, v_b_926_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1___boxed(lean_object* v_as_933_, lean_object* v_sz_934_, lean_object* v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
size_t v_sz_boxed_942_; size_t v_i_boxed_943_; lean_object* v_res_944_; 
v_sz_boxed_942_ = lean_unbox_usize(v_sz_934_);
lean_dec(v_sz_934_);
v_i_boxed_943_ = lean_unbox_usize(v_i_935_);
lean_dec(v_i_935_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__1(v_as_933_, v_sz_boxed_942_, v_i_boxed_943_, v_b_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec_ref(v_as_933_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg(lean_object* v_map_945_, lean_object* v_f_946_, lean_object* v_init_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_946_, v_map_945_, v_init_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg___boxed(lean_object* v_map_949_, lean_object* v_f_950_, lean_object* v_init_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___redArg(v_map_949_, v_f_950_, v_init_951_);
lean_dec_ref(v_map_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3(lean_object* v_00_u03c3_953_, lean_object* v_00_u03b2_954_, lean_object* v_map_955_, lean_object* v_f_956_, lean_object* v_init_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_956_, v_map_955_, v_init_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3___boxed(lean_object* v_00_u03c3_959_, lean_object* v_00_u03b2_960_, lean_object* v_map_961_, lean_object* v_f_962_, lean_object* v_init_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3(v_00_u03c3_959_, v_00_u03b2_960_, v_map_961_, v_f_962_, v_init_963_);
lean_dec_ref(v_map_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5(lean_object* v_as_965_, lean_object* v_as_x27_966_, lean_object* v_b_967_, lean_object* v_a_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___redArg(v_as_x27_966_, v_b_967_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5___boxed(lean_object* v_as_975_, lean_object* v_as_x27_976_, lean_object* v_b_977_, lean_object* v_a_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__5(v_as_975_, v_as_x27_976_, v_b_977_, v_a_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v_as_x27_976_);
lean_dec(v_as_975_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8(lean_object* v_as_985_, lean_object* v_as_x27_986_, lean_object* v_b_987_, lean_object* v_a_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___redArg(v_as_x27_986_, v_b_987_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8___boxed(lean_object* v_as_995_, lean_object* v_as_x27_996_, lean_object* v_b_997_, lean_object* v_a_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__8(v_as_995_, v_as_x27_996_, v_b_997_, v_a_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v_as_x27_996_);
lean_dec(v_as_995_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6(lean_object* v_00_u03c3_1005_, lean_object* v_00_u03b1_1006_, lean_object* v_00_u03b2_1007_, lean_object* v_f_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_1008_, v_x_1009_, v_x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1012_, lean_object* v_00_u03b1_1013_, lean_object* v_00_u03b2_1014_, lean_object* v_f_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6(v_00_u03c3_1012_, v_00_u03b1_1013_, v_00_u03b2_1014_, v_f_1015_, v_x_1016_, v_x_1017_);
lean_dec_ref(v_x_1016_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11(lean_object* v_00_u03b2_1019_, lean_object* v_m_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___redArg(v_m_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1022_, lean_object* v_m_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11(v_00_u03b2_1022_, v_m_1023_);
lean_dec_ref(v_m_1023_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7(lean_object* v_00_u03b1_1025_, lean_object* v_00_u03b2_1026_, lean_object* v_00_u03c3_1027_, lean_object* v_f_1028_, lean_object* v_as_1029_, size_t v_i_1030_, size_t v_stop_1031_, lean_object* v_b_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___redArg(v_f_1028_, v_as_1029_, v_i_1030_, v_stop_1031_, v_b_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7___boxed(lean_object* v_00_u03b1_1034_, lean_object* v_00_u03b2_1035_, lean_object* v_00_u03c3_1036_, lean_object* v_f_1037_, lean_object* v_as_1038_, lean_object* v_i_1039_, lean_object* v_stop_1040_, lean_object* v_b_1041_){
_start:
{
size_t v_i_boxed_1042_; size_t v_stop_boxed_1043_; lean_object* v_res_1044_; 
v_i_boxed_1042_ = lean_unbox_usize(v_i_1039_);
lean_dec(v_i_1039_);
v_stop_boxed_1043_ = lean_unbox_usize(v_stop_1040_);
lean_dec(v_stop_1040_);
v_res_1044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__7(v_00_u03b1_1034_, v_00_u03b2_1035_, v_00_u03c3_1036_, v_f_1037_, v_as_1038_, v_i_boxed_1042_, v_stop_boxed_1043_, v_b_1041_);
lean_dec_ref(v_as_1038_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8(lean_object* v_00_u03c3_1045_, lean_object* v_00_u03b1_1046_, lean_object* v_00_u03b2_1047_, lean_object* v_f_1048_, lean_object* v_keys_1049_, lean_object* v_vals_1050_, lean_object* v_heq_1051_, lean_object* v_i_1052_, lean_object* v_acc_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___redArg(v_f_1048_, v_keys_1049_, v_vals_1050_, v_i_1052_, v_acc_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03c3_1055_, lean_object* v_00_u03b1_1056_, lean_object* v_00_u03b2_1057_, lean_object* v_f_1058_, lean_object* v_keys_1059_, lean_object* v_vals_1060_, lean_object* v_heq_1061_, lean_object* v_i_1062_, lean_object* v_acc_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6_spec__8(v_00_u03c3_1055_, v_00_u03b1_1056_, v_00_u03b2_1057_, v_f_1058_, v_keys_1059_, v_vals_1060_, v_heq_1061_, v_i_1062_, v_acc_1063_);
lean_dec_ref(v_vals_1060_);
lean_dec_ref(v_keys_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14(lean_object* v_00_u03c3_1065_, lean_object* v_00_u03b2_1066_, lean_object* v_map_1067_, lean_object* v_f_1068_, lean_object* v_init_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___redArg(v_map_1067_, v_f_1068_, v_init_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14___boxed(lean_object* v_00_u03c3_1071_, lean_object* v_00_u03b2_1072_, lean_object* v_map_1073_, lean_object* v_f_1074_, lean_object* v_init_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14(v_00_u03c3_1071_, v_00_u03b2_1072_, v_map_1073_, v_f_1074_, v_init_1075_);
lean_dec_ref(v_map_1073_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___redArg(lean_object* v_map_1077_, lean_object* v_f_1078_, lean_object* v_init_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_1078_, v_map_1077_, v_init_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___redArg___boxed(lean_object* v_map_1081_, lean_object* v_f_1082_, lean_object* v_init_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___redArg(v_map_1081_, v_f_1082_, v_init_1083_);
lean_dec_ref(v_map_1081_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16(lean_object* v_00_u03c3_1085_, lean_object* v_00_u03b2_1086_, lean_object* v_map_1087_, lean_object* v_f_1088_, lean_object* v_init_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__3_spec__6___redArg(v_f_1088_, v_map_1087_, v_init_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16___boxed(lean_object* v_00_u03c3_1091_, lean_object* v_00_u03b2_1092_, lean_object* v_map_1093_, lean_object* v_f_1094_, lean_object* v_init_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Meta_Grind_mkNormSymTheorems_spec__7_spec__11_spec__14_spec__16(v_00_u03c3_1091_, v_00_u03b2_1092_, v_map_1093_, v_f_1094_, v_init_1095_);
lean_dec_ref(v_map_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0(lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; 
lean_inc_ref(v___y_1098_);
v___x_1109_ = l_Lean_Meta_Sym_Simp_reduceControl(v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
if (lean_obj_tag(v_a_1110_) == 0)
{
uint8_t v_done_1111_; 
v_done_1111_ = lean_ctor_get_uint8(v_a_1110_, 0);
if (v_done_1111_ == 0)
{
uint8_t v_contextDependent_1112_; lean_object* v___x_1113_; 
lean_dec_ref_known(v___x_1109_, 1);
v_contextDependent_1112_ = lean_ctor_get_uint8(v_a_1110_, 1);
lean_dec_ref_known(v_a_1110_, 0);
v___x_1113_ = l_Lean_Meta_Sym_Simp_simpExistsPropDomain(v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; uint8_t v___y_1116_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
if (v_contextDependent_1112_ == 0)
{
return v___x_1113_;
}
else
{
if (lean_obj_tag(v_a_1114_) == 0)
{
uint8_t v_contextDependent_1126_; 
v_contextDependent_1126_ = lean_ctor_get_uint8(v_a_1114_, 1);
v___y_1116_ = v_contextDependent_1126_;
goto v___jp_1115_;
}
else
{
uint8_t v_contextDependent_1127_; 
v_contextDependent_1127_ = lean_ctor_get_uint8(v_a_1114_, sizeof(void*)*2 + 1);
v___y_1116_ = v_contextDependent_1127_;
goto v___jp_1115_;
}
}
v___jp_1115_:
{
if (v___y_1116_ == 0)
{
lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1124_; 
lean_inc(v_a_1114_);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; 
v_unused_1125_ = lean_ctor_get(v___x_1113_, 0);
lean_dec(v_unused_1125_);
v___x_1118_ = v___x_1113_;
v_isShared_1119_ = v_isSharedCheck_1124_;
goto v_resetjp_1117_;
}
else
{
lean_dec(v___x_1113_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1124_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1114_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1120_);
v___x_1122_ = v___x_1118_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
else
{
return v___x_1113_;
}
}
}
else
{
return v___x_1113_;
}
}
else
{
lean_dec_ref_known(v_a_1110_, 0);
lean_dec_ref(v___y_1098_);
return v___x_1109_;
}
}
else
{
uint8_t v_done_1128_; 
v_done_1128_ = lean_ctor_get_uint8(v_a_1110_, sizeof(void*)*2);
if (v_done_1128_ == 0)
{
lean_object* v_e_x27_1129_; lean_object* v_proof_1130_; uint8_t v_contextDependent_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref_known(v___x_1109_, 1);
v_e_x27_1129_ = lean_ctor_get(v_a_1110_, 0);
v_proof_1130_ = lean_ctor_get(v_a_1110_, 1);
v_contextDependent_1131_ = lean_ctor_get_uint8(v_a_1110_, sizeof(void*)*2 + 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_a_1110_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1133_ = v_a_1110_;
v_isShared_1134_ = v_isSharedCheck_1181_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_proof_1130_);
lean_inc(v_e_x27_1129_);
lean_dec(v_a_1110_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1181_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; 
lean_inc_ref(v_e_x27_1129_);
v___x_1135_ = l_Lean_Meta_Sym_Simp_simpExistsPropDomain(v_e_x27_1129_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1180_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1180_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1180_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
if (lean_obj_tag(v_a_1136_) == 0)
{
uint8_t v_done_1140_; uint8_t v_contextDependent_1141_; uint8_t v___y_1143_; 
lean_dec_ref(v___y_1098_);
v_done_1140_ = lean_ctor_get_uint8(v_a_1136_, 0);
v_contextDependent_1141_ = lean_ctor_get_uint8(v_a_1136_, 1);
lean_dec_ref_known(v_a_1136_, 0);
if (v_contextDependent_1131_ == 0)
{
v___y_1143_ = v_contextDependent_1141_;
goto v___jp_1142_;
}
else
{
v___y_1143_ = v_contextDependent_1131_;
goto v___jp_1142_;
}
v___jp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1134_ == 0)
{
v___x_1145_ = v___x_1133_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_e_x27_1129_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_proof_1130_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*2, v_done_1140_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*2 + 1, v___y_1143_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1145_);
v___x_1147_ = v___x_1138_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v_e_x27_1150_; lean_object* v_proof_1151_; uint8_t v_done_1152_; uint8_t v_contextDependent_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1179_; 
lean_del_object(v___x_1138_);
lean_del_object(v___x_1133_);
v_e_x27_1150_ = lean_ctor_get(v_a_1136_, 0);
v_proof_1151_ = lean_ctor_get(v_a_1136_, 1);
v_done_1152_ = lean_ctor_get_uint8(v_a_1136_, sizeof(void*)*2);
v_contextDependent_1153_ = lean_ctor_get_uint8(v_a_1136_, sizeof(void*)*2 + 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_a_1136_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1155_ = v_a_1136_;
v_isShared_1156_ = v_isSharedCheck_1179_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_proof_1151_);
lean_inc(v_e_x27_1150_);
lean_dec(v_a_1136_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1179_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; 
lean_inc_ref(v_e_x27_1150_);
v___x_1157_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1098_, v_e_x27_1129_, v_proof_1130_, v_e_x27_1150_, v_proof_1151_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1170_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1170_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
uint8_t v___y_1163_; 
if (v_contextDependent_1131_ == 0)
{
v___y_1163_ = v_contextDependent_1153_;
goto v___jp_1162_;
}
else
{
v___y_1163_ = v_contextDependent_1131_;
goto v___jp_1162_;
}
v___jp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 1, v_a_1158_);
v___x_1165_ = v___x_1155_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_e_x27_1150_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_a_1158_);
lean_ctor_set_uint8(v_reuseFailAlloc_1169_, sizeof(void*)*2, v_done_1152_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
lean_ctor_set_uint8(v___x_1165_, sizeof(void*)*2 + 1, v___y_1163_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1165_);
v___x_1167_ = v___x_1160_;
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
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_del_object(v___x_1155_);
lean_dec_ref(v_e_x27_1150_);
v_a_1171_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1157_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1157_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1133_);
lean_dec_ref(v_proof_1130_);
lean_dec_ref(v_e_x27_1129_);
lean_dec_ref(v___y_1098_);
return v___x_1135_;
}
}
}
else
{
lean_dec_ref_known(v_a_1110_, 2);
lean_dec_ref(v___y_1098_);
return v___x_1109_;
}
}
}
else
{
lean_dec_ref(v___y_1098_);
return v___x_1109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0___boxed(lean_object* v_x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__0(v_x_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1(lean_object* v___f_1195_, lean_object* v_x_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_box(0);
lean_inc_ref(v___y_1197_);
v___x_1209_ = l_Lean_Meta_Sym_Simp_reduceProj___redArg(v___y_1197_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
if (lean_obj_tag(v_a_1210_) == 0)
{
uint8_t v_done_1211_; 
v_done_1211_ = lean_ctor_get_uint8(v_a_1210_, 0);
if (v_done_1211_ == 0)
{
uint8_t v_contextDependent_1212_; lean_object* v___x_1213_; 
lean_dec_ref_known(v___x_1209_, 1);
v_contextDependent_1212_ = lean_ctor_get_uint8(v_a_1210_, 1);
lean_dec_ref_known(v_a_1210_, 0);
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1203_);
lean_inc(v___y_1202_);
lean_inc_ref(v___y_1201_);
lean_inc(v___y_1200_);
lean_inc_ref(v___y_1199_);
lean_inc(v___y_1198_);
v___x_1213_ = lean_apply_12(v___f_1195_, v___x_1208_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, lean_box(0));
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; uint8_t v___y_1216_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
if (v_contextDependent_1212_ == 0)
{
lean_dec(v_a_1214_);
return v___x_1213_;
}
else
{
if (lean_obj_tag(v_a_1214_) == 0)
{
uint8_t v_contextDependent_1226_; 
v_contextDependent_1226_ = lean_ctor_get_uint8(v_a_1214_, 1);
v___y_1216_ = v_contextDependent_1226_;
goto v___jp_1215_;
}
else
{
uint8_t v_contextDependent_1227_; 
v_contextDependent_1227_ = lean_ctor_get_uint8(v_a_1214_, sizeof(void*)*2 + 1);
v___y_1216_ = v_contextDependent_1227_;
goto v___jp_1215_;
}
}
v___jp_1215_:
{
if (v___y_1216_ == 0)
{
lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1224_; 
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v___x_1213_, 0);
lean_dec(v_unused_1225_);
v___x_1218_ = v___x_1213_;
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
else
{
lean_dec(v___x_1213_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1220_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1214_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1220_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
lean_dec(v_a_1214_);
return v___x_1213_;
}
}
}
else
{
return v___x_1213_;
}
}
else
{
lean_dec_ref_known(v_a_1210_, 0);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v___f_1195_);
return v___x_1209_;
}
}
else
{
uint8_t v_done_1228_; 
v_done_1228_ = lean_ctor_get_uint8(v_a_1210_, sizeof(void*)*2);
if (v_done_1228_ == 0)
{
lean_object* v_e_x27_1229_; lean_object* v_proof_1230_; uint8_t v_contextDependent_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref_known(v___x_1209_, 1);
v_e_x27_1229_ = lean_ctor_get(v_a_1210_, 0);
v_proof_1230_ = lean_ctor_get(v_a_1210_, 1);
v_contextDependent_1231_ = lean_ctor_get_uint8(v_a_1210_, sizeof(void*)*2 + 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1233_ = v_a_1210_;
v_isShared_1234_ = v_isSharedCheck_1281_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_proof_1230_);
lean_inc(v_e_x27_1229_);
lean_dec(v_a_1210_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1281_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; 
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1203_);
lean_inc(v___y_1202_);
lean_inc_ref(v___y_1201_);
lean_inc(v___y_1200_);
lean_inc_ref(v___y_1199_);
lean_inc(v___y_1198_);
lean_inc_ref(v_e_x27_1229_);
v___x_1235_ = lean_apply_12(v___f_1195_, v___x_1208_, v_e_x27_1229_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, lean_box(0));
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1280_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1280_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1280_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
if (lean_obj_tag(v_a_1236_) == 0)
{
uint8_t v_done_1240_; uint8_t v_contextDependent_1241_; uint8_t v___y_1243_; 
lean_dec_ref(v___y_1197_);
v_done_1240_ = lean_ctor_get_uint8(v_a_1236_, 0);
v_contextDependent_1241_ = lean_ctor_get_uint8(v_a_1236_, 1);
lean_dec_ref_known(v_a_1236_, 0);
if (v_contextDependent_1231_ == 0)
{
v___y_1243_ = v_contextDependent_1241_;
goto v___jp_1242_;
}
else
{
v___y_1243_ = v_contextDependent_1231_;
goto v___jp_1242_;
}
v___jp_1242_:
{
lean_object* v___x_1245_; 
if (v_isShared_1234_ == 0)
{
v___x_1245_ = v___x_1233_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_e_x27_1229_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_proof_1230_);
v___x_1245_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1247_; 
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*2, v_done_1240_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*2 + 1, v___y_1243_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1245_);
v___x_1247_ = v___x_1238_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_e_x27_1250_; lean_object* v_proof_1251_; uint8_t v_done_1252_; uint8_t v_contextDependent_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1279_; 
lean_del_object(v___x_1238_);
lean_del_object(v___x_1233_);
v_e_x27_1250_ = lean_ctor_get(v_a_1236_, 0);
v_proof_1251_ = lean_ctor_get(v_a_1236_, 1);
v_done_1252_ = lean_ctor_get_uint8(v_a_1236_, sizeof(void*)*2);
v_contextDependent_1253_ = lean_ctor_get_uint8(v_a_1236_, sizeof(void*)*2 + 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_a_1236_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1255_ = v_a_1236_;
v_isShared_1256_ = v_isSharedCheck_1279_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_proof_1251_);
lean_inc(v_e_x27_1250_);
lean_dec(v_a_1236_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1279_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; 
lean_inc_ref(v_e_x27_1250_);
v___x_1257_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1197_, v_e_x27_1229_, v_proof_1230_, v_e_x27_1250_, v_proof_1251_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1270_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1270_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1270_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
uint8_t v___y_1263_; 
if (v_contextDependent_1231_ == 0)
{
v___y_1263_ = v_contextDependent_1253_;
goto v___jp_1262_;
}
else
{
v___y_1263_ = v_contextDependent_1231_;
goto v___jp_1262_;
}
v___jp_1262_:
{
lean_object* v___x_1265_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 1, v_a_1258_);
v___x_1265_ = v___x_1255_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_e_x27_1250_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_a_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*2, v_done_1252_);
v___x_1265_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1267_; 
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*2 + 1, v___y_1263_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1265_);
v___x_1267_ = v___x_1260_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_del_object(v___x_1255_);
lean_dec_ref(v_e_x27_1250_);
v_a_1271_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1257_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1257_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1233_);
lean_dec_ref(v_proof_1230_);
lean_dec_ref(v_e_x27_1229_);
lean_dec_ref(v___y_1197_);
return v___x_1235_;
}
}
}
else
{
lean_dec_ref_known(v_a_1210_, 2);
lean_dec_ref(v___y_1197_);
lean_dec_ref(v___f_1195_);
return v___x_1209_;
}
}
}
else
{
lean_dec_ref(v___y_1197_);
lean_dec_ref(v___f_1195_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1___boxed(lean_object* v___f_1282_, lean_object* v_x_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__1(v___f_1282_, v_x_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2(lean_object* v___f_1296_, lean_object* v_x_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_box(0);
lean_inc_ref(v___y_1298_);
v___x_1310_ = l_Lean_Meta_Sym_Simp_beta___redArg(v___y_1298_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
if (lean_obj_tag(v_a_1311_) == 0)
{
uint8_t v_done_1312_; 
v_done_1312_ = lean_ctor_get_uint8(v_a_1311_, 0);
if (v_done_1312_ == 0)
{
uint8_t v_contextDependent_1313_; lean_object* v___x_1314_; 
lean_dec_ref_known(v___x_1310_, 1);
v_contextDependent_1313_ = lean_ctor_get_uint8(v_a_1311_, 1);
lean_dec_ref_known(v_a_1311_, 0);
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
lean_inc(v___y_1301_);
lean_inc_ref(v___y_1300_);
lean_inc(v___y_1299_);
v___x_1314_ = lean_apply_12(v___f_1296_, v___x_1309_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, lean_box(0));
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; uint8_t v___y_1317_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
if (v_contextDependent_1313_ == 0)
{
lean_dec(v_a_1315_);
return v___x_1314_;
}
else
{
if (lean_obj_tag(v_a_1315_) == 0)
{
uint8_t v_contextDependent_1327_; 
v_contextDependent_1327_ = lean_ctor_get_uint8(v_a_1315_, 1);
v___y_1317_ = v_contextDependent_1327_;
goto v___jp_1316_;
}
else
{
uint8_t v_contextDependent_1328_; 
v_contextDependent_1328_ = lean_ctor_get_uint8(v_a_1315_, sizeof(void*)*2 + 1);
v___y_1317_ = v_contextDependent_1328_;
goto v___jp_1316_;
}
}
v___jp_1316_:
{
if (v___y_1317_ == 0)
{
lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1325_; 
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; 
v_unused_1326_ = lean_ctor_get(v___x_1314_, 0);
lean_dec(v_unused_1326_);
v___x_1319_ = v___x_1314_;
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
else
{
lean_dec(v___x_1314_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1315_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1321_);
v___x_1323_ = v___x_1319_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
else
{
lean_dec(v_a_1315_);
return v___x_1314_;
}
}
}
else
{
return v___x_1314_;
}
}
else
{
lean_dec_ref_known(v_a_1311_, 0);
lean_dec_ref(v___y_1298_);
lean_dec_ref(v___f_1296_);
return v___x_1310_;
}
}
else
{
uint8_t v_done_1329_; 
v_done_1329_ = lean_ctor_get_uint8(v_a_1311_, sizeof(void*)*2);
if (v_done_1329_ == 0)
{
lean_object* v_e_x27_1330_; lean_object* v_proof_1331_; uint8_t v_contextDependent_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1382_; 
lean_dec_ref_known(v___x_1310_, 1);
v_e_x27_1330_ = lean_ctor_get(v_a_1311_, 0);
v_proof_1331_ = lean_ctor_get(v_a_1311_, 1);
v_contextDependent_1332_ = lean_ctor_get_uint8(v_a_1311_, sizeof(void*)*2 + 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_a_1311_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1334_ = v_a_1311_;
v_isShared_1335_ = v_isSharedCheck_1382_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_proof_1331_);
lean_inc(v_e_x27_1330_);
lean_dec(v_a_1311_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1382_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; 
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
lean_inc(v___y_1301_);
lean_inc_ref(v___y_1300_);
lean_inc(v___y_1299_);
lean_inc_ref(v_e_x27_1330_);
v___x_1336_ = lean_apply_12(v___f_1296_, v___x_1309_, v_e_x27_1330_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, lean_box(0));
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1381_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1381_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1381_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
if (lean_obj_tag(v_a_1337_) == 0)
{
uint8_t v_done_1341_; uint8_t v_contextDependent_1342_; uint8_t v___y_1344_; 
lean_dec_ref(v___y_1298_);
v_done_1341_ = lean_ctor_get_uint8(v_a_1337_, 0);
v_contextDependent_1342_ = lean_ctor_get_uint8(v_a_1337_, 1);
lean_dec_ref_known(v_a_1337_, 0);
if (v_contextDependent_1332_ == 0)
{
v___y_1344_ = v_contextDependent_1342_;
goto v___jp_1343_;
}
else
{
v___y_1344_ = v_contextDependent_1332_;
goto v___jp_1343_;
}
v___jp_1343_:
{
lean_object* v___x_1346_; 
if (v_isShared_1335_ == 0)
{
v___x_1346_ = v___x_1334_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_e_x27_1330_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_proof_1331_);
v___x_1346_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1348_; 
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*2, v_done_1341_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*2 + 1, v___y_1344_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1346_);
v___x_1348_ = v___x_1339_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_e_x27_1351_; lean_object* v_proof_1352_; uint8_t v_done_1353_; uint8_t v_contextDependent_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1380_; 
lean_del_object(v___x_1339_);
lean_del_object(v___x_1334_);
v_e_x27_1351_ = lean_ctor_get(v_a_1337_, 0);
v_proof_1352_ = lean_ctor_get(v_a_1337_, 1);
v_done_1353_ = lean_ctor_get_uint8(v_a_1337_, sizeof(void*)*2);
v_contextDependent_1354_ = lean_ctor_get_uint8(v_a_1337_, sizeof(void*)*2 + 1);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_a_1337_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1356_ = v_a_1337_;
v_isShared_1357_ = v_isSharedCheck_1380_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_proof_1352_);
lean_inc(v_e_x27_1351_);
lean_dec(v_a_1337_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1380_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; 
lean_inc_ref(v_e_x27_1351_);
v___x_1358_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1298_, v_e_x27_1330_, v_proof_1331_, v_e_x27_1351_, v_proof_1352_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1371_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1371_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1371_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
uint8_t v___y_1364_; 
if (v_contextDependent_1332_ == 0)
{
v___y_1364_ = v_contextDependent_1354_;
goto v___jp_1363_;
}
else
{
v___y_1364_ = v_contextDependent_1332_;
goto v___jp_1363_;
}
v___jp_1363_:
{
lean_object* v___x_1366_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v_a_1359_);
v___x_1366_ = v___x_1356_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_e_x27_1351_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_a_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*2, v_done_1353_);
v___x_1366_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*2 + 1, v___y_1364_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1366_);
v___x_1368_ = v___x_1361_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_del_object(v___x_1356_);
lean_dec_ref(v_e_x27_1351_);
v_a_1372_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1358_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1358_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1334_);
lean_dec_ref(v_proof_1331_);
lean_dec_ref(v_e_x27_1330_);
lean_dec_ref(v___y_1298_);
return v___x_1336_;
}
}
}
else
{
lean_dec_ref_known(v_a_1311_, 2);
lean_dec_ref(v___y_1298_);
lean_dec_ref(v___f_1296_);
return v___x_1310_;
}
}
}
else
{
lean_dec_ref(v___y_1298_);
lean_dec_ref(v___f_1296_);
return v___x_1310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2___boxed(lean_object* v___f_1383_, lean_object* v_x_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__2(v___f_1383_, v_x_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3(lean_object* v___f_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_box(0);
lean_inc_ref(v___y_1399_);
v___x_1411_ = l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
if (lean_obj_tag(v_a_1412_) == 0)
{
uint8_t v_done_1413_; 
v_done_1413_ = lean_ctor_get_uint8(v_a_1412_, 0);
if (v_done_1413_ == 0)
{
uint8_t v_contextDependent_1414_; lean_object* v___x_1415_; 
lean_dec_ref_known(v___x_1411_, 1);
v_contextDependent_1414_ = lean_ctor_get_uint8(v_a_1412_, 1);
lean_dec_ref_known(v_a_1412_, 0);
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
v___x_1415_ = lean_apply_12(v___f_1397_, v___x_1410_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, lean_box(0));
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; uint8_t v___y_1418_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
if (v_contextDependent_1414_ == 0)
{
lean_dec(v_a_1416_);
return v___x_1415_;
}
else
{
if (lean_obj_tag(v_a_1416_) == 0)
{
uint8_t v_contextDependent_1428_; 
v_contextDependent_1428_ = lean_ctor_get_uint8(v_a_1416_, 1);
v___y_1418_ = v_contextDependent_1428_;
goto v___jp_1417_;
}
else
{
uint8_t v_contextDependent_1429_; 
v_contextDependent_1429_ = lean_ctor_get_uint8(v_a_1416_, sizeof(void*)*2 + 1);
v___y_1418_ = v_contextDependent_1429_;
goto v___jp_1417_;
}
}
v___jp_1417_:
{
if (v___y_1418_ == 0)
{
lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1426_; 
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; 
v_unused_1427_ = lean_ctor_get(v___x_1415_, 0);
lean_dec(v_unused_1427_);
v___x_1420_ = v___x_1415_;
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
else
{
lean_dec(v___x_1415_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1416_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1422_);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
else
{
lean_dec(v_a_1416_);
return v___x_1415_;
}
}
}
else
{
return v___x_1415_;
}
}
else
{
lean_dec_ref_known(v_a_1412_, 0);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v___f_1397_);
return v___x_1411_;
}
}
else
{
uint8_t v_done_1430_; 
v_done_1430_ = lean_ctor_get_uint8(v_a_1412_, sizeof(void*)*2);
if (v_done_1430_ == 0)
{
lean_object* v_e_x27_1431_; lean_object* v_proof_1432_; uint8_t v_contextDependent_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref_known(v___x_1411_, 1);
v_e_x27_1431_ = lean_ctor_get(v_a_1412_, 0);
v_proof_1432_ = lean_ctor_get(v_a_1412_, 1);
v_contextDependent_1433_ = lean_ctor_get_uint8(v_a_1412_, sizeof(void*)*2 + 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_a_1412_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1435_ = v_a_1412_;
v_isShared_1436_ = v_isSharedCheck_1483_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_proof_1432_);
lean_inc(v_e_x27_1431_);
lean_dec(v_a_1412_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1483_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; 
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v___y_1401_);
lean_inc(v___y_1400_);
lean_inc_ref(v_e_x27_1431_);
v___x_1437_ = lean_apply_12(v___f_1397_, v___x_1410_, v_e_x27_1431_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, lean_box(0));
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1482_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1482_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1482_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
if (lean_obj_tag(v_a_1438_) == 0)
{
uint8_t v_done_1442_; uint8_t v_contextDependent_1443_; uint8_t v___y_1445_; 
lean_dec_ref(v___y_1399_);
v_done_1442_ = lean_ctor_get_uint8(v_a_1438_, 0);
v_contextDependent_1443_ = lean_ctor_get_uint8(v_a_1438_, 1);
lean_dec_ref_known(v_a_1438_, 0);
if (v_contextDependent_1433_ == 0)
{
v___y_1445_ = v_contextDependent_1443_;
goto v___jp_1444_;
}
else
{
v___y_1445_ = v_contextDependent_1433_;
goto v___jp_1444_;
}
v___jp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1436_ == 0)
{
v___x_1447_ = v___x_1435_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_e_x27_1431_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_proof_1432_);
v___x_1447_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1449_; 
lean_ctor_set_uint8(v___x_1447_, sizeof(void*)*2, v_done_1442_);
lean_ctor_set_uint8(v___x_1447_, sizeof(void*)*2 + 1, v___y_1445_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1447_);
v___x_1449_ = v___x_1440_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v_e_x27_1452_; lean_object* v_proof_1453_; uint8_t v_done_1454_; uint8_t v_contextDependent_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1481_; 
lean_del_object(v___x_1440_);
lean_del_object(v___x_1435_);
v_e_x27_1452_ = lean_ctor_get(v_a_1438_, 0);
v_proof_1453_ = lean_ctor_get(v_a_1438_, 1);
v_done_1454_ = lean_ctor_get_uint8(v_a_1438_, sizeof(void*)*2);
v_contextDependent_1455_ = lean_ctor_get_uint8(v_a_1438_, sizeof(void*)*2 + 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_a_1438_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1457_ = v_a_1438_;
v_isShared_1458_ = v_isSharedCheck_1481_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_proof_1453_);
lean_inc(v_e_x27_1452_);
lean_dec(v_a_1438_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1481_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; 
lean_inc_ref(v_e_x27_1452_);
v___x_1459_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1399_, v_e_x27_1431_, v_proof_1432_, v_e_x27_1452_, v_proof_1453_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1472_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1472_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1472_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
uint8_t v___y_1465_; 
if (v_contextDependent_1433_ == 0)
{
v___y_1465_ = v_contextDependent_1455_;
goto v___jp_1464_;
}
else
{
v___y_1465_ = v_contextDependent_1433_;
goto v___jp_1464_;
}
v___jp_1464_:
{
lean_object* v___x_1467_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 1, v_a_1460_);
v___x_1467_ = v___x_1457_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_e_x27_1452_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_a_1460_);
lean_ctor_set_uint8(v_reuseFailAlloc_1471_, sizeof(void*)*2, v_done_1454_);
v___x_1467_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1469_; 
lean_ctor_set_uint8(v___x_1467_, sizeof(void*)*2 + 1, v___y_1465_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1467_);
v___x_1469_ = v___x_1462_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_del_object(v___x_1457_);
lean_dec_ref(v_e_x27_1452_);
v_a_1473_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1459_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1459_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1435_);
lean_dec_ref(v_proof_1432_);
lean_dec_ref(v_e_x27_1431_);
lean_dec_ref(v___y_1399_);
return v___x_1437_;
}
}
}
else
{
lean_dec_ref_known(v_a_1412_, 2);
lean_dec_ref(v___y_1399_);
lean_dec_ref(v___f_1397_);
return v___x_1411_;
}
}
}
else
{
lean_dec_ref(v___y_1399_);
lean_dec_ref(v___f_1397_);
return v___x_1411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3___boxed(lean_object* v___f_1484_, lean_object* v_x_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__3(v___f_1484_, v_x_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4(lean_object* v___f_1498_, lean_object* v_x_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_box(0);
lean_inc_ref(v___y_1500_);
v___x_1512_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v___y_1500_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
if (lean_obj_tag(v_a_1513_) == 0)
{
uint8_t v_done_1514_; 
v_done_1514_ = lean_ctor_get_uint8(v_a_1513_, 0);
if (v_done_1514_ == 0)
{
uint8_t v_contextDependent_1515_; lean_object* v___x_1516_; 
lean_dec_ref_known(v___x_1512_, 1);
v_contextDependent_1515_ = lean_ctor_get_uint8(v_a_1513_, 1);
lean_dec_ref_known(v_a_1513_, 0);
lean_inc(v___y_1509_);
lean_inc_ref(v___y_1508_);
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
lean_inc(v___y_1501_);
v___x_1516_ = lean_apply_12(v___f_1498_, v___x_1511_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, lean_box(0));
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; uint8_t v___y_1519_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
if (v_contextDependent_1515_ == 0)
{
lean_dec(v_a_1517_);
return v___x_1516_;
}
else
{
if (lean_obj_tag(v_a_1517_) == 0)
{
uint8_t v_contextDependent_1529_; 
v_contextDependent_1529_ = lean_ctor_get_uint8(v_a_1517_, 1);
v___y_1519_ = v_contextDependent_1529_;
goto v___jp_1518_;
}
else
{
uint8_t v_contextDependent_1530_; 
v_contextDependent_1530_ = lean_ctor_get_uint8(v_a_1517_, sizeof(void*)*2 + 1);
v___y_1519_ = v_contextDependent_1530_;
goto v___jp_1518_;
}
}
v___jp_1518_:
{
if (v___y_1519_ == 0)
{
lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1527_; 
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v___x_1516_, 0);
lean_dec(v_unused_1528_);
v___x_1521_ = v___x_1516_;
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
else
{
lean_dec(v___x_1516_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1523_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1517_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1523_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
else
{
lean_dec(v_a_1517_);
return v___x_1516_;
}
}
}
else
{
return v___x_1516_;
}
}
else
{
lean_dec_ref_known(v_a_1513_, 0);
lean_dec_ref(v___y_1500_);
lean_dec_ref(v___f_1498_);
return v___x_1512_;
}
}
else
{
uint8_t v_done_1531_; 
v_done_1531_ = lean_ctor_get_uint8(v_a_1513_, sizeof(void*)*2);
if (v_done_1531_ == 0)
{
lean_object* v_e_x27_1532_; lean_object* v_proof_1533_; uint8_t v_contextDependent_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref_known(v___x_1512_, 1);
v_e_x27_1532_ = lean_ctor_get(v_a_1513_, 0);
v_proof_1533_ = lean_ctor_get(v_a_1513_, 1);
v_contextDependent_1534_ = lean_ctor_get_uint8(v_a_1513_, sizeof(void*)*2 + 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_a_1513_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1536_ = v_a_1513_;
v_isShared_1537_ = v_isSharedCheck_1584_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_proof_1533_);
lean_inc(v_e_x27_1532_);
lean_dec(v_a_1513_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1584_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; 
lean_inc(v___y_1509_);
lean_inc_ref(v___y_1508_);
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
lean_inc(v___y_1505_);
lean_inc_ref(v___y_1504_);
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
lean_inc(v___y_1501_);
lean_inc_ref(v_e_x27_1532_);
v___x_1538_ = lean_apply_12(v___f_1498_, v___x_1511_, v_e_x27_1532_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, lean_box(0));
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1583_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1583_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1583_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
if (lean_obj_tag(v_a_1539_) == 0)
{
uint8_t v_done_1543_; uint8_t v_contextDependent_1544_; uint8_t v___y_1546_; 
lean_dec_ref(v___y_1500_);
v_done_1543_ = lean_ctor_get_uint8(v_a_1539_, 0);
v_contextDependent_1544_ = lean_ctor_get_uint8(v_a_1539_, 1);
lean_dec_ref_known(v_a_1539_, 0);
if (v_contextDependent_1534_ == 0)
{
v___y_1546_ = v_contextDependent_1544_;
goto v___jp_1545_;
}
else
{
v___y_1546_ = v_contextDependent_1534_;
goto v___jp_1545_;
}
v___jp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1537_ == 0)
{
v___x_1548_ = v___x_1536_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_e_x27_1532_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_proof_1533_);
v___x_1548_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1550_; 
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*2, v_done_1543_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*2 + 1, v___y_1546_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1548_);
v___x_1550_ = v___x_1541_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_e_x27_1553_; lean_object* v_proof_1554_; uint8_t v_done_1555_; uint8_t v_contextDependent_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1582_; 
lean_del_object(v___x_1541_);
lean_del_object(v___x_1536_);
v_e_x27_1553_ = lean_ctor_get(v_a_1539_, 0);
v_proof_1554_ = lean_ctor_get(v_a_1539_, 1);
v_done_1555_ = lean_ctor_get_uint8(v_a_1539_, sizeof(void*)*2);
v_contextDependent_1556_ = lean_ctor_get_uint8(v_a_1539_, sizeof(void*)*2 + 1);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_a_1539_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1558_ = v_a_1539_;
v_isShared_1559_ = v_isSharedCheck_1582_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_proof_1554_);
lean_inc(v_e_x27_1553_);
lean_dec(v_a_1539_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1582_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; 
lean_inc_ref(v_e_x27_1553_);
v___x_1560_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1500_, v_e_x27_1532_, v_proof_1533_, v_e_x27_1553_, v_proof_1554_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1573_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1573_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1573_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
uint8_t v___y_1566_; 
if (v_contextDependent_1534_ == 0)
{
v___y_1566_ = v_contextDependent_1556_;
goto v___jp_1565_;
}
else
{
v___y_1566_ = v_contextDependent_1534_;
goto v___jp_1565_;
}
v___jp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 1, v_a_1561_);
v___x_1568_ = v___x_1558_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_e_x27_1553_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_a_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1572_, sizeof(void*)*2, v_done_1555_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1570_; 
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*2 + 1, v___y_1566_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1568_);
v___x_1570_ = v___x_1563_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_del_object(v___x_1558_);
lean_dec_ref(v_e_x27_1553_);
v_a_1574_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1560_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1560_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1536_);
lean_dec_ref(v_proof_1533_);
lean_dec_ref(v_e_x27_1532_);
lean_dec_ref(v___y_1500_);
return v___x_1538_;
}
}
}
else
{
lean_dec_ref_known(v_a_1513_, 2);
lean_dec_ref(v___y_1500_);
lean_dec_ref(v___f_1498_);
return v___x_1512_;
}
}
}
else
{
lean_dec_ref(v___y_1500_);
lean_dec_ref(v___f_1498_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4___boxed(lean_object* v___f_1585_, lean_object* v_x_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__4(v___f_1585_, v_x_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5(lean_object* v_x_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; 
lean_inc_ref(v___y_1600_);
v___x_1611_ = l_Lean_Meta_Grind_NormSym_simpForall(v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
if (lean_obj_tag(v_a_1612_) == 0)
{
uint8_t v_done_1613_; 
v_done_1613_ = lean_ctor_get_uint8(v_a_1612_, 0);
if (v_done_1613_ == 0)
{
uint8_t v_contextDependent_1614_; lean_object* v___x_1615_; 
lean_dec_ref_known(v___x_1611_, 1);
v_contextDependent_1614_ = lean_ctor_get_uint8(v_a_1612_, 1);
lean_dec_ref_known(v_a_1612_, 0);
v___x_1615_ = l_Lean_Meta_Grind_NormSym_simpExists(v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; uint8_t v___y_1618_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
if (v_contextDependent_1614_ == 0)
{
return v___x_1615_;
}
else
{
if (lean_obj_tag(v_a_1616_) == 0)
{
uint8_t v_contextDependent_1628_; 
v_contextDependent_1628_ = lean_ctor_get_uint8(v_a_1616_, 1);
v___y_1618_ = v_contextDependent_1628_;
goto v___jp_1617_;
}
else
{
uint8_t v_contextDependent_1629_; 
v_contextDependent_1629_ = lean_ctor_get_uint8(v_a_1616_, sizeof(void*)*2 + 1);
v___y_1618_ = v_contextDependent_1629_;
goto v___jp_1617_;
}
}
v___jp_1617_:
{
if (v___y_1618_ == 0)
{
lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1626_; 
lean_inc(v_a_1616_);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v___x_1615_, 0);
lean_dec(v_unused_1627_);
v___x_1620_ = v___x_1615_;
v_isShared_1621_ = v_isSharedCheck_1626_;
goto v_resetjp_1619_;
}
else
{
lean_dec(v___x_1615_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1626_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1622_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1616_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1622_);
v___x_1624_ = v___x_1620_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
else
{
return v___x_1615_;
}
}
}
else
{
return v___x_1615_;
}
}
else
{
lean_dec_ref_known(v_a_1612_, 0);
lean_dec_ref(v___y_1600_);
return v___x_1611_;
}
}
else
{
uint8_t v_done_1630_; 
v_done_1630_ = lean_ctor_get_uint8(v_a_1612_, sizeof(void*)*2);
if (v_done_1630_ == 0)
{
lean_object* v_e_x27_1631_; lean_object* v_proof_1632_; uint8_t v_contextDependent_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref_known(v___x_1611_, 1);
v_e_x27_1631_ = lean_ctor_get(v_a_1612_, 0);
v_proof_1632_ = lean_ctor_get(v_a_1612_, 1);
v_contextDependent_1633_ = lean_ctor_get_uint8(v_a_1612_, sizeof(void*)*2 + 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_a_1612_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1635_ = v_a_1612_;
v_isShared_1636_ = v_isSharedCheck_1683_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_proof_1632_);
lean_inc(v_e_x27_1631_);
lean_dec(v_a_1612_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1683_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; 
lean_inc_ref(v_e_x27_1631_);
v___x_1637_ = l_Lean_Meta_Grind_NormSym_simpExists(v_e_x27_1631_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1682_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1682_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1682_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
if (lean_obj_tag(v_a_1638_) == 0)
{
uint8_t v_done_1642_; uint8_t v_contextDependent_1643_; uint8_t v___y_1645_; 
lean_dec_ref(v___y_1600_);
v_done_1642_ = lean_ctor_get_uint8(v_a_1638_, 0);
v_contextDependent_1643_ = lean_ctor_get_uint8(v_a_1638_, 1);
lean_dec_ref_known(v_a_1638_, 0);
if (v_contextDependent_1633_ == 0)
{
v___y_1645_ = v_contextDependent_1643_;
goto v___jp_1644_;
}
else
{
v___y_1645_ = v_contextDependent_1633_;
goto v___jp_1644_;
}
v___jp_1644_:
{
lean_object* v___x_1647_; 
if (v_isShared_1636_ == 0)
{
v___x_1647_ = v___x_1635_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_e_x27_1631_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_proof_1632_);
v___x_1647_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*2, v_done_1642_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*2 + 1, v___y_1645_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1647_);
v___x_1649_ = v___x_1640_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v_e_x27_1652_; lean_object* v_proof_1653_; uint8_t v_done_1654_; uint8_t v_contextDependent_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1681_; 
lean_del_object(v___x_1640_);
lean_del_object(v___x_1635_);
v_e_x27_1652_ = lean_ctor_get(v_a_1638_, 0);
v_proof_1653_ = lean_ctor_get(v_a_1638_, 1);
v_done_1654_ = lean_ctor_get_uint8(v_a_1638_, sizeof(void*)*2);
v_contextDependent_1655_ = lean_ctor_get_uint8(v_a_1638_, sizeof(void*)*2 + 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_a_1638_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1657_ = v_a_1638_;
v_isShared_1658_ = v_isSharedCheck_1681_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_proof_1653_);
lean_inc(v_e_x27_1652_);
lean_dec(v_a_1638_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1681_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; 
lean_inc_ref(v_e_x27_1652_);
v___x_1659_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1600_, v_e_x27_1631_, v_proof_1632_, v_e_x27_1652_, v_proof_1653_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1672_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1672_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1672_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
uint8_t v___y_1665_; 
if (v_contextDependent_1633_ == 0)
{
v___y_1665_ = v_contextDependent_1655_;
goto v___jp_1664_;
}
else
{
v___y_1665_ = v_contextDependent_1633_;
goto v___jp_1664_;
}
v___jp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v_a_1660_);
v___x_1667_ = v___x_1657_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_e_x27_1652_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_a_1660_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*2, v_done_1654_);
v___x_1667_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1669_; 
lean_ctor_set_uint8(v___x_1667_, sizeof(void*)*2 + 1, v___y_1665_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1667_);
v___x_1669_ = v___x_1662_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_del_object(v___x_1657_);
lean_dec_ref(v_e_x27_1652_);
v_a_1673_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1659_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1659_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1635_);
lean_dec_ref(v_proof_1632_);
lean_dec_ref(v_e_x27_1631_);
lean_dec_ref(v___y_1600_);
return v___x_1637_;
}
}
}
else
{
lean_dec_ref_known(v_a_1612_, 2);
lean_dec_ref(v___y_1600_);
return v___x_1611_;
}
}
}
else
{
lean_dec_ref(v___y_1600_);
return v___x_1611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed(lean_object* v_x_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__5(v_x_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6(lean_object* v___f_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_box(0);
lean_inc_ref(v___y_1699_);
v___x_1711_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
if (lean_obj_tag(v_a_1712_) == 0)
{
uint8_t v_done_1713_; 
v_done_1713_ = lean_ctor_get_uint8(v_a_1712_, 0);
if (v_done_1713_ == 0)
{
uint8_t v_contextDependent_1714_; lean_object* v___x_1715_; 
lean_dec_ref_known(v___x_1711_, 1);
v_contextDependent_1714_ = lean_ctor_get_uint8(v_a_1712_, 1);
lean_dec_ref_known(v_a_1712_, 0);
lean_inc(v___y_1708_);
lean_inc_ref(v___y_1707_);
lean_inc(v___y_1706_);
lean_inc_ref(v___y_1705_);
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1701_);
lean_inc(v___y_1700_);
v___x_1715_ = lean_apply_12(v___f_1697_, v___x_1710_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, lean_box(0));
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; uint8_t v___y_1718_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
if (v_contextDependent_1714_ == 0)
{
lean_dec(v_a_1716_);
return v___x_1715_;
}
else
{
if (lean_obj_tag(v_a_1716_) == 0)
{
uint8_t v_contextDependent_1728_; 
v_contextDependent_1728_ = lean_ctor_get_uint8(v_a_1716_, 1);
v___y_1718_ = v_contextDependent_1728_;
goto v___jp_1717_;
}
else
{
uint8_t v_contextDependent_1729_; 
v_contextDependent_1729_ = lean_ctor_get_uint8(v_a_1716_, sizeof(void*)*2 + 1);
v___y_1718_ = v_contextDependent_1729_;
goto v___jp_1717_;
}
}
v___jp_1717_:
{
if (v___y_1718_ == 0)
{
lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1726_; 
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v___x_1715_, 0);
lean_dec(v_unused_1727_);
v___x_1720_ = v___x_1715_;
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
else
{
lean_dec(v___x_1715_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1716_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
else
{
lean_dec(v_a_1716_);
return v___x_1715_;
}
}
}
else
{
return v___x_1715_;
}
}
else
{
lean_dec_ref_known(v_a_1712_, 0);
lean_dec_ref(v___y_1699_);
lean_dec_ref(v___f_1697_);
return v___x_1711_;
}
}
else
{
uint8_t v_done_1730_; 
v_done_1730_ = lean_ctor_get_uint8(v_a_1712_, sizeof(void*)*2);
if (v_done_1730_ == 0)
{
lean_object* v_e_x27_1731_; lean_object* v_proof_1732_; uint8_t v_contextDependent_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1783_; 
lean_dec_ref_known(v___x_1711_, 1);
v_e_x27_1731_ = lean_ctor_get(v_a_1712_, 0);
v_proof_1732_ = lean_ctor_get(v_a_1712_, 1);
v_contextDependent_1733_ = lean_ctor_get_uint8(v_a_1712_, sizeof(void*)*2 + 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_a_1712_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1735_ = v_a_1712_;
v_isShared_1736_ = v_isSharedCheck_1783_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_proof_1732_);
lean_inc(v_e_x27_1731_);
lean_dec(v_a_1712_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1783_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; 
lean_inc(v___y_1708_);
lean_inc_ref(v___y_1707_);
lean_inc(v___y_1706_);
lean_inc_ref(v___y_1705_);
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1701_);
lean_inc(v___y_1700_);
lean_inc_ref(v_e_x27_1731_);
v___x_1737_ = lean_apply_12(v___f_1697_, v___x_1710_, v_e_x27_1731_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, lean_box(0));
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1782_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1782_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1782_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
if (lean_obj_tag(v_a_1738_) == 0)
{
uint8_t v_done_1742_; uint8_t v_contextDependent_1743_; uint8_t v___y_1745_; 
lean_dec_ref(v___y_1699_);
v_done_1742_ = lean_ctor_get_uint8(v_a_1738_, 0);
v_contextDependent_1743_ = lean_ctor_get_uint8(v_a_1738_, 1);
lean_dec_ref_known(v_a_1738_, 0);
if (v_contextDependent_1733_ == 0)
{
v___y_1745_ = v_contextDependent_1743_;
goto v___jp_1744_;
}
else
{
v___y_1745_ = v_contextDependent_1733_;
goto v___jp_1744_;
}
v___jp_1744_:
{
lean_object* v___x_1747_; 
if (v_isShared_1736_ == 0)
{
v___x_1747_ = v___x_1735_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_e_x27_1731_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_proof_1732_);
v___x_1747_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1749_; 
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*2, v_done_1742_);
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*2 + 1, v___y_1745_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1747_);
v___x_1749_ = v___x_1740_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
else
{
lean_object* v_e_x27_1752_; lean_object* v_proof_1753_; uint8_t v_done_1754_; uint8_t v_contextDependent_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1781_; 
lean_del_object(v___x_1740_);
lean_del_object(v___x_1735_);
v_e_x27_1752_ = lean_ctor_get(v_a_1738_, 0);
v_proof_1753_ = lean_ctor_get(v_a_1738_, 1);
v_done_1754_ = lean_ctor_get_uint8(v_a_1738_, sizeof(void*)*2);
v_contextDependent_1755_ = lean_ctor_get_uint8(v_a_1738_, sizeof(void*)*2 + 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_a_1738_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1757_ = v_a_1738_;
v_isShared_1758_ = v_isSharedCheck_1781_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_proof_1753_);
lean_inc(v_e_x27_1752_);
lean_dec(v_a_1738_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1781_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; 
lean_inc_ref(v_e_x27_1752_);
v___x_1759_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1699_, v_e_x27_1731_, v_proof_1732_, v_e_x27_1752_, v_proof_1753_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1772_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1772_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1772_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
uint8_t v___y_1765_; 
if (v_contextDependent_1733_ == 0)
{
v___y_1765_ = v_contextDependent_1755_;
goto v___jp_1764_;
}
else
{
v___y_1765_ = v_contextDependent_1733_;
goto v___jp_1764_;
}
v___jp_1764_:
{
lean_object* v___x_1767_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v_a_1760_);
v___x_1767_ = v___x_1757_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_e_x27_1752_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_a_1760_);
lean_ctor_set_uint8(v_reuseFailAlloc_1771_, sizeof(void*)*2, v_done_1754_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1769_; 
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*2 + 1, v___y_1765_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v___x_1767_);
v___x_1769_ = v___x_1762_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_del_object(v___x_1757_);
lean_dec_ref(v_e_x27_1752_);
v_a_1773_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1759_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1759_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1735_);
lean_dec_ref(v_proof_1732_);
lean_dec_ref(v_e_x27_1731_);
lean_dec_ref(v___y_1699_);
return v___x_1737_;
}
}
}
else
{
lean_dec_ref_known(v_a_1712_, 2);
lean_dec_ref(v___y_1699_);
lean_dec_ref(v___f_1697_);
return v___x_1711_;
}
}
}
else
{
lean_dec_ref(v___y_1699_);
lean_dec_ref(v___f_1697_);
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed(lean_object* v___f_1784_, lean_object* v_x_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__6(v___f_1784_, v_x_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7(lean_object* v___f_1798_, lean_object* v_x_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_box(0);
lean_inc_ref(v___y_1800_);
v___x_1812_ = l_Lean_Meta_Grind_NormSym_simpDIte(v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
if (lean_obj_tag(v_a_1813_) == 0)
{
uint8_t v_done_1814_; 
v_done_1814_ = lean_ctor_get_uint8(v_a_1813_, 0);
if (v_done_1814_ == 0)
{
uint8_t v_contextDependent_1815_; lean_object* v___x_1816_; 
lean_dec_ref_known(v___x_1812_, 1);
v_contextDependent_1815_ = lean_ctor_get_uint8(v_a_1813_, 1);
lean_dec_ref_known(v_a_1813_, 0);
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1808_);
lean_inc(v___y_1807_);
lean_inc_ref(v___y_1806_);
lean_inc(v___y_1805_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1803_);
lean_inc_ref(v___y_1802_);
lean_inc(v___y_1801_);
v___x_1816_ = lean_apply_12(v___f_1798_, v___x_1811_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, lean_box(0));
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; uint8_t v___y_1819_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
if (v_contextDependent_1815_ == 0)
{
lean_dec(v_a_1817_);
return v___x_1816_;
}
else
{
if (lean_obj_tag(v_a_1817_) == 0)
{
uint8_t v_contextDependent_1829_; 
v_contextDependent_1829_ = lean_ctor_get_uint8(v_a_1817_, 1);
v___y_1819_ = v_contextDependent_1829_;
goto v___jp_1818_;
}
else
{
uint8_t v_contextDependent_1830_; 
v_contextDependent_1830_ = lean_ctor_get_uint8(v_a_1817_, sizeof(void*)*2 + 1);
v___y_1819_ = v_contextDependent_1830_;
goto v___jp_1818_;
}
}
v___jp_1818_:
{
if (v___y_1819_ == 0)
{
lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1827_; 
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v___x_1816_, 0);
lean_dec(v_unused_1828_);
v___x_1821_ = v___x_1816_;
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
else
{
lean_dec(v___x_1816_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1817_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
else
{
lean_dec(v_a_1817_);
return v___x_1816_;
}
}
}
else
{
return v___x_1816_;
}
}
else
{
lean_dec_ref_known(v_a_1813_, 0);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v___f_1798_);
return v___x_1812_;
}
}
else
{
uint8_t v_done_1831_; 
v_done_1831_ = lean_ctor_get_uint8(v_a_1813_, sizeof(void*)*2);
if (v_done_1831_ == 0)
{
lean_object* v_e_x27_1832_; lean_object* v_proof_1833_; uint8_t v_contextDependent_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref_known(v___x_1812_, 1);
v_e_x27_1832_ = lean_ctor_get(v_a_1813_, 0);
v_proof_1833_ = lean_ctor_get(v_a_1813_, 1);
v_contextDependent_1834_ = lean_ctor_get_uint8(v_a_1813_, sizeof(void*)*2 + 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_a_1813_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1836_ = v_a_1813_;
v_isShared_1837_ = v_isSharedCheck_1884_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_proof_1833_);
lean_inc(v_e_x27_1832_);
lean_dec(v_a_1813_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1884_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; 
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1808_);
lean_inc(v___y_1807_);
lean_inc_ref(v___y_1806_);
lean_inc(v___y_1805_);
lean_inc_ref(v___y_1804_);
lean_inc(v___y_1803_);
lean_inc_ref(v___y_1802_);
lean_inc(v___y_1801_);
lean_inc_ref(v_e_x27_1832_);
v___x_1838_ = lean_apply_12(v___f_1798_, v___x_1811_, v_e_x27_1832_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, lean_box(0));
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1883_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1883_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1883_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
if (lean_obj_tag(v_a_1839_) == 0)
{
uint8_t v_done_1843_; uint8_t v_contextDependent_1844_; uint8_t v___y_1846_; 
lean_dec_ref(v___y_1800_);
v_done_1843_ = lean_ctor_get_uint8(v_a_1839_, 0);
v_contextDependent_1844_ = lean_ctor_get_uint8(v_a_1839_, 1);
lean_dec_ref_known(v_a_1839_, 0);
if (v_contextDependent_1834_ == 0)
{
v___y_1846_ = v_contextDependent_1844_;
goto v___jp_1845_;
}
else
{
v___y_1846_ = v_contextDependent_1834_;
goto v___jp_1845_;
}
v___jp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1837_ == 0)
{
v___x_1848_ = v___x_1836_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_e_x27_1832_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_proof_1833_);
v___x_1848_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1850_; 
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*2, v_done_1843_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*2 + 1, v___y_1846_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1848_);
v___x_1850_ = v___x_1841_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_object* v_e_x27_1853_; lean_object* v_proof_1854_; uint8_t v_done_1855_; uint8_t v_contextDependent_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1882_; 
lean_del_object(v___x_1841_);
lean_del_object(v___x_1836_);
v_e_x27_1853_ = lean_ctor_get(v_a_1839_, 0);
v_proof_1854_ = lean_ctor_get(v_a_1839_, 1);
v_done_1855_ = lean_ctor_get_uint8(v_a_1839_, sizeof(void*)*2);
v_contextDependent_1856_ = lean_ctor_get_uint8(v_a_1839_, sizeof(void*)*2 + 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_a_1839_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1858_ = v_a_1839_;
v_isShared_1859_ = v_isSharedCheck_1882_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_proof_1854_);
lean_inc(v_e_x27_1853_);
lean_dec(v_a_1839_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1882_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; 
lean_inc_ref(v_e_x27_1853_);
v___x_1860_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1800_, v_e_x27_1832_, v_proof_1833_, v_e_x27_1853_, v_proof_1854_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1873_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1873_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1873_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
uint8_t v___y_1866_; 
if (v_contextDependent_1834_ == 0)
{
v___y_1866_ = v_contextDependent_1856_;
goto v___jp_1865_;
}
else
{
v___y_1866_ = v_contextDependent_1834_;
goto v___jp_1865_;
}
v___jp_1865_:
{
lean_object* v___x_1868_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v_a_1861_);
v___x_1868_ = v___x_1858_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_e_x27_1853_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_a_1861_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*2, v_done_1855_);
v___x_1868_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1870_; 
lean_ctor_set_uint8(v___x_1868_, sizeof(void*)*2 + 1, v___y_1866_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1868_);
v___x_1870_ = v___x_1863_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_del_object(v___x_1858_);
lean_dec_ref(v_e_x27_1853_);
v_a_1874_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1860_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1860_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1836_);
lean_dec_ref(v_proof_1833_);
lean_dec_ref(v_e_x27_1832_);
lean_dec_ref(v___y_1800_);
return v___x_1838_;
}
}
}
else
{
lean_dec_ref_known(v_a_1813_, 2);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v___f_1798_);
return v___x_1812_;
}
}
}
else
{
lean_dec_ref(v___y_1800_);
lean_dec_ref(v___f_1798_);
return v___x_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7___boxed(lean_object* v___f_1885_, lean_object* v_x_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__7(v___f_1885_, v_x_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8(lean_object* v___f_1899_, lean_object* v_x_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_box(0);
lean_inc_ref(v___y_1901_);
v___x_1913_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v___y_1901_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
if (lean_obj_tag(v_a_1914_) == 0)
{
uint8_t v_done_1915_; 
v_done_1915_ = lean_ctor_get_uint8(v_a_1914_, 0);
if (v_done_1915_ == 0)
{
uint8_t v_contextDependent_1916_; lean_object* v___x_1917_; 
lean_dec_ref_known(v___x_1913_, 1);
v_contextDependent_1916_ = lean_ctor_get_uint8(v_a_1914_, 1);
lean_dec_ref_known(v_a_1914_, 0);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
lean_inc(v___y_1908_);
lean_inc_ref(v___y_1907_);
lean_inc(v___y_1906_);
lean_inc_ref(v___y_1905_);
lean_inc(v___y_1904_);
lean_inc_ref(v___y_1903_);
lean_inc(v___y_1902_);
v___x_1917_ = lean_apply_12(v___f_1899_, v___x_1912_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, lean_box(0));
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; uint8_t v___y_1920_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
if (v_contextDependent_1916_ == 0)
{
lean_dec(v_a_1918_);
return v___x_1917_;
}
else
{
if (lean_obj_tag(v_a_1918_) == 0)
{
uint8_t v_contextDependent_1930_; 
v_contextDependent_1930_ = lean_ctor_get_uint8(v_a_1918_, 1);
v___y_1920_ = v_contextDependent_1930_;
goto v___jp_1919_;
}
else
{
uint8_t v_contextDependent_1931_; 
v_contextDependent_1931_ = lean_ctor_get_uint8(v_a_1918_, sizeof(void*)*2 + 1);
v___y_1920_ = v_contextDependent_1931_;
goto v___jp_1919_;
}
}
v___jp_1919_:
{
if (v___y_1920_ == 0)
{
lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1928_; 
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v___x_1917_, 0);
lean_dec(v_unused_1929_);
v___x_1922_ = v___x_1917_;
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
else
{
lean_dec(v___x_1917_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1918_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
else
{
lean_dec(v_a_1918_);
return v___x_1917_;
}
}
}
else
{
return v___x_1917_;
}
}
else
{
lean_dec_ref_known(v_a_1914_, 0);
lean_dec_ref(v___y_1901_);
lean_dec_ref(v___f_1899_);
return v___x_1913_;
}
}
else
{
uint8_t v_done_1932_; 
v_done_1932_ = lean_ctor_get_uint8(v_a_1914_, sizeof(void*)*2);
if (v_done_1932_ == 0)
{
lean_object* v_e_x27_1933_; lean_object* v_proof_1934_; uint8_t v_contextDependent_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref_known(v___x_1913_, 1);
v_e_x27_1933_ = lean_ctor_get(v_a_1914_, 0);
v_proof_1934_ = lean_ctor_get(v_a_1914_, 1);
v_contextDependent_1935_ = lean_ctor_get_uint8(v_a_1914_, sizeof(void*)*2 + 1);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_a_1914_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1937_ = v_a_1914_;
v_isShared_1938_ = v_isSharedCheck_1985_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_proof_1934_);
lean_inc(v_e_x27_1933_);
lean_dec(v_a_1914_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1985_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; 
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
lean_inc(v___y_1908_);
lean_inc_ref(v___y_1907_);
lean_inc(v___y_1906_);
lean_inc_ref(v___y_1905_);
lean_inc(v___y_1904_);
lean_inc_ref(v___y_1903_);
lean_inc(v___y_1902_);
lean_inc_ref(v_e_x27_1933_);
v___x_1939_ = lean_apply_12(v___f_1899_, v___x_1912_, v_e_x27_1933_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, lean_box(0));
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1984_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1984_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1984_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
if (lean_obj_tag(v_a_1940_) == 0)
{
uint8_t v_done_1944_; uint8_t v_contextDependent_1945_; uint8_t v___y_1947_; 
lean_dec_ref(v___y_1901_);
v_done_1944_ = lean_ctor_get_uint8(v_a_1940_, 0);
v_contextDependent_1945_ = lean_ctor_get_uint8(v_a_1940_, 1);
lean_dec_ref_known(v_a_1940_, 0);
if (v_contextDependent_1935_ == 0)
{
v___y_1947_ = v_contextDependent_1945_;
goto v___jp_1946_;
}
else
{
v___y_1947_ = v_contextDependent_1935_;
goto v___jp_1946_;
}
v___jp_1946_:
{
lean_object* v___x_1949_; 
if (v_isShared_1938_ == 0)
{
v___x_1949_ = v___x_1937_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_e_x27_1933_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_proof_1934_);
v___x_1949_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1951_; 
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*2, v_done_1944_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*2 + 1, v___y_1947_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1949_);
v___x_1951_ = v___x_1942_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v_e_x27_1954_; lean_object* v_proof_1955_; uint8_t v_done_1956_; uint8_t v_contextDependent_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1983_; 
lean_del_object(v___x_1942_);
lean_del_object(v___x_1937_);
v_e_x27_1954_ = lean_ctor_get(v_a_1940_, 0);
v_proof_1955_ = lean_ctor_get(v_a_1940_, 1);
v_done_1956_ = lean_ctor_get_uint8(v_a_1940_, sizeof(void*)*2);
v_contextDependent_1957_ = lean_ctor_get_uint8(v_a_1940_, sizeof(void*)*2 + 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_a_1940_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1959_ = v_a_1940_;
v_isShared_1960_ = v_isSharedCheck_1983_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_proof_1955_);
lean_inc(v_e_x27_1954_);
lean_dec(v_a_1940_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1983_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; 
lean_inc_ref(v_e_x27_1954_);
v___x_1961_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1901_, v_e_x27_1933_, v_proof_1934_, v_e_x27_1954_, v_proof_1955_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1974_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1974_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
uint8_t v___y_1967_; 
if (v_contextDependent_1935_ == 0)
{
v___y_1967_ = v_contextDependent_1957_;
goto v___jp_1966_;
}
else
{
v___y_1967_ = v_contextDependent_1935_;
goto v___jp_1966_;
}
v___jp_1966_:
{
lean_object* v___x_1969_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v_a_1962_);
v___x_1969_ = v___x_1959_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_e_x27_1954_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_a_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1973_, sizeof(void*)*2, v_done_1956_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*2 + 1, v___y_1967_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1969_);
v___x_1971_ = v___x_1964_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_del_object(v___x_1959_);
lean_dec_ref(v_e_x27_1954_);
v_a_1975_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1961_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1961_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1937_);
lean_dec_ref(v_proof_1934_);
lean_dec_ref(v_e_x27_1933_);
lean_dec_ref(v___y_1901_);
return v___x_1939_;
}
}
}
else
{
lean_dec_ref_known(v_a_1914_, 2);
lean_dec_ref(v___y_1901_);
lean_dec_ref(v___f_1899_);
return v___x_1913_;
}
}
}
else
{
lean_dec_ref(v___y_1901_);
lean_dec_ref(v___f_1899_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8___boxed(lean_object* v___f_1986_, lean_object* v_x_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__8(v___f_1986_, v_x_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9(lean_object* v___f_2000_, lean_object* v_x_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_box(0);
lean_inc_ref(v___y_2002_);
v___x_2014_ = l_Lean_Meta_Grind_NormSym_simpEq(v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
if (lean_obj_tag(v_a_2015_) == 0)
{
uint8_t v_done_2016_; 
v_done_2016_ = lean_ctor_get_uint8(v_a_2015_, 0);
if (v_done_2016_ == 0)
{
uint8_t v_contextDependent_2017_; lean_object* v___x_2018_; 
lean_dec_ref_known(v___x_2014_, 1);
v_contextDependent_2017_ = lean_ctor_get_uint8(v_a_2015_, 1);
lean_dec_ref_known(v_a_2015_, 0);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
lean_inc(v___y_2007_);
lean_inc_ref(v___y_2006_);
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
v___x_2018_ = lean_apply_12(v___f_2000_, v___x_2013_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, lean_box(0));
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; uint8_t v___y_2021_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
if (v_contextDependent_2017_ == 0)
{
lean_dec(v_a_2019_);
return v___x_2018_;
}
else
{
if (lean_obj_tag(v_a_2019_) == 0)
{
uint8_t v_contextDependent_2031_; 
v_contextDependent_2031_ = lean_ctor_get_uint8(v_a_2019_, 1);
v___y_2021_ = v_contextDependent_2031_;
goto v___jp_2020_;
}
else
{
uint8_t v_contextDependent_2032_; 
v_contextDependent_2032_ = lean_ctor_get_uint8(v_a_2019_, sizeof(void*)*2 + 1);
v___y_2021_ = v_contextDependent_2032_;
goto v___jp_2020_;
}
}
v___jp_2020_:
{
if (v___y_2021_ == 0)
{
lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2029_; 
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v___x_2018_, 0);
lean_dec(v_unused_2030_);
v___x_2023_ = v___x_2018_;
v_isShared_2024_ = v_isSharedCheck_2029_;
goto v_resetjp_2022_;
}
else
{
lean_dec(v___x_2018_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2029_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2019_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2025_);
v___x_2027_ = v___x_2023_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
lean_dec(v_a_2019_);
return v___x_2018_;
}
}
}
else
{
return v___x_2018_;
}
}
else
{
lean_dec_ref_known(v_a_2015_, 0);
lean_dec_ref(v___y_2002_);
lean_dec_ref(v___f_2000_);
return v___x_2014_;
}
}
else
{
uint8_t v_done_2033_; 
v_done_2033_ = lean_ctor_get_uint8(v_a_2015_, sizeof(void*)*2);
if (v_done_2033_ == 0)
{
lean_object* v_e_x27_2034_; lean_object* v_proof_2035_; uint8_t v_contextDependent_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref_known(v___x_2014_, 1);
v_e_x27_2034_ = lean_ctor_get(v_a_2015_, 0);
v_proof_2035_ = lean_ctor_get(v_a_2015_, 1);
v_contextDependent_2036_ = lean_ctor_get_uint8(v_a_2015_, sizeof(void*)*2 + 1);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2038_ = v_a_2015_;
v_isShared_2039_ = v_isSharedCheck_2086_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_proof_2035_);
lean_inc(v_e_x27_2034_);
lean_dec(v_a_2015_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2086_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; 
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
lean_inc(v___y_2007_);
lean_inc_ref(v___y_2006_);
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc_ref(v_e_x27_2034_);
v___x_2040_ = lean_apply_12(v___f_2000_, v___x_2013_, v_e_x27_2034_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, lean_box(0));
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2085_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2085_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2085_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
if (lean_obj_tag(v_a_2041_) == 0)
{
uint8_t v_done_2045_; uint8_t v_contextDependent_2046_; uint8_t v___y_2048_; 
lean_dec_ref(v___y_2002_);
v_done_2045_ = lean_ctor_get_uint8(v_a_2041_, 0);
v_contextDependent_2046_ = lean_ctor_get_uint8(v_a_2041_, 1);
lean_dec_ref_known(v_a_2041_, 0);
if (v_contextDependent_2036_ == 0)
{
v___y_2048_ = v_contextDependent_2046_;
goto v___jp_2047_;
}
else
{
v___y_2048_ = v_contextDependent_2036_;
goto v___jp_2047_;
}
v___jp_2047_:
{
lean_object* v___x_2050_; 
if (v_isShared_2039_ == 0)
{
v___x_2050_ = v___x_2038_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_e_x27_2034_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_proof_2035_);
v___x_2050_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2052_; 
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*2, v_done_2045_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*2 + 1, v___y_2048_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2050_);
v___x_2052_ = v___x_2043_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_e_x27_2055_; lean_object* v_proof_2056_; uint8_t v_done_2057_; uint8_t v_contextDependent_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2084_; 
lean_del_object(v___x_2043_);
lean_del_object(v___x_2038_);
v_e_x27_2055_ = lean_ctor_get(v_a_2041_, 0);
v_proof_2056_ = lean_ctor_get(v_a_2041_, 1);
v_done_2057_ = lean_ctor_get_uint8(v_a_2041_, sizeof(void*)*2);
v_contextDependent_2058_ = lean_ctor_get_uint8(v_a_2041_, sizeof(void*)*2 + 1);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_a_2041_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2060_ = v_a_2041_;
v_isShared_2061_ = v_isSharedCheck_2084_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_proof_2056_);
lean_inc(v_e_x27_2055_);
lean_dec(v_a_2041_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2084_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; 
lean_inc_ref(v_e_x27_2055_);
v___x_2062_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2002_, v_e_x27_2034_, v_proof_2035_, v_e_x27_2055_, v_proof_2056_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2075_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2075_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2075_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
uint8_t v___y_2068_; 
if (v_contextDependent_2036_ == 0)
{
v___y_2068_ = v_contextDependent_2058_;
goto v___jp_2067_;
}
else
{
v___y_2068_ = v_contextDependent_2036_;
goto v___jp_2067_;
}
v___jp_2067_:
{
lean_object* v___x_2070_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v_a_2063_);
v___x_2070_ = v___x_2060_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_e_x27_2055_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_a_2063_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*2, v_done_2057_);
v___x_2070_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
lean_ctor_set_uint8(v___x_2070_, sizeof(void*)*2 + 1, v___y_2068_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2070_);
v___x_2072_ = v___x_2065_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_del_object(v___x_2060_);
lean_dec_ref(v_e_x27_2055_);
v_a_2076_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2062_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2062_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
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
}
}
}
else
{
lean_del_object(v___x_2038_);
lean_dec_ref(v_proof_2035_);
lean_dec_ref(v_e_x27_2034_);
lean_dec_ref(v___y_2002_);
return v___x_2040_;
}
}
}
else
{
lean_dec_ref_known(v_a_2015_, 2);
lean_dec_ref(v___y_2002_);
lean_dec_ref(v___f_2000_);
return v___x_2014_;
}
}
}
else
{
lean_dec_ref(v___y_2002_);
lean_dec_ref(v___f_2000_);
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9___boxed(lean_object* v___f_2087_, lean_object* v_x_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__9(v___f_2087_, v_x_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10(lean_object* v___f_2101_, lean_object* v_x_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_box(0);
lean_inc_ref(v___y_2103_);
v___x_2115_ = l_Lean_Meta_Sym_Simp_simpNatRel___redArg(v___y_2103_, v___y_2107_, v___y_2110_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
if (lean_obj_tag(v_a_2116_) == 0)
{
uint8_t v_done_2117_; 
v_done_2117_ = lean_ctor_get_uint8(v_a_2116_, 0);
if (v_done_2117_ == 0)
{
uint8_t v_contextDependent_2118_; lean_object* v___x_2119_; 
lean_dec_ref_known(v___x_2115_, 1);
v_contextDependent_2118_ = lean_ctor_get_uint8(v_a_2116_, 1);
lean_dec_ref_known(v_a_2116_, 0);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
lean_inc(v___y_2106_);
lean_inc_ref(v___y_2105_);
lean_inc(v___y_2104_);
v___x_2119_ = lean_apply_12(v___f_2101_, v___x_2114_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, lean_box(0));
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; uint8_t v___y_2122_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
if (v_contextDependent_2118_ == 0)
{
lean_dec(v_a_2120_);
return v___x_2119_;
}
else
{
if (lean_obj_tag(v_a_2120_) == 0)
{
uint8_t v_contextDependent_2132_; 
v_contextDependent_2132_ = lean_ctor_get_uint8(v_a_2120_, 1);
v___y_2122_ = v_contextDependent_2132_;
goto v___jp_2121_;
}
else
{
uint8_t v_contextDependent_2133_; 
v_contextDependent_2133_ = lean_ctor_get_uint8(v_a_2120_, sizeof(void*)*2 + 1);
v___y_2122_ = v_contextDependent_2133_;
goto v___jp_2121_;
}
}
v___jp_2121_:
{
if (v___y_2122_ == 0)
{
lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v___x_2119_, 0);
lean_dec(v_unused_2131_);
v___x_2124_ = v___x_2119_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v___x_2119_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2120_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
else
{
lean_dec(v_a_2120_);
return v___x_2119_;
}
}
}
else
{
return v___x_2119_;
}
}
else
{
lean_dec_ref_known(v_a_2116_, 0);
lean_dec_ref(v___y_2103_);
lean_dec_ref(v___f_2101_);
return v___x_2115_;
}
}
else
{
uint8_t v_done_2134_; 
v_done_2134_ = lean_ctor_get_uint8(v_a_2116_, sizeof(void*)*2);
if (v_done_2134_ == 0)
{
lean_object* v_e_x27_2135_; lean_object* v_proof_2136_; uint8_t v_contextDependent_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref_known(v___x_2115_, 1);
v_e_x27_2135_ = lean_ctor_get(v_a_2116_, 0);
v_proof_2136_ = lean_ctor_get(v_a_2116_, 1);
v_contextDependent_2137_ = lean_ctor_get_uint8(v_a_2116_, sizeof(void*)*2 + 1);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_a_2116_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2139_ = v_a_2116_;
v_isShared_2140_ = v_isSharedCheck_2187_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_proof_2136_);
lean_inc(v_e_x27_2135_);
lean_dec(v_a_2116_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2187_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; 
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
lean_inc(v___y_2110_);
lean_inc_ref(v___y_2109_);
lean_inc(v___y_2108_);
lean_inc_ref(v___y_2107_);
lean_inc(v___y_2106_);
lean_inc_ref(v___y_2105_);
lean_inc(v___y_2104_);
lean_inc_ref(v_e_x27_2135_);
v___x_2141_ = lean_apply_12(v___f_2101_, v___x_2114_, v_e_x27_2135_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, lean_box(0));
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2186_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2186_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2186_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
if (lean_obj_tag(v_a_2142_) == 0)
{
uint8_t v_done_2146_; uint8_t v_contextDependent_2147_; uint8_t v___y_2149_; 
lean_dec_ref(v___y_2103_);
v_done_2146_ = lean_ctor_get_uint8(v_a_2142_, 0);
v_contextDependent_2147_ = lean_ctor_get_uint8(v_a_2142_, 1);
lean_dec_ref_known(v_a_2142_, 0);
if (v_contextDependent_2137_ == 0)
{
v___y_2149_ = v_contextDependent_2147_;
goto v___jp_2148_;
}
else
{
v___y_2149_ = v_contextDependent_2137_;
goto v___jp_2148_;
}
v___jp_2148_:
{
lean_object* v___x_2151_; 
if (v_isShared_2140_ == 0)
{
v___x_2151_ = v___x_2139_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_e_x27_2135_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_proof_2136_);
v___x_2151_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2153_; 
lean_ctor_set_uint8(v___x_2151_, sizeof(void*)*2, v_done_2146_);
lean_ctor_set_uint8(v___x_2151_, sizeof(void*)*2 + 1, v___y_2149_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2151_);
v___x_2153_ = v___x_2144_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_e_x27_2156_; lean_object* v_proof_2157_; uint8_t v_done_2158_; uint8_t v_contextDependent_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2185_; 
lean_del_object(v___x_2144_);
lean_del_object(v___x_2139_);
v_e_x27_2156_ = lean_ctor_get(v_a_2142_, 0);
v_proof_2157_ = lean_ctor_get(v_a_2142_, 1);
v_done_2158_ = lean_ctor_get_uint8(v_a_2142_, sizeof(void*)*2);
v_contextDependent_2159_ = lean_ctor_get_uint8(v_a_2142_, sizeof(void*)*2 + 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_a_2142_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2161_ = v_a_2142_;
v_isShared_2162_ = v_isSharedCheck_2185_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_proof_2157_);
lean_inc(v_e_x27_2156_);
lean_dec(v_a_2142_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2185_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; 
lean_inc_ref(v_e_x27_2156_);
v___x_2163_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2103_, v_e_x27_2135_, v_proof_2136_, v_e_x27_2156_, v_proof_2157_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2176_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2176_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2176_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
uint8_t v___y_2169_; 
if (v_contextDependent_2137_ == 0)
{
v___y_2169_ = v_contextDependent_2159_;
goto v___jp_2168_;
}
else
{
v___y_2169_ = v_contextDependent_2137_;
goto v___jp_2168_;
}
v___jp_2168_:
{
lean_object* v___x_2171_; 
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v_a_2164_);
v___x_2171_ = v___x_2161_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_e_x27_2156_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_a_2164_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*2, v_done_2158_);
v___x_2171_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2173_; 
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*2 + 1, v___y_2169_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2171_);
v___x_2173_ = v___x_2166_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_del_object(v___x_2161_);
lean_dec_ref(v_e_x27_2156_);
v_a_2177_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2163_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2163_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2139_);
lean_dec_ref(v_proof_2136_);
lean_dec_ref(v_e_x27_2135_);
lean_dec_ref(v___y_2103_);
return v___x_2141_;
}
}
}
else
{
lean_dec_ref_known(v_a_2116_, 2);
lean_dec_ref(v___y_2103_);
lean_dec_ref(v___f_2101_);
return v___x_2115_;
}
}
}
else
{
lean_dec_ref(v___y_2103_);
lean_dec_ref(v___f_2101_);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10___boxed(lean_object* v___f_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__10(v___f_2188_, v_x_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11(lean_object* v___f_2205_, lean_object* v_x_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__11___closed__0));
v___x_2219_ = lean_box(0);
lean_inc_ref(v___y_2207_);
v___x_2220_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_2207_, v___x_2218_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
if (lean_obj_tag(v_a_2221_) == 0)
{
uint8_t v_done_2222_; 
v_done_2222_ = lean_ctor_get_uint8(v_a_2221_, 0);
if (v_done_2222_ == 0)
{
uint8_t v_contextDependent_2223_; lean_object* v___x_2224_; 
lean_dec_ref_known(v___x_2220_, 1);
v_contextDependent_2223_ = lean_ctor_get_uint8(v_a_2221_, 1);
lean_dec_ref_known(v_a_2221_, 0);
lean_inc(v___y_2216_);
lean_inc_ref(v___y_2215_);
lean_inc(v___y_2214_);
lean_inc_ref(v___y_2213_);
lean_inc(v___y_2212_);
lean_inc_ref(v___y_2211_);
lean_inc(v___y_2210_);
lean_inc_ref(v___y_2209_);
lean_inc(v___y_2208_);
v___x_2224_ = lean_apply_12(v___f_2205_, v___x_2219_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, lean_box(0));
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; uint8_t v___y_2227_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
if (v_contextDependent_2223_ == 0)
{
lean_dec(v_a_2225_);
return v___x_2224_;
}
else
{
if (lean_obj_tag(v_a_2225_) == 0)
{
uint8_t v_contextDependent_2237_; 
v_contextDependent_2237_ = lean_ctor_get_uint8(v_a_2225_, 1);
v___y_2227_ = v_contextDependent_2237_;
goto v___jp_2226_;
}
else
{
uint8_t v_contextDependent_2238_; 
v_contextDependent_2238_ = lean_ctor_get_uint8(v_a_2225_, sizeof(void*)*2 + 1);
v___y_2227_ = v_contextDependent_2238_;
goto v___jp_2226_;
}
}
v___jp_2226_:
{
if (v___y_2227_ == 0)
{
lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2235_; 
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2235_ == 0)
{
lean_object* v_unused_2236_; 
v_unused_2236_ = lean_ctor_get(v___x_2224_, 0);
lean_dec(v_unused_2236_);
v___x_2229_ = v___x_2224_;
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
else
{
lean_dec(v___x_2224_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2225_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
lean_dec(v_a_2225_);
return v___x_2224_;
}
}
}
else
{
return v___x_2224_;
}
}
else
{
lean_dec_ref_known(v_a_2221_, 0);
lean_dec_ref(v___y_2207_);
lean_dec_ref(v___f_2205_);
return v___x_2220_;
}
}
else
{
uint8_t v_done_2239_; 
v_done_2239_ = lean_ctor_get_uint8(v_a_2221_, sizeof(void*)*2);
if (v_done_2239_ == 0)
{
lean_object* v_e_x27_2240_; lean_object* v_proof_2241_; uint8_t v_contextDependent_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2292_; 
lean_dec_ref_known(v___x_2220_, 1);
v_e_x27_2240_ = lean_ctor_get(v_a_2221_, 0);
v_proof_2241_ = lean_ctor_get(v_a_2221_, 1);
v_contextDependent_2242_ = lean_ctor_get_uint8(v_a_2221_, sizeof(void*)*2 + 1);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_a_2221_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2244_ = v_a_2221_;
v_isShared_2245_ = v_isSharedCheck_2292_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_proof_2241_);
lean_inc(v_e_x27_2240_);
lean_dec(v_a_2221_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2292_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; 
lean_inc(v___y_2216_);
lean_inc_ref(v___y_2215_);
lean_inc(v___y_2214_);
lean_inc_ref(v___y_2213_);
lean_inc(v___y_2212_);
lean_inc_ref(v___y_2211_);
lean_inc(v___y_2210_);
lean_inc_ref(v___y_2209_);
lean_inc(v___y_2208_);
lean_inc_ref(v_e_x27_2240_);
v___x_2246_ = lean_apply_12(v___f_2205_, v___x_2219_, v_e_x27_2240_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, lean_box(0));
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2291_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2291_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2291_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
if (lean_obj_tag(v_a_2247_) == 0)
{
uint8_t v_done_2251_; uint8_t v_contextDependent_2252_; uint8_t v___y_2254_; 
lean_dec_ref(v___y_2207_);
v_done_2251_ = lean_ctor_get_uint8(v_a_2247_, 0);
v_contextDependent_2252_ = lean_ctor_get_uint8(v_a_2247_, 1);
lean_dec_ref_known(v_a_2247_, 0);
if (v_contextDependent_2242_ == 0)
{
v___y_2254_ = v_contextDependent_2252_;
goto v___jp_2253_;
}
else
{
v___y_2254_ = v_contextDependent_2242_;
goto v___jp_2253_;
}
v___jp_2253_:
{
lean_object* v___x_2256_; 
if (v_isShared_2245_ == 0)
{
v___x_2256_ = v___x_2244_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_e_x27_2240_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_proof_2241_);
v___x_2256_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2258_; 
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*2, v_done_2251_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*2 + 1, v___y_2254_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2256_);
v___x_2258_ = v___x_2249_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v_e_x27_2261_; lean_object* v_proof_2262_; uint8_t v_done_2263_; uint8_t v_contextDependent_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2290_; 
lean_del_object(v___x_2249_);
lean_del_object(v___x_2244_);
v_e_x27_2261_ = lean_ctor_get(v_a_2247_, 0);
v_proof_2262_ = lean_ctor_get(v_a_2247_, 1);
v_done_2263_ = lean_ctor_get_uint8(v_a_2247_, sizeof(void*)*2);
v_contextDependent_2264_ = lean_ctor_get_uint8(v_a_2247_, sizeof(void*)*2 + 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_a_2247_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2266_ = v_a_2247_;
v_isShared_2267_ = v_isSharedCheck_2290_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_proof_2262_);
lean_inc(v_e_x27_2261_);
lean_dec(v_a_2247_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2290_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; 
lean_inc_ref(v_e_x27_2261_);
v___x_2268_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2207_, v_e_x27_2240_, v_proof_2241_, v_e_x27_2261_, v_proof_2262_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2281_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2281_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2281_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
uint8_t v___y_2274_; 
if (v_contextDependent_2242_ == 0)
{
v___y_2274_ = v_contextDependent_2264_;
goto v___jp_2273_;
}
else
{
v___y_2274_ = v_contextDependent_2242_;
goto v___jp_2273_;
}
v___jp_2273_:
{
lean_object* v___x_2276_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 1, v_a_2269_);
v___x_2276_ = v___x_2266_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_e_x27_2261_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_a_2269_);
lean_ctor_set_uint8(v_reuseFailAlloc_2280_, sizeof(void*)*2, v_done_2263_);
v___x_2276_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
lean_ctor_set_uint8(v___x_2276_, sizeof(void*)*2 + 1, v___y_2274_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2276_);
v___x_2278_ = v___x_2271_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_del_object(v___x_2266_);
lean_dec_ref(v_e_x27_2261_);
v_a_2282_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2268_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2268_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2244_);
lean_dec_ref(v_proof_2241_);
lean_dec_ref(v_e_x27_2240_);
lean_dec_ref(v___y_2207_);
return v___x_2246_;
}
}
}
else
{
lean_dec_ref_known(v_a_2221_, 2);
lean_dec_ref(v___y_2207_);
lean_dec_ref(v___f_2205_);
return v___x_2220_;
}
}
}
else
{
lean_dec_ref(v___y_2207_);
lean_dec_ref(v___f_2205_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed(lean_object* v___f_2293_, lean_object* v_x_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__11(v___f_2293_, v_x_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12(lean_object* v_thms_2307_, lean_object* v_d_2308_, lean_object* v_x_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_pre_2321_; lean_object* v___x_2322_; 
v_pre_2321_ = lean_ctor_get(v_thms_2307_, 0);
v___x_2322_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_pre_2321_, v_d_2308_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed(lean_object* v_thms_2323_, lean_object* v_d_2324_, lean_object* v_x_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__12(v_thms_2323_, v_d_2324_, v_x_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v_thms_2323_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13(lean_object* v_d_2338_, uint8_t v_distrib_2339_, lean_object* v___f_2340_, lean_object* v_x_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = 1;
v___x_2354_ = lean_box(0);
lean_inc_ref(v___y_2342_);
v___x_2355_ = l_Lean_Meta_Sym_Simp_simpArith(v_d_2338_, v___x_2353_, v_distrib_2339_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
if (lean_obj_tag(v_a_2356_) == 0)
{
uint8_t v_done_2357_; 
v_done_2357_ = lean_ctor_get_uint8(v_a_2356_, 0);
if (v_done_2357_ == 0)
{
uint8_t v_contextDependent_2358_; lean_object* v___x_2359_; 
lean_dec_ref_known(v___x_2355_, 1);
v_contextDependent_2358_ = lean_ctor_get_uint8(v_a_2356_, 1);
lean_dec_ref_known(v_a_2356_, 0);
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___y_2343_);
v___x_2359_ = lean_apply_12(v___f_2340_, v___x_2354_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, lean_box(0));
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; uint8_t v___y_2362_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
if (v_contextDependent_2358_ == 0)
{
lean_dec(v_a_2360_);
return v___x_2359_;
}
else
{
if (lean_obj_tag(v_a_2360_) == 0)
{
uint8_t v_contextDependent_2372_; 
v_contextDependent_2372_ = lean_ctor_get_uint8(v_a_2360_, 1);
v___y_2362_ = v_contextDependent_2372_;
goto v___jp_2361_;
}
else
{
uint8_t v_contextDependent_2373_; 
v_contextDependent_2373_ = lean_ctor_get_uint8(v_a_2360_, sizeof(void*)*2 + 1);
v___y_2362_ = v_contextDependent_2373_;
goto v___jp_2361_;
}
}
v___jp_2361_:
{
if (v___y_2362_ == 0)
{
lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2370_; 
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v___x_2359_, 0);
lean_dec(v_unused_2371_);
v___x_2364_ = v___x_2359_;
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
else
{
lean_dec(v___x_2359_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2366_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2360_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2366_);
v___x_2368_ = v___x_2364_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
lean_dec(v_a_2360_);
return v___x_2359_;
}
}
}
else
{
return v___x_2359_;
}
}
else
{
lean_dec_ref_known(v_a_2356_, 0);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___f_2340_);
return v___x_2355_;
}
}
else
{
uint8_t v_done_2374_; 
v_done_2374_ = lean_ctor_get_uint8(v_a_2356_, sizeof(void*)*2);
if (v_done_2374_ == 0)
{
lean_object* v_e_x27_2375_; lean_object* v_proof_2376_; uint8_t v_contextDependent_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2427_; 
lean_dec_ref_known(v___x_2355_, 1);
v_e_x27_2375_ = lean_ctor_get(v_a_2356_, 0);
v_proof_2376_ = lean_ctor_get(v_a_2356_, 1);
v_contextDependent_2377_ = lean_ctor_get_uint8(v_a_2356_, sizeof(void*)*2 + 1);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_a_2356_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2379_ = v_a_2356_;
v_isShared_2380_ = v_isSharedCheck_2427_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_proof_2376_);
lean_inc(v_e_x27_2375_);
lean_dec(v_a_2356_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2427_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; 
lean_inc(v___y_2351_);
lean_inc_ref(v___y_2350_);
lean_inc(v___y_2349_);
lean_inc_ref(v___y_2348_);
lean_inc(v___y_2347_);
lean_inc_ref(v___y_2346_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___y_2343_);
lean_inc_ref(v_e_x27_2375_);
v___x_2381_ = lean_apply_12(v___f_2340_, v___x_2354_, v_e_x27_2375_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, lean_box(0));
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2426_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2426_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2426_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
if (lean_obj_tag(v_a_2382_) == 0)
{
uint8_t v_done_2386_; uint8_t v_contextDependent_2387_; uint8_t v___y_2389_; 
lean_dec_ref(v___y_2342_);
v_done_2386_ = lean_ctor_get_uint8(v_a_2382_, 0);
v_contextDependent_2387_ = lean_ctor_get_uint8(v_a_2382_, 1);
lean_dec_ref_known(v_a_2382_, 0);
if (v_contextDependent_2377_ == 0)
{
v___y_2389_ = v_contextDependent_2387_;
goto v___jp_2388_;
}
else
{
v___y_2389_ = v_contextDependent_2377_;
goto v___jp_2388_;
}
v___jp_2388_:
{
lean_object* v___x_2391_; 
if (v_isShared_2380_ == 0)
{
v___x_2391_ = v___x_2379_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_e_x27_2375_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_proof_2376_);
v___x_2391_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2393_; 
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*2, v_done_2386_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*2 + 1, v___y_2389_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2391_);
v___x_2393_ = v___x_2384_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_object* v_e_x27_2396_; lean_object* v_proof_2397_; uint8_t v_done_2398_; uint8_t v_contextDependent_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2425_; 
lean_del_object(v___x_2384_);
lean_del_object(v___x_2379_);
v_e_x27_2396_ = lean_ctor_get(v_a_2382_, 0);
v_proof_2397_ = lean_ctor_get(v_a_2382_, 1);
v_done_2398_ = lean_ctor_get_uint8(v_a_2382_, sizeof(void*)*2);
v_contextDependent_2399_ = lean_ctor_get_uint8(v_a_2382_, sizeof(void*)*2 + 1);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_a_2382_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2401_ = v_a_2382_;
v_isShared_2402_ = v_isSharedCheck_2425_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_proof_2397_);
lean_inc(v_e_x27_2396_);
lean_dec(v_a_2382_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2425_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; 
lean_inc_ref(v_e_x27_2396_);
v___x_2403_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2342_, v_e_x27_2375_, v_proof_2376_, v_e_x27_2396_, v_proof_2397_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2416_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2416_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2416_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
uint8_t v___y_2409_; 
if (v_contextDependent_2377_ == 0)
{
v___y_2409_ = v_contextDependent_2399_;
goto v___jp_2408_;
}
else
{
v___y_2409_ = v_contextDependent_2377_;
goto v___jp_2408_;
}
v___jp_2408_:
{
lean_object* v___x_2411_; 
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 1, v_a_2404_);
v___x_2411_ = v___x_2401_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_e_x27_2396_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_a_2404_);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, sizeof(void*)*2, v_done_2398_);
v___x_2411_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2413_; 
lean_ctor_set_uint8(v___x_2411_, sizeof(void*)*2 + 1, v___y_2409_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2411_);
v___x_2413_ = v___x_2406_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_del_object(v___x_2401_);
lean_dec_ref(v_e_x27_2396_);
v_a_2417_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2403_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2403_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2379_);
lean_dec_ref(v_proof_2376_);
lean_dec_ref(v_e_x27_2375_);
lean_dec_ref(v___y_2342_);
return v___x_2381_;
}
}
}
else
{
lean_dec_ref_known(v_a_2356_, 2);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___f_2340_);
return v___x_2355_;
}
}
}
else
{
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___f_2340_);
return v___x_2355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed(lean_object* v_d_2428_, lean_object* v_distrib_2429_, lean_object* v___f_2430_, lean_object* v_x_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
uint8_t v_distrib_boxed_2443_; lean_object* v_res_2444_; 
v_distrib_boxed_2443_ = lean_unbox(v_distrib_2429_);
v_res_2444_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__13(v_d_2428_, v_distrib_boxed_2443_, v___f_2430_, v_x_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14(lean_object* v___f_2445_, lean_object* v_x_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_box(0);
lean_inc_ref(v___y_2447_);
v___x_2459_ = l_Lean_Meta_Grind_NormSym_pushNot(v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
if (lean_obj_tag(v_a_2460_) == 0)
{
uint8_t v_done_2461_; 
v_done_2461_ = lean_ctor_get_uint8(v_a_2460_, 0);
if (v_done_2461_ == 0)
{
uint8_t v_contextDependent_2462_; lean_object* v___x_2463_; 
lean_dec_ref_known(v___x_2459_, 1);
v_contextDependent_2462_ = lean_ctor_get_uint8(v_a_2460_, 1);
lean_dec_ref_known(v_a_2460_, 0);
lean_inc(v___y_2456_);
lean_inc_ref(v___y_2455_);
lean_inc(v___y_2454_);
lean_inc_ref(v___y_2453_);
lean_inc(v___y_2452_);
lean_inc_ref(v___y_2451_);
lean_inc(v___y_2450_);
lean_inc_ref(v___y_2449_);
lean_inc(v___y_2448_);
v___x_2463_ = lean_apply_12(v___f_2445_, v___x_2458_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, lean_box(0));
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; uint8_t v___y_2466_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
if (v_contextDependent_2462_ == 0)
{
lean_dec(v_a_2464_);
return v___x_2463_;
}
else
{
if (lean_obj_tag(v_a_2464_) == 0)
{
uint8_t v_contextDependent_2476_; 
v_contextDependent_2476_ = lean_ctor_get_uint8(v_a_2464_, 1);
v___y_2466_ = v_contextDependent_2476_;
goto v___jp_2465_;
}
else
{
uint8_t v_contextDependent_2477_; 
v_contextDependent_2477_ = lean_ctor_get_uint8(v_a_2464_, sizeof(void*)*2 + 1);
v___y_2466_ = v_contextDependent_2477_;
goto v___jp_2465_;
}
}
v___jp_2465_:
{
if (v___y_2466_ == 0)
{
lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2474_; 
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v___x_2463_, 0);
lean_dec(v_unused_2475_);
v___x_2468_ = v___x_2463_;
v_isShared_2469_ = v_isSharedCheck_2474_;
goto v_resetjp_2467_;
}
else
{
lean_dec(v___x_2463_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2474_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2470_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2464_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2470_);
v___x_2472_ = v___x_2468_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
else
{
lean_dec(v_a_2464_);
return v___x_2463_;
}
}
}
else
{
return v___x_2463_;
}
}
else
{
lean_dec_ref_known(v_a_2460_, 0);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___f_2445_);
return v___x_2459_;
}
}
else
{
uint8_t v_done_2478_; 
v_done_2478_ = lean_ctor_get_uint8(v_a_2460_, sizeof(void*)*2);
if (v_done_2478_ == 0)
{
lean_object* v_e_x27_2479_; lean_object* v_proof_2480_; uint8_t v_contextDependent_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref_known(v___x_2459_, 1);
v_e_x27_2479_ = lean_ctor_get(v_a_2460_, 0);
v_proof_2480_ = lean_ctor_get(v_a_2460_, 1);
v_contextDependent_2481_ = lean_ctor_get_uint8(v_a_2460_, sizeof(void*)*2 + 1);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_a_2460_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2483_ = v_a_2460_;
v_isShared_2484_ = v_isSharedCheck_2531_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_proof_2480_);
lean_inc(v_e_x27_2479_);
lean_dec(v_a_2460_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2531_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2485_; 
lean_inc(v___y_2456_);
lean_inc_ref(v___y_2455_);
lean_inc(v___y_2454_);
lean_inc_ref(v___y_2453_);
lean_inc(v___y_2452_);
lean_inc_ref(v___y_2451_);
lean_inc(v___y_2450_);
lean_inc_ref(v___y_2449_);
lean_inc(v___y_2448_);
lean_inc_ref(v_e_x27_2479_);
v___x_2485_ = lean_apply_12(v___f_2445_, v___x_2458_, v_e_x27_2479_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, lean_box(0));
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2530_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2530_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2530_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
if (lean_obj_tag(v_a_2486_) == 0)
{
uint8_t v_done_2490_; uint8_t v_contextDependent_2491_; uint8_t v___y_2493_; 
lean_dec_ref(v___y_2447_);
v_done_2490_ = lean_ctor_get_uint8(v_a_2486_, 0);
v_contextDependent_2491_ = lean_ctor_get_uint8(v_a_2486_, 1);
lean_dec_ref_known(v_a_2486_, 0);
if (v_contextDependent_2481_ == 0)
{
v___y_2493_ = v_contextDependent_2491_;
goto v___jp_2492_;
}
else
{
v___y_2493_ = v_contextDependent_2481_;
goto v___jp_2492_;
}
v___jp_2492_:
{
lean_object* v___x_2495_; 
if (v_isShared_2484_ == 0)
{
v___x_2495_ = v___x_2483_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_e_x27_2479_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_proof_2480_);
v___x_2495_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2497_; 
lean_ctor_set_uint8(v___x_2495_, sizeof(void*)*2, v_done_2490_);
lean_ctor_set_uint8(v___x_2495_, sizeof(void*)*2 + 1, v___y_2493_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v___x_2495_);
v___x_2497_ = v___x_2488_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
else
{
lean_object* v_e_x27_2500_; lean_object* v_proof_2501_; uint8_t v_done_2502_; uint8_t v_contextDependent_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2529_; 
lean_del_object(v___x_2488_);
lean_del_object(v___x_2483_);
v_e_x27_2500_ = lean_ctor_get(v_a_2486_, 0);
v_proof_2501_ = lean_ctor_get(v_a_2486_, 1);
v_done_2502_ = lean_ctor_get_uint8(v_a_2486_, sizeof(void*)*2);
v_contextDependent_2503_ = lean_ctor_get_uint8(v_a_2486_, sizeof(void*)*2 + 1);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_a_2486_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2505_ = v_a_2486_;
v_isShared_2506_ = v_isSharedCheck_2529_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_proof_2501_);
lean_inc(v_e_x27_2500_);
lean_dec(v_a_2486_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2529_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; 
lean_inc_ref(v_e_x27_2500_);
v___x_2507_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2447_, v_e_x27_2479_, v_proof_2480_, v_e_x27_2500_, v_proof_2501_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2520_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2520_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2520_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
uint8_t v___y_2513_; 
if (v_contextDependent_2481_ == 0)
{
v___y_2513_ = v_contextDependent_2503_;
goto v___jp_2512_;
}
else
{
v___y_2513_ = v_contextDependent_2481_;
goto v___jp_2512_;
}
v___jp_2512_:
{
lean_object* v___x_2515_; 
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 1, v_a_2508_);
v___x_2515_ = v___x_2505_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_e_x27_2500_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_a_2508_);
lean_ctor_set_uint8(v_reuseFailAlloc_2519_, sizeof(void*)*2, v_done_2502_);
v___x_2515_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2517_; 
lean_ctor_set_uint8(v___x_2515_, sizeof(void*)*2 + 1, v___y_2513_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v___x_2515_);
v___x_2517_ = v___x_2510_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_del_object(v___x_2505_);
lean_dec_ref(v_e_x27_2500_);
v_a_2521_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2507_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2507_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2483_);
lean_dec_ref(v_proof_2480_);
lean_dec_ref(v_e_x27_2479_);
lean_dec_ref(v___y_2447_);
return v___x_2485_;
}
}
}
else
{
lean_dec_ref_known(v_a_2460_, 2);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___f_2445_);
return v___x_2459_;
}
}
}
else
{
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___f_2445_);
return v___x_2459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed(lean_object* v___f_2532_, lean_object* v_x_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__14(v___f_2532_, v_x_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15(lean_object* v_pre_2546_, lean_object* v___f_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_box(0);
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
lean_inc(v___y_2553_);
lean_inc_ref(v___y_2552_);
lean_inc(v___y_2551_);
lean_inc_ref(v___y_2550_);
lean_inc(v___y_2549_);
lean_inc_ref(v___y_2548_);
v___x_2560_ = lean_apply_11(v_pre_2546_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, lean_box(0));
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
if (lean_obj_tag(v_a_2561_) == 0)
{
uint8_t v_done_2562_; 
v_done_2562_ = lean_ctor_get_uint8(v_a_2561_, 0);
if (v_done_2562_ == 0)
{
uint8_t v_contextDependent_2563_; lean_object* v___x_2564_; 
lean_dec_ref_known(v___x_2560_, 1);
v_contextDependent_2563_ = lean_ctor_get_uint8(v_a_2561_, 1);
lean_dec_ref_known(v_a_2561_, 0);
v___x_2564_ = lean_apply_12(v___f_2547_, v___x_2559_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, lean_box(0));
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; uint8_t v___y_2567_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2565_);
if (v_contextDependent_2563_ == 0)
{
lean_dec(v_a_2565_);
return v___x_2564_;
}
else
{
if (lean_obj_tag(v_a_2565_) == 0)
{
uint8_t v_contextDependent_2577_; 
v_contextDependent_2577_ = lean_ctor_get_uint8(v_a_2565_, 1);
v___y_2567_ = v_contextDependent_2577_;
goto v___jp_2566_;
}
else
{
uint8_t v_contextDependent_2578_; 
v_contextDependent_2578_ = lean_ctor_get_uint8(v_a_2565_, sizeof(void*)*2 + 1);
v___y_2567_ = v_contextDependent_2578_;
goto v___jp_2566_;
}
}
v___jp_2566_:
{
if (v___y_2567_ == 0)
{
lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2575_; 
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v___x_2564_, 0);
lean_dec(v_unused_2576_);
v___x_2569_ = v___x_2564_;
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
else
{
lean_dec(v___x_2564_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2575_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2571_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2565_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2571_);
v___x_2573_ = v___x_2569_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
else
{
lean_dec(v_a_2565_);
return v___x_2564_;
}
}
}
else
{
return v___x_2564_;
}
}
else
{
lean_dec_ref_known(v_a_2561_, 0);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec_ref(v___f_2547_);
return v___x_2560_;
}
}
else
{
uint8_t v_done_2579_; 
v_done_2579_ = lean_ctor_get_uint8(v_a_2561_, sizeof(void*)*2);
if (v_done_2579_ == 0)
{
lean_object* v_e_x27_2580_; lean_object* v_proof_2581_; uint8_t v_contextDependent_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref_known(v___x_2560_, 1);
v_e_x27_2580_ = lean_ctor_get(v_a_2561_, 0);
v_proof_2581_ = lean_ctor_get(v_a_2561_, 1);
v_contextDependent_2582_ = lean_ctor_get_uint8(v_a_2561_, sizeof(void*)*2 + 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_a_2561_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2584_ = v_a_2561_;
v_isShared_2585_ = v_isSharedCheck_2632_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_proof_2581_);
lean_inc(v_e_x27_2580_);
lean_dec(v_a_2561_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2632_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; 
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
lean_inc(v___y_2553_);
lean_inc_ref(v___y_2552_);
lean_inc_ref(v_e_x27_2580_);
v___x_2586_ = lean_apply_12(v___f_2547_, v___x_2559_, v_e_x27_2580_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, lean_box(0));
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2631_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2631_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2631_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
if (lean_obj_tag(v_a_2587_) == 0)
{
uint8_t v_done_2591_; uint8_t v_contextDependent_2592_; uint8_t v___y_2594_; 
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v___y_2548_);
v_done_2591_ = lean_ctor_get_uint8(v_a_2587_, 0);
v_contextDependent_2592_ = lean_ctor_get_uint8(v_a_2587_, 1);
lean_dec_ref_known(v_a_2587_, 0);
if (v_contextDependent_2582_ == 0)
{
v___y_2594_ = v_contextDependent_2592_;
goto v___jp_2593_;
}
else
{
v___y_2594_ = v_contextDependent_2582_;
goto v___jp_2593_;
}
v___jp_2593_:
{
lean_object* v___x_2596_; 
if (v_isShared_2585_ == 0)
{
v___x_2596_ = v___x_2584_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_e_x27_2580_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_proof_2581_);
v___x_2596_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2598_; 
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*2, v_done_2591_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*2 + 1, v___y_2594_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v___x_2596_);
v___x_2598_ = v___x_2589_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v_e_x27_2601_; lean_object* v_proof_2602_; uint8_t v_done_2603_; uint8_t v_contextDependent_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2630_; 
lean_del_object(v___x_2589_);
lean_del_object(v___x_2584_);
v_e_x27_2601_ = lean_ctor_get(v_a_2587_, 0);
v_proof_2602_ = lean_ctor_get(v_a_2587_, 1);
v_done_2603_ = lean_ctor_get_uint8(v_a_2587_, sizeof(void*)*2);
v_contextDependent_2604_ = lean_ctor_get_uint8(v_a_2587_, sizeof(void*)*2 + 1);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_a_2587_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2606_ = v_a_2587_;
v_isShared_2607_ = v_isSharedCheck_2630_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_proof_2602_);
lean_inc(v_e_x27_2601_);
lean_dec(v_a_2587_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2630_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; 
lean_inc_ref(v_e_x27_2601_);
v___x_2608_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2548_, v_e_x27_2580_, v_proof_2581_, v_e_x27_2601_, v_proof_2602_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2621_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2621_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2621_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
uint8_t v___y_2614_; 
if (v_contextDependent_2582_ == 0)
{
v___y_2614_ = v_contextDependent_2604_;
goto v___jp_2613_;
}
else
{
v___y_2614_ = v_contextDependent_2582_;
goto v___jp_2613_;
}
v___jp_2613_:
{
lean_object* v___x_2616_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 1, v_a_2609_);
v___x_2616_ = v___x_2606_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_e_x27_2601_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_a_2609_);
lean_ctor_set_uint8(v_reuseFailAlloc_2620_, sizeof(void*)*2, v_done_2603_);
v___x_2616_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2618_; 
lean_ctor_set_uint8(v___x_2616_, sizeof(void*)*2 + 1, v___y_2614_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2616_);
v___x_2618_ = v___x_2611_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_del_object(v___x_2606_);
lean_dec_ref(v_e_x27_2601_);
v_a_2622_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2608_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2608_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2584_);
lean_dec_ref(v_proof_2581_);
lean_dec_ref(v_e_x27_2580_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v___y_2548_);
return v___x_2586_;
}
}
}
else
{
lean_dec_ref_known(v_a_2561_, 2);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec_ref(v___f_2547_);
return v___x_2560_;
}
}
}
else
{
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec_ref(v___f_2547_);
return v___x_2560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed(lean_object* v_pre_2633_, lean_object* v___f_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__15(v_pre_2633_, v___f_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16(lean_object* v_post_2647_, lean_object* v_d_2648_, lean_object* v___f_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = lean_box(0);
lean_inc_ref(v___y_2650_);
v___x_2662_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_post_2647_, v_d_2648_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
if (lean_obj_tag(v_a_2663_) == 0)
{
uint8_t v_done_2664_; 
v_done_2664_ = lean_ctor_get_uint8(v_a_2663_, 0);
if (v_done_2664_ == 0)
{
uint8_t v_contextDependent_2665_; lean_object* v___x_2666_; 
lean_dec_ref_known(v___x_2662_, 1);
v_contextDependent_2665_ = lean_ctor_get_uint8(v_a_2663_, 1);
lean_dec_ref_known(v_a_2663_, 0);
v___x_2666_ = lean_apply_12(v___f_2649_, v___x_2661_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, lean_box(0));
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; uint8_t v___y_2669_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
if (v_contextDependent_2665_ == 0)
{
lean_dec(v_a_2667_);
return v___x_2666_;
}
else
{
if (lean_obj_tag(v_a_2667_) == 0)
{
uint8_t v_contextDependent_2679_; 
v_contextDependent_2679_ = lean_ctor_get_uint8(v_a_2667_, 1);
v___y_2669_ = v_contextDependent_2679_;
goto v___jp_2668_;
}
else
{
uint8_t v_contextDependent_2680_; 
v_contextDependent_2680_ = lean_ctor_get_uint8(v_a_2667_, sizeof(void*)*2 + 1);
v___y_2669_ = v_contextDependent_2680_;
goto v___jp_2668_;
}
}
v___jp_2668_:
{
if (v___y_2669_ == 0)
{
lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2677_; 
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v___x_2666_, 0);
lean_dec(v_unused_2678_);
v___x_2671_ = v___x_2666_;
v_isShared_2672_ = v_isSharedCheck_2677_;
goto v_resetjp_2670_;
}
else
{
lean_dec(v___x_2666_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2677_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2667_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2673_);
v___x_2675_ = v___x_2671_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_dec(v_a_2667_);
return v___x_2666_;
}
}
}
else
{
return v___x_2666_;
}
}
else
{
lean_dec_ref_known(v_a_2663_, 0);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___f_2649_);
return v___x_2662_;
}
}
else
{
uint8_t v_done_2681_; 
v_done_2681_ = lean_ctor_get_uint8(v_a_2663_, sizeof(void*)*2);
if (v_done_2681_ == 0)
{
lean_object* v_e_x27_2682_; lean_object* v_proof_2683_; uint8_t v_contextDependent_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2734_; 
lean_dec_ref_known(v___x_2662_, 1);
v_e_x27_2682_ = lean_ctor_get(v_a_2663_, 0);
v_proof_2683_ = lean_ctor_get(v_a_2663_, 1);
v_contextDependent_2684_ = lean_ctor_get_uint8(v_a_2663_, sizeof(void*)*2 + 1);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_a_2663_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2686_ = v_a_2663_;
v_isShared_2687_ = v_isSharedCheck_2734_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_proof_2683_);
lean_inc(v_e_x27_2682_);
lean_dec(v_a_2663_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2734_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; 
lean_inc(v___y_2659_);
lean_inc_ref(v___y_2658_);
lean_inc(v___y_2657_);
lean_inc_ref(v___y_2656_);
lean_inc(v___y_2655_);
lean_inc_ref(v___y_2654_);
lean_inc_ref(v_e_x27_2682_);
v___x_2688_ = lean_apply_12(v___f_2649_, v___x_2661_, v_e_x27_2682_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, lean_box(0));
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2733_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2733_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2733_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
if (lean_obj_tag(v_a_2689_) == 0)
{
uint8_t v_done_2693_; uint8_t v_contextDependent_2694_; uint8_t v___y_2696_; 
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec_ref(v___y_2650_);
v_done_2693_ = lean_ctor_get_uint8(v_a_2689_, 0);
v_contextDependent_2694_ = lean_ctor_get_uint8(v_a_2689_, 1);
lean_dec_ref_known(v_a_2689_, 0);
if (v_contextDependent_2684_ == 0)
{
v___y_2696_ = v_contextDependent_2694_;
goto v___jp_2695_;
}
else
{
v___y_2696_ = v_contextDependent_2684_;
goto v___jp_2695_;
}
v___jp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2687_ == 0)
{
v___x_2698_ = v___x_2686_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_e_x27_2682_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_proof_2683_);
v___x_2698_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2700_; 
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*2, v_done_2693_);
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*2 + 1, v___y_2696_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v___x_2698_);
v___x_2700_ = v___x_2691_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_object* v_e_x27_2703_; lean_object* v_proof_2704_; uint8_t v_done_2705_; uint8_t v_contextDependent_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2732_; 
lean_del_object(v___x_2691_);
lean_del_object(v___x_2686_);
v_e_x27_2703_ = lean_ctor_get(v_a_2689_, 0);
v_proof_2704_ = lean_ctor_get(v_a_2689_, 1);
v_done_2705_ = lean_ctor_get_uint8(v_a_2689_, sizeof(void*)*2);
v_contextDependent_2706_ = lean_ctor_get_uint8(v_a_2689_, sizeof(void*)*2 + 1);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_a_2689_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2708_ = v_a_2689_;
v_isShared_2709_ = v_isSharedCheck_2732_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_proof_2704_);
lean_inc(v_e_x27_2703_);
lean_dec(v_a_2689_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2732_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; 
lean_inc_ref(v_e_x27_2703_);
v___x_2710_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2650_, v_e_x27_2682_, v_proof_2683_, v_e_x27_2703_, v_proof_2704_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2723_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2723_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2723_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
uint8_t v___y_2716_; 
if (v_contextDependent_2684_ == 0)
{
v___y_2716_ = v_contextDependent_2706_;
goto v___jp_2715_;
}
else
{
v___y_2716_ = v_contextDependent_2684_;
goto v___jp_2715_;
}
v___jp_2715_:
{
lean_object* v___x_2718_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 1, v_a_2711_);
v___x_2718_ = v___x_2708_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_e_x27_2703_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v_a_2711_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, sizeof(void*)*2, v_done_2705_);
v___x_2718_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2720_; 
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*2 + 1, v___y_2716_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2718_);
v___x_2720_ = v___x_2713_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_del_object(v___x_2708_);
lean_dec_ref(v_e_x27_2703_);
v_a_2724_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2710_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2710_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2686_);
lean_dec_ref(v_proof_2683_);
lean_dec_ref(v_e_x27_2682_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec_ref(v___y_2650_);
return v___x_2688_;
}
}
}
else
{
lean_dec_ref_known(v_a_2663_, 2);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___f_2649_);
return v___x_2662_;
}
}
}
else
{
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___f_2649_);
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed(lean_object* v_post_2735_, lean_object* v_d_2736_, lean_object* v___f_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__16(v_post_2735_, v_d_2736_, v___f_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec_ref(v_post_2735_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17(lean_object* v_pre_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2762_; 
lean_inc(v___y_2760_);
lean_inc_ref(v___y_2759_);
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2757_);
lean_inc(v___y_2756_);
lean_inc_ref(v___y_2755_);
lean_inc_ref(v___y_2751_);
v___x_2762_ = lean_apply_11(v_pre_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, lean_box(0));
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
if (lean_obj_tag(v_a_2763_) == 0)
{
uint8_t v_done_2764_; 
v_done_2764_ = lean_ctor_get_uint8(v_a_2763_, 0);
if (v_done_2764_ == 0)
{
uint8_t v_contextDependent_2765_; lean_object* v___x_2766_; 
lean_dec_ref_known(v___x_2762_, 1);
v_contextDependent_2765_ = lean_ctor_get_uint8(v_a_2763_, 1);
lean_dec_ref_known(v_a_2763_, 0);
v___x_2766_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v___y_2751_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; uint8_t v___y_2769_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
if (v_contextDependent_2765_ == 0)
{
return v___x_2766_;
}
else
{
if (lean_obj_tag(v_a_2767_) == 0)
{
uint8_t v_contextDependent_2779_; 
v_contextDependent_2779_ = lean_ctor_get_uint8(v_a_2767_, 1);
v___y_2769_ = v_contextDependent_2779_;
goto v___jp_2768_;
}
else
{
uint8_t v_contextDependent_2780_; 
v_contextDependent_2780_ = lean_ctor_get_uint8(v_a_2767_, sizeof(void*)*2 + 1);
v___y_2769_ = v_contextDependent_2780_;
goto v___jp_2768_;
}
}
v___jp_2768_:
{
if (v___y_2769_ == 0)
{
lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2777_; 
lean_inc(v_a_2767_);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2777_ == 0)
{
lean_object* v_unused_2778_; 
v_unused_2778_ = lean_ctor_get(v___x_2766_, 0);
lean_dec(v_unused_2778_);
v___x_2771_ = v___x_2766_;
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
else
{
lean_dec(v___x_2766_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2773_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2767_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2773_);
v___x_2775_ = v___x_2771_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
else
{
return v___x_2766_;
}
}
}
else
{
return v___x_2766_;
}
}
else
{
lean_dec_ref_known(v_a_2763_, 0);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec_ref(v___y_2751_);
return v___x_2762_;
}
}
else
{
uint8_t v_done_2781_; 
v_done_2781_ = lean_ctor_get_uint8(v_a_2763_, sizeof(void*)*2);
if (v_done_2781_ == 0)
{
lean_object* v_e_x27_2782_; lean_object* v_proof_2783_; uint8_t v_contextDependent_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2834_; 
lean_dec_ref_known(v___x_2762_, 1);
v_e_x27_2782_ = lean_ctor_get(v_a_2763_, 0);
v_proof_2783_ = lean_ctor_get(v_a_2763_, 1);
v_contextDependent_2784_ = lean_ctor_get_uint8(v_a_2763_, sizeof(void*)*2 + 1);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_a_2763_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2786_ = v_a_2763_;
v_isShared_2787_ = v_isSharedCheck_2834_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_proof_2783_);
lean_inc(v_e_x27_2782_);
lean_dec(v_a_2763_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2834_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2788_; 
lean_inc_ref(v_e_x27_2782_);
v___x_2788_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v_e_x27_2782_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2833_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2833_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2833_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
if (lean_obj_tag(v_a_2789_) == 0)
{
uint8_t v_done_2793_; uint8_t v_contextDependent_2794_; uint8_t v___y_2796_; 
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec_ref(v___y_2751_);
v_done_2793_ = lean_ctor_get_uint8(v_a_2789_, 0);
v_contextDependent_2794_ = lean_ctor_get_uint8(v_a_2789_, 1);
lean_dec_ref_known(v_a_2789_, 0);
if (v_contextDependent_2784_ == 0)
{
v___y_2796_ = v_contextDependent_2794_;
goto v___jp_2795_;
}
else
{
v___y_2796_ = v_contextDependent_2784_;
goto v___jp_2795_;
}
v___jp_2795_:
{
lean_object* v___x_2798_; 
if (v_isShared_2787_ == 0)
{
v___x_2798_ = v___x_2786_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_e_x27_2782_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_proof_2783_);
v___x_2798_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2800_; 
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*2, v_done_2793_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*2 + 1, v___y_2796_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2798_);
v___x_2800_ = v___x_2791_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
else
{
lean_object* v_e_x27_2803_; lean_object* v_proof_2804_; uint8_t v_done_2805_; uint8_t v_contextDependent_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2832_; 
lean_del_object(v___x_2791_);
lean_del_object(v___x_2786_);
v_e_x27_2803_ = lean_ctor_get(v_a_2789_, 0);
v_proof_2804_ = lean_ctor_get(v_a_2789_, 1);
v_done_2805_ = lean_ctor_get_uint8(v_a_2789_, sizeof(void*)*2);
v_contextDependent_2806_ = lean_ctor_get_uint8(v_a_2789_, sizeof(void*)*2 + 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_a_2789_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2808_ = v_a_2789_;
v_isShared_2809_ = v_isSharedCheck_2832_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_proof_2804_);
lean_inc(v_e_x27_2803_);
lean_dec(v_a_2789_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2832_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2810_; 
lean_inc_ref(v_e_x27_2803_);
v___x_2810_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2751_, v_e_x27_2782_, v_proof_2783_, v_e_x27_2803_, v_proof_2804_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2823_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2823_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2823_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
uint8_t v___y_2816_; 
if (v_contextDependent_2784_ == 0)
{
v___y_2816_ = v_contextDependent_2806_;
goto v___jp_2815_;
}
else
{
v___y_2816_ = v_contextDependent_2784_;
goto v___jp_2815_;
}
v___jp_2815_:
{
lean_object* v___x_2818_; 
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 1, v_a_2811_);
v___x_2818_ = v___x_2808_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_e_x27_2803_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_a_2811_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, sizeof(void*)*2, v_done_2805_);
v___x_2818_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
lean_ctor_set_uint8(v___x_2818_, sizeof(void*)*2 + 1, v___y_2816_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2818_);
v___x_2820_ = v___x_2813_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_del_object(v___x_2808_);
lean_dec_ref(v_e_x27_2803_);
v_a_2824_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2810_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2810_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2786_);
lean_dec_ref(v_proof_2783_);
lean_dec_ref(v_e_x27_2782_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec_ref(v___y_2751_);
return v___x_2788_;
}
}
}
else
{
lean_dec_ref_known(v_a_2763_, 2);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec_ref(v___y_2751_);
return v___x_2762_;
}
}
}
else
{
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec_ref(v___y_2751_);
return v___x_2762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed(lean_object* v_pre_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__17(v_pre_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18(lean_object* v___f_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_box(0);
lean_inc_ref(v___y_2849_);
v___x_2861_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_2849_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
if (lean_obj_tag(v_a_2862_) == 0)
{
uint8_t v_done_2863_; 
v_done_2863_ = lean_ctor_get_uint8(v_a_2862_, 0);
if (v_done_2863_ == 0)
{
uint8_t v_contextDependent_2864_; lean_object* v___x_2865_; 
lean_dec_ref_known(v___x_2861_, 1);
v_contextDependent_2864_ = lean_ctor_get_uint8(v_a_2862_, 1);
lean_dec_ref_known(v_a_2862_, 0);
v___x_2865_ = lean_apply_12(v___f_2848_, v___x_2860_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, lean_box(0));
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; uint8_t v___y_2868_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
if (v_contextDependent_2864_ == 0)
{
lean_dec(v_a_2866_);
return v___x_2865_;
}
else
{
if (lean_obj_tag(v_a_2866_) == 0)
{
uint8_t v_contextDependent_2878_; 
v_contextDependent_2878_ = lean_ctor_get_uint8(v_a_2866_, 1);
v___y_2868_ = v_contextDependent_2878_;
goto v___jp_2867_;
}
else
{
uint8_t v_contextDependent_2879_; 
v_contextDependent_2879_ = lean_ctor_get_uint8(v_a_2866_, sizeof(void*)*2 + 1);
v___y_2868_ = v_contextDependent_2879_;
goto v___jp_2867_;
}
}
v___jp_2867_:
{
if (v___y_2868_ == 0)
{
lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2876_; 
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2876_ == 0)
{
lean_object* v_unused_2877_; 
v_unused_2877_ = lean_ctor_get(v___x_2865_, 0);
lean_dec(v_unused_2877_);
v___x_2870_ = v___x_2865_;
v_isShared_2871_ = v_isSharedCheck_2876_;
goto v_resetjp_2869_;
}
else
{
lean_dec(v___x_2865_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2876_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2872_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2866_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2872_);
v___x_2874_ = v___x_2870_;
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
else
{
lean_dec(v_a_2866_);
return v___x_2865_;
}
}
}
else
{
return v___x_2865_;
}
}
else
{
lean_dec_ref_known(v_a_2862_, 0);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v___f_2848_);
return v___x_2861_;
}
}
else
{
uint8_t v_done_2880_; 
v_done_2880_ = lean_ctor_get_uint8(v_a_2862_, sizeof(void*)*2);
if (v_done_2880_ == 0)
{
lean_object* v_e_x27_2881_; lean_object* v_proof_2882_; uint8_t v_contextDependent_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref_known(v___x_2861_, 1);
v_e_x27_2881_ = lean_ctor_get(v_a_2862_, 0);
v_proof_2882_ = lean_ctor_get(v_a_2862_, 1);
v_contextDependent_2883_ = lean_ctor_get_uint8(v_a_2862_, sizeof(void*)*2 + 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_a_2862_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2885_ = v_a_2862_;
v_isShared_2886_ = v_isSharedCheck_2933_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_proof_2882_);
lean_inc(v_e_x27_2881_);
lean_dec(v_a_2862_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2933_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; 
lean_inc(v___y_2858_);
lean_inc_ref(v___y_2857_);
lean_inc(v___y_2856_);
lean_inc_ref(v___y_2855_);
lean_inc(v___y_2854_);
lean_inc_ref(v___y_2853_);
lean_inc_ref(v_e_x27_2881_);
v___x_2887_ = lean_apply_12(v___f_2848_, v___x_2860_, v_e_x27_2881_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, lean_box(0));
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2932_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2890_ = v___x_2887_;
v_isShared_2891_ = v_isSharedCheck_2932_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2887_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2932_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
if (lean_obj_tag(v_a_2888_) == 0)
{
uint8_t v_done_2892_; uint8_t v_contextDependent_2893_; uint8_t v___y_2895_; 
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec_ref(v___y_2849_);
v_done_2892_ = lean_ctor_get_uint8(v_a_2888_, 0);
v_contextDependent_2893_ = lean_ctor_get_uint8(v_a_2888_, 1);
lean_dec_ref_known(v_a_2888_, 0);
if (v_contextDependent_2883_ == 0)
{
v___y_2895_ = v_contextDependent_2893_;
goto v___jp_2894_;
}
else
{
v___y_2895_ = v_contextDependent_2883_;
goto v___jp_2894_;
}
v___jp_2894_:
{
lean_object* v___x_2897_; 
if (v_isShared_2886_ == 0)
{
v___x_2897_ = v___x_2885_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_e_x27_2881_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_proof_2882_);
v___x_2897_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2899_; 
lean_ctor_set_uint8(v___x_2897_, sizeof(void*)*2, v_done_2892_);
lean_ctor_set_uint8(v___x_2897_, sizeof(void*)*2 + 1, v___y_2895_);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2897_);
v___x_2899_ = v___x_2890_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
else
{
lean_object* v_e_x27_2902_; lean_object* v_proof_2903_; uint8_t v_done_2904_; uint8_t v_contextDependent_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2931_; 
lean_del_object(v___x_2890_);
lean_del_object(v___x_2885_);
v_e_x27_2902_ = lean_ctor_get(v_a_2888_, 0);
v_proof_2903_ = lean_ctor_get(v_a_2888_, 1);
v_done_2904_ = lean_ctor_get_uint8(v_a_2888_, sizeof(void*)*2);
v_contextDependent_2905_ = lean_ctor_get_uint8(v_a_2888_, sizeof(void*)*2 + 1);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_a_2888_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2907_ = v_a_2888_;
v_isShared_2908_ = v_isSharedCheck_2931_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_proof_2903_);
lean_inc(v_e_x27_2902_);
lean_dec(v_a_2888_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2931_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; 
lean_inc_ref(v_e_x27_2902_);
v___x_2909_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2849_, v_e_x27_2881_, v_proof_2882_, v_e_x27_2902_, v_proof_2903_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2922_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2922_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2922_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
uint8_t v___y_2915_; 
if (v_contextDependent_2883_ == 0)
{
v___y_2915_ = v_contextDependent_2905_;
goto v___jp_2914_;
}
else
{
v___y_2915_ = v_contextDependent_2883_;
goto v___jp_2914_;
}
v___jp_2914_:
{
lean_object* v___x_2917_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v_a_2910_);
v___x_2917_ = v___x_2907_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_e_x27_2902_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_a_2910_);
lean_ctor_set_uint8(v_reuseFailAlloc_2921_, sizeof(void*)*2, v_done_2904_);
v___x_2917_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2919_; 
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*2 + 1, v___y_2915_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2917_);
v___x_2919_ = v___x_2912_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2917_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_del_object(v___x_2907_);
lean_dec_ref(v_e_x27_2902_);
v_a_2923_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2909_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2909_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2885_);
lean_dec_ref(v_proof_2882_);
lean_dec_ref(v_e_x27_2881_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec_ref(v___y_2849_);
return v___x_2887_;
}
}
}
else
{
lean_dec_ref_known(v_a_2862_, 2);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v___f_2848_);
return v___x_2861_;
}
}
}
else
{
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v___f_2848_);
return v___x_2861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18___boxed(lean_object* v___f_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__18(v___f_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__19(lean_object* v___f_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v___y_2960_; lean_object* v___y_2961_; uint8_t v___y_2962_; uint8_t v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; uint8_t v___y_2969_; lean_object* v___y_2973_; lean_object* v___y_2974_; uint8_t v___y_2975_; uint8_t v___y_2976_; lean_object* v___y_2980_; lean_object* v_e_x27_2981_; lean_object* v_proof_2982_; uint8_t v_done_2983_; uint8_t v_contextDependent_2984_; lean_object* v___y_3006_; lean_object* v_a_3007_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_box(0);
lean_inc_ref(v___y_2948_);
v___x_3019_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_2948_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
if (lean_obj_tag(v_a_3020_) == 0)
{
uint8_t v_done_3021_; 
v_done_3021_ = lean_ctor_get_uint8(v_a_3020_, 0);
if (v_done_3021_ == 0)
{
uint8_t v_contextDependent_3022_; lean_object* v___x_3023_; 
lean_dec_ref_known(v___x_3019_, 1);
v_contextDependent_3022_ = lean_ctor_get_uint8(v_a_3020_, 1);
lean_dec_ref_known(v_a_3020_, 0);
lean_inc(v___y_2957_);
lean_inc_ref(v___y_2956_);
lean_inc(v___y_2955_);
lean_inc_ref(v___y_2954_);
lean_inc(v___y_2953_);
lean_inc_ref(v___y_2952_);
lean_inc_ref(v___y_2948_);
v___x_3023_ = lean_apply_12(v___f_2947_, v___x_3018_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, lean_box(0));
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; uint8_t v___y_3026_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
if (v_contextDependent_3022_ == 0)
{
v___y_3006_ = v___x_3023_;
v_a_3007_ = v_a_3024_;
goto v___jp_3005_;
}
else
{
if (lean_obj_tag(v_a_3024_) == 0)
{
uint8_t v_contextDependent_3036_; 
v_contextDependent_3036_ = lean_ctor_get_uint8(v_a_3024_, 1);
v___y_3026_ = v_contextDependent_3036_;
goto v___jp_3025_;
}
else
{
uint8_t v_contextDependent_3037_; 
v_contextDependent_3037_ = lean_ctor_get_uint8(v_a_3024_, sizeof(void*)*2 + 1);
v___y_3026_ = v_contextDependent_3037_;
goto v___jp_3025_;
}
}
v___jp_3025_:
{
if (v___y_3026_ == 0)
{
lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3034_; 
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3034_ == 0)
{
lean_object* v_unused_3035_; 
v_unused_3035_ = lean_ctor_get(v___x_3023_, 0);
lean_dec(v_unused_3035_);
v___x_3028_ = v___x_3023_;
v_isShared_3029_ = v_isSharedCheck_3034_;
goto v_resetjp_3027_;
}
else
{
lean_dec(v___x_3023_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3034_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3030_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3024_);
lean_inc_ref(v___x_3030_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3030_);
v___x_3032_ = v___x_3028_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
v___y_3006_ = v___x_3032_;
v_a_3007_ = v___x_3030_;
goto v___jp_3005_;
}
}
}
else
{
v___y_3006_ = v___x_3023_;
v_a_3007_ = v_a_3024_;
goto v___jp_3005_;
}
}
}
else
{
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec_ref(v___y_2948_);
return v___x_3023_;
}
}
else
{
lean_dec_ref_known(v_a_3020_, 0);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___f_2947_);
return v___x_3019_;
}
}
else
{
uint8_t v_done_3038_; 
v_done_3038_ = lean_ctor_get_uint8(v_a_3020_, sizeof(void*)*2);
if (v_done_3038_ == 0)
{
lean_object* v_e_x27_3039_; lean_object* v_proof_3040_; uint8_t v_contextDependent_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref_known(v___x_3019_, 1);
v_e_x27_3039_ = lean_ctor_get(v_a_3020_, 0);
v_proof_3040_ = lean_ctor_get(v_a_3020_, 1);
v_contextDependent_3041_ = lean_ctor_get_uint8(v_a_3020_, sizeof(void*)*2 + 1);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_a_3020_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3043_ = v_a_3020_;
v_isShared_3044_ = v_isSharedCheck_3091_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_proof_3040_);
lean_inc(v_e_x27_3039_);
lean_dec(v_a_3020_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3091_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; 
lean_inc(v___y_2957_);
lean_inc_ref(v___y_2956_);
lean_inc(v___y_2955_);
lean_inc_ref(v___y_2954_);
lean_inc(v___y_2953_);
lean_inc_ref(v___y_2952_);
lean_inc_ref(v_e_x27_3039_);
v___x_3045_ = lean_apply_12(v___f_2947_, v___x_3018_, v_e_x27_3039_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, lean_box(0));
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3090_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3090_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3090_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
if (lean_obj_tag(v_a_3046_) == 0)
{
uint8_t v_done_3050_; uint8_t v_contextDependent_3051_; uint8_t v___y_3053_; 
v_done_3050_ = lean_ctor_get_uint8(v_a_3046_, 0);
v_contextDependent_3051_ = lean_ctor_get_uint8(v_a_3046_, 1);
lean_dec_ref_known(v_a_3046_, 0);
if (v_contextDependent_3041_ == 0)
{
v___y_3053_ = v_contextDependent_3051_;
goto v___jp_3052_;
}
else
{
v___y_3053_ = v_contextDependent_3041_;
goto v___jp_3052_;
}
v___jp_3052_:
{
lean_object* v___x_3055_; 
lean_inc_ref(v_proof_3040_);
lean_inc_ref(v_e_x27_3039_);
if (v_isShared_3044_ == 0)
{
v___x_3055_ = v___x_3043_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_e_x27_3039_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_proof_3040_);
v___x_3055_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3057_; 
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*2, v_done_3050_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*2 + 1, v___y_3053_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 0, v___x_3055_);
v___x_3057_ = v___x_3048_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
v___y_2980_ = v___x_3057_;
v_e_x27_2981_ = v_e_x27_3039_;
v_proof_2982_ = v_proof_3040_;
v_done_2983_ = v_done_3050_;
v_contextDependent_2984_ = v___y_3053_;
goto v___jp_2979_;
}
}
}
}
else
{
lean_object* v_e_x27_3060_; lean_object* v_proof_3061_; uint8_t v_done_3062_; uint8_t v_contextDependent_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3089_; 
lean_del_object(v___x_3048_);
lean_del_object(v___x_3043_);
v_e_x27_3060_ = lean_ctor_get(v_a_3046_, 0);
v_proof_3061_ = lean_ctor_get(v_a_3046_, 1);
v_done_3062_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*2);
v_contextDependent_3063_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*2 + 1);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_a_3046_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3065_ = v_a_3046_;
v_isShared_3066_ = v_isSharedCheck_3089_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_proof_3061_);
lean_inc(v_e_x27_3060_);
lean_dec(v_a_3046_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3089_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; 
lean_inc_ref(v_e_x27_3060_);
lean_inc_ref(v___y_2948_);
v___x_3067_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2948_, v_e_x27_3039_, v_proof_3040_, v_e_x27_3060_, v_proof_3061_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3080_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3070_ = v___x_3067_;
v_isShared_3071_ = v_isSharedCheck_3080_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3080_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
uint8_t v___y_3073_; 
if (v_contextDependent_3041_ == 0)
{
v___y_3073_ = v_contextDependent_3063_;
goto v___jp_3072_;
}
else
{
v___y_3073_ = v_contextDependent_3041_;
goto v___jp_3072_;
}
v___jp_3072_:
{
lean_object* v___x_3075_; 
lean_inc(v_a_3068_);
lean_inc_ref(v_e_x27_3060_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 1, v_a_3068_);
v___x_3075_ = v___x_3065_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_e_x27_3060_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_a_3068_);
lean_ctor_set_uint8(v_reuseFailAlloc_3079_, sizeof(void*)*2, v_done_3062_);
v___x_3075_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3077_; 
lean_ctor_set_uint8(v___x_3075_, sizeof(void*)*2 + 1, v___y_3073_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v___x_3075_);
v___x_3077_ = v___x_3070_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
v___y_2980_ = v___x_3077_;
v_e_x27_2981_ = v_e_x27_3060_;
v_proof_2982_ = v_a_3068_;
v_done_2983_ = v_done_3062_;
v_contextDependent_2984_ = v___y_3073_;
goto v___jp_2979_;
}
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_del_object(v___x_3065_);
lean_dec_ref(v_e_x27_3060_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec_ref(v___y_2948_);
v_a_3081_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3067_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3067_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3043_);
lean_dec_ref(v_proof_3040_);
lean_dec_ref(v_e_x27_3039_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec_ref(v___y_2948_);
return v___x_3045_;
}
}
}
else
{
lean_dec_ref_known(v_a_3020_, 2);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___f_2947_);
return v___x_3019_;
}
}
}
else
{
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___f_2947_);
return v___x_3019_;
}
v___jp_2959_:
{
if (v___y_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
lean_dec_ref(v___y_2960_);
v___x_2963_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_2961_);
v___x_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
return v___x_2964_;
}
else
{
lean_dec_ref(v___y_2961_);
return v___y_2960_;
}
}
v___jp_2965_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2970_, 0, v___y_2967_);
lean_ctor_set(v___x_2970_, 1, v___y_2968_);
lean_ctor_set_uint8(v___x_2970_, sizeof(void*)*2, v___y_2966_);
lean_ctor_set_uint8(v___x_2970_, sizeof(void*)*2 + 1, v___y_2969_);
v___x_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
return v___x_2971_;
}
v___jp_2972_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2977_, 0, v___y_2974_);
lean_ctor_set(v___x_2977_, 1, v___y_2973_);
lean_ctor_set_uint8(v___x_2977_, sizeof(void*)*2, v___y_2975_);
lean_ctor_set_uint8(v___x_2977_, sizeof(void*)*2 + 1, v___y_2976_);
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
v___jp_2979_:
{
if (v_done_2983_ == 0)
{
lean_object* v___x_2985_; 
lean_dec_ref(v___y_2980_);
lean_inc_ref(v_e_x27_2981_);
v___x_2985_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v_e_x27_2981_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
if (lean_obj_tag(v_a_2986_) == 0)
{
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec_ref(v___y_2948_);
if (v_contextDependent_2984_ == 0)
{
uint8_t v_done_2987_; uint8_t v_contextDependent_2988_; 
v_done_2987_ = lean_ctor_get_uint8(v_a_2986_, 0);
v_contextDependent_2988_ = lean_ctor_get_uint8(v_a_2986_, 1);
lean_dec_ref_known(v_a_2986_, 0);
v___y_2973_ = v_proof_2982_;
v___y_2974_ = v_e_x27_2981_;
v___y_2975_ = v_done_2987_;
v___y_2976_ = v_contextDependent_2988_;
goto v___jp_2972_;
}
else
{
uint8_t v_done_2989_; 
v_done_2989_ = lean_ctor_get_uint8(v_a_2986_, 0);
lean_dec_ref_known(v_a_2986_, 0);
v___y_2973_ = v_proof_2982_;
v___y_2974_ = v_e_x27_2981_;
v___y_2975_ = v_done_2989_;
v___y_2976_ = v_contextDependent_2984_;
goto v___jp_2972_;
}
}
else
{
lean_object* v_e_x27_2990_; lean_object* v_proof_2991_; uint8_t v_done_2992_; uint8_t v_contextDependent_2993_; lean_object* v___x_2994_; 
v_e_x27_2990_ = lean_ctor_get(v_a_2986_, 0);
lean_inc_ref_n(v_e_x27_2990_, 2);
v_proof_2991_ = lean_ctor_get(v_a_2986_, 1);
lean_inc_ref(v_proof_2991_);
v_done_2992_ = lean_ctor_get_uint8(v_a_2986_, sizeof(void*)*2);
v_contextDependent_2993_ = lean_ctor_get_uint8(v_a_2986_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2986_, 2);
v___x_2994_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2948_, v_e_x27_2981_, v_proof_2982_, v_e_x27_2990_, v_proof_2991_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
if (lean_obj_tag(v___x_2994_) == 0)
{
if (v_contextDependent_2984_ == 0)
{
lean_object* v_a_2995_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref_known(v___x_2994_, 1);
v___y_2966_ = v_done_2992_;
v___y_2967_ = v_e_x27_2990_;
v___y_2968_ = v_a_2995_;
v___y_2969_ = v_contextDependent_2993_;
goto v___jp_2965_;
}
else
{
lean_object* v_a_2996_; 
v_a_2996_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2994_, 1);
v___y_2966_ = v_done_2992_;
v___y_2967_ = v_e_x27_2990_;
v___y_2968_ = v_a_2996_;
v___y_2969_ = v_contextDependent_2984_;
goto v___jp_2965_;
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec_ref(v_e_x27_2990_);
v_a_2997_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2994_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2994_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_2982_);
lean_dec_ref(v_e_x27_2981_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec_ref(v___y_2948_);
return v___x_2985_;
}
}
else
{
lean_dec_ref(v_proof_2982_);
lean_dec_ref(v_e_x27_2981_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec_ref(v___y_2948_);
return v___y_2980_;
}
}
v___jp_3005_:
{
if (lean_obj_tag(v_a_3007_) == 0)
{
uint8_t v_done_3008_; 
v_done_3008_ = lean_ctor_get_uint8(v_a_3007_, 0);
if (v_done_3008_ == 0)
{
uint8_t v_contextDependent_3009_; lean_object* v___x_3010_; 
lean_dec_ref(v___y_3006_);
v_contextDependent_3009_ = lean_ctor_get_uint8(v_a_3007_, 1);
lean_dec_ref_known(v_a_3007_, 0);
v___x_3010_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v___y_2948_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
if (lean_obj_tag(v___x_3010_) == 0)
{
if (v_contextDependent_3009_ == 0)
{
return v___x_3010_;
}
else
{
lean_object* v_a_3011_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
if (lean_obj_tag(v_a_3011_) == 0)
{
uint8_t v_contextDependent_3012_; 
v_contextDependent_3012_ = lean_ctor_get_uint8(v_a_3011_, 1);
v___y_2960_ = v___x_3010_;
v___y_2961_ = v_a_3011_;
v___y_2962_ = v_contextDependent_3012_;
goto v___jp_2959_;
}
else
{
uint8_t v_contextDependent_3013_; 
v_contextDependent_3013_ = lean_ctor_get_uint8(v_a_3011_, sizeof(void*)*2 + 1);
v___y_2960_ = v___x_3010_;
v___y_2961_ = v_a_3011_;
v___y_2962_ = v_contextDependent_3013_;
goto v___jp_2959_;
}
}
}
else
{
return v___x_3010_;
}
}
else
{
lean_dec_ref_known(v_a_3007_, 0);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec_ref(v___y_2948_);
return v___y_3006_;
}
}
else
{
lean_object* v_e_x27_3014_; lean_object* v_proof_3015_; uint8_t v_done_3016_; uint8_t v_contextDependent_3017_; 
v_e_x27_3014_ = lean_ctor_get(v_a_3007_, 0);
lean_inc_ref(v_e_x27_3014_);
v_proof_3015_ = lean_ctor_get(v_a_3007_, 1);
lean_inc_ref(v_proof_3015_);
v_done_3016_ = lean_ctor_get_uint8(v_a_3007_, sizeof(void*)*2);
v_contextDependent_3017_ = lean_ctor_get_uint8(v_a_3007_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_3007_, 2);
v___y_2980_ = v___y_3006_;
v_e_x27_2981_ = v_e_x27_3014_;
v_proof_2982_ = v_proof_3015_;
v_done_2983_ = v_done_3016_;
v_contextDependent_2984_ = v_contextDependent_3017_;
goto v___jp_2979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__19___boxed(lean_object* v___f_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__19(v___f_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object* v_config_3132_, lean_object* v_thms_3133_){
_start:
{
uint8_t v_zetaDelta_3134_; uint8_t v_zeta_3135_; uint8_t v_distrib_3136_; lean_object* v___f_3137_; lean_object* v_d_3138_; lean_object* v___f_3139_; lean_object* v___x_3140_; lean_object* v___f_3141_; lean_object* v___f_3142_; lean_object* v_pre_3144_; lean_object* v_pre_3150_; 
v_zetaDelta_3134_ = lean_ctor_get_uint8(v_config_3132_, sizeof(void*)*14 + 19);
v_zeta_3135_ = lean_ctor_get_uint8(v_config_3132_, sizeof(void*)*14 + 20);
v_distrib_3136_ = lean_ctor_get_uint8(v_config_3132_, sizeof(void*)*14 + 21);
v___f_3137_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__11));
v_d_3138_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__12));
lean_inc_ref(v_thms_3133_);
v___f_3139_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed), 14, 2);
lean_closure_set(v___f_3139_, 0, v_thms_3133_);
lean_closure_set(v___f_3139_, 1, v_d_3138_);
v___x_3140_ = lean_box(v_distrib_3136_);
v___f_3141_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed), 15, 3);
lean_closure_set(v___f_3141_, 0, v_d_3138_);
lean_closure_set(v___f_3141_, 1, v___x_3140_);
lean_closure_set(v___f_3141_, 2, v___f_3139_);
v___f_3142_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed), 13, 1);
lean_closure_set(v___f_3142_, 0, v___f_3141_);
if (v_zeta_3135_ == 0)
{
lean_object* v_pre_3152_; 
v_pre_3152_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__13));
v_pre_3150_ = v_pre_3152_;
goto v___jp_3149_;
}
else
{
lean_object* v_pre_3153_; 
v_pre_3153_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__14));
v_pre_3150_ = v_pre_3153_;
goto v___jp_3149_;
}
v___jp_3143_:
{
lean_object* v_post_3145_; lean_object* v_pre_3146_; lean_object* v_post_3147_; lean_object* v___x_3148_; 
v_post_3145_ = lean_ctor_get(v_thms_3133_, 1);
lean_inc_ref(v_post_3145_);
lean_dec_ref(v_thms_3133_);
v_pre_3146_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed), 13, 2);
lean_closure_set(v_pre_3146_, 0, v_pre_3144_);
lean_closure_set(v_pre_3146_, 1, v___f_3142_);
v_post_3147_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed), 14, 3);
lean_closure_set(v_post_3147_, 0, v_post_3145_);
lean_closure_set(v_post_3147_, 1, v_d_3138_);
lean_closure_set(v_post_3147_, 2, v___f_3137_);
v___x_3148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3148_, 0, v_pre_3146_);
lean_ctor_set(v___x_3148_, 1, v_post_3147_);
return v___x_3148_;
}
v___jp_3149_:
{
if (v_zetaDelta_3134_ == 0)
{
lean_inc_ref(v_pre_3150_);
v_pre_3144_ = v_pre_3150_;
goto v___jp_3143_;
}
else
{
lean_object* v_pre_3151_; 
lean_inc_ref(v_pre_3150_);
v_pre_3151_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed), 12, 1);
lean_closure_set(v_pre_3151_, 0, v_pre_3150_);
v_pre_3144_ = v_pre_3151_;
goto v___jp_3143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___boxed(lean_object* v_config_3154_, lean_object* v_thms_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_Meta_Grind_mkNormSymMethods(v_config_3154_, v_thms_3155_);
lean_dec_ref(v_config_3154_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(lean_object* v_x_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; 
lean_inc_ref(v___y_3158_);
v___x_3169_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v___y_3158_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
if (lean_obj_tag(v_a_3170_) == 0)
{
uint8_t v_done_3171_; 
v_done_3171_ = lean_ctor_get_uint8(v_a_3170_, 0);
lean_dec_ref_known(v_a_3170_, 0);
if (v_done_3171_ == 0)
{
lean_object* v___x_3172_; 
lean_dec_ref_known(v___x_3169_, 1);
v___x_3172_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_3158_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec_ref(v___y_3158_);
return v___x_3172_;
}
else
{
lean_dec_ref(v___y_3158_);
return v___x_3169_;
}
}
else
{
uint8_t v_done_3173_; 
lean_dec_ref(v___y_3158_);
v_done_3173_ = lean_ctor_get_uint8(v_a_3170_, sizeof(void*)*1);
if (v_done_3173_ == 0)
{
lean_object* v_e_x27_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3192_; 
lean_dec_ref_known(v___x_3169_, 1);
v_e_x27_3174_ = lean_ctor_get(v_a_3170_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_a_3170_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3176_ = v_a_3170_;
v_isShared_3177_ = v_isSharedCheck_3192_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_e_x27_3174_);
lean_dec(v_a_3170_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3192_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_x27_3174_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
if (lean_obj_tag(v_a_3179_) == 0)
{
lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3190_; 
lean_inc_ref(v_a_3179_);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v___x_3178_, 0);
lean_dec(v_unused_3191_);
v___x_3181_ = v___x_3178_;
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
else
{
lean_dec(v___x_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
uint8_t v_done_3183_; lean_object* v___x_3185_; 
v_done_3183_ = lean_ctor_get_uint8(v_a_3179_, 0);
lean_dec_ref_known(v_a_3179_, 0);
if (v_isShared_3177_ == 0)
{
v___x_3185_ = v___x_3176_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_e_x27_3174_);
v___x_3185_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3187_; 
lean_ctor_set_uint8(v___x_3185_, sizeof(void*)*1, v_done_3183_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v___x_3185_);
v___x_3187_ = v___x_3181_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_del_object(v___x_3176_);
lean_dec_ref(v_e_x27_3174_);
return v___x_3178_;
}
}
else
{
lean_del_object(v___x_3176_);
lean_dec_ref(v_e_x27_3174_);
return v___x_3178_;
}
}
}
else
{
lean_dec_ref_known(v_a_3170_, 1);
return v___x_3169_;
}
}
}
else
{
lean_dec_ref(v___y_3158_);
return v___x_3169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0___boxed(lean_object* v_x_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(v_x_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(lean_object* v_x_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = lean_unsigned_to_nat(255u);
v___x_3219_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_3218_, v___y_3207_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___boxed(lean_object* v_x_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(v_x_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(lean_object* v_dsimp_3233_, lean_object* v___f_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = lean_box(0);
lean_inc_ref(v___y_3235_);
v___x_3247_ = l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(v_dsimp_3233_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
if (lean_obj_tag(v_a_3248_) == 0)
{
uint8_t v_done_3249_; 
v_done_3249_ = lean_ctor_get_uint8(v_a_3248_, 0);
lean_dec_ref_known(v_a_3248_, 0);
if (v_done_3249_ == 0)
{
lean_object* v___x_3250_; 
lean_dec_ref_known(v___x_3247_, 1);
v___x_3250_ = lean_apply_12(v___f_3234_, v___x_3246_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, lean_box(0));
return v___x_3250_;
}
else
{
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___f_3234_);
return v___x_3247_;
}
}
else
{
uint8_t v_done_3251_; 
lean_dec_ref(v___y_3235_);
v_done_3251_ = lean_ctor_get_uint8(v_a_3248_, sizeof(void*)*1);
if (v_done_3251_ == 0)
{
lean_object* v_e_x27_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref_known(v___x_3247_, 1);
v_e_x27_3252_ = lean_ctor_get(v_a_3248_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v_a_3248_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3254_ = v_a_3248_;
v_isShared_3255_ = v_isSharedCheck_3270_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_e_x27_3252_);
lean_dec(v_a_3248_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3270_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; 
lean_inc_ref(v_e_x27_3252_);
v___x_3256_ = lean_apply_12(v___f_3234_, v___x_3246_, v_e_x27_3252_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, lean_box(0));
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
if (lean_obj_tag(v_a_3257_) == 0)
{
lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3268_; 
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3268_ == 0)
{
lean_object* v_unused_3269_; 
v_unused_3269_ = lean_ctor_get(v___x_3256_, 0);
lean_dec(v_unused_3269_);
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3268_;
goto v_resetjp_3258_;
}
else
{
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3268_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
uint8_t v_done_3261_; lean_object* v___x_3263_; 
v_done_3261_ = lean_ctor_get_uint8(v_a_3257_, 0);
lean_dec_ref_known(v_a_3257_, 0);
if (v_isShared_3255_ == 0)
{
v___x_3263_ = v___x_3254_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_e_x27_3252_);
v___x_3263_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
lean_object* v___x_3265_; 
lean_ctor_set_uint8(v___x_3263_, sizeof(void*)*1, v_done_3261_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v___x_3263_);
v___x_3265_ = v___x_3259_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3257_, 1);
lean_del_object(v___x_3254_);
lean_dec_ref(v_e_x27_3252_);
return v___x_3256_;
}
}
else
{
lean_del_object(v___x_3254_);
lean_dec_ref(v_e_x27_3252_);
return v___x_3256_;
}
}
}
else
{
lean_dec_ref_known(v_a_3248_, 1);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___f_3234_);
return v___x_3247_;
}
}
}
else
{
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___f_3234_);
return v___x_3247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed(lean_object* v_dsimp_3271_, lean_object* v___f_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(v_dsimp_3271_, v___f_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec_ref(v_dsimp_3271_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(lean_object* v_pre_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v___x_3297_; 
lean_inc(v___y_3295_);
lean_inc_ref(v___y_3294_);
lean_inc(v___y_3293_);
lean_inc_ref(v___y_3292_);
lean_inc(v___y_3291_);
lean_inc_ref(v___y_3290_);
lean_inc_ref(v___y_3286_);
v___x_3297_ = lean_apply_11(v_pre_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, lean_box(0));
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
if (lean_obj_tag(v_a_3298_) == 0)
{
uint8_t v_done_3299_; 
v_done_3299_ = lean_ctor_get_uint8(v_a_3298_, 0);
lean_dec_ref_known(v_a_3298_, 0);
if (v_done_3299_ == 0)
{
lean_object* v___x_3300_; 
lean_dec_ref_known(v___x_3297_, 1);
v___x_3300_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_3286_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
return v___x_3300_;
}
else
{
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec_ref(v___y_3286_);
return v___x_3297_;
}
}
else
{
uint8_t v_done_3301_; 
lean_dec_ref(v___y_3286_);
v_done_3301_ = lean_ctor_get_uint8(v_a_3298_, sizeof(void*)*1);
if (v_done_3301_ == 0)
{
lean_object* v_e_x27_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3320_; 
lean_dec_ref_known(v___x_3297_, 1);
v_e_x27_3302_ = lean_ctor_get(v_a_3298_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_a_3298_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3304_ = v_a_3298_;
v_isShared_3305_ = v_isSharedCheck_3320_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_e_x27_3302_);
lean_dec(v_a_3298_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3320_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; 
lean_inc_ref(v_e_x27_3302_);
v___x_3306_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_x27_3302_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
if (lean_obj_tag(v_a_3307_) == 0)
{
lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3318_; 
lean_inc_ref(v_a_3307_);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3318_ == 0)
{
lean_object* v_unused_3319_; 
v_unused_3319_ = lean_ctor_get(v___x_3306_, 0);
lean_dec(v_unused_3319_);
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3318_;
goto v_resetjp_3308_;
}
else
{
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3318_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
uint8_t v_done_3311_; lean_object* v___x_3313_; 
v_done_3311_ = lean_ctor_get_uint8(v_a_3307_, 0);
lean_dec_ref_known(v_a_3307_, 0);
if (v_isShared_3305_ == 0)
{
v___x_3313_ = v___x_3304_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_e_x27_3302_);
v___x_3313_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3315_; 
lean_ctor_set_uint8(v___x_3313_, sizeof(void*)*1, v_done_3311_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3313_);
v___x_3315_ = v___x_3309_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
else
{
lean_del_object(v___x_3304_);
lean_dec_ref(v_e_x27_3302_);
return v___x_3306_;
}
}
else
{
lean_del_object(v___x_3304_);
lean_dec_ref(v_e_x27_3302_);
return v___x_3306_;
}
}
}
else
{
lean_dec_ref_known(v_a_3298_, 1);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
return v___x_3297_;
}
}
}
else
{
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec_ref(v___y_3286_);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed(lean_object* v_pre_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(v_pre_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(lean_object* v___f_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = lean_box(0);
lean_inc_ref(v___y_3335_);
v___x_3347_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_3335_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
if (lean_obj_tag(v_a_3348_) == 0)
{
uint8_t v_done_3349_; 
v_done_3349_ = lean_ctor_get_uint8(v_a_3348_, 0);
lean_dec_ref_known(v_a_3348_, 0);
if (v_done_3349_ == 0)
{
lean_object* v___x_3350_; 
lean_dec_ref_known(v___x_3347_, 1);
v___x_3350_ = lean_apply_12(v___f_3334_, v___x_3346_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, lean_box(0));
return v___x_3350_;
}
else
{
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___f_3334_);
return v___x_3347_;
}
}
else
{
uint8_t v_done_3351_; 
lean_dec_ref(v___y_3335_);
v_done_3351_ = lean_ctor_get_uint8(v_a_3348_, sizeof(void*)*1);
if (v_done_3351_ == 0)
{
lean_object* v_e_x27_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3370_; 
lean_dec_ref_known(v___x_3347_, 1);
v_e_x27_3352_ = lean_ctor_get(v_a_3348_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_a_3348_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3354_ = v_a_3348_;
v_isShared_3355_ = v_isSharedCheck_3370_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_e_x27_3352_);
lean_dec(v_a_3348_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3370_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; 
lean_inc_ref(v_e_x27_3352_);
v___x_3356_ = lean_apply_12(v___f_3334_, v___x_3346_, v_e_x27_3352_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, lean_box(0));
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
if (lean_obj_tag(v_a_3357_) == 0)
{
lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3368_; 
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; 
v_unused_3369_ = lean_ctor_get(v___x_3356_, 0);
lean_dec(v_unused_3369_);
v___x_3359_ = v___x_3356_;
v_isShared_3360_ = v_isSharedCheck_3368_;
goto v_resetjp_3358_;
}
else
{
lean_dec(v___x_3356_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3368_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
uint8_t v_done_3361_; lean_object* v___x_3363_; 
v_done_3361_ = lean_ctor_get_uint8(v_a_3357_, 0);
lean_dec_ref_known(v_a_3357_, 0);
if (v_isShared_3355_ == 0)
{
v___x_3363_ = v___x_3354_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_e_x27_3352_);
v___x_3363_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3365_; 
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*1, v_done_3361_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3363_);
v___x_3365_ = v___x_3359_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_3357_, 1);
lean_del_object(v___x_3354_);
lean_dec_ref(v_e_x27_3352_);
return v___x_3356_;
}
}
else
{
lean_del_object(v___x_3354_);
lean_dec_ref(v_e_x27_3352_);
return v___x_3356_;
}
}
}
else
{
lean_dec_ref_known(v_a_3348_, 1);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___f_3334_);
return v___x_3347_;
}
}
}
else
{
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___f_3334_);
return v___x_3347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4___boxed(lean_object* v___f_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(v___f_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(lean_object* v___f_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___y_3397_; lean_object* v_e_x27_3398_; uint8_t v_done_3399_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = lean_box(0);
lean_inc_ref(v___y_3385_);
v___x_3413_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_3385_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
if (lean_obj_tag(v_a_3414_) == 0)
{
uint8_t v_done_3415_; 
v_done_3415_ = lean_ctor_get_uint8(v_a_3414_, 0);
lean_dec_ref_known(v_a_3414_, 0);
if (v_done_3415_ == 0)
{
lean_object* v___x_3416_; 
lean_dec_ref_known(v___x_3413_, 1);
lean_inc(v___y_3394_);
lean_inc_ref(v___y_3393_);
lean_inc(v___y_3392_);
lean_inc_ref(v___y_3391_);
lean_inc(v___y_3390_);
lean_inc_ref(v___y_3389_);
lean_inc_ref(v___y_3385_);
v___x_3416_ = lean_apply_12(v___f_3384_, v___x_3412_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, lean_box(0));
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
if (lean_obj_tag(v_a_3417_) == 0)
{
uint8_t v_done_3418_; 
v_done_3418_ = lean_ctor_get_uint8(v_a_3417_, 0);
lean_dec_ref_known(v_a_3417_, 0);
if (v_done_3418_ == 0)
{
lean_object* v___x_3419_; 
lean_dec_ref_known(v___x_3416_, 1);
v___x_3419_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_3385_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v___x_3419_;
}
else
{
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec_ref(v___y_3385_);
return v___x_3416_;
}
}
else
{
lean_object* v_e_x27_3420_; uint8_t v_done_3421_; 
lean_dec_ref(v___y_3385_);
v_e_x27_3420_ = lean_ctor_get(v_a_3417_, 0);
lean_inc_ref(v_e_x27_3420_);
v_done_3421_ = lean_ctor_get_uint8(v_a_3417_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3417_, 1);
v___y_3397_ = v___x_3416_;
v_e_x27_3398_ = v_e_x27_3420_;
v_done_3399_ = v_done_3421_;
goto v___jp_3396_;
}
}
else
{
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec_ref(v___y_3385_);
return v___x_3416_;
}
}
else
{
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec_ref(v___f_3384_);
return v___x_3413_;
}
}
else
{
uint8_t v_done_3422_; 
lean_dec_ref(v___y_3385_);
v_done_3422_ = lean_ctor_get_uint8(v_a_3414_, sizeof(void*)*1);
if (v_done_3422_ == 0)
{
lean_object* v_e_x27_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref_known(v___x_3413_, 1);
v_e_x27_3423_ = lean_ctor_get(v_a_3414_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_a_3414_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3425_ = v_a_3414_;
v_isShared_3426_ = v_isSharedCheck_3443_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_e_x27_3423_);
lean_dec(v_a_3414_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3443_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; 
lean_inc(v___y_3394_);
lean_inc_ref(v___y_3393_);
lean_inc(v___y_3392_);
lean_inc_ref(v___y_3391_);
lean_inc(v___y_3390_);
lean_inc_ref(v___y_3389_);
lean_inc_ref(v_e_x27_3423_);
v___x_3427_ = lean_apply_12(v___f_3384_, v___x_3412_, v_e_x27_3423_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, lean_box(0));
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
if (lean_obj_tag(v_a_3428_) == 0)
{
lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3439_; 
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3439_ == 0)
{
lean_object* v_unused_3440_; 
v_unused_3440_ = lean_ctor_get(v___x_3427_, 0);
lean_dec(v_unused_3440_);
v___x_3430_ = v___x_3427_;
v_isShared_3431_ = v_isSharedCheck_3439_;
goto v_resetjp_3429_;
}
else
{
lean_dec(v___x_3427_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3439_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
uint8_t v_done_3432_; lean_object* v___x_3434_; 
v_done_3432_ = lean_ctor_get_uint8(v_a_3428_, 0);
lean_dec_ref_known(v_a_3428_, 0);
lean_inc_ref(v_e_x27_3423_);
if (v_isShared_3426_ == 0)
{
v___x_3434_ = v___x_3425_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_e_x27_3423_);
v___x_3434_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
lean_object* v___x_3436_; 
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*1, v_done_3432_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3434_);
v___x_3436_ = v___x_3430_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
v___y_3397_ = v___x_3436_;
v_e_x27_3398_ = v_e_x27_3423_;
v_done_3399_ = v_done_3432_;
goto v___jp_3396_;
}
}
}
}
else
{
lean_object* v_e_x27_3441_; uint8_t v_done_3442_; 
lean_del_object(v___x_3425_);
lean_dec_ref(v_e_x27_3423_);
v_e_x27_3441_ = lean_ctor_get(v_a_3428_, 0);
lean_inc_ref(v_e_x27_3441_);
v_done_3442_ = lean_ctor_get_uint8(v_a_3428_, sizeof(void*)*1);
lean_dec_ref_known(v_a_3428_, 1);
v___y_3397_ = v___x_3427_;
v_e_x27_3398_ = v_e_x27_3441_;
v_done_3399_ = v_done_3442_;
goto v___jp_3396_;
}
}
else
{
lean_del_object(v___x_3425_);
lean_dec_ref(v_e_x27_3423_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v___x_3427_;
}
}
}
else
{
lean_dec_ref_known(v_a_3414_, 1);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___f_3384_);
return v___x_3413_;
}
}
}
else
{
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec_ref(v___f_3384_);
return v___x_3413_;
}
v___jp_3396_:
{
if (v_done_3399_ == 0)
{
lean_object* v___x_3400_; 
lean_dec_ref(v___y_3397_);
lean_inc_ref(v_e_x27_3398_);
v___x_3400_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_x27_3398_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
if (lean_obj_tag(v_a_3401_) == 0)
{
lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3410_; 
lean_inc_ref(v_a_3401_);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3410_ == 0)
{
lean_object* v_unused_3411_; 
v_unused_3411_ = lean_ctor_get(v___x_3400_, 0);
lean_dec(v_unused_3411_);
v___x_3403_ = v___x_3400_;
v_isShared_3404_ = v_isSharedCheck_3410_;
goto v_resetjp_3402_;
}
else
{
lean_dec(v___x_3400_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3410_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
uint8_t v_done_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
v_done_3405_ = lean_ctor_get_uint8(v_a_3401_, 0);
lean_dec_ref_known(v_a_3401_, 0);
v___x_3406_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_3406_, 0, v_e_x27_3398_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*1, v_done_3405_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3406_);
v___x_3408_ = v___x_3403_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
else
{
lean_dec_ref(v_e_x27_3398_);
return v___x_3400_;
}
}
else
{
lean_dec_ref(v_e_x27_3398_);
return v___x_3400_;
}
}
else
{
lean_dec_ref(v_e_x27_3398_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v___y_3397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5___boxed(lean_object* v___f_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(v___f_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods(lean_object* v_config_3463_, lean_object* v_thms_3464_){
_start:
{
uint8_t v_zetaDelta_3465_; uint8_t v_zeta_3466_; lean_object* v___f_3467_; lean_object* v_pre_3469_; lean_object* v_pre_3474_; 
v_zetaDelta_3465_ = lean_ctor_get_uint8(v_config_3463_, sizeof(void*)*14 + 19);
v_zeta_3466_ = lean_ctor_get_uint8(v_config_3463_, sizeof(void*)*14 + 20);
v___f_3467_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__1));
if (v_zeta_3466_ == 0)
{
lean_object* v_pre_3476_; 
v_pre_3476_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__2));
v_pre_3474_ = v_pre_3476_;
goto v___jp_3473_;
}
else
{
lean_object* v_pre_3477_; 
v_pre_3477_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__3));
v_pre_3474_ = v_pre_3477_;
goto v___jp_3473_;
}
v___jp_3468_:
{
lean_object* v_dsimp_3470_; lean_object* v_post_3471_; lean_object* v___x_3472_; 
v_dsimp_3470_ = lean_ctor_get(v_thms_3464_, 2);
lean_inc_ref(v_dsimp_3470_);
lean_dec_ref(v_thms_3464_);
v_post_3471_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed), 13, 2);
lean_closure_set(v_post_3471_, 0, v_dsimp_3470_);
lean_closure_set(v_post_3471_, 1, v___f_3467_);
v___x_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3472_, 0, v_pre_3469_);
lean_ctor_set(v___x_3472_, 1, v_post_3471_);
return v___x_3472_;
}
v___jp_3473_:
{
if (v_zetaDelta_3465_ == 0)
{
lean_inc_ref(v_pre_3474_);
v_pre_3469_ = v_pre_3474_;
goto v___jp_3468_;
}
else
{
lean_object* v_pre_3475_; 
lean_inc_ref(v_pre_3474_);
v_pre_3475_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed), 12, 1);
lean_closure_set(v_pre_3475_, 0, v_pre_3474_);
v_pre_3469_ = v_pre_3475_;
goto v___jp_3468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___boxed(lean_object* v_config_3478_, lean_object* v_thms_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_config_3478_, v_thms_3479_);
lean_dec_ref(v_config_3478_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(lean_object* v_e_3481_, lean_object* v___y_3482_){
_start:
{
uint8_t v___x_3484_; 
v___x_3484_ = l_Lean_Expr_hasMVar(v_e_3481_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v_e_3481_);
return v___x_3485_;
}
else
{
lean_object* v___x_3486_; lean_object* v_mctx_3487_; lean_object* v___x_3488_; lean_object* v_fst_3489_; lean_object* v_snd_3490_; lean_object* v___x_3491_; lean_object* v_cache_3492_; lean_object* v_zetaDeltaFVarIds_3493_; lean_object* v_postponed_3494_; lean_object* v_diag_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3504_; 
v___x_3486_ = lean_st_ref_get(v___y_3482_);
v_mctx_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc_ref(v_mctx_3487_);
lean_dec(v___x_3486_);
v___x_3488_ = l_Lean_instantiateMVarsCore(v_mctx_3487_, v_e_3481_);
v_fst_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_fst_3489_);
v_snd_3490_ = lean_ctor_get(v___x_3488_, 1);
lean_inc(v_snd_3490_);
lean_dec_ref(v___x_3488_);
v___x_3491_ = lean_st_ref_take(v___y_3482_);
v_cache_3492_ = lean_ctor_get(v___x_3491_, 1);
v_zetaDeltaFVarIds_3493_ = lean_ctor_get(v___x_3491_, 2);
v_postponed_3494_ = lean_ctor_get(v___x_3491_, 3);
v_diag_3495_ = lean_ctor_get(v___x_3491_, 4);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3504_ == 0)
{
lean_object* v_unused_3505_; 
v_unused_3505_ = lean_ctor_get(v___x_3491_, 0);
lean_dec(v_unused_3505_);
v___x_3497_ = v___x_3491_;
v_isShared_3498_ = v_isSharedCheck_3504_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_diag_3495_);
lean_inc(v_postponed_3494_);
lean_inc(v_zetaDeltaFVarIds_3493_);
lean_inc(v_cache_3492_);
lean_dec(v___x_3491_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3504_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v_snd_3490_);
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_snd_3490_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_cache_3492_);
lean_ctor_set(v_reuseFailAlloc_3503_, 2, v_zetaDeltaFVarIds_3493_);
lean_ctor_set(v_reuseFailAlloc_3503_, 3, v_postponed_3494_);
lean_ctor_set(v_reuseFailAlloc_3503_, 4, v_diag_3495_);
v___x_3500_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = lean_st_ref_put(v___y_3482_, v___x_3500_);
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v_fst_3489_);
return v___x_3502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg___boxed(lean_object* v_e_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_3506_, v___y_3507_);
lean_dec(v___y_3507_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(lean_object* v_e_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_3510_, v___y_3517_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___boxed(lean_object* v_e_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(v_e_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy(lean_object* v_e_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v___x_3545_; lean_object* v_a_3546_; lean_object* v___x_3547_; 
v___x_3545_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_3534_, v_a_3541_);
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_a_3546_);
lean_dec_ref(v___x_3545_);
v___x_3547_ = l_Lean_Meta_Grind_simpCore(v_a_3546_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v_expr_3549_; lean_object* v_proof_x3f_3550_; uint8_t v_cache_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3575_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
v_expr_3549_ = lean_ctor_get(v_a_3548_, 0);
v_proof_x3f_3550_ = lean_ctor_get(v_a_3548_, 1);
v_cache_3551_ = lean_ctor_get_uint8(v_a_3548_, sizeof(void*)*2);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_a_3548_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3553_ = v_a_3548_;
v_isShared_3554_ = v_isSharedCheck_3575_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_proof_x3f_3550_);
lean_inc(v_expr_3549_);
lean_dec(v_a_3548_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3575_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_expr_3549_, v_a_3542_, v_a_3543_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3566_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3566_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3566_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v_a_3556_);
v___x_3561_ = v___x_3553_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3556_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_proof_x3f_3550_);
lean_ctor_set_uint8(v_reuseFailAlloc_3565_, sizeof(void*)*2, v_cache_3551_);
v___x_3561_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v___x_3561_);
v___x_3563_ = v___x_3558_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_del_object(v___x_3553_);
lean_dec(v_proof_x3f_3550_);
v_a_3567_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3555_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3555_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
else
{
return v___x_3547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy___boxed(lean_object* v_e_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Meta_Grind_normLegacy(v_e_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
return v_res_3587_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__0(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = lean_obj_once(&l_Lean_Meta_Grind_mkNormSymTheorems___closed__1, &l_Lean_Meta_Grind_mkNormSymTheorems___closed__1_once, _init_l_Lean_Meta_Grind_mkNormSymTheorems___closed__1);
v___x_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
return v___x_3589_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__1(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__0, &l_Lean_Meta_Grind_normSym___redArg___closed__0_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__0);
v___x_3591_ = lean_unsigned_to_nat(0u);
v___x_3592_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
lean_ctor_set(v___x_3592_, 1, v___x_3590_);
lean_ctor_set(v___x_3592_, 2, v___x_3590_);
lean_ctor_set(v___x_3592_, 3, v___x_3590_);
return v___x_3592_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__2(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3593_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__0, &l_Lean_Meta_Grind_normSym___redArg___closed__0_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__0);
v___x_3594_ = lean_unsigned_to_nat(0u);
v___x_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
lean_ctor_set(v___x_3595_, 1, v___x_3593_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg(lean_object* v_e_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l_Lean_Meta_Grind_mkNormSymTheorems(v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3607_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v___x_3605_, 1);
v___x_3607_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3597_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
lean_inc(v_a_3606_);
v___x_3609_ = l_Lean_Meta_Grind_mkNormSymMethods(v_a_3608_, v_a_3606_);
v___x_3610_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_a_3608_, v_a_3606_);
lean_dec(v_a_3608_);
v___x_3611_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__1, &l_Lean_Meta_Grind_normSym___redArg___closed__1_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__1);
v___x_3612_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__2, &l_Lean_Meta_Grind_normSym___redArg___closed__2_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__2);
v___x_3613_ = l_Lean_Meta_Grind_symNorm(v_e_3596_, v___x_3609_, v___x_3610_, v___x_3611_, v___x_3612_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3622_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3616_ = v___x_3613_;
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3613_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v_fst_3618_; lean_object* v___x_3620_; 
v_fst_3618_ = lean_ctor_get(v_a_3614_, 0);
lean_inc(v_fst_3618_);
lean_dec(v_a_3614_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v_fst_3618_);
v___x_3620_ = v___x_3616_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_fst_3618_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
v_a_3623_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3613_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3613_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec(v_a_3606_);
lean_dec_ref(v_e_3596_);
v_a_3631_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3607_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3607_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec_ref(v_e_3596_);
v_a_3639_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3605_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3605_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg___boxed(lean_object* v_e_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_Meta_Grind_normSym___redArg(v_e_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
lean_dec(v_a_3654_);
lean_dec_ref(v_a_3653_);
lean_dec(v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3649_);
lean_dec_ref(v_a_3648_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym(lean_object* v_e_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_Meta_Grind_normSym___redArg(v_e_3657_, v_a_3659_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___boxed(lean_object* v_e_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_Meta_Grind_normSym(v_e_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_);
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
return v_res_3680_;
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
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
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
lean_object* initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
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
