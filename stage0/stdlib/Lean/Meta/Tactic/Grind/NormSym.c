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
extern lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Meta_Grind_normSymExt;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_Grind_symNorm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_simpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormSymTheorems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormSymTheorems___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormSymTheorems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormSymTheorems___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Grind_normSym___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normSym___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormSymTheorems___redArg(lean_object* v_a_1_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v_env_5_; lean_object* v___x_6_; lean_object* v_ext_7_; lean_object* v_toEnvExtension_8_; lean_object* v_asyncMode_9_; uint8_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_3_ = l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default;
v___x_4_ = lean_st_ref_get(v_a_1_);
v_env_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_env_5_);
lean_dec(v___x_4_);
v___x_6_ = l_Lean_Meta_Grind_normSymExt;
v_ext_7_ = lean_ctor_get(v___x_6_, 1);
v_toEnvExtension_8_ = lean_ctor_get(v_ext_7_, 0);
v_asyncMode_9_ = lean_ctor_get(v_toEnvExtension_8_, 2);
v___x_10_ = 0;
v___x_11_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3_, v___x_6_, v_env_5_, v_asyncMode_9_, v___x_10_);
v___x_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormSymTheorems___redArg___boxed(lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Meta_Grind_getNormSymTheorems___redArg(v_a_13_);
lean_dec(v_a_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormSymTheorems(lean_object* v_a_16_, lean_object* v_a_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Meta_Grind_getNormSymTheorems___redArg(v_a_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getNormSymTheorems___boxed(lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Meta_Grind_getNormSymTheorems(v_a_20_, v_a_21_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0(lean_object* v_x_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
lean_inc_ref(v___y_25_);
v___x_36_ = l_Lean_Meta_Sym_Simp_reduceControl(v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_a_37_);
if (lean_obj_tag(v_a_37_) == 0)
{
uint8_t v_done_38_; 
v_done_38_ = lean_ctor_get_uint8(v_a_37_, 0);
if (v_done_38_ == 0)
{
uint8_t v_contextDependent_39_; lean_object* v___x_40_; 
lean_dec_ref_known(v___x_36_, 1);
v_contextDependent_39_ = lean_ctor_get_uint8(v_a_37_, 1);
lean_dec_ref_known(v_a_37_, 0);
v___x_40_ = l_Lean_Meta_Sym_Simp_simpExistsPropDomain(v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; uint8_t v___y_43_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
if (v_contextDependent_39_ == 0)
{
return v___x_40_;
}
else
{
if (lean_obj_tag(v_a_41_) == 0)
{
uint8_t v_contextDependent_53_; 
v_contextDependent_53_ = lean_ctor_get_uint8(v_a_41_, 1);
v___y_43_ = v_contextDependent_53_;
goto v___jp_42_;
}
else
{
uint8_t v_contextDependent_54_; 
v_contextDependent_54_ = lean_ctor_get_uint8(v_a_41_, sizeof(void*)*2 + 1);
v___y_43_ = v_contextDependent_54_;
goto v___jp_42_;
}
}
v___jp_42_:
{
if (v___y_43_ == 0)
{
lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
lean_inc(v_a_41_);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_51_ == 0)
{
lean_object* v_unused_52_; 
v_unused_52_ = lean_ctor_get(v___x_40_, 0);
lean_dec(v_unused_52_);
v___x_45_ = v___x_40_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_dec(v___x_40_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_47_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_41_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
else
{
return v___x_40_;
}
}
}
else
{
return v___x_40_;
}
}
else
{
lean_dec_ref_known(v_a_37_, 0);
lean_dec_ref(v___y_25_);
return v___x_36_;
}
}
else
{
uint8_t v_done_55_; 
v_done_55_ = lean_ctor_get_uint8(v_a_37_, sizeof(void*)*2);
if (v_done_55_ == 0)
{
lean_object* v_e_x27_56_; lean_object* v_proof_57_; uint8_t v_contextDependent_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_108_; 
lean_dec_ref_known(v___x_36_, 1);
v_e_x27_56_ = lean_ctor_get(v_a_37_, 0);
v_proof_57_ = lean_ctor_get(v_a_37_, 1);
v_contextDependent_58_ = lean_ctor_get_uint8(v_a_37_, sizeof(void*)*2 + 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_a_37_);
if (v_isSharedCheck_108_ == 0)
{
v___x_60_ = v_a_37_;
v_isShared_61_ = v_isSharedCheck_108_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_proof_57_);
lean_inc(v_e_x27_56_);
lean_dec(v_a_37_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_108_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; 
lean_inc_ref(v_e_x27_56_);
v___x_62_ = l_Lean_Meta_Sym_Simp_simpExistsPropDomain(v_e_x27_56_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_107_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_107_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_107_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_107_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
if (lean_obj_tag(v_a_63_) == 0)
{
uint8_t v_done_67_; uint8_t v_contextDependent_68_; uint8_t v___y_70_; 
lean_dec_ref(v___y_25_);
v_done_67_ = lean_ctor_get_uint8(v_a_63_, 0);
v_contextDependent_68_ = lean_ctor_get_uint8(v_a_63_, 1);
lean_dec_ref_known(v_a_63_, 0);
if (v_contextDependent_58_ == 0)
{
v___y_70_ = v_contextDependent_68_;
goto v___jp_69_;
}
else
{
v___y_70_ = v_contextDependent_58_;
goto v___jp_69_;
}
v___jp_69_:
{
lean_object* v___x_72_; 
if (v_isShared_61_ == 0)
{
v___x_72_ = v___x_60_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_e_x27_56_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_proof_57_);
v___x_72_ = v_reuseFailAlloc_76_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_74_; 
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*2, v_done_67_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*2 + 1, v___y_70_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_72_);
v___x_74_ = v___x_65_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
else
{
lean_object* v_e_x27_77_; lean_object* v_proof_78_; uint8_t v_done_79_; uint8_t v_contextDependent_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_106_; 
lean_del_object(v___x_65_);
lean_del_object(v___x_60_);
v_e_x27_77_ = lean_ctor_get(v_a_63_, 0);
v_proof_78_ = lean_ctor_get(v_a_63_, 1);
v_done_79_ = lean_ctor_get_uint8(v_a_63_, sizeof(void*)*2);
v_contextDependent_80_ = lean_ctor_get_uint8(v_a_63_, sizeof(void*)*2 + 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_a_63_);
if (v_isSharedCheck_106_ == 0)
{
v___x_82_ = v_a_63_;
v_isShared_83_ = v_isSharedCheck_106_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_proof_78_);
lean_inc(v_e_x27_77_);
lean_dec(v_a_63_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_106_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; 
lean_inc_ref(v_e_x27_77_);
v___x_84_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_25_, v_e_x27_56_, v_proof_57_, v_e_x27_77_, v_proof_78_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_97_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_97_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_97_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_97_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
uint8_t v___y_90_; 
if (v_contextDependent_58_ == 0)
{
v___y_90_ = v_contextDependent_80_;
goto v___jp_89_;
}
else
{
v___y_90_ = v_contextDependent_58_;
goto v___jp_89_;
}
v___jp_89_:
{
lean_object* v___x_92_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_a_85_);
v___x_92_ = v___x_82_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_e_x27_77_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_a_85_);
lean_ctor_set_uint8(v_reuseFailAlloc_96_, sizeof(void*)*2, v_done_79_);
v___x_92_ = v_reuseFailAlloc_96_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_94_; 
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*2 + 1, v___y_90_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_92_);
v___x_94_ = v___x_87_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_del_object(v___x_82_);
lean_dec_ref(v_e_x27_77_);
v_a_98_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_84_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_84_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_60_);
lean_dec_ref(v_proof_57_);
lean_dec_ref(v_e_x27_56_);
lean_dec_ref(v___y_25_);
return v___x_62_;
}
}
}
else
{
lean_dec_ref_known(v_a_37_, 2);
lean_dec_ref(v___y_25_);
return v___x_36_;
}
}
}
else
{
lean_dec_ref(v___y_25_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__0___boxed(lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__0(v_x_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1(lean_object* v___f_122_, lean_object* v_x_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_box(0);
lean_inc_ref(v___y_124_);
v___x_136_ = l_Lean_Meta_Sym_Simp_reduceProj___redArg(v___y_124_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
if (lean_obj_tag(v_a_137_) == 0)
{
uint8_t v_done_138_; 
v_done_138_ = lean_ctor_get_uint8(v_a_137_, 0);
if (v_done_138_ == 0)
{
uint8_t v_contextDependent_139_; lean_object* v___x_140_; 
lean_dec_ref_known(v___x_136_, 1);
v_contextDependent_139_ = lean_ctor_get_uint8(v_a_137_, 1);
lean_dec_ref_known(v_a_137_, 0);
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
lean_inc(v___y_131_);
lean_inc_ref(v___y_130_);
lean_inc(v___y_129_);
lean_inc_ref(v___y_128_);
lean_inc(v___y_127_);
lean_inc_ref(v___y_126_);
lean_inc(v___y_125_);
v___x_140_ = lean_apply_12(v___f_122_, v___x_135_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, lean_box(0));
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; uint8_t v___y_143_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
if (v_contextDependent_139_ == 0)
{
lean_dec(v_a_141_);
return v___x_140_;
}
else
{
if (lean_obj_tag(v_a_141_) == 0)
{
uint8_t v_contextDependent_153_; 
v_contextDependent_153_ = lean_ctor_get_uint8(v_a_141_, 1);
v___y_143_ = v_contextDependent_153_;
goto v___jp_142_;
}
else
{
uint8_t v_contextDependent_154_; 
v_contextDependent_154_ = lean_ctor_get_uint8(v_a_141_, sizeof(void*)*2 + 1);
v___y_143_ = v_contextDependent_154_;
goto v___jp_142_;
}
}
v___jp_142_:
{
if (v___y_143_ == 0)
{
lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_151_; 
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v___x_140_, 0);
lean_dec(v_unused_152_);
v___x_145_ = v___x_140_;
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
else
{
lean_dec(v___x_140_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_141_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_147_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
else
{
lean_dec(v_a_141_);
return v___x_140_;
}
}
}
else
{
return v___x_140_;
}
}
else
{
lean_dec_ref_known(v_a_137_, 0);
lean_dec_ref(v___y_124_);
lean_dec_ref(v___f_122_);
return v___x_136_;
}
}
else
{
uint8_t v_done_155_; 
v_done_155_ = lean_ctor_get_uint8(v_a_137_, sizeof(void*)*2);
if (v_done_155_ == 0)
{
lean_object* v_e_x27_156_; lean_object* v_proof_157_; uint8_t v_contextDependent_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref_known(v___x_136_, 1);
v_e_x27_156_ = lean_ctor_get(v_a_137_, 0);
v_proof_157_ = lean_ctor_get(v_a_137_, 1);
v_contextDependent_158_ = lean_ctor_get_uint8(v_a_137_, sizeof(void*)*2 + 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_a_137_);
if (v_isSharedCheck_208_ == 0)
{
v___x_160_ = v_a_137_;
v_isShared_161_ = v_isSharedCheck_208_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_proof_157_);
lean_inc(v_e_x27_156_);
lean_dec(v_a_137_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_208_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; 
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
lean_inc(v___y_131_);
lean_inc_ref(v___y_130_);
lean_inc(v___y_129_);
lean_inc_ref(v___y_128_);
lean_inc(v___y_127_);
lean_inc_ref(v___y_126_);
lean_inc(v___y_125_);
lean_inc_ref(v_e_x27_156_);
v___x_162_ = lean_apply_12(v___f_122_, v___x_135_, v_e_x27_156_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, lean_box(0));
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_207_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_207_ == 0)
{
v___x_165_ = v___x_162_;
v_isShared_166_ = v_isSharedCheck_207_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_207_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
if (lean_obj_tag(v_a_163_) == 0)
{
uint8_t v_done_167_; uint8_t v_contextDependent_168_; uint8_t v___y_170_; 
lean_dec_ref(v___y_124_);
v_done_167_ = lean_ctor_get_uint8(v_a_163_, 0);
v_contextDependent_168_ = lean_ctor_get_uint8(v_a_163_, 1);
lean_dec_ref_known(v_a_163_, 0);
if (v_contextDependent_158_ == 0)
{
v___y_170_ = v_contextDependent_168_;
goto v___jp_169_;
}
else
{
v___y_170_ = v_contextDependent_158_;
goto v___jp_169_;
}
v___jp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_161_ == 0)
{
v___x_172_ = v___x_160_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_e_x27_156_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_proof_157_);
v___x_172_ = v_reuseFailAlloc_176_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_174_; 
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*2, v_done_167_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*2 + 1, v___y_170_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_172_);
v___x_174_ = v___x_165_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_e_x27_177_; lean_object* v_proof_178_; uint8_t v_done_179_; uint8_t v_contextDependent_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_206_; 
lean_del_object(v___x_165_);
lean_del_object(v___x_160_);
v_e_x27_177_ = lean_ctor_get(v_a_163_, 0);
v_proof_178_ = lean_ctor_get(v_a_163_, 1);
v_done_179_ = lean_ctor_get_uint8(v_a_163_, sizeof(void*)*2);
v_contextDependent_180_ = lean_ctor_get_uint8(v_a_163_, sizeof(void*)*2 + 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_a_163_);
if (v_isSharedCheck_206_ == 0)
{
v___x_182_ = v_a_163_;
v_isShared_183_ = v_isSharedCheck_206_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_proof_178_);
lean_inc(v_e_x27_177_);
lean_dec(v_a_163_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_206_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; 
lean_inc_ref(v_e_x27_177_);
v___x_184_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_124_, v_e_x27_156_, v_proof_157_, v_e_x27_177_, v_proof_178_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_197_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_197_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_197_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_197_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
uint8_t v___y_190_; 
if (v_contextDependent_158_ == 0)
{
v___y_190_ = v_contextDependent_180_;
goto v___jp_189_;
}
else
{
v___y_190_ = v_contextDependent_158_;
goto v___jp_189_;
}
v___jp_189_:
{
lean_object* v___x_192_; 
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v_a_185_);
v___x_192_ = v___x_182_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_e_x27_177_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_a_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_196_, sizeof(void*)*2, v_done_179_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_194_; 
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*2 + 1, v___y_190_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_192_);
v___x_194_ = v___x_187_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_del_object(v___x_182_);
lean_dec_ref(v_e_x27_177_);
v_a_198_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_184_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_184_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_160_);
lean_dec_ref(v_proof_157_);
lean_dec_ref(v_e_x27_156_);
lean_dec_ref(v___y_124_);
return v___x_162_;
}
}
}
else
{
lean_dec_ref_known(v_a_137_, 2);
lean_dec_ref(v___y_124_);
lean_dec_ref(v___f_122_);
return v___x_136_;
}
}
}
else
{
lean_dec_ref(v___y_124_);
lean_dec_ref(v___f_122_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__1___boxed(lean_object* v___f_209_, lean_object* v_x_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__1(v___f_209_, v_x_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2(lean_object* v___f_223_, lean_object* v_x_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_box(0);
lean_inc_ref(v___y_225_);
v___x_237_ = l_Lean_Meta_Sym_Simp_beta___redArg(v___y_225_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
if (lean_obj_tag(v_a_238_) == 0)
{
uint8_t v_done_239_; 
v_done_239_ = lean_ctor_get_uint8(v_a_238_, 0);
if (v_done_239_ == 0)
{
uint8_t v_contextDependent_240_; lean_object* v___x_241_; 
lean_dec_ref_known(v___x_237_, 1);
v_contextDependent_240_ = lean_ctor_get_uint8(v_a_238_, 1);
lean_dec_ref_known(v_a_238_, 0);
lean_inc(v___y_234_);
lean_inc_ref(v___y_233_);
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
lean_inc(v___y_228_);
lean_inc_ref(v___y_227_);
lean_inc(v___y_226_);
v___x_241_ = lean_apply_12(v___f_223_, v___x_236_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, lean_box(0));
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; uint8_t v___y_244_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_a_242_);
if (v_contextDependent_240_ == 0)
{
lean_dec(v_a_242_);
return v___x_241_;
}
else
{
if (lean_obj_tag(v_a_242_) == 0)
{
uint8_t v_contextDependent_254_; 
v_contextDependent_254_ = lean_ctor_get_uint8(v_a_242_, 1);
v___y_244_ = v_contextDependent_254_;
goto v___jp_243_;
}
else
{
uint8_t v_contextDependent_255_; 
v_contextDependent_255_ = lean_ctor_get_uint8(v_a_242_, sizeof(void*)*2 + 1);
v___y_244_ = v_contextDependent_255_;
goto v___jp_243_;
}
}
v___jp_243_:
{
if (v___y_244_ == 0)
{
lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_252_; 
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v___x_241_, 0);
lean_dec(v_unused_253_);
v___x_246_ = v___x_241_;
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
else
{
lean_dec(v___x_241_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_242_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_dec(v_a_242_);
return v___x_241_;
}
}
}
else
{
return v___x_241_;
}
}
else
{
lean_dec_ref_known(v_a_238_, 0);
lean_dec_ref(v___y_225_);
lean_dec_ref(v___f_223_);
return v___x_237_;
}
}
else
{
uint8_t v_done_256_; 
v_done_256_ = lean_ctor_get_uint8(v_a_238_, sizeof(void*)*2);
if (v_done_256_ == 0)
{
lean_object* v_e_x27_257_; lean_object* v_proof_258_; uint8_t v_contextDependent_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_309_; 
lean_dec_ref_known(v___x_237_, 1);
v_e_x27_257_ = lean_ctor_get(v_a_238_, 0);
v_proof_258_ = lean_ctor_get(v_a_238_, 1);
v_contextDependent_259_ = lean_ctor_get_uint8(v_a_238_, sizeof(void*)*2 + 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v_a_238_);
if (v_isSharedCheck_309_ == 0)
{
v___x_261_ = v_a_238_;
v_isShared_262_ = v_isSharedCheck_309_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_proof_258_);
lean_inc(v_e_x27_257_);
lean_dec(v_a_238_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_309_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; 
lean_inc(v___y_234_);
lean_inc_ref(v___y_233_);
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
lean_inc(v___y_228_);
lean_inc_ref(v___y_227_);
lean_inc(v___y_226_);
lean_inc_ref(v_e_x27_257_);
v___x_263_ = lean_apply_12(v___f_223_, v___x_236_, v_e_x27_257_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, lean_box(0));
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_308_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_308_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_308_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_308_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
if (lean_obj_tag(v_a_264_) == 0)
{
uint8_t v_done_268_; uint8_t v_contextDependent_269_; uint8_t v___y_271_; 
lean_dec_ref(v___y_225_);
v_done_268_ = lean_ctor_get_uint8(v_a_264_, 0);
v_contextDependent_269_ = lean_ctor_get_uint8(v_a_264_, 1);
lean_dec_ref_known(v_a_264_, 0);
if (v_contextDependent_259_ == 0)
{
v___y_271_ = v_contextDependent_269_;
goto v___jp_270_;
}
else
{
v___y_271_ = v_contextDependent_259_;
goto v___jp_270_;
}
v___jp_270_:
{
lean_object* v___x_273_; 
if (v_isShared_262_ == 0)
{
v___x_273_ = v___x_261_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_e_x27_257_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_proof_258_);
v___x_273_ = v_reuseFailAlloc_277_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_275_; 
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*2, v_done_268_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*2 + 1, v___y_271_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_273_);
v___x_275_ = v___x_266_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v_e_x27_278_; lean_object* v_proof_279_; uint8_t v_done_280_; uint8_t v_contextDependent_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_307_; 
lean_del_object(v___x_266_);
lean_del_object(v___x_261_);
v_e_x27_278_ = lean_ctor_get(v_a_264_, 0);
v_proof_279_ = lean_ctor_get(v_a_264_, 1);
v_done_280_ = lean_ctor_get_uint8(v_a_264_, sizeof(void*)*2);
v_contextDependent_281_ = lean_ctor_get_uint8(v_a_264_, sizeof(void*)*2 + 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_a_264_);
if (v_isSharedCheck_307_ == 0)
{
v___x_283_ = v_a_264_;
v_isShared_284_ = v_isSharedCheck_307_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_proof_279_);
lean_inc(v_e_x27_278_);
lean_dec(v_a_264_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_307_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; 
lean_inc_ref(v_e_x27_278_);
v___x_285_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_225_, v_e_x27_257_, v_proof_258_, v_e_x27_278_, v_proof_279_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_298_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_298_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_298_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_298_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
uint8_t v___y_291_; 
if (v_contextDependent_259_ == 0)
{
v___y_291_ = v_contextDependent_281_;
goto v___jp_290_;
}
else
{
v___y_291_ = v_contextDependent_259_;
goto v___jp_290_;
}
v___jp_290_:
{
lean_object* v___x_293_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_a_286_);
v___x_293_ = v___x_283_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_e_x27_278_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_a_286_);
lean_ctor_set_uint8(v_reuseFailAlloc_297_, sizeof(void*)*2, v_done_280_);
v___x_293_ = v_reuseFailAlloc_297_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*2 + 1, v___y_291_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_293_);
v___x_295_ = v___x_288_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_del_object(v___x_283_);
lean_dec_ref(v_e_x27_278_);
v_a_299_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_285_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_285_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_261_);
lean_dec_ref(v_proof_258_);
lean_dec_ref(v_e_x27_257_);
lean_dec_ref(v___y_225_);
return v___x_263_;
}
}
}
else
{
lean_dec_ref_known(v_a_238_, 2);
lean_dec_ref(v___y_225_);
lean_dec_ref(v___f_223_);
return v___x_237_;
}
}
}
else
{
lean_dec_ref(v___y_225_);
lean_dec_ref(v___f_223_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__2___boxed(lean_object* v___f_310_, lean_object* v_x_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__2(v___f_310_, v_x_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3(lean_object* v___f_324_, lean_object* v_x_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_box(0);
lean_inc_ref(v___y_326_);
v___x_338_ = l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
if (lean_obj_tag(v_a_339_) == 0)
{
uint8_t v_done_340_; 
v_done_340_ = lean_ctor_get_uint8(v_a_339_, 0);
if (v_done_340_ == 0)
{
uint8_t v_contextDependent_341_; lean_object* v___x_342_; 
lean_dec_ref_known(v___x_338_, 1);
v_contextDependent_341_ = lean_ctor_get_uint8(v_a_339_, 1);
lean_dec_ref_known(v_a_339_, 0);
lean_inc(v___y_335_);
lean_inc_ref(v___y_334_);
lean_inc(v___y_333_);
lean_inc_ref(v___y_332_);
lean_inc(v___y_331_);
lean_inc_ref(v___y_330_);
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_327_);
v___x_342_ = lean_apply_12(v___f_324_, v___x_337_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, lean_box(0));
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; uint8_t v___y_345_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
if (v_contextDependent_341_ == 0)
{
lean_dec(v_a_343_);
return v___x_342_;
}
else
{
if (lean_obj_tag(v_a_343_) == 0)
{
uint8_t v_contextDependent_355_; 
v_contextDependent_355_ = lean_ctor_get_uint8(v_a_343_, 1);
v___y_345_ = v_contextDependent_355_;
goto v___jp_344_;
}
else
{
uint8_t v_contextDependent_356_; 
v_contextDependent_356_ = lean_ctor_get_uint8(v_a_343_, sizeof(void*)*2 + 1);
v___y_345_ = v_contextDependent_356_;
goto v___jp_344_;
}
}
v___jp_344_:
{
if (v___y_345_ == 0)
{
lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_353_; 
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; 
v_unused_354_ = lean_ctor_get(v___x_342_, 0);
lean_dec(v_unused_354_);
v___x_347_ = v___x_342_;
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
else
{
lean_dec(v___x_342_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_343_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_349_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
else
{
lean_dec(v_a_343_);
return v___x_342_;
}
}
}
else
{
return v___x_342_;
}
}
else
{
lean_dec_ref_known(v_a_339_, 0);
lean_dec_ref(v___y_326_);
lean_dec_ref(v___f_324_);
return v___x_338_;
}
}
else
{
uint8_t v_done_357_; 
v_done_357_ = lean_ctor_get_uint8(v_a_339_, sizeof(void*)*2);
if (v_done_357_ == 0)
{
lean_object* v_e_x27_358_; lean_object* v_proof_359_; uint8_t v_contextDependent_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref_known(v___x_338_, 1);
v_e_x27_358_ = lean_ctor_get(v_a_339_, 0);
v_proof_359_ = lean_ctor_get(v_a_339_, 1);
v_contextDependent_360_ = lean_ctor_get_uint8(v_a_339_, sizeof(void*)*2 + 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_a_339_);
if (v_isSharedCheck_410_ == 0)
{
v___x_362_ = v_a_339_;
v_isShared_363_ = v_isSharedCheck_410_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_proof_359_);
lean_inc(v_e_x27_358_);
lean_dec(v_a_339_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_410_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; 
lean_inc(v___y_335_);
lean_inc_ref(v___y_334_);
lean_inc(v___y_333_);
lean_inc_ref(v___y_332_);
lean_inc(v___y_331_);
lean_inc_ref(v___y_330_);
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_327_);
lean_inc_ref(v_e_x27_358_);
v___x_364_ = lean_apply_12(v___f_324_, v___x_337_, v_e_x27_358_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, lean_box(0));
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_409_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_409_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_409_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_409_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
if (lean_obj_tag(v_a_365_) == 0)
{
uint8_t v_done_369_; uint8_t v_contextDependent_370_; uint8_t v___y_372_; 
lean_dec_ref(v___y_326_);
v_done_369_ = lean_ctor_get_uint8(v_a_365_, 0);
v_contextDependent_370_ = lean_ctor_get_uint8(v_a_365_, 1);
lean_dec_ref_known(v_a_365_, 0);
if (v_contextDependent_360_ == 0)
{
v___y_372_ = v_contextDependent_370_;
goto v___jp_371_;
}
else
{
v___y_372_ = v_contextDependent_360_;
goto v___jp_371_;
}
v___jp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_363_ == 0)
{
v___x_374_ = v___x_362_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_e_x27_358_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_proof_359_);
v___x_374_ = v_reuseFailAlloc_378_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*2, v_done_369_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*2 + 1, v___y_372_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_374_);
v___x_376_ = v___x_367_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v_e_x27_379_; lean_object* v_proof_380_; uint8_t v_done_381_; uint8_t v_contextDependent_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_408_; 
lean_del_object(v___x_367_);
lean_del_object(v___x_362_);
v_e_x27_379_ = lean_ctor_get(v_a_365_, 0);
v_proof_380_ = lean_ctor_get(v_a_365_, 1);
v_done_381_ = lean_ctor_get_uint8(v_a_365_, sizeof(void*)*2);
v_contextDependent_382_ = lean_ctor_get_uint8(v_a_365_, sizeof(void*)*2 + 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v_a_365_);
if (v_isSharedCheck_408_ == 0)
{
v___x_384_ = v_a_365_;
v_isShared_385_ = v_isSharedCheck_408_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_proof_380_);
lean_inc(v_e_x27_379_);
lean_dec(v_a_365_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_408_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; 
lean_inc_ref(v_e_x27_379_);
v___x_386_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_326_, v_e_x27_358_, v_proof_359_, v_e_x27_379_, v_proof_380_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_399_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_399_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint8_t v___y_392_; 
if (v_contextDependent_360_ == 0)
{
v___y_392_ = v_contextDependent_382_;
goto v___jp_391_;
}
else
{
v___y_392_ = v_contextDependent_360_;
goto v___jp_391_;
}
v___jp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 1, v_a_387_);
v___x_394_ = v___x_384_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_e_x27_379_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_a_387_);
lean_ctor_set_uint8(v_reuseFailAlloc_398_, sizeof(void*)*2, v_done_381_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*2 + 1, v___y_392_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_394_);
v___x_396_ = v___x_389_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_del_object(v___x_384_);
lean_dec_ref(v_e_x27_379_);
v_a_400_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_386_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_386_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_362_);
lean_dec_ref(v_proof_359_);
lean_dec_ref(v_e_x27_358_);
lean_dec_ref(v___y_326_);
return v___x_364_;
}
}
}
else
{
lean_dec_ref_known(v_a_339_, 2);
lean_dec_ref(v___y_326_);
lean_dec_ref(v___f_324_);
return v___x_338_;
}
}
}
else
{
lean_dec_ref(v___y_326_);
lean_dec_ref(v___f_324_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__3___boxed(lean_object* v___f_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__3(v___f_411_, v_x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4(lean_object* v___f_425_, lean_object* v_x_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_box(0);
lean_inc_ref(v___y_427_);
v___x_439_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v___y_427_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
if (lean_obj_tag(v_a_440_) == 0)
{
uint8_t v_done_441_; 
v_done_441_ = lean_ctor_get_uint8(v_a_440_, 0);
if (v_done_441_ == 0)
{
uint8_t v_contextDependent_442_; lean_object* v___x_443_; 
lean_dec_ref_known(v___x_439_, 1);
v_contextDependent_442_ = lean_ctor_get_uint8(v_a_440_, 1);
lean_dec_ref_known(v_a_440_, 0);
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
v___x_443_ = lean_apply_12(v___f_425_, v___x_438_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, lean_box(0));
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; uint8_t v___y_446_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
if (v_contextDependent_442_ == 0)
{
lean_dec(v_a_444_);
return v___x_443_;
}
else
{
if (lean_obj_tag(v_a_444_) == 0)
{
uint8_t v_contextDependent_456_; 
v_contextDependent_456_ = lean_ctor_get_uint8(v_a_444_, 1);
v___y_446_ = v_contextDependent_456_;
goto v___jp_445_;
}
else
{
uint8_t v_contextDependent_457_; 
v_contextDependent_457_ = lean_ctor_get_uint8(v_a_444_, sizeof(void*)*2 + 1);
v___y_446_ = v_contextDependent_457_;
goto v___jp_445_;
}
}
v___jp_445_:
{
if (v___y_446_ == 0)
{
lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_454_; 
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_454_ == 0)
{
lean_object* v_unused_455_; 
v_unused_455_ = lean_ctor_get(v___x_443_, 0);
lean_dec(v_unused_455_);
v___x_448_ = v___x_443_;
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
else
{
lean_dec(v___x_443_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_444_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_450_);
v___x_452_ = v___x_448_;
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
else
{
lean_dec(v_a_444_);
return v___x_443_;
}
}
}
else
{
return v___x_443_;
}
}
else
{
lean_dec_ref_known(v_a_440_, 0);
lean_dec_ref(v___y_427_);
lean_dec_ref(v___f_425_);
return v___x_439_;
}
}
else
{
uint8_t v_done_458_; 
v_done_458_ = lean_ctor_get_uint8(v_a_440_, sizeof(void*)*2);
if (v_done_458_ == 0)
{
lean_object* v_e_x27_459_; lean_object* v_proof_460_; uint8_t v_contextDependent_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref_known(v___x_439_, 1);
v_e_x27_459_ = lean_ctor_get(v_a_440_, 0);
v_proof_460_ = lean_ctor_get(v_a_440_, 1);
v_contextDependent_461_ = lean_ctor_get_uint8(v_a_440_, sizeof(void*)*2 + 1);
v_isSharedCheck_511_ = !lean_is_exclusive(v_a_440_);
if (v_isSharedCheck_511_ == 0)
{
v___x_463_ = v_a_440_;
v_isShared_464_ = v_isSharedCheck_511_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_proof_460_);
lean_inc(v_e_x27_459_);
lean_dec(v_a_440_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_511_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; 
lean_inc(v___y_436_);
lean_inc_ref(v___y_435_);
lean_inc(v___y_434_);
lean_inc_ref(v___y_433_);
lean_inc(v___y_432_);
lean_inc_ref(v___y_431_);
lean_inc(v___y_430_);
lean_inc_ref(v___y_429_);
lean_inc(v___y_428_);
lean_inc_ref(v_e_x27_459_);
v___x_465_ = lean_apply_12(v___f_425_, v___x_438_, v_e_x27_459_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, lean_box(0));
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_510_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_510_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_510_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_510_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
if (lean_obj_tag(v_a_466_) == 0)
{
uint8_t v_done_470_; uint8_t v_contextDependent_471_; uint8_t v___y_473_; 
lean_dec_ref(v___y_427_);
v_done_470_ = lean_ctor_get_uint8(v_a_466_, 0);
v_contextDependent_471_ = lean_ctor_get_uint8(v_a_466_, 1);
lean_dec_ref_known(v_a_466_, 0);
if (v_contextDependent_461_ == 0)
{
v___y_473_ = v_contextDependent_471_;
goto v___jp_472_;
}
else
{
v___y_473_ = v_contextDependent_461_;
goto v___jp_472_;
}
v___jp_472_:
{
lean_object* v___x_475_; 
if (v_isShared_464_ == 0)
{
v___x_475_ = v___x_463_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_e_x27_459_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_proof_460_);
v___x_475_ = v_reuseFailAlloc_479_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*2, v_done_470_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*2 + 1, v___y_473_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_475_);
v___x_477_ = v___x_468_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v_e_x27_480_; lean_object* v_proof_481_; uint8_t v_done_482_; uint8_t v_contextDependent_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_509_; 
lean_del_object(v___x_468_);
lean_del_object(v___x_463_);
v_e_x27_480_ = lean_ctor_get(v_a_466_, 0);
v_proof_481_ = lean_ctor_get(v_a_466_, 1);
v_done_482_ = lean_ctor_get_uint8(v_a_466_, sizeof(void*)*2);
v_contextDependent_483_ = lean_ctor_get_uint8(v_a_466_, sizeof(void*)*2 + 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_a_466_);
if (v_isSharedCheck_509_ == 0)
{
v___x_485_ = v_a_466_;
v_isShared_486_ = v_isSharedCheck_509_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_proof_481_);
lean_inc(v_e_x27_480_);
lean_dec(v_a_466_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_509_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; 
lean_inc_ref(v_e_x27_480_);
v___x_487_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_427_, v_e_x27_459_, v_proof_460_, v_e_x27_480_, v_proof_481_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_500_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_500_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_500_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_500_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
uint8_t v___y_493_; 
if (v_contextDependent_461_ == 0)
{
v___y_493_ = v_contextDependent_483_;
goto v___jp_492_;
}
else
{
v___y_493_ = v_contextDependent_461_;
goto v___jp_492_;
}
v___jp_492_:
{
lean_object* v___x_495_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v_a_488_);
v___x_495_ = v___x_485_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_e_x27_480_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_a_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*2, v_done_482_);
v___x_495_ = v_reuseFailAlloc_499_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*2 + 1, v___y_493_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_495_);
v___x_497_ = v___x_490_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_del_object(v___x_485_);
lean_dec_ref(v_e_x27_480_);
v_a_501_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_487_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_487_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_463_);
lean_dec_ref(v_proof_460_);
lean_dec_ref(v_e_x27_459_);
lean_dec_ref(v___y_427_);
return v___x_465_;
}
}
}
else
{
lean_dec_ref_known(v_a_440_, 2);
lean_dec_ref(v___y_427_);
lean_dec_ref(v___f_425_);
return v___x_439_;
}
}
}
else
{
lean_dec_ref(v___y_427_);
lean_dec_ref(v___f_425_);
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__4___boxed(lean_object* v___f_512_, lean_object* v_x_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__4(v___f_512_, v_x_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5(lean_object* v_x_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___x_538_; 
lean_inc_ref(v___y_527_);
v___x_538_ = l_Lean_Meta_Grind_NormSym_simpForall(v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
if (lean_obj_tag(v_a_539_) == 0)
{
uint8_t v_done_540_; 
v_done_540_ = lean_ctor_get_uint8(v_a_539_, 0);
if (v_done_540_ == 0)
{
uint8_t v_contextDependent_541_; lean_object* v___x_542_; 
lean_dec_ref_known(v___x_538_, 1);
v_contextDependent_541_ = lean_ctor_get_uint8(v_a_539_, 1);
lean_dec_ref_known(v_a_539_, 0);
v___x_542_ = l_Lean_Meta_Grind_NormSym_simpExists(v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; uint8_t v___y_545_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
if (v_contextDependent_541_ == 0)
{
return v___x_542_;
}
else
{
if (lean_obj_tag(v_a_543_) == 0)
{
uint8_t v_contextDependent_555_; 
v_contextDependent_555_ = lean_ctor_get_uint8(v_a_543_, 1);
v___y_545_ = v_contextDependent_555_;
goto v___jp_544_;
}
else
{
uint8_t v_contextDependent_556_; 
v_contextDependent_556_ = lean_ctor_get_uint8(v_a_543_, sizeof(void*)*2 + 1);
v___y_545_ = v_contextDependent_556_;
goto v___jp_544_;
}
}
v___jp_544_:
{
if (v___y_545_ == 0)
{
lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_553_; 
lean_inc(v_a_543_);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v___x_542_, 0);
lean_dec(v_unused_554_);
v___x_547_ = v___x_542_;
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
else
{
lean_dec(v___x_542_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_543_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_549_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
else
{
return v___x_542_;
}
}
}
else
{
return v___x_542_;
}
}
else
{
lean_dec_ref_known(v_a_539_, 0);
lean_dec_ref(v___y_527_);
return v___x_538_;
}
}
else
{
uint8_t v_done_557_; 
v_done_557_ = lean_ctor_get_uint8(v_a_539_, sizeof(void*)*2);
if (v_done_557_ == 0)
{
lean_object* v_e_x27_558_; lean_object* v_proof_559_; uint8_t v_contextDependent_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref_known(v___x_538_, 1);
v_e_x27_558_ = lean_ctor_get(v_a_539_, 0);
v_proof_559_ = lean_ctor_get(v_a_539_, 1);
v_contextDependent_560_ = lean_ctor_get_uint8(v_a_539_, sizeof(void*)*2 + 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_a_539_);
if (v_isSharedCheck_610_ == 0)
{
v___x_562_ = v_a_539_;
v_isShared_563_ = v_isSharedCheck_610_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_proof_559_);
lean_inc(v_e_x27_558_);
lean_dec(v_a_539_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_610_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; 
lean_inc_ref(v_e_x27_558_);
v___x_564_ = l_Lean_Meta_Grind_NormSym_simpExists(v_e_x27_558_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_609_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_609_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_609_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_609_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
if (lean_obj_tag(v_a_565_) == 0)
{
uint8_t v_done_569_; uint8_t v_contextDependent_570_; uint8_t v___y_572_; 
lean_dec_ref(v___y_527_);
v_done_569_ = lean_ctor_get_uint8(v_a_565_, 0);
v_contextDependent_570_ = lean_ctor_get_uint8(v_a_565_, 1);
lean_dec_ref_known(v_a_565_, 0);
if (v_contextDependent_560_ == 0)
{
v___y_572_ = v_contextDependent_570_;
goto v___jp_571_;
}
else
{
v___y_572_ = v_contextDependent_560_;
goto v___jp_571_;
}
v___jp_571_:
{
lean_object* v___x_574_; 
if (v_isShared_563_ == 0)
{
v___x_574_ = v___x_562_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_e_x27_558_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_proof_559_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*2, v_done_569_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*2 + 1, v___y_572_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_574_);
v___x_576_ = v___x_567_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_object* v_e_x27_579_; lean_object* v_proof_580_; uint8_t v_done_581_; uint8_t v_contextDependent_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_608_; 
lean_del_object(v___x_567_);
lean_del_object(v___x_562_);
v_e_x27_579_ = lean_ctor_get(v_a_565_, 0);
v_proof_580_ = lean_ctor_get(v_a_565_, 1);
v_done_581_ = lean_ctor_get_uint8(v_a_565_, sizeof(void*)*2);
v_contextDependent_582_ = lean_ctor_get_uint8(v_a_565_, sizeof(void*)*2 + 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v_a_565_);
if (v_isSharedCheck_608_ == 0)
{
v___x_584_ = v_a_565_;
v_isShared_585_ = v_isSharedCheck_608_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_proof_580_);
lean_inc(v_e_x27_579_);
lean_dec(v_a_565_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_608_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; 
lean_inc_ref(v_e_x27_579_);
v___x_586_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_527_, v_e_x27_558_, v_proof_559_, v_e_x27_579_, v_proof_580_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_599_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_599_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_599_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_599_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
uint8_t v___y_592_; 
if (v_contextDependent_560_ == 0)
{
v___y_592_ = v_contextDependent_582_;
goto v___jp_591_;
}
else
{
v___y_592_ = v_contextDependent_560_;
goto v___jp_591_;
}
v___jp_591_:
{
lean_object* v___x_594_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 1, v_a_587_);
v___x_594_ = v___x_584_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_e_x27_579_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_a_587_);
lean_ctor_set_uint8(v_reuseFailAlloc_598_, sizeof(void*)*2, v_done_581_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_596_; 
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*2 + 1, v___y_592_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v___x_594_);
v___x_596_ = v___x_589_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_del_object(v___x_584_);
lean_dec_ref(v_e_x27_579_);
v_a_600_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_586_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_586_);
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
}
}
}
else
{
lean_del_object(v___x_562_);
lean_dec_ref(v_proof_559_);
lean_dec_ref(v_e_x27_558_);
lean_dec_ref(v___y_527_);
return v___x_564_;
}
}
}
else
{
lean_dec_ref_known(v_a_539_, 2);
lean_dec_ref(v___y_527_);
return v___x_538_;
}
}
}
else
{
lean_dec_ref(v___y_527_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed(lean_object* v_x_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__5(v_x_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6(lean_object* v___f_624_, lean_object* v_x_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_box(0);
lean_inc_ref(v___y_626_);
v___x_638_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
if (lean_obj_tag(v_a_639_) == 0)
{
uint8_t v_done_640_; 
v_done_640_ = lean_ctor_get_uint8(v_a_639_, 0);
if (v_done_640_ == 0)
{
uint8_t v_contextDependent_641_; lean_object* v___x_642_; 
lean_dec_ref_known(v___x_638_, 1);
v_contextDependent_641_ = lean_ctor_get_uint8(v_a_639_, 1);
lean_dec_ref_known(v_a_639_, 0);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc(v___y_633_);
lean_inc_ref(v___y_632_);
lean_inc(v___y_631_);
lean_inc_ref(v___y_630_);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc(v___y_627_);
v___x_642_ = lean_apply_12(v___f_624_, v___x_637_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, lean_box(0));
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; uint8_t v___y_645_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
if (v_contextDependent_641_ == 0)
{
lean_dec(v_a_643_);
return v___x_642_;
}
else
{
if (lean_obj_tag(v_a_643_) == 0)
{
uint8_t v_contextDependent_655_; 
v_contextDependent_655_ = lean_ctor_get_uint8(v_a_643_, 1);
v___y_645_ = v_contextDependent_655_;
goto v___jp_644_;
}
else
{
uint8_t v_contextDependent_656_; 
v_contextDependent_656_ = lean_ctor_get_uint8(v_a_643_, sizeof(void*)*2 + 1);
v___y_645_ = v_contextDependent_656_;
goto v___jp_644_;
}
}
v___jp_644_:
{
if (v___y_645_ == 0)
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v___x_642_, 0);
lean_dec(v_unused_654_);
v___x_647_ = v___x_642_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_dec(v___x_642_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_643_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
lean_dec(v_a_643_);
return v___x_642_;
}
}
}
else
{
return v___x_642_;
}
}
else
{
lean_dec_ref_known(v_a_639_, 0);
lean_dec_ref(v___y_626_);
lean_dec_ref(v___f_624_);
return v___x_638_;
}
}
else
{
uint8_t v_done_657_; 
v_done_657_ = lean_ctor_get_uint8(v_a_639_, sizeof(void*)*2);
if (v_done_657_ == 0)
{
lean_object* v_e_x27_658_; lean_object* v_proof_659_; uint8_t v_contextDependent_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref_known(v___x_638_, 1);
v_e_x27_658_ = lean_ctor_get(v_a_639_, 0);
v_proof_659_ = lean_ctor_get(v_a_639_, 1);
v_contextDependent_660_ = lean_ctor_get_uint8(v_a_639_, sizeof(void*)*2 + 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_a_639_);
if (v_isSharedCheck_710_ == 0)
{
v___x_662_ = v_a_639_;
v_isShared_663_ = v_isSharedCheck_710_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_proof_659_);
lean_inc(v_e_x27_658_);
lean_dec(v_a_639_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_710_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; 
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc(v___y_633_);
lean_inc_ref(v___y_632_);
lean_inc(v___y_631_);
lean_inc_ref(v___y_630_);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc(v___y_627_);
lean_inc_ref(v_e_x27_658_);
v___x_664_ = lean_apply_12(v___f_624_, v___x_637_, v_e_x27_658_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, lean_box(0));
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_709_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_709_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_709_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_709_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
if (lean_obj_tag(v_a_665_) == 0)
{
uint8_t v_done_669_; uint8_t v_contextDependent_670_; uint8_t v___y_672_; 
lean_dec_ref(v___y_626_);
v_done_669_ = lean_ctor_get_uint8(v_a_665_, 0);
v_contextDependent_670_ = lean_ctor_get_uint8(v_a_665_, 1);
lean_dec_ref_known(v_a_665_, 0);
if (v_contextDependent_660_ == 0)
{
v___y_672_ = v_contextDependent_670_;
goto v___jp_671_;
}
else
{
v___y_672_ = v_contextDependent_660_;
goto v___jp_671_;
}
v___jp_671_:
{
lean_object* v___x_674_; 
if (v_isShared_663_ == 0)
{
v___x_674_ = v___x_662_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_e_x27_658_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_proof_659_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*2, v_done_669_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*2 + 1, v___y_672_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_674_);
v___x_676_ = v___x_667_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v_e_x27_679_; lean_object* v_proof_680_; uint8_t v_done_681_; uint8_t v_contextDependent_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_708_; 
lean_del_object(v___x_667_);
lean_del_object(v___x_662_);
v_e_x27_679_ = lean_ctor_get(v_a_665_, 0);
v_proof_680_ = lean_ctor_get(v_a_665_, 1);
v_done_681_ = lean_ctor_get_uint8(v_a_665_, sizeof(void*)*2);
v_contextDependent_682_ = lean_ctor_get_uint8(v_a_665_, sizeof(void*)*2 + 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_665_);
if (v_isSharedCheck_708_ == 0)
{
v___x_684_ = v_a_665_;
v_isShared_685_ = v_isSharedCheck_708_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_proof_680_);
lean_inc(v_e_x27_679_);
lean_dec(v_a_665_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_708_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; 
lean_inc_ref(v_e_x27_679_);
v___x_686_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_626_, v_e_x27_658_, v_proof_659_, v_e_x27_679_, v_proof_680_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_699_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_699_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_699_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_699_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
uint8_t v___y_692_; 
if (v_contextDependent_660_ == 0)
{
v___y_692_ = v_contextDependent_682_;
goto v___jp_691_;
}
else
{
v___y_692_ = v_contextDependent_660_;
goto v___jp_691_;
}
v___jp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_a_687_);
v___x_694_ = v___x_684_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_e_x27_679_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_a_687_);
lean_ctor_set_uint8(v_reuseFailAlloc_698_, sizeof(void*)*2, v_done_681_);
v___x_694_ = v_reuseFailAlloc_698_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_696_; 
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*2 + 1, v___y_692_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_694_);
v___x_696_ = v___x_689_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_del_object(v___x_684_);
lean_dec_ref(v_e_x27_679_);
v_a_700_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_686_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_686_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_662_);
lean_dec_ref(v_proof_659_);
lean_dec_ref(v_e_x27_658_);
lean_dec_ref(v___y_626_);
return v___x_664_;
}
}
}
else
{
lean_dec_ref_known(v_a_639_, 2);
lean_dec_ref(v___y_626_);
lean_dec_ref(v___f_624_);
return v___x_638_;
}
}
}
else
{
lean_dec_ref(v___y_626_);
lean_dec_ref(v___f_624_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed(lean_object* v___f_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__6(v___f_711_, v_x_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7(lean_object* v___f_725_, lean_object* v_x_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_box(0);
lean_inc_ref(v___y_727_);
v___x_739_ = l_Lean_Meta_Grind_NormSym_simpDIte(v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
if (lean_obj_tag(v_a_740_) == 0)
{
uint8_t v_done_741_; 
v_done_741_ = lean_ctor_get_uint8(v_a_740_, 0);
if (v_done_741_ == 0)
{
uint8_t v_contextDependent_742_; lean_object* v___x_743_; 
lean_dec_ref_known(v___x_739_, 1);
v_contextDependent_742_ = lean_ctor_get_uint8(v_a_740_, 1);
lean_dec_ref_known(v_a_740_, 0);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
v___x_743_ = lean_apply_12(v___f_725_, v___x_738_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, lean_box(0));
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; uint8_t v___y_746_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
if (v_contextDependent_742_ == 0)
{
lean_dec(v_a_744_);
return v___x_743_;
}
else
{
if (lean_obj_tag(v_a_744_) == 0)
{
uint8_t v_contextDependent_756_; 
v_contextDependent_756_ = lean_ctor_get_uint8(v_a_744_, 1);
v___y_746_ = v_contextDependent_756_;
goto v___jp_745_;
}
else
{
uint8_t v_contextDependent_757_; 
v_contextDependent_757_ = lean_ctor_get_uint8(v_a_744_, sizeof(void*)*2 + 1);
v___y_746_ = v_contextDependent_757_;
goto v___jp_745_;
}
}
v___jp_745_:
{
if (v___y_746_ == 0)
{
lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v___x_743_, 0);
lean_dec(v_unused_755_);
v___x_748_ = v___x_743_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_dec(v___x_743_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_744_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
else
{
lean_dec(v_a_744_);
return v___x_743_;
}
}
}
else
{
return v___x_743_;
}
}
else
{
lean_dec_ref_known(v_a_740_, 0);
lean_dec_ref(v___y_727_);
lean_dec_ref(v___f_725_);
return v___x_739_;
}
}
else
{
uint8_t v_done_758_; 
v_done_758_ = lean_ctor_get_uint8(v_a_740_, sizeof(void*)*2);
if (v_done_758_ == 0)
{
lean_object* v_e_x27_759_; lean_object* v_proof_760_; uint8_t v_contextDependent_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref_known(v___x_739_, 1);
v_e_x27_759_ = lean_ctor_get(v_a_740_, 0);
v_proof_760_ = lean_ctor_get(v_a_740_, 1);
v_contextDependent_761_ = lean_ctor_get_uint8(v_a_740_, sizeof(void*)*2 + 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_a_740_);
if (v_isSharedCheck_811_ == 0)
{
v___x_763_ = v_a_740_;
v_isShared_764_ = v_isSharedCheck_811_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_proof_760_);
lean_inc(v_e_x27_759_);
lean_dec(v_a_740_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_811_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; 
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc(v___y_730_);
lean_inc_ref(v___y_729_);
lean_inc(v___y_728_);
lean_inc_ref(v_e_x27_759_);
v___x_765_ = lean_apply_12(v___f_725_, v___x_738_, v_e_x27_759_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, lean_box(0));
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_810_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_810_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_810_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_810_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
if (lean_obj_tag(v_a_766_) == 0)
{
uint8_t v_done_770_; uint8_t v_contextDependent_771_; uint8_t v___y_773_; 
lean_dec_ref(v___y_727_);
v_done_770_ = lean_ctor_get_uint8(v_a_766_, 0);
v_contextDependent_771_ = lean_ctor_get_uint8(v_a_766_, 1);
lean_dec_ref_known(v_a_766_, 0);
if (v_contextDependent_761_ == 0)
{
v___y_773_ = v_contextDependent_771_;
goto v___jp_772_;
}
else
{
v___y_773_ = v_contextDependent_761_;
goto v___jp_772_;
}
v___jp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_764_ == 0)
{
v___x_775_ = v___x_763_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_e_x27_759_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_proof_760_);
v___x_775_ = v_reuseFailAlloc_779_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*2, v_done_770_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*2 + 1, v___y_773_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_775_);
v___x_777_ = v___x_768_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v_e_x27_780_; lean_object* v_proof_781_; uint8_t v_done_782_; uint8_t v_contextDependent_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_809_; 
lean_del_object(v___x_768_);
lean_del_object(v___x_763_);
v_e_x27_780_ = lean_ctor_get(v_a_766_, 0);
v_proof_781_ = lean_ctor_get(v_a_766_, 1);
v_done_782_ = lean_ctor_get_uint8(v_a_766_, sizeof(void*)*2);
v_contextDependent_783_ = lean_ctor_get_uint8(v_a_766_, sizeof(void*)*2 + 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_a_766_);
if (v_isSharedCheck_809_ == 0)
{
v___x_785_ = v_a_766_;
v_isShared_786_ = v_isSharedCheck_809_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_proof_781_);
lean_inc(v_e_x27_780_);
lean_dec(v_a_766_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_809_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; 
lean_inc_ref(v_e_x27_780_);
v___x_787_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_727_, v_e_x27_759_, v_proof_760_, v_e_x27_780_, v_proof_781_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_800_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_800_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_800_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_800_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
uint8_t v___y_793_; 
if (v_contextDependent_761_ == 0)
{
v___y_793_ = v_contextDependent_783_;
goto v___jp_792_;
}
else
{
v___y_793_ = v_contextDependent_761_;
goto v___jp_792_;
}
v___jp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v_a_788_);
v___x_795_ = v___x_785_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_e_x27_780_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_a_788_);
lean_ctor_set_uint8(v_reuseFailAlloc_799_, sizeof(void*)*2, v_done_782_);
v___x_795_ = v_reuseFailAlloc_799_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_797_; 
lean_ctor_set_uint8(v___x_795_, sizeof(void*)*2 + 1, v___y_793_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_795_);
v___x_797_ = v___x_790_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
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
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_del_object(v___x_785_);
lean_dec_ref(v_e_x27_780_);
v_a_801_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_787_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_787_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_763_);
lean_dec_ref(v_proof_760_);
lean_dec_ref(v_e_x27_759_);
lean_dec_ref(v___y_727_);
return v___x_765_;
}
}
}
else
{
lean_dec_ref_known(v_a_740_, 2);
lean_dec_ref(v___y_727_);
lean_dec_ref(v___f_725_);
return v___x_739_;
}
}
}
else
{
lean_dec_ref(v___y_727_);
lean_dec_ref(v___f_725_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7___boxed(lean_object* v___f_812_, lean_object* v_x_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__7(v___f_812_, v_x_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8(lean_object* v___f_826_, lean_object* v_x_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_box(0);
lean_inc_ref(v___y_828_);
v___x_840_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v___y_828_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
if (lean_obj_tag(v_a_841_) == 0)
{
uint8_t v_done_842_; 
v_done_842_ = lean_ctor_get_uint8(v_a_841_, 0);
if (v_done_842_ == 0)
{
uint8_t v_contextDependent_843_; lean_object* v___x_844_; 
lean_dec_ref_known(v___x_840_, 1);
v_contextDependent_843_ = lean_ctor_get_uint8(v_a_841_, 1);
lean_dec_ref_known(v_a_841_, 0);
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_829_);
v___x_844_ = lean_apply_12(v___f_826_, v___x_839_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, lean_box(0));
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; uint8_t v___y_847_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
if (v_contextDependent_843_ == 0)
{
lean_dec(v_a_845_);
return v___x_844_;
}
else
{
if (lean_obj_tag(v_a_845_) == 0)
{
uint8_t v_contextDependent_857_; 
v_contextDependent_857_ = lean_ctor_get_uint8(v_a_845_, 1);
v___y_847_ = v_contextDependent_857_;
goto v___jp_846_;
}
else
{
uint8_t v_contextDependent_858_; 
v_contextDependent_858_ = lean_ctor_get_uint8(v_a_845_, sizeof(void*)*2 + 1);
v___y_847_ = v_contextDependent_858_;
goto v___jp_846_;
}
}
v___jp_846_:
{
if (v___y_847_ == 0)
{
lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_855_; 
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; 
v_unused_856_ = lean_ctor_get(v___x_844_, 0);
lean_dec(v_unused_856_);
v___x_849_ = v___x_844_;
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
else
{
lean_dec(v___x_844_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_845_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_dec(v_a_845_);
return v___x_844_;
}
}
}
else
{
return v___x_844_;
}
}
else
{
lean_dec_ref_known(v_a_841_, 0);
lean_dec_ref(v___y_828_);
lean_dec_ref(v___f_826_);
return v___x_840_;
}
}
else
{
uint8_t v_done_859_; 
v_done_859_ = lean_ctor_get_uint8(v_a_841_, sizeof(void*)*2);
if (v_done_859_ == 0)
{
lean_object* v_e_x27_860_; lean_object* v_proof_861_; uint8_t v_contextDependent_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref_known(v___x_840_, 1);
v_e_x27_860_ = lean_ctor_get(v_a_841_, 0);
v_proof_861_ = lean_ctor_get(v_a_841_, 1);
v_contextDependent_862_ = lean_ctor_get_uint8(v_a_841_, sizeof(void*)*2 + 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_a_841_);
if (v_isSharedCheck_912_ == 0)
{
v___x_864_ = v_a_841_;
v_isShared_865_ = v_isSharedCheck_912_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_proof_861_);
lean_inc(v_e_x27_860_);
lean_dec(v_a_841_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_912_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; 
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_829_);
lean_inc_ref(v_e_x27_860_);
v___x_866_ = lean_apply_12(v___f_826_, v___x_839_, v_e_x27_860_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, lean_box(0));
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_911_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_911_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_911_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_911_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
if (lean_obj_tag(v_a_867_) == 0)
{
uint8_t v_done_871_; uint8_t v_contextDependent_872_; uint8_t v___y_874_; 
lean_dec_ref(v___y_828_);
v_done_871_ = lean_ctor_get_uint8(v_a_867_, 0);
v_contextDependent_872_ = lean_ctor_get_uint8(v_a_867_, 1);
lean_dec_ref_known(v_a_867_, 0);
if (v_contextDependent_862_ == 0)
{
v___y_874_ = v_contextDependent_872_;
goto v___jp_873_;
}
else
{
v___y_874_ = v_contextDependent_862_;
goto v___jp_873_;
}
v___jp_873_:
{
lean_object* v___x_876_; 
if (v_isShared_865_ == 0)
{
v___x_876_ = v___x_864_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_e_x27_860_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_proof_861_);
v___x_876_ = v_reuseFailAlloc_880_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_878_; 
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*2, v_done_871_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*2 + 1, v___y_874_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_876_);
v___x_878_ = v___x_869_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
lean_object* v_e_x27_881_; lean_object* v_proof_882_; uint8_t v_done_883_; uint8_t v_contextDependent_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_910_; 
lean_del_object(v___x_869_);
lean_del_object(v___x_864_);
v_e_x27_881_ = lean_ctor_get(v_a_867_, 0);
v_proof_882_ = lean_ctor_get(v_a_867_, 1);
v_done_883_ = lean_ctor_get_uint8(v_a_867_, sizeof(void*)*2);
v_contextDependent_884_ = lean_ctor_get_uint8(v_a_867_, sizeof(void*)*2 + 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_a_867_);
if (v_isSharedCheck_910_ == 0)
{
v___x_886_ = v_a_867_;
v_isShared_887_ = v_isSharedCheck_910_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_proof_882_);
lean_inc(v_e_x27_881_);
lean_dec(v_a_867_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_910_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; 
lean_inc_ref(v_e_x27_881_);
v___x_888_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_828_, v_e_x27_860_, v_proof_861_, v_e_x27_881_, v_proof_882_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_901_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_901_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
uint8_t v___y_894_; 
if (v_contextDependent_862_ == 0)
{
v___y_894_ = v_contextDependent_884_;
goto v___jp_893_;
}
else
{
v___y_894_ = v_contextDependent_862_;
goto v___jp_893_;
}
v___jp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v_a_889_);
v___x_896_ = v___x_886_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_e_x27_881_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_a_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_900_, sizeof(void*)*2, v_done_883_);
v___x_896_ = v_reuseFailAlloc_900_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_898_; 
lean_ctor_set_uint8(v___x_896_, sizeof(void*)*2 + 1, v___y_894_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_896_);
v___x_898_ = v___x_891_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
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
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_del_object(v___x_886_);
lean_dec_ref(v_e_x27_881_);
v_a_902_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_888_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_888_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_864_);
lean_dec_ref(v_proof_861_);
lean_dec_ref(v_e_x27_860_);
lean_dec_ref(v___y_828_);
return v___x_866_;
}
}
}
else
{
lean_dec_ref_known(v_a_841_, 2);
lean_dec_ref(v___y_828_);
lean_dec_ref(v___f_826_);
return v___x_840_;
}
}
}
else
{
lean_dec_ref(v___y_828_);
lean_dec_ref(v___f_826_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8___boxed(lean_object* v___f_913_, lean_object* v_x_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__8(v___f_913_, v_x_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9(lean_object* v___f_927_, lean_object* v_x_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_box(0);
lean_inc_ref(v___y_929_);
v___x_941_ = l_Lean_Meta_Grind_NormSym_simpEq(v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
if (lean_obj_tag(v_a_942_) == 0)
{
uint8_t v_done_943_; 
v_done_943_ = lean_ctor_get_uint8(v_a_942_, 0);
if (v_done_943_ == 0)
{
uint8_t v_contextDependent_944_; lean_object* v___x_945_; 
lean_dec_ref_known(v___x_941_, 1);
v_contextDependent_944_ = lean_ctor_get_uint8(v_a_942_, 1);
lean_dec_ref_known(v_a_942_, 0);
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
lean_inc(v___y_932_);
lean_inc_ref(v___y_931_);
lean_inc(v___y_930_);
v___x_945_ = lean_apply_12(v___f_927_, v___x_940_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, lean_box(0));
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; uint8_t v___y_948_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_946_);
if (v_contextDependent_944_ == 0)
{
lean_dec(v_a_946_);
return v___x_945_;
}
else
{
if (lean_obj_tag(v_a_946_) == 0)
{
uint8_t v_contextDependent_958_; 
v_contextDependent_958_ = lean_ctor_get_uint8(v_a_946_, 1);
v___y_948_ = v_contextDependent_958_;
goto v___jp_947_;
}
else
{
uint8_t v_contextDependent_959_; 
v_contextDependent_959_ = lean_ctor_get_uint8(v_a_946_, sizeof(void*)*2 + 1);
v___y_948_ = v_contextDependent_959_;
goto v___jp_947_;
}
}
v___jp_947_:
{
if (v___y_948_ == 0)
{
lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_956_; 
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v___x_945_, 0);
lean_dec(v_unused_957_);
v___x_950_ = v___x_945_;
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
else
{
lean_dec(v___x_945_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_946_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
else
{
lean_dec(v_a_946_);
return v___x_945_;
}
}
}
else
{
return v___x_945_;
}
}
else
{
lean_dec_ref_known(v_a_942_, 0);
lean_dec_ref(v___y_929_);
lean_dec_ref(v___f_927_);
return v___x_941_;
}
}
else
{
uint8_t v_done_960_; 
v_done_960_ = lean_ctor_get_uint8(v_a_942_, sizeof(void*)*2);
if (v_done_960_ == 0)
{
lean_object* v_e_x27_961_; lean_object* v_proof_962_; uint8_t v_contextDependent_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref_known(v___x_941_, 1);
v_e_x27_961_ = lean_ctor_get(v_a_942_, 0);
v_proof_962_ = lean_ctor_get(v_a_942_, 1);
v_contextDependent_963_ = lean_ctor_get_uint8(v_a_942_, sizeof(void*)*2 + 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_a_942_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_965_ = v_a_942_;
v_isShared_966_ = v_isSharedCheck_1013_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_proof_962_);
lean_inc(v_e_x27_961_);
lean_dec(v_a_942_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1013_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; 
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
lean_inc(v___y_934_);
lean_inc_ref(v___y_933_);
lean_inc(v___y_932_);
lean_inc_ref(v___y_931_);
lean_inc(v___y_930_);
lean_inc_ref(v_e_x27_961_);
v___x_967_ = lean_apply_12(v___f_927_, v___x_940_, v_e_x27_961_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, lean_box(0));
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1012_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_1012_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1012_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
if (lean_obj_tag(v_a_968_) == 0)
{
uint8_t v_done_972_; uint8_t v_contextDependent_973_; uint8_t v___y_975_; 
lean_dec_ref(v___y_929_);
v_done_972_ = lean_ctor_get_uint8(v_a_968_, 0);
v_contextDependent_973_ = lean_ctor_get_uint8(v_a_968_, 1);
lean_dec_ref_known(v_a_968_, 0);
if (v_contextDependent_963_ == 0)
{
v___y_975_ = v_contextDependent_973_;
goto v___jp_974_;
}
else
{
v___y_975_ = v_contextDependent_963_;
goto v___jp_974_;
}
v___jp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_966_ == 0)
{
v___x_977_ = v___x_965_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_e_x27_961_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_proof_962_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_979_; 
lean_ctor_set_uint8(v___x_977_, sizeof(void*)*2, v_done_972_);
lean_ctor_set_uint8(v___x_977_, sizeof(void*)*2 + 1, v___y_975_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_977_);
v___x_979_ = v___x_970_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_e_x27_982_; lean_object* v_proof_983_; uint8_t v_done_984_; uint8_t v_contextDependent_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1011_; 
lean_del_object(v___x_970_);
lean_del_object(v___x_965_);
v_e_x27_982_ = lean_ctor_get(v_a_968_, 0);
v_proof_983_ = lean_ctor_get(v_a_968_, 1);
v_done_984_ = lean_ctor_get_uint8(v_a_968_, sizeof(void*)*2);
v_contextDependent_985_ = lean_ctor_get_uint8(v_a_968_, sizeof(void*)*2 + 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_a_968_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_987_ = v_a_968_;
v_isShared_988_ = v_isSharedCheck_1011_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_proof_983_);
lean_inc(v_e_x27_982_);
lean_dec(v_a_968_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1011_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; 
lean_inc_ref(v_e_x27_982_);
v___x_989_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_929_, v_e_x27_961_, v_proof_962_, v_e_x27_982_, v_proof_983_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1002_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1002_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1002_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v___y_995_; 
if (v_contextDependent_963_ == 0)
{
v___y_995_ = v_contextDependent_985_;
goto v___jp_994_;
}
else
{
v___y_995_ = v_contextDependent_963_;
goto v___jp_994_;
}
v___jp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_a_990_);
v___x_997_ = v___x_987_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_e_x27_982_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_a_990_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, sizeof(void*)*2, v_done_984_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
lean_ctor_set_uint8(v___x_997_, sizeof(void*)*2 + 1, v___y_995_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_997_);
v___x_999_ = v___x_992_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_del_object(v___x_987_);
lean_dec_ref(v_e_x27_982_);
v_a_1003_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_989_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_989_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_965_);
lean_dec_ref(v_proof_962_);
lean_dec_ref(v_e_x27_961_);
lean_dec_ref(v___y_929_);
return v___x_967_;
}
}
}
else
{
lean_dec_ref_known(v_a_942_, 2);
lean_dec_ref(v___y_929_);
lean_dec_ref(v___f_927_);
return v___x_941_;
}
}
}
else
{
lean_dec_ref(v___y_929_);
lean_dec_ref(v___f_927_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9___boxed(lean_object* v___f_1014_, lean_object* v_x_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__9(v___f_1014_, v_x_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10(lean_object* v___f_1028_, lean_object* v_x_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_box(0);
lean_inc_ref(v___y_1030_);
v___x_1042_ = l_Lean_Meta_Sym_Simp_simpNatRel___redArg(v___y_1030_, v___y_1034_, v___y_1037_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
if (lean_obj_tag(v_a_1043_) == 0)
{
uint8_t v_done_1044_; 
v_done_1044_ = lean_ctor_get_uint8(v_a_1043_, 0);
if (v_done_1044_ == 0)
{
uint8_t v_contextDependent_1045_; lean_object* v___x_1046_; 
lean_dec_ref_known(v___x_1042_, 1);
v_contextDependent_1045_ = lean_ctor_get_uint8(v_a_1043_, 1);
lean_dec_ref_known(v_a_1043_, 0);
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc_ref(v___y_1034_);
lean_inc(v___y_1033_);
lean_inc_ref(v___y_1032_);
lean_inc(v___y_1031_);
v___x_1046_ = lean_apply_12(v___f_1028_, v___x_1041_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, lean_box(0));
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; uint8_t v___y_1049_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
if (v_contextDependent_1045_ == 0)
{
lean_dec(v_a_1047_);
return v___x_1046_;
}
else
{
if (lean_obj_tag(v_a_1047_) == 0)
{
uint8_t v_contextDependent_1059_; 
v_contextDependent_1059_ = lean_ctor_get_uint8(v_a_1047_, 1);
v___y_1049_ = v_contextDependent_1059_;
goto v___jp_1048_;
}
else
{
uint8_t v_contextDependent_1060_; 
v_contextDependent_1060_ = lean_ctor_get_uint8(v_a_1047_, sizeof(void*)*2 + 1);
v___y_1049_ = v_contextDependent_1060_;
goto v___jp_1048_;
}
}
v___jp_1048_:
{
if (v___y_1049_ == 0)
{
lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v___x_1046_, 0);
lean_dec(v_unused_1058_);
v___x_1051_ = v___x_1046_;
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
else
{
lean_dec(v___x_1046_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1047_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
else
{
lean_dec(v_a_1047_);
return v___x_1046_;
}
}
}
else
{
return v___x_1046_;
}
}
else
{
lean_dec_ref_known(v_a_1043_, 0);
lean_dec_ref(v___y_1030_);
lean_dec_ref(v___f_1028_);
return v___x_1042_;
}
}
else
{
uint8_t v_done_1061_; 
v_done_1061_ = lean_ctor_get_uint8(v_a_1043_, sizeof(void*)*2);
if (v_done_1061_ == 0)
{
lean_object* v_e_x27_1062_; lean_object* v_proof_1063_; uint8_t v_contextDependent_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref_known(v___x_1042_, 1);
v_e_x27_1062_ = lean_ctor_get(v_a_1043_, 0);
v_proof_1063_ = lean_ctor_get(v_a_1043_, 1);
v_contextDependent_1064_ = lean_ctor_get_uint8(v_a_1043_, sizeof(void*)*2 + 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_a_1043_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1066_ = v_a_1043_;
v_isShared_1067_ = v_isSharedCheck_1114_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_proof_1063_);
lean_inc(v_e_x27_1062_);
lean_dec(v_a_1043_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1114_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; 
lean_inc(v___y_1039_);
lean_inc_ref(v___y_1038_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc_ref(v___y_1034_);
lean_inc(v___y_1033_);
lean_inc_ref(v___y_1032_);
lean_inc(v___y_1031_);
lean_inc_ref(v_e_x27_1062_);
v___x_1068_ = lean_apply_12(v___f_1028_, v___x_1041_, v_e_x27_1062_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, lean_box(0));
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1113_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1113_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1113_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
if (lean_obj_tag(v_a_1069_) == 0)
{
uint8_t v_done_1073_; uint8_t v_contextDependent_1074_; uint8_t v___y_1076_; 
lean_dec_ref(v___y_1030_);
v_done_1073_ = lean_ctor_get_uint8(v_a_1069_, 0);
v_contextDependent_1074_ = lean_ctor_get_uint8(v_a_1069_, 1);
lean_dec_ref_known(v_a_1069_, 0);
if (v_contextDependent_1064_ == 0)
{
v___y_1076_ = v_contextDependent_1074_;
goto v___jp_1075_;
}
else
{
v___y_1076_ = v_contextDependent_1064_;
goto v___jp_1075_;
}
v___jp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1067_ == 0)
{
v___x_1078_ = v___x_1066_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_e_x27_1062_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_proof_1063_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
lean_ctor_set_uint8(v___x_1078_, sizeof(void*)*2, v_done_1073_);
lean_ctor_set_uint8(v___x_1078_, sizeof(void*)*2 + 1, v___y_1076_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1078_);
v___x_1080_ = v___x_1071_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v_e_x27_1083_; lean_object* v_proof_1084_; uint8_t v_done_1085_; uint8_t v_contextDependent_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1112_; 
lean_del_object(v___x_1071_);
lean_del_object(v___x_1066_);
v_e_x27_1083_ = lean_ctor_get(v_a_1069_, 0);
v_proof_1084_ = lean_ctor_get(v_a_1069_, 1);
v_done_1085_ = lean_ctor_get_uint8(v_a_1069_, sizeof(void*)*2);
v_contextDependent_1086_ = lean_ctor_get_uint8(v_a_1069_, sizeof(void*)*2 + 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_a_1069_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1088_ = v_a_1069_;
v_isShared_1089_ = v_isSharedCheck_1112_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_proof_1084_);
lean_inc(v_e_x27_1083_);
lean_dec(v_a_1069_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1112_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; 
lean_inc_ref(v_e_x27_1083_);
v___x_1090_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1030_, v_e_x27_1062_, v_proof_1063_, v_e_x27_1083_, v_proof_1084_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1103_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1103_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1103_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
uint8_t v___y_1096_; 
if (v_contextDependent_1064_ == 0)
{
v___y_1096_ = v_contextDependent_1086_;
goto v___jp_1095_;
}
else
{
v___y_1096_ = v_contextDependent_1064_;
goto v___jp_1095_;
}
v___jp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v_a_1091_);
v___x_1098_ = v___x_1088_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_e_x27_1083_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_a_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*2, v_done_1085_);
v___x_1098_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1100_; 
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*2 + 1, v___y_1096_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1098_);
v___x_1100_ = v___x_1093_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_del_object(v___x_1088_);
lean_dec_ref(v_e_x27_1083_);
v_a_1104_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1090_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1090_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1066_);
lean_dec_ref(v_proof_1063_);
lean_dec_ref(v_e_x27_1062_);
lean_dec_ref(v___y_1030_);
return v___x_1068_;
}
}
}
else
{
lean_dec_ref_known(v_a_1043_, 2);
lean_dec_ref(v___y_1030_);
lean_dec_ref(v___f_1028_);
return v___x_1042_;
}
}
}
else
{
lean_dec_ref(v___y_1030_);
lean_dec_ref(v___f_1028_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10___boxed(lean_object* v___f_1115_, lean_object* v_x_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__10(v___f_1115_, v_x_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11(lean_object* v___f_1132_, lean_object* v_x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__11___closed__0));
v___x_1146_ = lean_box(0);
lean_inc_ref(v___y_1134_);
v___x_1147_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_1134_, v___x_1145_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
if (lean_obj_tag(v_a_1148_) == 0)
{
uint8_t v_done_1149_; 
v_done_1149_ = lean_ctor_get_uint8(v_a_1148_, 0);
if (v_done_1149_ == 0)
{
uint8_t v_contextDependent_1150_; lean_object* v___x_1151_; 
lean_dec_ref_known(v___x_1147_, 1);
v_contextDependent_1150_ = lean_ctor_get_uint8(v_a_1148_, 1);
lean_dec_ref_known(v_a_1148_, 0);
lean_inc(v___y_1143_);
lean_inc_ref(v___y_1142_);
lean_inc(v___y_1141_);
lean_inc_ref(v___y_1140_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
v___x_1151_ = lean_apply_12(v___f_1132_, v___x_1146_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, lean_box(0));
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; uint8_t v___y_1154_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
if (v_contextDependent_1150_ == 0)
{
lean_dec(v_a_1152_);
return v___x_1151_;
}
else
{
if (lean_obj_tag(v_a_1152_) == 0)
{
uint8_t v_contextDependent_1164_; 
v_contextDependent_1164_ = lean_ctor_get_uint8(v_a_1152_, 1);
v___y_1154_ = v_contextDependent_1164_;
goto v___jp_1153_;
}
else
{
uint8_t v_contextDependent_1165_; 
v_contextDependent_1165_ = lean_ctor_get_uint8(v_a_1152_, sizeof(void*)*2 + 1);
v___y_1154_ = v_contextDependent_1165_;
goto v___jp_1153_;
}
}
v___jp_1153_:
{
if (v___y_1154_ == 0)
{
lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1162_; 
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v___x_1151_, 0);
lean_dec(v_unused_1163_);
v___x_1156_ = v___x_1151_;
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
else
{
lean_dec(v___x_1151_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1152_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1158_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
else
{
lean_dec(v_a_1152_);
return v___x_1151_;
}
}
}
else
{
return v___x_1151_;
}
}
else
{
lean_dec_ref_known(v_a_1148_, 0);
lean_dec_ref(v___y_1134_);
lean_dec_ref(v___f_1132_);
return v___x_1147_;
}
}
else
{
uint8_t v_done_1166_; 
v_done_1166_ = lean_ctor_get_uint8(v_a_1148_, sizeof(void*)*2);
if (v_done_1166_ == 0)
{
lean_object* v_e_x27_1167_; lean_object* v_proof_1168_; uint8_t v_contextDependent_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref_known(v___x_1147_, 1);
v_e_x27_1167_ = lean_ctor_get(v_a_1148_, 0);
v_proof_1168_ = lean_ctor_get(v_a_1148_, 1);
v_contextDependent_1169_ = lean_ctor_get_uint8(v_a_1148_, sizeof(void*)*2 + 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_a_1148_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1171_ = v_a_1148_;
v_isShared_1172_ = v_isSharedCheck_1219_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_proof_1168_);
lean_inc(v_e_x27_1167_);
lean_dec(v_a_1148_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1219_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; 
lean_inc(v___y_1143_);
lean_inc_ref(v___y_1142_);
lean_inc(v___y_1141_);
lean_inc_ref(v___y_1140_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
lean_inc_ref(v_e_x27_1167_);
v___x_1173_ = lean_apply_12(v___f_1132_, v___x_1146_, v_e_x27_1167_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, lean_box(0));
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1218_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1218_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1218_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
if (lean_obj_tag(v_a_1174_) == 0)
{
uint8_t v_done_1178_; uint8_t v_contextDependent_1179_; uint8_t v___y_1181_; 
lean_dec_ref(v___y_1134_);
v_done_1178_ = lean_ctor_get_uint8(v_a_1174_, 0);
v_contextDependent_1179_ = lean_ctor_get_uint8(v_a_1174_, 1);
lean_dec_ref_known(v_a_1174_, 0);
if (v_contextDependent_1169_ == 0)
{
v___y_1181_ = v_contextDependent_1179_;
goto v___jp_1180_;
}
else
{
v___y_1181_ = v_contextDependent_1169_;
goto v___jp_1180_;
}
v___jp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1172_ == 0)
{
v___x_1183_ = v___x_1171_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_e_x27_1167_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_proof_1168_);
v___x_1183_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1185_; 
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*2, v_done_1178_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*2 + 1, v___y_1181_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1183_);
v___x_1185_ = v___x_1176_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v_e_x27_1188_; lean_object* v_proof_1189_; uint8_t v_done_1190_; uint8_t v_contextDependent_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1217_; 
lean_del_object(v___x_1176_);
lean_del_object(v___x_1171_);
v_e_x27_1188_ = lean_ctor_get(v_a_1174_, 0);
v_proof_1189_ = lean_ctor_get(v_a_1174_, 1);
v_done_1190_ = lean_ctor_get_uint8(v_a_1174_, sizeof(void*)*2);
v_contextDependent_1191_ = lean_ctor_get_uint8(v_a_1174_, sizeof(void*)*2 + 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_a_1174_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1193_ = v_a_1174_;
v_isShared_1194_ = v_isSharedCheck_1217_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_proof_1189_);
lean_inc(v_e_x27_1188_);
lean_dec(v_a_1174_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1217_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; 
lean_inc_ref(v_e_x27_1188_);
v___x_1195_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1134_, v_e_x27_1167_, v_proof_1168_, v_e_x27_1188_, v_proof_1189_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1208_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1208_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1208_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
uint8_t v___y_1201_; 
if (v_contextDependent_1169_ == 0)
{
v___y_1201_ = v_contextDependent_1191_;
goto v___jp_1200_;
}
else
{
v___y_1201_ = v_contextDependent_1169_;
goto v___jp_1200_;
}
v___jp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v_a_1196_);
v___x_1203_ = v___x_1193_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_e_x27_1188_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_a_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1207_, sizeof(void*)*2, v_done_1190_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*2 + 1, v___y_1201_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1203_);
v___x_1205_ = v___x_1198_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_del_object(v___x_1193_);
lean_dec_ref(v_e_x27_1188_);
v_a_1209_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1195_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1195_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1171_);
lean_dec_ref(v_proof_1168_);
lean_dec_ref(v_e_x27_1167_);
lean_dec_ref(v___y_1134_);
return v___x_1173_;
}
}
}
else
{
lean_dec_ref_known(v_a_1148_, 2);
lean_dec_ref(v___y_1134_);
lean_dec_ref(v___f_1132_);
return v___x_1147_;
}
}
}
else
{
lean_dec_ref(v___y_1134_);
lean_dec_ref(v___f_1132_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed(lean_object* v___f_1220_, lean_object* v_x_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__11(v___f_1220_, v_x_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12(lean_object* v_thms_1234_, lean_object* v_d_1235_, lean_object* v_x_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_pre_1248_; lean_object* v___x_1249_; 
v_pre_1248_ = lean_ctor_get(v_thms_1234_, 0);
v___x_1249_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_pre_1248_, v_d_1235_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed(lean_object* v_thms_1250_, lean_object* v_d_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__12(v_thms_1250_, v_d_1251_, v_x_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v_thms_1250_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13(lean_object* v_d_1265_, uint8_t v_distrib_1266_, lean_object* v___f_1267_, lean_object* v_x_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = 1;
v___x_1281_ = lean_box(0);
lean_inc_ref(v___y_1269_);
v___x_1282_ = l_Lean_Meta_Sym_Simp_simpArith(v_d_1265_, v___x_1280_, v_distrib_1266_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
if (lean_obj_tag(v_a_1283_) == 0)
{
uint8_t v_done_1284_; 
v_done_1284_ = lean_ctor_get_uint8(v_a_1283_, 0);
if (v_done_1284_ == 0)
{
uint8_t v_contextDependent_1285_; lean_object* v___x_1286_; 
lean_dec_ref_known(v___x_1282_, 1);
v_contextDependent_1285_ = lean_ctor_get_uint8(v_a_1283_, 1);
lean_dec_ref_known(v_a_1283_, 0);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
lean_inc(v___y_1270_);
v___x_1286_ = lean_apply_12(v___f_1267_, v___x_1281_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, lean_box(0));
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; uint8_t v___y_1289_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
if (v_contextDependent_1285_ == 0)
{
lean_dec(v_a_1287_);
return v___x_1286_;
}
else
{
if (lean_obj_tag(v_a_1287_) == 0)
{
uint8_t v_contextDependent_1299_; 
v_contextDependent_1299_ = lean_ctor_get_uint8(v_a_1287_, 1);
v___y_1289_ = v_contextDependent_1299_;
goto v___jp_1288_;
}
else
{
uint8_t v_contextDependent_1300_; 
v_contextDependent_1300_ = lean_ctor_get_uint8(v_a_1287_, sizeof(void*)*2 + 1);
v___y_1289_ = v_contextDependent_1300_;
goto v___jp_1288_;
}
}
v___jp_1288_:
{
if (v___y_1289_ == 0)
{
lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1297_; 
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v___x_1286_, 0);
lean_dec(v_unused_1298_);
v___x_1291_ = v___x_1286_;
v_isShared_1292_ = v_isSharedCheck_1297_;
goto v_resetjp_1290_;
}
else
{
lean_dec(v___x_1286_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1297_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1293_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1287_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1293_);
v___x_1295_ = v___x_1291_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
else
{
lean_dec(v_a_1287_);
return v___x_1286_;
}
}
}
else
{
return v___x_1286_;
}
}
else
{
lean_dec_ref_known(v_a_1283_, 0);
lean_dec_ref(v___y_1269_);
lean_dec_ref(v___f_1267_);
return v___x_1282_;
}
}
else
{
uint8_t v_done_1301_; 
v_done_1301_ = lean_ctor_get_uint8(v_a_1283_, sizeof(void*)*2);
if (v_done_1301_ == 0)
{
lean_object* v_e_x27_1302_; lean_object* v_proof_1303_; uint8_t v_contextDependent_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1354_; 
lean_dec_ref_known(v___x_1282_, 1);
v_e_x27_1302_ = lean_ctor_get(v_a_1283_, 0);
v_proof_1303_ = lean_ctor_get(v_a_1283_, 1);
v_contextDependent_1304_ = lean_ctor_get_uint8(v_a_1283_, sizeof(void*)*2 + 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_a_1283_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1306_ = v_a_1283_;
v_isShared_1307_ = v_isSharedCheck_1354_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_proof_1303_);
lean_inc(v_e_x27_1302_);
lean_dec(v_a_1283_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1354_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; 
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
lean_inc(v___y_1270_);
lean_inc_ref(v_e_x27_1302_);
v___x_1308_ = lean_apply_12(v___f_1267_, v___x_1281_, v_e_x27_1302_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, lean_box(0));
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1353_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1353_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1353_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
if (lean_obj_tag(v_a_1309_) == 0)
{
uint8_t v_done_1313_; uint8_t v_contextDependent_1314_; uint8_t v___y_1316_; 
lean_dec_ref(v___y_1269_);
v_done_1313_ = lean_ctor_get_uint8(v_a_1309_, 0);
v_contextDependent_1314_ = lean_ctor_get_uint8(v_a_1309_, 1);
lean_dec_ref_known(v_a_1309_, 0);
if (v_contextDependent_1304_ == 0)
{
v___y_1316_ = v_contextDependent_1314_;
goto v___jp_1315_;
}
else
{
v___y_1316_ = v_contextDependent_1304_;
goto v___jp_1315_;
}
v___jp_1315_:
{
lean_object* v___x_1318_; 
if (v_isShared_1307_ == 0)
{
v___x_1318_ = v___x_1306_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_e_x27_1302_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_proof_1303_);
v___x_1318_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1320_; 
lean_ctor_set_uint8(v___x_1318_, sizeof(void*)*2, v_done_1313_);
lean_ctor_set_uint8(v___x_1318_, sizeof(void*)*2 + 1, v___y_1316_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1318_);
v___x_1320_ = v___x_1311_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
else
{
lean_object* v_e_x27_1323_; lean_object* v_proof_1324_; uint8_t v_done_1325_; uint8_t v_contextDependent_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1352_; 
lean_del_object(v___x_1311_);
lean_del_object(v___x_1306_);
v_e_x27_1323_ = lean_ctor_get(v_a_1309_, 0);
v_proof_1324_ = lean_ctor_get(v_a_1309_, 1);
v_done_1325_ = lean_ctor_get_uint8(v_a_1309_, sizeof(void*)*2);
v_contextDependent_1326_ = lean_ctor_get_uint8(v_a_1309_, sizeof(void*)*2 + 1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_a_1309_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1328_ = v_a_1309_;
v_isShared_1329_ = v_isSharedCheck_1352_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_proof_1324_);
lean_inc(v_e_x27_1323_);
lean_dec(v_a_1309_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1352_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; 
lean_inc_ref(v_e_x27_1323_);
v___x_1330_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1269_, v_e_x27_1302_, v_proof_1303_, v_e_x27_1323_, v_proof_1324_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1343_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1343_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1343_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
uint8_t v___y_1336_; 
if (v_contextDependent_1304_ == 0)
{
v___y_1336_ = v_contextDependent_1326_;
goto v___jp_1335_;
}
else
{
v___y_1336_ = v_contextDependent_1304_;
goto v___jp_1335_;
}
v___jp_1335_:
{
lean_object* v___x_1338_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 1, v_a_1331_);
v___x_1338_ = v___x_1328_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_e_x27_1323_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_a_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*2, v_done_1325_);
v___x_1338_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1340_; 
lean_ctor_set_uint8(v___x_1338_, sizeof(void*)*2 + 1, v___y_1336_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1338_);
v___x_1340_ = v___x_1333_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_del_object(v___x_1328_);
lean_dec_ref(v_e_x27_1323_);
v_a_1344_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1330_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1330_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1306_);
lean_dec_ref(v_proof_1303_);
lean_dec_ref(v_e_x27_1302_);
lean_dec_ref(v___y_1269_);
return v___x_1308_;
}
}
}
else
{
lean_dec_ref_known(v_a_1283_, 2);
lean_dec_ref(v___y_1269_);
lean_dec_ref(v___f_1267_);
return v___x_1282_;
}
}
}
else
{
lean_dec_ref(v___y_1269_);
lean_dec_ref(v___f_1267_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed(lean_object* v_d_1355_, lean_object* v_distrib_1356_, lean_object* v___f_1357_, lean_object* v_x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v_distrib_boxed_1370_; lean_object* v_res_1371_; 
v_distrib_boxed_1370_ = lean_unbox(v_distrib_1356_);
v_res_1371_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__13(v_d_1355_, v_distrib_boxed_1370_, v___f_1357_, v_x_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14(lean_object* v___f_1372_, lean_object* v_x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = lean_box(0);
lean_inc_ref(v___y_1374_);
v___x_1386_ = l_Lean_Meta_Grind_NormSym_pushNot(v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
if (lean_obj_tag(v_a_1387_) == 0)
{
uint8_t v_done_1388_; 
v_done_1388_ = lean_ctor_get_uint8(v_a_1387_, 0);
if (v_done_1388_ == 0)
{
uint8_t v_contextDependent_1389_; lean_object* v___x_1390_; 
lean_dec_ref_known(v___x_1386_, 1);
v_contextDependent_1389_ = lean_ctor_get_uint8(v_a_1387_, 1);
lean_dec_ref_known(v_a_1387_, 0);
lean_inc(v___y_1383_);
lean_inc_ref(v___y_1382_);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
lean_inc(v___y_1379_);
lean_inc_ref(v___y_1378_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
v___x_1390_ = lean_apply_12(v___f_1372_, v___x_1385_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, lean_box(0));
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; uint8_t v___y_1393_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
if (v_contextDependent_1389_ == 0)
{
lean_dec(v_a_1391_);
return v___x_1390_;
}
else
{
if (lean_obj_tag(v_a_1391_) == 0)
{
uint8_t v_contextDependent_1403_; 
v_contextDependent_1403_ = lean_ctor_get_uint8(v_a_1391_, 1);
v___y_1393_ = v_contextDependent_1403_;
goto v___jp_1392_;
}
else
{
uint8_t v_contextDependent_1404_; 
v_contextDependent_1404_ = lean_ctor_get_uint8(v_a_1391_, sizeof(void*)*2 + 1);
v___y_1393_ = v_contextDependent_1404_;
goto v___jp_1392_;
}
}
v___jp_1392_:
{
if (v___y_1393_ == 0)
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1401_; 
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v___x_1390_, 0);
lean_dec(v_unused_1402_);
v___x_1395_ = v___x_1390_;
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v___x_1390_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1391_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
else
{
lean_dec(v_a_1391_);
return v___x_1390_;
}
}
}
else
{
return v___x_1390_;
}
}
else
{
lean_dec_ref_known(v_a_1387_, 0);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___f_1372_);
return v___x_1386_;
}
}
else
{
uint8_t v_done_1405_; 
v_done_1405_ = lean_ctor_get_uint8(v_a_1387_, sizeof(void*)*2);
if (v_done_1405_ == 0)
{
lean_object* v_e_x27_1406_; lean_object* v_proof_1407_; uint8_t v_contextDependent_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref_known(v___x_1386_, 1);
v_e_x27_1406_ = lean_ctor_get(v_a_1387_, 0);
v_proof_1407_ = lean_ctor_get(v_a_1387_, 1);
v_contextDependent_1408_ = lean_ctor_get_uint8(v_a_1387_, sizeof(void*)*2 + 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_a_1387_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1410_ = v_a_1387_;
v_isShared_1411_ = v_isSharedCheck_1458_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_proof_1407_);
lean_inc(v_e_x27_1406_);
lean_dec(v_a_1387_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1458_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; 
lean_inc(v___y_1383_);
lean_inc_ref(v___y_1382_);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
lean_inc(v___y_1379_);
lean_inc_ref(v___y_1378_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc_ref(v_e_x27_1406_);
v___x_1412_ = lean_apply_12(v___f_1372_, v___x_1385_, v_e_x27_1406_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, lean_box(0));
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1457_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1457_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1457_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
if (lean_obj_tag(v_a_1413_) == 0)
{
uint8_t v_done_1417_; uint8_t v_contextDependent_1418_; uint8_t v___y_1420_; 
lean_dec_ref(v___y_1374_);
v_done_1417_ = lean_ctor_get_uint8(v_a_1413_, 0);
v_contextDependent_1418_ = lean_ctor_get_uint8(v_a_1413_, 1);
lean_dec_ref_known(v_a_1413_, 0);
if (v_contextDependent_1408_ == 0)
{
v___y_1420_ = v_contextDependent_1418_;
goto v___jp_1419_;
}
else
{
v___y_1420_ = v_contextDependent_1408_;
goto v___jp_1419_;
}
v___jp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1411_ == 0)
{
v___x_1422_ = v___x_1410_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_e_x27_1406_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_proof_1407_);
v___x_1422_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1424_; 
lean_ctor_set_uint8(v___x_1422_, sizeof(void*)*2, v_done_1417_);
lean_ctor_set_uint8(v___x_1422_, sizeof(void*)*2 + 1, v___y_1420_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1422_);
v___x_1424_ = v___x_1415_;
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
}
else
{
lean_object* v_e_x27_1427_; lean_object* v_proof_1428_; uint8_t v_done_1429_; uint8_t v_contextDependent_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1456_; 
lean_del_object(v___x_1415_);
lean_del_object(v___x_1410_);
v_e_x27_1427_ = lean_ctor_get(v_a_1413_, 0);
v_proof_1428_ = lean_ctor_get(v_a_1413_, 1);
v_done_1429_ = lean_ctor_get_uint8(v_a_1413_, sizeof(void*)*2);
v_contextDependent_1430_ = lean_ctor_get_uint8(v_a_1413_, sizeof(void*)*2 + 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_a_1413_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1432_ = v_a_1413_;
v_isShared_1433_ = v_isSharedCheck_1456_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_proof_1428_);
lean_inc(v_e_x27_1427_);
lean_dec(v_a_1413_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1456_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; 
lean_inc_ref(v_e_x27_1427_);
v___x_1434_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1374_, v_e_x27_1406_, v_proof_1407_, v_e_x27_1427_, v_proof_1428_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1447_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1447_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1447_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
uint8_t v___y_1440_; 
if (v_contextDependent_1408_ == 0)
{
v___y_1440_ = v_contextDependent_1430_;
goto v___jp_1439_;
}
else
{
v___y_1440_ = v_contextDependent_1408_;
goto v___jp_1439_;
}
v___jp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v_a_1435_);
v___x_1442_ = v___x_1432_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_e_x27_1427_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_a_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1446_, sizeof(void*)*2, v_done_1429_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
lean_ctor_set_uint8(v___x_1442_, sizeof(void*)*2 + 1, v___y_1440_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1442_);
v___x_1444_ = v___x_1437_;
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
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_del_object(v___x_1432_);
lean_dec_ref(v_e_x27_1427_);
v_a_1448_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1434_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1434_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1410_);
lean_dec_ref(v_proof_1407_);
lean_dec_ref(v_e_x27_1406_);
lean_dec_ref(v___y_1374_);
return v___x_1412_;
}
}
}
else
{
lean_dec_ref_known(v_a_1387_, 2);
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___f_1372_);
return v___x_1386_;
}
}
}
else
{
lean_dec_ref(v___y_1374_);
lean_dec_ref(v___f_1372_);
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed(lean_object* v___f_1459_, lean_object* v_x_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__14(v___f_1459_, v_x_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15(lean_object* v_pre_1473_, lean_object* v___f_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_box(0);
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1483_);
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1481_);
lean_inc(v___y_1480_);
lean_inc_ref(v___y_1479_);
lean_inc(v___y_1478_);
lean_inc_ref(v___y_1477_);
lean_inc(v___y_1476_);
lean_inc_ref(v___y_1475_);
v___x_1487_ = lean_apply_11(v_pre_1473_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, lean_box(0));
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
if (lean_obj_tag(v_a_1488_) == 0)
{
uint8_t v_done_1489_; 
v_done_1489_ = lean_ctor_get_uint8(v_a_1488_, 0);
if (v_done_1489_ == 0)
{
uint8_t v_contextDependent_1490_; lean_object* v___x_1491_; 
lean_dec_ref_known(v___x_1487_, 1);
v_contextDependent_1490_ = lean_ctor_get_uint8(v_a_1488_, 1);
lean_dec_ref_known(v_a_1488_, 0);
v___x_1491_ = lean_apply_12(v___f_1474_, v___x_1486_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, lean_box(0));
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; uint8_t v___y_1494_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
if (v_contextDependent_1490_ == 0)
{
lean_dec(v_a_1492_);
return v___x_1491_;
}
else
{
if (lean_obj_tag(v_a_1492_) == 0)
{
uint8_t v_contextDependent_1504_; 
v_contextDependent_1504_ = lean_ctor_get_uint8(v_a_1492_, 1);
v___y_1494_ = v_contextDependent_1504_;
goto v___jp_1493_;
}
else
{
uint8_t v_contextDependent_1505_; 
v_contextDependent_1505_ = lean_ctor_get_uint8(v_a_1492_, sizeof(void*)*2 + 1);
v___y_1494_ = v_contextDependent_1505_;
goto v___jp_1493_;
}
}
v___jp_1493_:
{
if (v___y_1494_ == 0)
{
lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1502_; 
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v___x_1491_, 0);
lean_dec(v_unused_1503_);
v___x_1496_ = v___x_1491_;
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
else
{
lean_dec(v___x_1491_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1492_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1498_);
v___x_1500_ = v___x_1496_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
else
{
lean_dec(v_a_1492_);
return v___x_1491_;
}
}
}
else
{
return v___x_1491_;
}
}
else
{
lean_dec_ref_known(v_a_1488_, 0);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec_ref(v___f_1474_);
return v___x_1487_;
}
}
else
{
uint8_t v_done_1506_; 
v_done_1506_ = lean_ctor_get_uint8(v_a_1488_, sizeof(void*)*2);
if (v_done_1506_ == 0)
{
lean_object* v_e_x27_1507_; lean_object* v_proof_1508_; uint8_t v_contextDependent_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref_known(v___x_1487_, 1);
v_e_x27_1507_ = lean_ctor_get(v_a_1488_, 0);
v_proof_1508_ = lean_ctor_get(v_a_1488_, 1);
v_contextDependent_1509_ = lean_ctor_get_uint8(v_a_1488_, sizeof(void*)*2 + 1);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_a_1488_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1511_ = v_a_1488_;
v_isShared_1512_ = v_isSharedCheck_1559_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_proof_1508_);
lean_inc(v_e_x27_1507_);
lean_dec(v_a_1488_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1559_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; 
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1483_);
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1481_);
lean_inc(v___y_1480_);
lean_inc_ref(v___y_1479_);
lean_inc_ref(v_e_x27_1507_);
v___x_1513_ = lean_apply_12(v___f_1474_, v___x_1486_, v_e_x27_1507_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, lean_box(0));
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1558_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1558_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1558_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
if (lean_obj_tag(v_a_1514_) == 0)
{
uint8_t v_done_1518_; uint8_t v_contextDependent_1519_; uint8_t v___y_1521_; 
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec_ref(v___y_1475_);
v_done_1518_ = lean_ctor_get_uint8(v_a_1514_, 0);
v_contextDependent_1519_ = lean_ctor_get_uint8(v_a_1514_, 1);
lean_dec_ref_known(v_a_1514_, 0);
if (v_contextDependent_1509_ == 0)
{
v___y_1521_ = v_contextDependent_1519_;
goto v___jp_1520_;
}
else
{
v___y_1521_ = v_contextDependent_1509_;
goto v___jp_1520_;
}
v___jp_1520_:
{
lean_object* v___x_1523_; 
if (v_isShared_1512_ == 0)
{
v___x_1523_ = v___x_1511_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_e_x27_1507_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_proof_1508_);
v___x_1523_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1525_; 
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*2, v_done_1518_);
lean_ctor_set_uint8(v___x_1523_, sizeof(void*)*2 + 1, v___y_1521_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1523_);
v___x_1525_ = v___x_1516_;
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
}
else
{
lean_object* v_e_x27_1528_; lean_object* v_proof_1529_; uint8_t v_done_1530_; uint8_t v_contextDependent_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1557_; 
lean_del_object(v___x_1516_);
lean_del_object(v___x_1511_);
v_e_x27_1528_ = lean_ctor_get(v_a_1514_, 0);
v_proof_1529_ = lean_ctor_get(v_a_1514_, 1);
v_done_1530_ = lean_ctor_get_uint8(v_a_1514_, sizeof(void*)*2);
v_contextDependent_1531_ = lean_ctor_get_uint8(v_a_1514_, sizeof(void*)*2 + 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_a_1514_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1533_ = v_a_1514_;
v_isShared_1534_ = v_isSharedCheck_1557_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_proof_1529_);
lean_inc(v_e_x27_1528_);
lean_dec(v_a_1514_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1557_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; 
lean_inc_ref(v_e_x27_1528_);
v___x_1535_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1475_, v_e_x27_1507_, v_proof_1508_, v_e_x27_1528_, v_proof_1529_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1548_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1548_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1548_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
uint8_t v___y_1541_; 
if (v_contextDependent_1509_ == 0)
{
v___y_1541_ = v_contextDependent_1531_;
goto v___jp_1540_;
}
else
{
v___y_1541_ = v_contextDependent_1509_;
goto v___jp_1540_;
}
v___jp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v_a_1536_);
v___x_1543_ = v___x_1533_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_e_x27_1528_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_a_1536_);
lean_ctor_set_uint8(v_reuseFailAlloc_1547_, sizeof(void*)*2, v_done_1530_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*2 + 1, v___y_1541_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1543_);
v___x_1545_ = v___x_1538_;
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
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_del_object(v___x_1533_);
lean_dec_ref(v_e_x27_1528_);
v_a_1549_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1535_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1535_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1511_);
lean_dec_ref(v_proof_1508_);
lean_dec_ref(v_e_x27_1507_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec_ref(v___y_1475_);
return v___x_1513_;
}
}
}
else
{
lean_dec_ref_known(v_a_1488_, 2);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec_ref(v___f_1474_);
return v___x_1487_;
}
}
}
else
{
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec_ref(v___f_1474_);
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed(lean_object* v_pre_1560_, lean_object* v___f_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__15(v_pre_1560_, v___f_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16(lean_object* v_post_1574_, lean_object* v_d_1575_, lean_object* v___f_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_box(0);
lean_inc_ref(v___y_1577_);
v___x_1589_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_post_1574_, v_d_1575_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
if (lean_obj_tag(v_a_1590_) == 0)
{
uint8_t v_done_1591_; 
v_done_1591_ = lean_ctor_get_uint8(v_a_1590_, 0);
if (v_done_1591_ == 0)
{
uint8_t v_contextDependent_1592_; lean_object* v___x_1593_; 
lean_dec_ref_known(v___x_1589_, 1);
v_contextDependent_1592_ = lean_ctor_get_uint8(v_a_1590_, 1);
lean_dec_ref_known(v_a_1590_, 0);
v___x_1593_ = lean_apply_12(v___f_1576_, v___x_1588_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, lean_box(0));
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; uint8_t v___y_1596_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
if (v_contextDependent_1592_ == 0)
{
lean_dec(v_a_1594_);
return v___x_1593_;
}
else
{
if (lean_obj_tag(v_a_1594_) == 0)
{
uint8_t v_contextDependent_1606_; 
v_contextDependent_1606_ = lean_ctor_get_uint8(v_a_1594_, 1);
v___y_1596_ = v_contextDependent_1606_;
goto v___jp_1595_;
}
else
{
uint8_t v_contextDependent_1607_; 
v_contextDependent_1607_ = lean_ctor_get_uint8(v_a_1594_, sizeof(void*)*2 + 1);
v___y_1596_ = v_contextDependent_1607_;
goto v___jp_1595_;
}
}
v___jp_1595_:
{
if (v___y_1596_ == 0)
{
lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1604_; 
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; 
v_unused_1605_ = lean_ctor_get(v___x_1593_, 0);
lean_dec(v_unused_1605_);
v___x_1598_ = v___x_1593_;
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
else
{
lean_dec(v___x_1593_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1600_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1594_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1600_);
v___x_1602_ = v___x_1598_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
else
{
lean_dec(v_a_1594_);
return v___x_1593_;
}
}
}
else
{
return v___x_1593_;
}
}
else
{
lean_dec_ref_known(v_a_1590_, 0);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec_ref(v___f_1576_);
return v___x_1589_;
}
}
else
{
uint8_t v_done_1608_; 
v_done_1608_ = lean_ctor_get_uint8(v_a_1590_, sizeof(void*)*2);
if (v_done_1608_ == 0)
{
lean_object* v_e_x27_1609_; lean_object* v_proof_1610_; uint8_t v_contextDependent_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref_known(v___x_1589_, 1);
v_e_x27_1609_ = lean_ctor_get(v_a_1590_, 0);
v_proof_1610_ = lean_ctor_get(v_a_1590_, 1);
v_contextDependent_1611_ = lean_ctor_get_uint8(v_a_1590_, sizeof(void*)*2 + 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_a_1590_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1613_ = v_a_1590_;
v_isShared_1614_ = v_isSharedCheck_1661_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_proof_1610_);
lean_inc(v_e_x27_1609_);
lean_dec(v_a_1590_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1661_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; 
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
lean_inc(v___y_1584_);
lean_inc_ref(v___y_1583_);
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1581_);
lean_inc_ref(v_e_x27_1609_);
v___x_1615_ = lean_apply_12(v___f_1576_, v___x_1588_, v_e_x27_1609_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, lean_box(0));
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1660_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1660_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1660_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
if (lean_obj_tag(v_a_1616_) == 0)
{
uint8_t v_done_1620_; uint8_t v_contextDependent_1621_; uint8_t v___y_1623_; 
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec_ref(v___y_1577_);
v_done_1620_ = lean_ctor_get_uint8(v_a_1616_, 0);
v_contextDependent_1621_ = lean_ctor_get_uint8(v_a_1616_, 1);
lean_dec_ref_known(v_a_1616_, 0);
if (v_contextDependent_1611_ == 0)
{
v___y_1623_ = v_contextDependent_1621_;
goto v___jp_1622_;
}
else
{
v___y_1623_ = v_contextDependent_1611_;
goto v___jp_1622_;
}
v___jp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1614_ == 0)
{
v___x_1625_ = v___x_1613_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_e_x27_1609_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_proof_1610_);
v___x_1625_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1627_; 
lean_ctor_set_uint8(v___x_1625_, sizeof(void*)*2, v_done_1620_);
lean_ctor_set_uint8(v___x_1625_, sizeof(void*)*2 + 1, v___y_1623_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1625_);
v___x_1627_ = v___x_1618_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_e_x27_1630_; lean_object* v_proof_1631_; uint8_t v_done_1632_; uint8_t v_contextDependent_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1659_; 
lean_del_object(v___x_1618_);
lean_del_object(v___x_1613_);
v_e_x27_1630_ = lean_ctor_get(v_a_1616_, 0);
v_proof_1631_ = lean_ctor_get(v_a_1616_, 1);
v_done_1632_ = lean_ctor_get_uint8(v_a_1616_, sizeof(void*)*2);
v_contextDependent_1633_ = lean_ctor_get_uint8(v_a_1616_, sizeof(void*)*2 + 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_a_1616_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1635_ = v_a_1616_;
v_isShared_1636_ = v_isSharedCheck_1659_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_proof_1631_);
lean_inc(v_e_x27_1630_);
lean_dec(v_a_1616_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1659_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; 
lean_inc_ref(v_e_x27_1630_);
v___x_1637_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1577_, v_e_x27_1609_, v_proof_1610_, v_e_x27_1630_, v_proof_1631_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1650_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1650_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1650_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
uint8_t v___y_1643_; 
if (v_contextDependent_1611_ == 0)
{
v___y_1643_ = v_contextDependent_1633_;
goto v___jp_1642_;
}
else
{
v___y_1643_ = v_contextDependent_1611_;
goto v___jp_1642_;
}
v___jp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 1, v_a_1638_);
v___x_1645_ = v___x_1635_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_e_x27_1630_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_a_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1649_, sizeof(void*)*2, v_done_1632_);
v___x_1645_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1647_; 
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*2 + 1, v___y_1643_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1645_);
v___x_1647_ = v___x_1640_;
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
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_del_object(v___x_1635_);
lean_dec_ref(v_e_x27_1630_);
v_a_1651_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1637_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1637_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1613_);
lean_dec_ref(v_proof_1610_);
lean_dec_ref(v_e_x27_1609_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec_ref(v___y_1577_);
return v___x_1615_;
}
}
}
else
{
lean_dec_ref_known(v_a_1590_, 2);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec_ref(v___f_1576_);
return v___x_1589_;
}
}
}
else
{
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec_ref(v___f_1576_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed(lean_object* v_post_1662_, lean_object* v_d_1663_, lean_object* v___f_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__16(v_post_1662_, v_d_1663_, v___f_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec_ref(v_post_1662_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17(lean_object* v_pre_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; 
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc_ref(v___y_1678_);
v___x_1689_ = lean_apply_11(v_pre_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, lean_box(0));
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
if (lean_obj_tag(v_a_1690_) == 0)
{
uint8_t v_done_1691_; 
v_done_1691_ = lean_ctor_get_uint8(v_a_1690_, 0);
if (v_done_1691_ == 0)
{
uint8_t v_contextDependent_1692_; lean_object* v___x_1693_; 
lean_dec_ref_known(v___x_1689_, 1);
v_contextDependent_1692_ = lean_ctor_get_uint8(v_a_1690_, 1);
lean_dec_ref_known(v_a_1690_, 0);
v___x_1693_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v___y_1678_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; uint8_t v___y_1696_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
if (v_contextDependent_1692_ == 0)
{
return v___x_1693_;
}
else
{
if (lean_obj_tag(v_a_1694_) == 0)
{
uint8_t v_contextDependent_1706_; 
v_contextDependent_1706_ = lean_ctor_get_uint8(v_a_1694_, 1);
v___y_1696_ = v_contextDependent_1706_;
goto v___jp_1695_;
}
else
{
uint8_t v_contextDependent_1707_; 
v_contextDependent_1707_ = lean_ctor_get_uint8(v_a_1694_, sizeof(void*)*2 + 1);
v___y_1696_ = v_contextDependent_1707_;
goto v___jp_1695_;
}
}
v___jp_1695_:
{
if (v___y_1696_ == 0)
{
lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1704_; 
lean_inc(v_a_1694_);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; 
v_unused_1705_ = lean_ctor_get(v___x_1693_, 0);
lean_dec(v_unused_1705_);
v___x_1698_ = v___x_1693_;
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
else
{
lean_dec(v___x_1693_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1694_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1700_);
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
else
{
return v___x_1693_;
}
}
}
else
{
return v___x_1693_;
}
}
else
{
lean_dec_ref_known(v_a_1690_, 0);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v___y_1678_);
return v___x_1689_;
}
}
else
{
uint8_t v_done_1708_; 
v_done_1708_ = lean_ctor_get_uint8(v_a_1690_, sizeof(void*)*2);
if (v_done_1708_ == 0)
{
lean_object* v_e_x27_1709_; lean_object* v_proof_1710_; uint8_t v_contextDependent_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref_known(v___x_1689_, 1);
v_e_x27_1709_ = lean_ctor_get(v_a_1690_, 0);
v_proof_1710_ = lean_ctor_get(v_a_1690_, 1);
v_contextDependent_1711_ = lean_ctor_get_uint8(v_a_1690_, sizeof(void*)*2 + 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_a_1690_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1713_ = v_a_1690_;
v_isShared_1714_ = v_isSharedCheck_1761_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_proof_1710_);
lean_inc(v_e_x27_1709_);
lean_dec(v_a_1690_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1761_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; 
lean_inc_ref(v_e_x27_1709_);
v___x_1715_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v_e_x27_1709_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1760_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1760_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1760_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
if (lean_obj_tag(v_a_1716_) == 0)
{
uint8_t v_done_1720_; uint8_t v_contextDependent_1721_; uint8_t v___y_1723_; 
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v___y_1678_);
v_done_1720_ = lean_ctor_get_uint8(v_a_1716_, 0);
v_contextDependent_1721_ = lean_ctor_get_uint8(v_a_1716_, 1);
lean_dec_ref_known(v_a_1716_, 0);
if (v_contextDependent_1711_ == 0)
{
v___y_1723_ = v_contextDependent_1721_;
goto v___jp_1722_;
}
else
{
v___y_1723_ = v_contextDependent_1711_;
goto v___jp_1722_;
}
v___jp_1722_:
{
lean_object* v___x_1725_; 
if (v_isShared_1714_ == 0)
{
v___x_1725_ = v___x_1713_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_e_x27_1709_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_proof_1710_);
v___x_1725_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1727_; 
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*2, v_done_1720_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*2 + 1, v___y_1723_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1725_);
v___x_1727_ = v___x_1718_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_object* v_e_x27_1730_; lean_object* v_proof_1731_; uint8_t v_done_1732_; uint8_t v_contextDependent_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1759_; 
lean_del_object(v___x_1718_);
lean_del_object(v___x_1713_);
v_e_x27_1730_ = lean_ctor_get(v_a_1716_, 0);
v_proof_1731_ = lean_ctor_get(v_a_1716_, 1);
v_done_1732_ = lean_ctor_get_uint8(v_a_1716_, sizeof(void*)*2);
v_contextDependent_1733_ = lean_ctor_get_uint8(v_a_1716_, sizeof(void*)*2 + 1);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_a_1716_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1735_ = v_a_1716_;
v_isShared_1736_ = v_isSharedCheck_1759_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_proof_1731_);
lean_inc(v_e_x27_1730_);
lean_dec(v_a_1716_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1759_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; 
lean_inc_ref(v_e_x27_1730_);
v___x_1737_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1678_, v_e_x27_1709_, v_proof_1710_, v_e_x27_1730_, v_proof_1731_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1750_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1750_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1750_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
uint8_t v___y_1743_; 
if (v_contextDependent_1711_ == 0)
{
v___y_1743_ = v_contextDependent_1733_;
goto v___jp_1742_;
}
else
{
v___y_1743_ = v_contextDependent_1711_;
goto v___jp_1742_;
}
v___jp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 1, v_a_1738_);
v___x_1745_ = v___x_1735_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_e_x27_1730_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_a_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1749_, sizeof(void*)*2, v_done_1732_);
v___x_1745_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1747_; 
lean_ctor_set_uint8(v___x_1745_, sizeof(void*)*2 + 1, v___y_1743_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1745_);
v___x_1747_ = v___x_1740_;
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
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_del_object(v___x_1735_);
lean_dec_ref(v_e_x27_1730_);
v_a_1751_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1737_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1737_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1713_);
lean_dec_ref(v_proof_1710_);
lean_dec_ref(v_e_x27_1709_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v___y_1678_);
return v___x_1715_;
}
}
}
else
{
lean_dec_ref_known(v_a_1690_, 2);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v___y_1678_);
return v___x_1689_;
}
}
}
else
{
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v___y_1678_);
return v___x_1689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed(lean_object* v_pre_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__17(v_pre_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18(lean_object* v___f_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_box(0);
lean_inc_ref(v___y_1776_);
v___x_1788_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_1776_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
if (lean_obj_tag(v_a_1789_) == 0)
{
uint8_t v_done_1790_; 
v_done_1790_ = lean_ctor_get_uint8(v_a_1789_, 0);
if (v_done_1790_ == 0)
{
uint8_t v_contextDependent_1791_; lean_object* v___x_1792_; 
lean_dec_ref_known(v___x_1788_, 1);
v_contextDependent_1791_ = lean_ctor_get_uint8(v_a_1789_, 1);
lean_dec_ref_known(v_a_1789_, 0);
v___x_1792_ = lean_apply_12(v___f_1775_, v___x_1787_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, lean_box(0));
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; uint8_t v___y_1795_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
if (v_contextDependent_1791_ == 0)
{
lean_dec(v_a_1793_);
return v___x_1792_;
}
else
{
if (lean_obj_tag(v_a_1793_) == 0)
{
uint8_t v_contextDependent_1805_; 
v_contextDependent_1805_ = lean_ctor_get_uint8(v_a_1793_, 1);
v___y_1795_ = v_contextDependent_1805_;
goto v___jp_1794_;
}
else
{
uint8_t v_contextDependent_1806_; 
v_contextDependent_1806_ = lean_ctor_get_uint8(v_a_1793_, sizeof(void*)*2 + 1);
v___y_1795_ = v_contextDependent_1806_;
goto v___jp_1794_;
}
}
v___jp_1794_:
{
if (v___y_1795_ == 0)
{
lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1803_; 
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1803_ == 0)
{
lean_object* v_unused_1804_; 
v_unused_1804_ = lean_ctor_get(v___x_1792_, 0);
lean_dec(v_unused_1804_);
v___x_1797_ = v___x_1792_;
v_isShared_1798_ = v_isSharedCheck_1803_;
goto v_resetjp_1796_;
}
else
{
lean_dec(v___x_1792_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1803_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1799_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1793_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1799_);
v___x_1801_ = v___x_1797_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
else
{
lean_dec(v_a_1793_);
return v___x_1792_;
}
}
}
else
{
return v___x_1792_;
}
}
else
{
lean_dec_ref_known(v_a_1789_, 0);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___f_1775_);
return v___x_1788_;
}
}
else
{
uint8_t v_done_1807_; 
v_done_1807_ = lean_ctor_get_uint8(v_a_1789_, sizeof(void*)*2);
if (v_done_1807_ == 0)
{
lean_object* v_e_x27_1808_; lean_object* v_proof_1809_; uint8_t v_contextDependent_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref_known(v___x_1788_, 1);
v_e_x27_1808_ = lean_ctor_get(v_a_1789_, 0);
v_proof_1809_ = lean_ctor_get(v_a_1789_, 1);
v_contextDependent_1810_ = lean_ctor_get_uint8(v_a_1789_, sizeof(void*)*2 + 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_a_1789_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1812_ = v_a_1789_;
v_isShared_1813_ = v_isSharedCheck_1860_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_proof_1809_);
lean_inc(v_e_x27_1808_);
lean_dec(v_a_1789_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1860_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; 
lean_inc(v___y_1785_);
lean_inc_ref(v___y_1784_);
lean_inc(v___y_1783_);
lean_inc_ref(v___y_1782_);
lean_inc(v___y_1781_);
lean_inc_ref(v___y_1780_);
lean_inc_ref(v_e_x27_1808_);
v___x_1814_ = lean_apply_12(v___f_1775_, v___x_1787_, v_e_x27_1808_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, lean_box(0));
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1859_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1859_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1859_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
if (lean_obj_tag(v_a_1815_) == 0)
{
uint8_t v_done_1819_; uint8_t v_contextDependent_1820_; uint8_t v___y_1822_; 
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1776_);
v_done_1819_ = lean_ctor_get_uint8(v_a_1815_, 0);
v_contextDependent_1820_ = lean_ctor_get_uint8(v_a_1815_, 1);
lean_dec_ref_known(v_a_1815_, 0);
if (v_contextDependent_1810_ == 0)
{
v___y_1822_ = v_contextDependent_1820_;
goto v___jp_1821_;
}
else
{
v___y_1822_ = v_contextDependent_1810_;
goto v___jp_1821_;
}
v___jp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1813_ == 0)
{
v___x_1824_ = v___x_1812_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_e_x27_1808_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_proof_1809_);
v___x_1824_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
lean_ctor_set_uint8(v___x_1824_, sizeof(void*)*2, v_done_1819_);
lean_ctor_set_uint8(v___x_1824_, sizeof(void*)*2 + 1, v___y_1822_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1824_);
v___x_1826_ = v___x_1817_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
else
{
lean_object* v_e_x27_1829_; lean_object* v_proof_1830_; uint8_t v_done_1831_; uint8_t v_contextDependent_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1858_; 
lean_del_object(v___x_1817_);
lean_del_object(v___x_1812_);
v_e_x27_1829_ = lean_ctor_get(v_a_1815_, 0);
v_proof_1830_ = lean_ctor_get(v_a_1815_, 1);
v_done_1831_ = lean_ctor_get_uint8(v_a_1815_, sizeof(void*)*2);
v_contextDependent_1832_ = lean_ctor_get_uint8(v_a_1815_, sizeof(void*)*2 + 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_a_1815_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1834_ = v_a_1815_;
v_isShared_1835_ = v_isSharedCheck_1858_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_proof_1830_);
lean_inc(v_e_x27_1829_);
lean_dec(v_a_1815_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1858_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; 
lean_inc_ref(v_e_x27_1829_);
v___x_1836_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1776_, v_e_x27_1808_, v_proof_1809_, v_e_x27_1829_, v_proof_1830_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1849_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1849_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1849_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
uint8_t v___y_1842_; 
if (v_contextDependent_1810_ == 0)
{
v___y_1842_ = v_contextDependent_1832_;
goto v___jp_1841_;
}
else
{
v___y_1842_ = v_contextDependent_1810_;
goto v___jp_1841_;
}
v___jp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v_a_1837_);
v___x_1844_ = v___x_1834_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_e_x27_1829_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_a_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1848_, sizeof(void*)*2, v_done_1831_);
v___x_1844_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
lean_ctor_set_uint8(v___x_1844_, sizeof(void*)*2 + 1, v___y_1842_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1844_);
v___x_1846_ = v___x_1839_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_del_object(v___x_1834_);
lean_dec_ref(v_e_x27_1829_);
v_a_1850_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1836_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1836_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1812_);
lean_dec_ref(v_proof_1809_);
lean_dec_ref(v_e_x27_1808_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1776_);
return v___x_1814_;
}
}
}
else
{
lean_dec_ref_known(v_a_1789_, 2);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___f_1775_);
return v___x_1788_;
}
}
}
else
{
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___f_1775_);
return v___x_1788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18___boxed(lean_object* v___f_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__18(v___f_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__19(lean_object* v___f_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___y_1887_; lean_object* v___y_1888_; uint8_t v___y_1889_; lean_object* v___y_1893_; uint8_t v___y_1894_; lean_object* v___y_1895_; uint8_t v___y_1896_; lean_object* v___y_1900_; uint8_t v___y_1901_; lean_object* v___y_1902_; uint8_t v___y_1903_; lean_object* v___y_1907_; lean_object* v_e_x27_1908_; lean_object* v_proof_1909_; uint8_t v_done_1910_; uint8_t v_contextDependent_1911_; lean_object* v___y_1933_; lean_object* v_a_1934_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_box(0);
lean_inc_ref(v___y_1875_);
v___x_1946_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_1875_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
if (lean_obj_tag(v_a_1947_) == 0)
{
uint8_t v_done_1948_; 
v_done_1948_ = lean_ctor_get_uint8(v_a_1947_, 0);
if (v_done_1948_ == 0)
{
uint8_t v_contextDependent_1949_; lean_object* v___x_1950_; 
lean_dec_ref_known(v___x_1946_, 1);
v_contextDependent_1949_ = lean_ctor_get_uint8(v_a_1947_, 1);
lean_dec_ref_known(v_a_1947_, 0);
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1883_);
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1881_);
lean_inc(v___y_1880_);
lean_inc_ref(v___y_1879_);
lean_inc_ref(v___y_1875_);
v___x_1950_ = lean_apply_12(v___f_1874_, v___x_1945_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, lean_box(0));
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; uint8_t v___y_1953_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
if (v_contextDependent_1949_ == 0)
{
v___y_1933_ = v___x_1950_;
v_a_1934_ = v_a_1951_;
goto v___jp_1932_;
}
else
{
if (lean_obj_tag(v_a_1951_) == 0)
{
uint8_t v_contextDependent_1963_; 
v_contextDependent_1963_ = lean_ctor_get_uint8(v_a_1951_, 1);
v___y_1953_ = v_contextDependent_1963_;
goto v___jp_1952_;
}
else
{
uint8_t v_contextDependent_1964_; 
v_contextDependent_1964_ = lean_ctor_get_uint8(v_a_1951_, sizeof(void*)*2 + 1);
v___y_1953_ = v_contextDependent_1964_;
goto v___jp_1952_;
}
}
v___jp_1952_:
{
if (v___y_1953_ == 0)
{
lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1961_; 
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v___x_1950_, 0);
lean_dec(v_unused_1962_);
v___x_1955_ = v___x_1950_;
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
else
{
lean_dec(v___x_1950_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1957_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1951_);
lean_inc_ref(v___x_1957_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 0, v___x_1957_);
v___x_1959_ = v___x_1955_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
v___y_1933_ = v___x_1959_;
v_a_1934_ = v___x_1957_;
goto v___jp_1932_;
}
}
}
else
{
v___y_1933_ = v___x_1950_;
v_a_1934_ = v_a_1951_;
goto v___jp_1932_;
}
}
}
else
{
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec_ref(v___y_1875_);
return v___x_1950_;
}
}
else
{
lean_dec_ref_known(v_a_1947_, 0);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v___f_1874_);
return v___x_1946_;
}
}
else
{
uint8_t v_done_1965_; 
v_done_1965_ = lean_ctor_get_uint8(v_a_1947_, sizeof(void*)*2);
if (v_done_1965_ == 0)
{
lean_object* v_e_x27_1966_; lean_object* v_proof_1967_; uint8_t v_contextDependent_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref_known(v___x_1946_, 1);
v_e_x27_1966_ = lean_ctor_get(v_a_1947_, 0);
v_proof_1967_ = lean_ctor_get(v_a_1947_, 1);
v_contextDependent_1968_ = lean_ctor_get_uint8(v_a_1947_, sizeof(void*)*2 + 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_a_1947_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1970_ = v_a_1947_;
v_isShared_1971_ = v_isSharedCheck_2018_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_proof_1967_);
lean_inc(v_e_x27_1966_);
lean_dec(v_a_1947_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2018_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; 
lean_inc(v___y_1884_);
lean_inc_ref(v___y_1883_);
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1881_);
lean_inc(v___y_1880_);
lean_inc_ref(v___y_1879_);
lean_inc_ref(v_e_x27_1966_);
v___x_1972_ = lean_apply_12(v___f_1874_, v___x_1945_, v_e_x27_1966_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, lean_box(0));
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2017_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_2017_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2017_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
if (lean_obj_tag(v_a_1973_) == 0)
{
uint8_t v_done_1977_; uint8_t v_contextDependent_1978_; uint8_t v___y_1980_; 
v_done_1977_ = lean_ctor_get_uint8(v_a_1973_, 0);
v_contextDependent_1978_ = lean_ctor_get_uint8(v_a_1973_, 1);
lean_dec_ref_known(v_a_1973_, 0);
if (v_contextDependent_1968_ == 0)
{
v___y_1980_ = v_contextDependent_1978_;
goto v___jp_1979_;
}
else
{
v___y_1980_ = v_contextDependent_1968_;
goto v___jp_1979_;
}
v___jp_1979_:
{
lean_object* v___x_1982_; 
lean_inc_ref(v_proof_1967_);
lean_inc_ref(v_e_x27_1966_);
if (v_isShared_1971_ == 0)
{
v___x_1982_ = v___x_1970_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_e_x27_1966_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_proof_1967_);
v___x_1982_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1984_; 
lean_ctor_set_uint8(v___x_1982_, sizeof(void*)*2, v_done_1977_);
lean_ctor_set_uint8(v___x_1982_, sizeof(void*)*2 + 1, v___y_1980_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1982_);
v___x_1984_ = v___x_1975_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
v___y_1907_ = v___x_1984_;
v_e_x27_1908_ = v_e_x27_1966_;
v_proof_1909_ = v_proof_1967_;
v_done_1910_ = v_done_1977_;
v_contextDependent_1911_ = v___y_1980_;
goto v___jp_1906_;
}
}
}
}
else
{
lean_object* v_e_x27_1987_; lean_object* v_proof_1988_; uint8_t v_done_1989_; uint8_t v_contextDependent_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2016_; 
lean_del_object(v___x_1975_);
lean_del_object(v___x_1970_);
v_e_x27_1987_ = lean_ctor_get(v_a_1973_, 0);
v_proof_1988_ = lean_ctor_get(v_a_1973_, 1);
v_done_1989_ = lean_ctor_get_uint8(v_a_1973_, sizeof(void*)*2);
v_contextDependent_1990_ = lean_ctor_get_uint8(v_a_1973_, sizeof(void*)*2 + 1);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_a_1973_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1992_ = v_a_1973_;
v_isShared_1993_ = v_isSharedCheck_2016_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_proof_1988_);
lean_inc(v_e_x27_1987_);
lean_dec(v_a_1973_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2016_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; 
lean_inc_ref(v_e_x27_1987_);
lean_inc_ref(v___y_1875_);
v___x_1994_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1875_, v_e_x27_1966_, v_proof_1967_, v_e_x27_1987_, v_proof_1988_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2007_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2007_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2007_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
uint8_t v___y_2000_; 
if (v_contextDependent_1968_ == 0)
{
v___y_2000_ = v_contextDependent_1990_;
goto v___jp_1999_;
}
else
{
v___y_2000_ = v_contextDependent_1968_;
goto v___jp_1999_;
}
v___jp_1999_:
{
lean_object* v___x_2002_; 
lean_inc(v_a_1995_);
lean_inc_ref(v_e_x27_1987_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v_a_1995_);
v___x_2002_ = v___x_1992_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_e_x27_1987_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_a_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*2, v_done_1989_);
v___x_2002_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2004_; 
lean_ctor_set_uint8(v___x_2002_, sizeof(void*)*2 + 1, v___y_2000_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2002_);
v___x_2004_ = v___x_1997_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
v___y_1907_ = v___x_2004_;
v_e_x27_1908_ = v_e_x27_1987_;
v_proof_1909_ = v_a_1995_;
v_done_1910_ = v_done_1989_;
v_contextDependent_1911_ = v___y_2000_;
goto v___jp_1906_;
}
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_del_object(v___x_1992_);
lean_dec_ref(v_e_x27_1987_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec_ref(v___y_1875_);
v_a_2008_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1994_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1994_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1970_);
lean_dec_ref(v_proof_1967_);
lean_dec_ref(v_e_x27_1966_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec_ref(v___y_1875_);
return v___x_1972_;
}
}
}
else
{
lean_dec_ref_known(v_a_1947_, 2);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v___f_1874_);
return v___x_1946_;
}
}
}
else
{
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v___f_1874_);
return v___x_1946_;
}
v___jp_1886_:
{
if (v___y_1889_ == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec_ref(v___y_1888_);
v___x_1890_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1887_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
else
{
lean_dec_ref(v___y_1887_);
return v___y_1888_;
}
}
v___jp_1892_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1897_, 0, v___y_1895_);
lean_ctor_set(v___x_1897_, 1, v___y_1893_);
lean_ctor_set_uint8(v___x_1897_, sizeof(void*)*2, v___y_1894_);
lean_ctor_set_uint8(v___x_1897_, sizeof(void*)*2 + 1, v___y_1896_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
v___jp_1899_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1904_, 0, v___y_1900_);
lean_ctor_set(v___x_1904_, 1, v___y_1902_);
lean_ctor_set_uint8(v___x_1904_, sizeof(void*)*2, v___y_1901_);
lean_ctor_set_uint8(v___x_1904_, sizeof(void*)*2 + 1, v___y_1903_);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
v___jp_1906_:
{
if (v_done_1910_ == 0)
{
lean_object* v___x_1912_; 
lean_dec_ref(v___y_1907_);
lean_inc_ref(v_e_x27_1908_);
v___x_1912_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v_e_x27_1908_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
if (lean_obj_tag(v_a_1913_) == 0)
{
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec_ref(v___y_1875_);
if (v_contextDependent_1911_ == 0)
{
uint8_t v_done_1914_; uint8_t v_contextDependent_1915_; 
v_done_1914_ = lean_ctor_get_uint8(v_a_1913_, 0);
v_contextDependent_1915_ = lean_ctor_get_uint8(v_a_1913_, 1);
lean_dec_ref_known(v_a_1913_, 0);
v___y_1900_ = v_e_x27_1908_;
v___y_1901_ = v_done_1914_;
v___y_1902_ = v_proof_1909_;
v___y_1903_ = v_contextDependent_1915_;
goto v___jp_1899_;
}
else
{
uint8_t v_done_1916_; 
v_done_1916_ = lean_ctor_get_uint8(v_a_1913_, 0);
lean_dec_ref_known(v_a_1913_, 0);
v___y_1900_ = v_e_x27_1908_;
v___y_1901_ = v_done_1916_;
v___y_1902_ = v_proof_1909_;
v___y_1903_ = v_contextDependent_1911_;
goto v___jp_1899_;
}
}
else
{
lean_object* v_e_x27_1917_; lean_object* v_proof_1918_; uint8_t v_done_1919_; uint8_t v_contextDependent_1920_; lean_object* v___x_1921_; 
v_e_x27_1917_ = lean_ctor_get(v_a_1913_, 0);
lean_inc_ref_n(v_e_x27_1917_, 2);
v_proof_1918_ = lean_ctor_get(v_a_1913_, 1);
lean_inc_ref(v_proof_1918_);
v_done_1919_ = lean_ctor_get_uint8(v_a_1913_, sizeof(void*)*2);
v_contextDependent_1920_ = lean_ctor_get_uint8(v_a_1913_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1913_, 2);
v___x_1921_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1875_, v_e_x27_1908_, v_proof_1909_, v_e_x27_1917_, v_proof_1918_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
if (lean_obj_tag(v___x_1921_) == 0)
{
if (v_contextDependent_1911_ == 0)
{
lean_object* v_a_1922_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___y_1893_ = v_a_1922_;
v___y_1894_ = v_done_1919_;
v___y_1895_ = v_e_x27_1917_;
v___y_1896_ = v_contextDependent_1920_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1923_; 
v_a_1923_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1921_, 1);
v___y_1893_ = v_a_1923_;
v___y_1894_ = v_done_1919_;
v___y_1895_ = v_e_x27_1917_;
v___y_1896_ = v_contextDependent_1911_;
goto v___jp_1892_;
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec_ref(v_e_x27_1917_);
v_a_1924_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1921_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1921_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_1909_);
lean_dec_ref(v_e_x27_1908_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec_ref(v___y_1875_);
return v___x_1912_;
}
}
else
{
lean_dec_ref(v_proof_1909_);
lean_dec_ref(v_e_x27_1908_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec_ref(v___y_1875_);
return v___y_1907_;
}
}
v___jp_1932_:
{
if (lean_obj_tag(v_a_1934_) == 0)
{
uint8_t v_done_1935_; 
v_done_1935_ = lean_ctor_get_uint8(v_a_1934_, 0);
if (v_done_1935_ == 0)
{
uint8_t v_contextDependent_1936_; lean_object* v___x_1937_; 
lean_dec_ref(v___y_1933_);
v_contextDependent_1936_ = lean_ctor_get_uint8(v_a_1934_, 1);
lean_dec_ref_known(v_a_1934_, 0);
v___x_1937_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v___y_1875_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
if (lean_obj_tag(v___x_1937_) == 0)
{
if (v_contextDependent_1936_ == 0)
{
return v___x_1937_;
}
else
{
lean_object* v_a_1938_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
if (lean_obj_tag(v_a_1938_) == 0)
{
uint8_t v_contextDependent_1939_; 
v_contextDependent_1939_ = lean_ctor_get_uint8(v_a_1938_, 1);
v___y_1887_ = v_a_1938_;
v___y_1888_ = v___x_1937_;
v___y_1889_ = v_contextDependent_1939_;
goto v___jp_1886_;
}
else
{
uint8_t v_contextDependent_1940_; 
v_contextDependent_1940_ = lean_ctor_get_uint8(v_a_1938_, sizeof(void*)*2 + 1);
v___y_1887_ = v_a_1938_;
v___y_1888_ = v___x_1937_;
v___y_1889_ = v_contextDependent_1940_;
goto v___jp_1886_;
}
}
}
else
{
return v___x_1937_;
}
}
else
{
lean_dec_ref_known(v_a_1934_, 0);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec_ref(v___y_1875_);
return v___y_1933_;
}
}
else
{
lean_object* v_e_x27_1941_; lean_object* v_proof_1942_; uint8_t v_done_1943_; uint8_t v_contextDependent_1944_; 
v_e_x27_1941_ = lean_ctor_get(v_a_1934_, 0);
lean_inc_ref(v_e_x27_1941_);
v_proof_1942_ = lean_ctor_get(v_a_1934_, 1);
lean_inc_ref(v_proof_1942_);
v_done_1943_ = lean_ctor_get_uint8(v_a_1934_, sizeof(void*)*2);
v_contextDependent_1944_ = lean_ctor_get_uint8(v_a_1934_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1934_, 2);
v___y_1907_ = v___y_1933_;
v_e_x27_1908_ = v_e_x27_1941_;
v_proof_1909_ = v_proof_1942_;
v_done_1910_ = v_done_1943_;
v_contextDependent_1911_ = v_contextDependent_1944_;
goto v___jp_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__19___boxed(lean_object* v___f_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__19(v___f_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object* v_config_2059_, lean_object* v_thms_2060_){
_start:
{
uint8_t v_zetaDelta_2061_; uint8_t v_zeta_2062_; uint8_t v_distrib_2063_; lean_object* v___f_2064_; lean_object* v_d_2065_; lean_object* v___f_2066_; lean_object* v___x_2067_; lean_object* v___f_2068_; lean_object* v___f_2069_; lean_object* v_pre_2071_; lean_object* v_pre_2077_; 
v_zetaDelta_2061_ = lean_ctor_get_uint8(v_config_2059_, sizeof(void*)*14 + 19);
v_zeta_2062_ = lean_ctor_get_uint8(v_config_2059_, sizeof(void*)*14 + 20);
v_distrib_2063_ = lean_ctor_get_uint8(v_config_2059_, sizeof(void*)*14 + 21);
v___f_2064_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__11));
v_d_2065_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__12));
lean_inc_ref(v_thms_2060_);
v___f_2066_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed), 14, 2);
lean_closure_set(v___f_2066_, 0, v_thms_2060_);
lean_closure_set(v___f_2066_, 1, v_d_2065_);
v___x_2067_ = lean_box(v_distrib_2063_);
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed), 15, 3);
lean_closure_set(v___f_2068_, 0, v_d_2065_);
lean_closure_set(v___f_2068_, 1, v___x_2067_);
lean_closure_set(v___f_2068_, 2, v___f_2066_);
v___f_2069_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed), 13, 1);
lean_closure_set(v___f_2069_, 0, v___f_2068_);
if (v_zeta_2062_ == 0)
{
lean_object* v_pre_2079_; 
v_pre_2079_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__13));
v_pre_2077_ = v_pre_2079_;
goto v___jp_2076_;
}
else
{
lean_object* v_pre_2080_; 
v_pre_2080_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__14));
v_pre_2077_ = v_pre_2080_;
goto v___jp_2076_;
}
v___jp_2070_:
{
lean_object* v_post_2072_; lean_object* v_pre_2073_; lean_object* v_post_2074_; lean_object* v___x_2075_; 
v_post_2072_ = lean_ctor_get(v_thms_2060_, 1);
lean_inc_ref(v_post_2072_);
lean_dec_ref(v_thms_2060_);
v_pre_2073_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed), 13, 2);
lean_closure_set(v_pre_2073_, 0, v_pre_2071_);
lean_closure_set(v_pre_2073_, 1, v___f_2069_);
v_post_2074_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed), 14, 3);
lean_closure_set(v_post_2074_, 0, v_post_2072_);
lean_closure_set(v_post_2074_, 1, v_d_2065_);
lean_closure_set(v_post_2074_, 2, v___f_2064_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_pre_2073_);
lean_ctor_set(v___x_2075_, 1, v_post_2074_);
return v___x_2075_;
}
v___jp_2076_:
{
if (v_zetaDelta_2061_ == 0)
{
lean_inc_ref(v_pre_2077_);
v_pre_2071_ = v_pre_2077_;
goto v___jp_2070_;
}
else
{
lean_object* v_pre_2078_; 
lean_inc_ref(v_pre_2077_);
v_pre_2078_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed), 12, 1);
lean_closure_set(v_pre_2078_, 0, v_pre_2077_);
v_pre_2071_ = v_pre_2078_;
goto v___jp_2070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___boxed(lean_object* v_config_2081_, lean_object* v_thms_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_Meta_Grind_mkNormSymMethods(v_config_2081_, v_thms_2082_);
lean_dec_ref(v_config_2081_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(lean_object* v_x_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; 
lean_inc_ref(v___y_2085_);
v___x_2096_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v___y_2085_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
if (lean_obj_tag(v_a_2097_) == 0)
{
uint8_t v_done_2098_; 
v_done_2098_ = lean_ctor_get_uint8(v_a_2097_, 0);
lean_dec_ref_known(v_a_2097_, 0);
if (v_done_2098_ == 0)
{
lean_object* v___x_2099_; 
lean_dec_ref_known(v___x_2096_, 1);
v___x_2099_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_2085_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec_ref(v___y_2085_);
return v___x_2099_;
}
else
{
lean_dec_ref(v___y_2085_);
return v___x_2096_;
}
}
else
{
uint8_t v_done_2100_; 
lean_dec_ref(v___y_2085_);
v_done_2100_ = lean_ctor_get_uint8(v_a_2097_, sizeof(void*)*1);
if (v_done_2100_ == 0)
{
lean_object* v_e_x27_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref_known(v___x_2096_, 1);
v_e_x27_2101_ = lean_ctor_get(v_a_2097_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_a_2097_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2103_ = v_a_2097_;
v_isShared_2104_ = v_isSharedCheck_2119_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_e_x27_2101_);
lean_dec(v_a_2097_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2119_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_x27_2101_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
if (lean_obj_tag(v_a_2106_) == 0)
{
lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2117_; 
lean_inc_ref(v_a_2106_);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v___x_2105_, 0);
lean_dec(v_unused_2118_);
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2117_;
goto v_resetjp_2107_;
}
else
{
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2117_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
uint8_t v_done_2110_; lean_object* v___x_2112_; 
v_done_2110_ = lean_ctor_get_uint8(v_a_2106_, 0);
lean_dec_ref_known(v_a_2106_, 0);
if (v_isShared_2104_ == 0)
{
v___x_2112_ = v___x_2103_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_e_x27_2101_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*1, v_done_2110_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2112_);
v___x_2114_ = v___x_2108_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_del_object(v___x_2103_);
lean_dec_ref(v_e_x27_2101_);
return v___x_2105_;
}
}
else
{
lean_del_object(v___x_2103_);
lean_dec_ref(v_e_x27_2101_);
return v___x_2105_;
}
}
}
else
{
lean_dec_ref_known(v_a_2097_, 1);
return v___x_2096_;
}
}
}
else
{
lean_dec_ref(v___y_2085_);
return v___x_2096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0___boxed(lean_object* v_x_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(v_x_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(lean_object* v_x_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_unsigned_to_nat(255u);
v___x_2146_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_2145_, v___y_2134_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___boxed(lean_object* v_x_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(v_x_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(lean_object* v_dsimp_2160_, lean_object* v___f_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_box(0);
lean_inc_ref(v___y_2162_);
v___x_2174_ = l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(v_dsimp_2160_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
if (lean_obj_tag(v_a_2175_) == 0)
{
uint8_t v_done_2176_; 
v_done_2176_ = lean_ctor_get_uint8(v_a_2175_, 0);
lean_dec_ref_known(v_a_2175_, 0);
if (v_done_2176_ == 0)
{
lean_object* v___x_2177_; 
lean_dec_ref_known(v___x_2174_, 1);
v___x_2177_ = lean_apply_12(v___f_2161_, v___x_2173_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, lean_box(0));
return v___x_2177_;
}
else
{
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec_ref(v___f_2161_);
return v___x_2174_;
}
}
else
{
uint8_t v_done_2178_; 
lean_dec_ref(v___y_2162_);
v_done_2178_ = lean_ctor_get_uint8(v_a_2175_, sizeof(void*)*1);
if (v_done_2178_ == 0)
{
lean_object* v_e_x27_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref_known(v___x_2174_, 1);
v_e_x27_2179_ = lean_ctor_get(v_a_2175_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_a_2175_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2181_ = v_a_2175_;
v_isShared_2182_ = v_isSharedCheck_2197_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_e_x27_2179_);
lean_dec(v_a_2175_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2197_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; 
lean_inc_ref(v_e_x27_2179_);
v___x_2183_ = lean_apply_12(v___f_2161_, v___x_2173_, v_e_x27_2179_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, lean_box(0));
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
if (lean_obj_tag(v_a_2184_) == 0)
{
lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2195_; 
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; 
v_unused_2196_ = lean_ctor_get(v___x_2183_, 0);
lean_dec(v_unused_2196_);
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2195_;
goto v_resetjp_2185_;
}
else
{
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2195_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
uint8_t v_done_2188_; lean_object* v___x_2190_; 
v_done_2188_ = lean_ctor_get_uint8(v_a_2184_, 0);
lean_dec_ref_known(v_a_2184_, 0);
if (v_isShared_2182_ == 0)
{
v___x_2190_ = v___x_2181_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_e_x27_2179_);
v___x_2190_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2192_; 
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*1, v_done_2188_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2190_);
v___x_2192_ = v___x_2186_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2184_, 1);
lean_del_object(v___x_2181_);
lean_dec_ref(v_e_x27_2179_);
return v___x_2183_;
}
}
else
{
lean_del_object(v___x_2181_);
lean_dec_ref(v_e_x27_2179_);
return v___x_2183_;
}
}
}
else
{
lean_dec_ref_known(v_a_2175_, 1);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___f_2161_);
return v___x_2174_;
}
}
}
else
{
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec_ref(v___f_2161_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed(lean_object* v_dsimp_2198_, lean_object* v___f_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(v_dsimp_2198_, v___f_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec_ref(v_dsimp_2198_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(lean_object* v_pre_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
lean_inc(v___y_2222_);
lean_inc_ref(v___y_2221_);
lean_inc(v___y_2220_);
lean_inc_ref(v___y_2219_);
lean_inc(v___y_2218_);
lean_inc_ref(v___y_2217_);
lean_inc_ref(v___y_2213_);
v___x_2224_ = lean_apply_11(v_pre_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, lean_box(0));
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
if (lean_obj_tag(v_a_2225_) == 0)
{
uint8_t v_done_2226_; 
v_done_2226_ = lean_ctor_get_uint8(v_a_2225_, 0);
lean_dec_ref_known(v_a_2225_, 0);
if (v_done_2226_ == 0)
{
lean_object* v___x_2227_; 
lean_dec_ref_known(v___x_2224_, 1);
v___x_2227_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_2213_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
return v___x_2227_;
}
else
{
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___y_2213_);
return v___x_2224_;
}
}
else
{
uint8_t v_done_2228_; 
lean_dec_ref(v___y_2213_);
v_done_2228_ = lean_ctor_get_uint8(v_a_2225_, sizeof(void*)*1);
if (v_done_2228_ == 0)
{
lean_object* v_e_x27_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2247_; 
lean_dec_ref_known(v___x_2224_, 1);
v_e_x27_2229_ = lean_ctor_get(v_a_2225_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_a_2225_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2231_ = v_a_2225_;
v_isShared_2232_ = v_isSharedCheck_2247_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_e_x27_2229_);
lean_dec(v_a_2225_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2247_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; 
lean_inc_ref(v_e_x27_2229_);
v___x_2233_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_x27_2229_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
if (lean_obj_tag(v_a_2234_) == 0)
{
lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2245_; 
lean_inc_ref(v_a_2234_);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; 
v_unused_2246_ = lean_ctor_get(v___x_2233_, 0);
lean_dec(v_unused_2246_);
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2245_;
goto v_resetjp_2235_;
}
else
{
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2245_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
uint8_t v_done_2238_; lean_object* v___x_2240_; 
v_done_2238_ = lean_ctor_get_uint8(v_a_2234_, 0);
lean_dec_ref_known(v_a_2234_, 0);
if (v_isShared_2232_ == 0)
{
v___x_2240_ = v___x_2231_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_e_x27_2229_);
v___x_2240_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2242_; 
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*1, v_done_2238_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v___x_2240_);
v___x_2242_ = v___x_2236_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_del_object(v___x_2231_);
lean_dec_ref(v_e_x27_2229_);
return v___x_2233_;
}
}
else
{
lean_del_object(v___x_2231_);
lean_dec_ref(v_e_x27_2229_);
return v___x_2233_;
}
}
}
else
{
lean_dec_ref_known(v_a_2225_, 1);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
return v___x_2224_;
}
}
}
else
{
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___y_2213_);
return v___x_2224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed(lean_object* v_pre_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(v_pre_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(lean_object* v___f_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_box(0);
lean_inc_ref(v___y_2262_);
v___x_2274_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_2262_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
if (lean_obj_tag(v_a_2275_) == 0)
{
uint8_t v_done_2276_; 
v_done_2276_ = lean_ctor_get_uint8(v_a_2275_, 0);
lean_dec_ref_known(v_a_2275_, 0);
if (v_done_2276_ == 0)
{
lean_object* v___x_2277_; 
lean_dec_ref_known(v___x_2274_, 1);
v___x_2277_ = lean_apply_12(v___f_2261_, v___x_2273_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, lean_box(0));
return v___x_2277_;
}
else
{
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v___f_2261_);
return v___x_2274_;
}
}
else
{
uint8_t v_done_2278_; 
lean_dec_ref(v___y_2262_);
v_done_2278_ = lean_ctor_get_uint8(v_a_2275_, sizeof(void*)*1);
if (v_done_2278_ == 0)
{
lean_object* v_e_x27_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref_known(v___x_2274_, 1);
v_e_x27_2279_ = lean_ctor_get(v_a_2275_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_a_2275_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2281_ = v_a_2275_;
v_isShared_2282_ = v_isSharedCheck_2297_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_e_x27_2279_);
lean_dec(v_a_2275_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2297_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; 
lean_inc_ref(v_e_x27_2279_);
v___x_2283_ = lean_apply_12(v___f_2261_, v___x_2273_, v_e_x27_2279_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, lean_box(0));
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
if (lean_obj_tag(v_a_2284_) == 0)
{
lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2295_; 
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; 
v_unused_2296_ = lean_ctor_get(v___x_2283_, 0);
lean_dec(v_unused_2296_);
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2295_;
goto v_resetjp_2285_;
}
else
{
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2295_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
uint8_t v_done_2288_; lean_object* v___x_2290_; 
v_done_2288_ = lean_ctor_get_uint8(v_a_2284_, 0);
lean_dec_ref_known(v_a_2284_, 0);
if (v_isShared_2282_ == 0)
{
v___x_2290_ = v___x_2281_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_e_x27_2279_);
v___x_2290_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2292_; 
lean_ctor_set_uint8(v___x_2290_, sizeof(void*)*1, v_done_2288_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2290_);
v___x_2292_ = v___x_2286_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2284_, 1);
lean_del_object(v___x_2281_);
lean_dec_ref(v_e_x27_2279_);
return v___x_2283_;
}
}
else
{
lean_del_object(v___x_2281_);
lean_dec_ref(v_e_x27_2279_);
return v___x_2283_;
}
}
}
else
{
lean_dec_ref_known(v_a_2275_, 1);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___f_2261_);
return v___x_2274_;
}
}
}
else
{
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v___f_2261_);
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4___boxed(lean_object* v___f_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(v___f_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(lean_object* v___f_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___y_2324_; lean_object* v_e_x27_2325_; uint8_t v_done_2326_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_box(0);
lean_inc_ref(v___y_2312_);
v___x_2340_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_2312_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
if (lean_obj_tag(v_a_2341_) == 0)
{
uint8_t v_done_2342_; 
v_done_2342_ = lean_ctor_get_uint8(v_a_2341_, 0);
lean_dec_ref_known(v_a_2341_, 0);
if (v_done_2342_ == 0)
{
lean_object* v___x_2343_; 
lean_dec_ref_known(v___x_2340_, 1);
lean_inc(v___y_2321_);
lean_inc_ref(v___y_2320_);
lean_inc(v___y_2319_);
lean_inc_ref(v___y_2318_);
lean_inc(v___y_2317_);
lean_inc_ref(v___y_2316_);
lean_inc_ref(v___y_2312_);
v___x_2343_ = lean_apply_12(v___f_2311_, v___x_2339_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, lean_box(0));
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
if (lean_obj_tag(v_a_2344_) == 0)
{
uint8_t v_done_2345_; 
v_done_2345_ = lean_ctor_get_uint8(v_a_2344_, 0);
lean_dec_ref_known(v_a_2344_, 0);
if (v_done_2345_ == 0)
{
lean_object* v___x_2346_; 
lean_dec_ref_known(v___x_2343_, 1);
v___x_2346_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_2312_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v___x_2346_;
}
else
{
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v___y_2312_);
return v___x_2343_;
}
}
else
{
lean_object* v_e_x27_2347_; uint8_t v_done_2348_; 
lean_dec_ref(v___y_2312_);
v_e_x27_2347_ = lean_ctor_get(v_a_2344_, 0);
lean_inc_ref(v_e_x27_2347_);
v_done_2348_ = lean_ctor_get_uint8(v_a_2344_, sizeof(void*)*1);
lean_dec_ref_known(v_a_2344_, 1);
v___y_2324_ = v___x_2343_;
v_e_x27_2325_ = v_e_x27_2347_;
v_done_2326_ = v_done_2348_;
goto v___jp_2323_;
}
}
else
{
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v___y_2312_);
return v___x_2343_;
}
}
else
{
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec_ref(v___f_2311_);
return v___x_2340_;
}
}
else
{
uint8_t v_done_2349_; 
lean_dec_ref(v___y_2312_);
v_done_2349_ = lean_ctor_get_uint8(v_a_2341_, sizeof(void*)*1);
if (v_done_2349_ == 0)
{
lean_object* v_e_x27_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref_known(v___x_2340_, 1);
v_e_x27_2350_ = lean_ctor_get(v_a_2341_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_a_2341_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2352_ = v_a_2341_;
v_isShared_2353_ = v_isSharedCheck_2370_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_e_x27_2350_);
lean_dec(v_a_2341_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2370_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; 
lean_inc(v___y_2321_);
lean_inc_ref(v___y_2320_);
lean_inc(v___y_2319_);
lean_inc_ref(v___y_2318_);
lean_inc(v___y_2317_);
lean_inc_ref(v___y_2316_);
lean_inc_ref(v_e_x27_2350_);
v___x_2354_ = lean_apply_12(v___f_2311_, v___x_2339_, v_e_x27_2350_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, lean_box(0));
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
if (lean_obj_tag(v_a_2355_) == 0)
{
lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2366_; 
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2366_ == 0)
{
lean_object* v_unused_2367_; 
v_unused_2367_ = lean_ctor_get(v___x_2354_, 0);
lean_dec(v_unused_2367_);
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2366_;
goto v_resetjp_2356_;
}
else
{
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2366_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
uint8_t v_done_2359_; lean_object* v___x_2361_; 
v_done_2359_ = lean_ctor_get_uint8(v_a_2355_, 0);
lean_dec_ref_known(v_a_2355_, 0);
lean_inc_ref(v_e_x27_2350_);
if (v_isShared_2353_ == 0)
{
v___x_2361_ = v___x_2352_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_e_x27_2350_);
v___x_2361_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*1, v_done_2359_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2361_);
v___x_2363_ = v___x_2357_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
v___y_2324_ = v___x_2363_;
v_e_x27_2325_ = v_e_x27_2350_;
v_done_2326_ = v_done_2359_;
goto v___jp_2323_;
}
}
}
}
else
{
lean_object* v_e_x27_2368_; uint8_t v_done_2369_; 
lean_del_object(v___x_2352_);
lean_dec_ref(v_e_x27_2350_);
v_e_x27_2368_ = lean_ctor_get(v_a_2355_, 0);
lean_inc_ref(v_e_x27_2368_);
v_done_2369_ = lean_ctor_get_uint8(v_a_2355_, sizeof(void*)*1);
lean_dec_ref_known(v_a_2355_, 1);
v___y_2324_ = v___x_2354_;
v_e_x27_2325_ = v_e_x27_2368_;
v_done_2326_ = v_done_2369_;
goto v___jp_2323_;
}
}
else
{
lean_del_object(v___x_2352_);
lean_dec_ref(v_e_x27_2350_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v___x_2354_;
}
}
}
else
{
lean_dec_ref_known(v_a_2341_, 1);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___f_2311_);
return v___x_2340_;
}
}
}
else
{
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec_ref(v___f_2311_);
return v___x_2340_;
}
v___jp_2323_:
{
if (v_done_2326_ == 0)
{
lean_object* v___x_2327_; 
lean_dec_ref(v___y_2324_);
lean_inc_ref(v_e_x27_2325_);
v___x_2327_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_x27_2325_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
if (lean_obj_tag(v_a_2328_) == 0)
{
lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2337_; 
lean_inc_ref(v_a_2328_);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v___x_2327_, 0);
lean_dec(v_unused_2338_);
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
else
{
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
uint8_t v_done_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v_done_2332_ = lean_ctor_get_uint8(v_a_2328_, 0);
lean_dec_ref_known(v_a_2328_, 0);
v___x_2333_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2333_, 0, v_e_x27_2325_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*1, v_done_2332_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v___x_2333_);
v___x_2335_ = v___x_2330_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
else
{
lean_dec_ref(v_e_x27_2325_);
return v___x_2327_;
}
}
else
{
lean_dec_ref(v_e_x27_2325_);
return v___x_2327_;
}
}
else
{
lean_dec_ref(v_e_x27_2325_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v___y_2324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5___boxed(lean_object* v___f_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(v___f_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods(lean_object* v_config_2390_, lean_object* v_thms_2391_){
_start:
{
uint8_t v_zetaDelta_2392_; uint8_t v_zeta_2393_; lean_object* v___f_2394_; lean_object* v_pre_2396_; lean_object* v_pre_2401_; 
v_zetaDelta_2392_ = lean_ctor_get_uint8(v_config_2390_, sizeof(void*)*14 + 19);
v_zeta_2393_ = lean_ctor_get_uint8(v_config_2390_, sizeof(void*)*14 + 20);
v___f_2394_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__1));
if (v_zeta_2393_ == 0)
{
lean_object* v_pre_2403_; 
v_pre_2403_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__2));
v_pre_2401_ = v_pre_2403_;
goto v___jp_2400_;
}
else
{
lean_object* v_pre_2404_; 
v_pre_2404_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__3));
v_pre_2401_ = v_pre_2404_;
goto v___jp_2400_;
}
v___jp_2395_:
{
lean_object* v_dsimp_2397_; lean_object* v_post_2398_; lean_object* v___x_2399_; 
v_dsimp_2397_ = lean_ctor_get(v_thms_2391_, 2);
lean_inc_ref(v_dsimp_2397_);
lean_dec_ref(v_thms_2391_);
v_post_2398_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed), 13, 2);
lean_closure_set(v_post_2398_, 0, v_dsimp_2397_);
lean_closure_set(v_post_2398_, 1, v___f_2394_);
v___x_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2399_, 0, v_pre_2396_);
lean_ctor_set(v___x_2399_, 1, v_post_2398_);
return v___x_2399_;
}
v___jp_2400_:
{
if (v_zetaDelta_2392_ == 0)
{
lean_inc_ref(v_pre_2401_);
v_pre_2396_ = v_pre_2401_;
goto v___jp_2395_;
}
else
{
lean_object* v_pre_2402_; 
lean_inc_ref(v_pre_2401_);
v_pre_2402_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed), 12, 1);
lean_closure_set(v_pre_2402_, 0, v_pre_2401_);
v_pre_2396_ = v_pre_2402_;
goto v___jp_2395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___boxed(lean_object* v_config_2405_, lean_object* v_thms_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_config_2405_, v_thms_2406_);
lean_dec_ref(v_config_2405_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(lean_object* v_e_2408_, lean_object* v___y_2409_){
_start:
{
uint8_t v___x_2411_; 
v___x_2411_ = l_Lean_Expr_hasMVar(v_e_2408_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v_e_2408_);
return v___x_2412_;
}
else
{
lean_object* v___x_2413_; lean_object* v_mctx_2414_; lean_object* v___x_2415_; lean_object* v_fst_2416_; lean_object* v_snd_2417_; lean_object* v___x_2418_; lean_object* v_cache_2419_; lean_object* v_zetaDeltaFVarIds_2420_; lean_object* v_postponed_2421_; lean_object* v_diag_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2431_; 
v___x_2413_ = lean_st_ref_get(v___y_2409_);
v_mctx_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_ref(v_mctx_2414_);
lean_dec(v___x_2413_);
v___x_2415_ = l_Lean_instantiateMVarsCore(v_mctx_2414_, v_e_2408_);
v_fst_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_fst_2416_);
v_snd_2417_ = lean_ctor_get(v___x_2415_, 1);
lean_inc(v_snd_2417_);
lean_dec_ref(v___x_2415_);
v___x_2418_ = lean_st_ref_take(v___y_2409_);
v_cache_2419_ = lean_ctor_get(v___x_2418_, 1);
v_zetaDeltaFVarIds_2420_ = lean_ctor_get(v___x_2418_, 2);
v_postponed_2421_ = lean_ctor_get(v___x_2418_, 3);
v_diag_2422_ = lean_ctor_get(v___x_2418_, 4);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2431_ == 0)
{
lean_object* v_unused_2432_; 
v_unused_2432_ = lean_ctor_get(v___x_2418_, 0);
lean_dec(v_unused_2432_);
v___x_2424_ = v___x_2418_;
v_isShared_2425_ = v_isSharedCheck_2431_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_diag_2422_);
lean_inc(v_postponed_2421_);
lean_inc(v_zetaDeltaFVarIds_2420_);
lean_inc(v_cache_2419_);
lean_dec(v___x_2418_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2431_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v_snd_2417_);
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_snd_2417_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_cache_2419_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_zetaDeltaFVarIds_2420_);
lean_ctor_set(v_reuseFailAlloc_2430_, 3, v_postponed_2421_);
lean_ctor_set(v_reuseFailAlloc_2430_, 4, v_diag_2422_);
v___x_2427_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = lean_st_ref_put(v___y_2409_, v___x_2427_);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v_fst_2416_);
return v___x_2429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg___boxed(lean_object* v_e_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2433_, v___y_2434_);
lean_dec(v___y_2434_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(lean_object* v_e_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2437_, v___y_2444_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___boxed(lean_object* v_e_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(v_e_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy(lean_object* v_e_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v___x_2472_; lean_object* v_a_2473_; lean_object* v___x_2474_; 
v___x_2472_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2461_, v_a_2468_);
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref(v___x_2472_);
v___x_2474_ = l_Lean_Meta_Grind_simpCore(v_a_2473_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v_expr_2476_; lean_object* v_proof_x3f_2477_; uint8_t v_cache_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2502_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v_expr_2476_ = lean_ctor_get(v_a_2475_, 0);
v_proof_x3f_2477_ = lean_ctor_get(v_a_2475_, 1);
v_cache_2478_ = lean_ctor_get_uint8(v_a_2475_, sizeof(void*)*2);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_a_2475_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2480_ = v_a_2475_;
v_isShared_2481_ = v_isSharedCheck_2502_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_proof_x3f_2477_);
lean_inc(v_expr_2476_);
lean_dec(v_a_2475_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2502_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_expr_2476_, v_a_2469_, v_a_2470_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2493_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2493_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2493_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v_a_2483_);
v___x_2488_ = v___x_2480_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2483_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_proof_x3f_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2492_, sizeof(void*)*2, v_cache_2478_);
v___x_2488_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2490_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2488_);
v___x_2490_ = v___x_2485_;
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
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_del_object(v___x_2480_);
lean_dec(v_proof_x3f_2477_);
v_a_2494_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2482_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2482_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
else
{
return v___x_2474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy___boxed(lean_object* v_e_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Meta_Grind_normLegacy(v_e_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
return v_res_2514_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__0(void){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2515_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__1(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__0, &l_Lean_Meta_Grind_normSym___redArg___closed__0_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__0);
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__2(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__1, &l_Lean_Meta_Grind_normSym___redArg___closed__1_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__1);
v___x_2519_ = lean_unsigned_to_nat(0u);
v___x_2520_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
lean_ctor_set(v___x_2520_, 1, v___x_2518_);
lean_ctor_set(v___x_2520_, 2, v___x_2518_);
lean_ctor_set(v___x_2520_, 3, v___x_2518_);
return v___x_2520_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__3(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2521_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__1, &l_Lean_Meta_Grind_normSym___redArg___closed__1_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__1);
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
lean_ctor_set(v___x_2523_, 1, v___x_2521_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg(lean_object* v_e_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v___x_2533_; lean_object* v_a_2534_; lean_object* v___x_2535_; 
v___x_2533_ = l_Lean_Meta_Grind_getNormSymTheorems___redArg(v_a_2531_);
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref(v___x_2533_);
v___x_2535_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2525_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2535_, 1);
lean_inc(v_a_2534_);
v___x_2537_ = l_Lean_Meta_Grind_mkNormSymMethods(v_a_2536_, v_a_2534_);
v___x_2538_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_a_2536_, v_a_2534_);
lean_dec(v_a_2536_);
v___x_2539_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__2, &l_Lean_Meta_Grind_normSym___redArg___closed__2_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__2);
v___x_2540_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__3, &l_Lean_Meta_Grind_normSym___redArg___closed__3_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__3);
v___x_2541_ = l_Lean_Meta_Grind_symNorm(v_e_2524_, v___x_2537_, v___x_2538_, v___x_2539_, v___x_2540_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2550_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2550_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2550_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v_fst_2546_; lean_object* v___x_2548_; 
v_fst_2546_ = lean_ctor_get(v_a_2542_, 0);
lean_inc(v_fst_2546_);
lean_dec(v_a_2542_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v_fst_2546_);
v___x_2548_ = v___x_2544_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_fst_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
v_a_2551_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2541_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2541_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v_a_2534_);
lean_dec_ref(v_e_2524_);
v_a_2559_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2535_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2535_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg___boxed(lean_object* v_e_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_Meta_Grind_normSym___redArg(v_e_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec_ref(v_a_2568_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym(lean_object* v_e_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_Meta_Grind_normSym___redArg(v_e_2577_, v_a_2579_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___boxed(lean_object* v_e_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lean_Meta_Grind_normSym(v_e_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
return v_res_2600_;
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
