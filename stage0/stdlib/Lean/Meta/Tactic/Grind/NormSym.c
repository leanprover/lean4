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
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Meta_Grind_normSymExt;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpNatSub(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpNatRel___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpArith(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_pushNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_reduceControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_reduceProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_etaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymMethods___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)(((size_t)(65536) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___lam__13___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__4_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__20___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__5_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__12_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___lam__21___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__5_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)(((size_t)(65536) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___closed__0_value;
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
lean_dec_ref(v___y_25_);
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
v___x_237_ = l_Lean_Meta_Grind_NormSym_etaReduce(v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
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
v___x_338_ = l_Lean_Meta_Sym_Simp_beta___redArg(v___y_326_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
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
v___x_439_ = l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5(lean_object* v___f_526_, lean_object* v_x_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_box(0);
v___x_540_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v___y_528_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
if (lean_obj_tag(v_a_541_) == 0)
{
uint8_t v_done_542_; 
v_done_542_ = lean_ctor_get_uint8(v_a_541_, 0);
if (v_done_542_ == 0)
{
uint8_t v_contextDependent_543_; lean_object* v___x_544_; 
lean_dec_ref_known(v___x_540_, 1);
v_contextDependent_543_ = lean_ctor_get_uint8(v_a_541_, 1);
lean_dec_ref_known(v_a_541_, 0);
lean_inc(v___y_537_);
lean_inc_ref(v___y_536_);
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
v___x_544_ = lean_apply_12(v___f_526_, v___x_539_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, lean_box(0));
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; uint8_t v___y_547_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
if (v_contextDependent_543_ == 0)
{
lean_dec(v_a_545_);
return v___x_544_;
}
else
{
if (lean_obj_tag(v_a_545_) == 0)
{
uint8_t v_contextDependent_557_; 
v_contextDependent_557_ = lean_ctor_get_uint8(v_a_545_, 1);
v___y_547_ = v_contextDependent_557_;
goto v___jp_546_;
}
else
{
uint8_t v_contextDependent_558_; 
v_contextDependent_558_ = lean_ctor_get_uint8(v_a_545_, sizeof(void*)*2 + 1);
v___y_547_ = v_contextDependent_558_;
goto v___jp_546_;
}
}
v___jp_546_:
{
if (v___y_547_ == 0)
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v___x_544_, 0);
lean_dec(v_unused_556_);
v___x_549_ = v___x_544_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_dec(v___x_544_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_545_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
lean_dec(v_a_545_);
return v___x_544_;
}
}
}
else
{
return v___x_544_;
}
}
else
{
lean_dec_ref_known(v_a_541_, 0);
lean_dec_ref(v___y_528_);
lean_dec_ref(v___f_526_);
return v___x_540_;
}
}
else
{
uint8_t v_done_559_; 
v_done_559_ = lean_ctor_get_uint8(v_a_541_, sizeof(void*)*2);
if (v_done_559_ == 0)
{
lean_object* v_e_x27_560_; lean_object* v_proof_561_; uint8_t v_contextDependent_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref_known(v___x_540_, 1);
v_e_x27_560_ = lean_ctor_get(v_a_541_, 0);
v_proof_561_ = lean_ctor_get(v_a_541_, 1);
v_contextDependent_562_ = lean_ctor_get_uint8(v_a_541_, sizeof(void*)*2 + 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_a_541_);
if (v_isSharedCheck_612_ == 0)
{
v___x_564_ = v_a_541_;
v_isShared_565_ = v_isSharedCheck_612_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_proof_561_);
lean_inc(v_e_x27_560_);
lean_dec(v_a_541_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_612_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; 
lean_inc(v___y_537_);
lean_inc_ref(v___y_536_);
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
lean_inc_ref(v_e_x27_560_);
v___x_566_ = lean_apply_12(v___f_526_, v___x_539_, v_e_x27_560_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, lean_box(0));
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_611_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_611_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_611_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_611_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
if (lean_obj_tag(v_a_567_) == 0)
{
uint8_t v_done_571_; uint8_t v_contextDependent_572_; uint8_t v___y_574_; 
lean_dec_ref(v___y_528_);
v_done_571_ = lean_ctor_get_uint8(v_a_567_, 0);
v_contextDependent_572_ = lean_ctor_get_uint8(v_a_567_, 1);
lean_dec_ref_known(v_a_567_, 0);
if (v_contextDependent_562_ == 0)
{
v___y_574_ = v_contextDependent_572_;
goto v___jp_573_;
}
else
{
v___y_574_ = v_contextDependent_562_;
goto v___jp_573_;
}
v___jp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_565_ == 0)
{
v___x_576_ = v___x_564_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_e_x27_560_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_proof_561_);
v___x_576_ = v_reuseFailAlloc_580_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*2, v_done_571_);
lean_ctor_set_uint8(v___x_576_, sizeof(void*)*2 + 1, v___y_574_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_576_);
v___x_578_ = v___x_569_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_object* v_e_x27_581_; lean_object* v_proof_582_; uint8_t v_done_583_; uint8_t v_contextDependent_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_610_; 
lean_del_object(v___x_569_);
lean_del_object(v___x_564_);
v_e_x27_581_ = lean_ctor_get(v_a_567_, 0);
v_proof_582_ = lean_ctor_get(v_a_567_, 1);
v_done_583_ = lean_ctor_get_uint8(v_a_567_, sizeof(void*)*2);
v_contextDependent_584_ = lean_ctor_get_uint8(v_a_567_, sizeof(void*)*2 + 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_a_567_);
if (v_isSharedCheck_610_ == 0)
{
v___x_586_ = v_a_567_;
v_isShared_587_ = v_isSharedCheck_610_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_proof_582_);
lean_inc(v_e_x27_581_);
lean_dec(v_a_567_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_610_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; 
lean_inc_ref(v_e_x27_581_);
v___x_588_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_528_, v_e_x27_560_, v_proof_561_, v_e_x27_581_, v_proof_582_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_601_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_601_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_601_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_601_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
uint8_t v___y_594_; 
if (v_contextDependent_562_ == 0)
{
v___y_594_ = v_contextDependent_584_;
goto v___jp_593_;
}
else
{
v___y_594_ = v_contextDependent_562_;
goto v___jp_593_;
}
v___jp_593_:
{
lean_object* v___x_596_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_a_589_);
v___x_596_ = v___x_586_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_e_x27_581_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_a_589_);
lean_ctor_set_uint8(v_reuseFailAlloc_600_, sizeof(void*)*2, v_done_583_);
v___x_596_ = v_reuseFailAlloc_600_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_598_; 
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*2 + 1, v___y_594_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_596_);
v___x_598_ = v___x_591_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_del_object(v___x_586_);
lean_dec_ref(v_e_x27_581_);
v_a_602_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_588_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_588_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_564_);
lean_dec_ref(v_proof_561_);
lean_dec_ref(v_e_x27_560_);
lean_dec_ref(v___y_528_);
return v___x_566_;
}
}
}
else
{
lean_dec_ref_known(v_a_541_, 2);
lean_dec_ref(v___y_528_);
lean_dec_ref(v___f_526_);
return v___x_540_;
}
}
}
else
{
lean_dec_ref(v___y_528_);
lean_dec_ref(v___f_526_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__5___boxed(lean_object* v___f_613_, lean_object* v_x_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__5(v___f_613_, v_x_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6(lean_object* v_x_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; 
lean_inc_ref(v___y_628_);
v___x_639_ = l_Lean_Meta_Grind_NormSym_simpForall(v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
if (lean_obj_tag(v_a_640_) == 0)
{
uint8_t v_done_641_; 
v_done_641_ = lean_ctor_get_uint8(v_a_640_, 0);
if (v_done_641_ == 0)
{
uint8_t v_contextDependent_642_; lean_object* v___x_643_; 
lean_dec_ref_known(v___x_639_, 1);
v_contextDependent_642_ = lean_ctor_get_uint8(v_a_640_, 1);
lean_dec_ref_known(v_a_640_, 0);
v___x_643_ = l_Lean_Meta_Grind_NormSym_simpExists___redArg(v___y_628_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec_ref(v___y_628_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; uint8_t v___y_646_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
if (v_contextDependent_642_ == 0)
{
return v___x_643_;
}
else
{
if (lean_obj_tag(v_a_644_) == 0)
{
uint8_t v_contextDependent_656_; 
v_contextDependent_656_ = lean_ctor_get_uint8(v_a_644_, 1);
v___y_646_ = v_contextDependent_656_;
goto v___jp_645_;
}
else
{
uint8_t v_contextDependent_657_; 
v_contextDependent_657_ = lean_ctor_get_uint8(v_a_644_, sizeof(void*)*2 + 1);
v___y_646_ = v_contextDependent_657_;
goto v___jp_645_;
}
}
v___jp_645_:
{
if (v___y_646_ == 0)
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
lean_inc(v_a_644_);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v___x_643_, 0);
lean_dec(v_unused_655_);
v___x_648_ = v___x_643_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_dec(v___x_643_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_644_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
else
{
return v___x_643_;
}
}
}
else
{
return v___x_643_;
}
}
else
{
lean_dec_ref_known(v_a_640_, 0);
lean_dec_ref(v___y_628_);
return v___x_639_;
}
}
else
{
uint8_t v_done_658_; 
v_done_658_ = lean_ctor_get_uint8(v_a_640_, sizeof(void*)*2);
if (v_done_658_ == 0)
{
lean_object* v_e_x27_659_; lean_object* v_proof_660_; uint8_t v_contextDependent_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref_known(v___x_639_, 1);
v_e_x27_659_ = lean_ctor_get(v_a_640_, 0);
v_proof_660_ = lean_ctor_get(v_a_640_, 1);
v_contextDependent_661_ = lean_ctor_get_uint8(v_a_640_, sizeof(void*)*2 + 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_a_640_);
if (v_isSharedCheck_711_ == 0)
{
v___x_663_ = v_a_640_;
v_isShared_664_ = v_isSharedCheck_711_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_proof_660_);
lean_inc(v_e_x27_659_);
lean_dec(v_a_640_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_711_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Meta_Grind_NormSym_simpExists___redArg(v_e_x27_659_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_710_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_710_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_710_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_710_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
if (lean_obj_tag(v_a_666_) == 0)
{
uint8_t v_done_670_; uint8_t v_contextDependent_671_; uint8_t v___y_673_; 
lean_dec_ref(v___y_628_);
v_done_670_ = lean_ctor_get_uint8(v_a_666_, 0);
v_contextDependent_671_ = lean_ctor_get_uint8(v_a_666_, 1);
lean_dec_ref_known(v_a_666_, 0);
if (v_contextDependent_661_ == 0)
{
v___y_673_ = v_contextDependent_671_;
goto v___jp_672_;
}
else
{
v___y_673_ = v_contextDependent_661_;
goto v___jp_672_;
}
v___jp_672_:
{
lean_object* v___x_675_; 
if (v_isShared_664_ == 0)
{
v___x_675_ = v___x_663_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_e_x27_659_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_proof_660_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*2, v_done_670_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*2 + 1, v___y_673_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_675_);
v___x_677_ = v___x_668_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v_e_x27_680_; lean_object* v_proof_681_; uint8_t v_done_682_; uint8_t v_contextDependent_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_709_; 
lean_del_object(v___x_668_);
lean_del_object(v___x_663_);
v_e_x27_680_ = lean_ctor_get(v_a_666_, 0);
v_proof_681_ = lean_ctor_get(v_a_666_, 1);
v_done_682_ = lean_ctor_get_uint8(v_a_666_, sizeof(void*)*2);
v_contextDependent_683_ = lean_ctor_get_uint8(v_a_666_, sizeof(void*)*2 + 1);
v_isSharedCheck_709_ = !lean_is_exclusive(v_a_666_);
if (v_isSharedCheck_709_ == 0)
{
v___x_685_ = v_a_666_;
v_isShared_686_ = v_isSharedCheck_709_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_proof_681_);
lean_inc(v_e_x27_680_);
lean_dec(v_a_666_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_709_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; 
lean_inc_ref(v_e_x27_680_);
v___x_687_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_628_, v_e_x27_659_, v_proof_660_, v_e_x27_680_, v_proof_681_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_700_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_700_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_700_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_700_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
uint8_t v___y_693_; 
if (v_contextDependent_661_ == 0)
{
v___y_693_ = v_contextDependent_683_;
goto v___jp_692_;
}
else
{
v___y_693_ = v_contextDependent_661_;
goto v___jp_692_;
}
v___jp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v_a_688_);
v___x_695_ = v___x_685_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_e_x27_680_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_a_688_);
lean_ctor_set_uint8(v_reuseFailAlloc_699_, sizeof(void*)*2, v_done_682_);
v___x_695_ = v_reuseFailAlloc_699_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_697_; 
lean_ctor_set_uint8(v___x_695_, sizeof(void*)*2 + 1, v___y_693_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_695_);
v___x_697_ = v___x_690_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_del_object(v___x_685_);
lean_dec_ref(v_e_x27_680_);
v_a_701_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_687_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_687_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_663_);
lean_dec_ref(v_proof_660_);
lean_dec_ref(v_e_x27_659_);
lean_dec_ref(v___y_628_);
return v___x_665_;
}
}
}
else
{
lean_dec_ref_known(v_a_640_, 2);
lean_dec_ref(v___y_628_);
return v___x_639_;
}
}
}
else
{
lean_dec_ref(v___y_628_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__6___boxed(lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__6(v_x_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
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
v___x_739_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
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
v___x_840_ = l_Lean_Meta_Grind_NormSym_simpDIte(v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
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
v___x_941_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v___y_929_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
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
v___x_1042_ = l_Lean_Meta_Grind_NormSym_simpEq(v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11(uint8_t v_distrib_1129_, lean_object* v___f_1130_, lean_object* v_x_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_box(0);
lean_inc_ref(v___y_1132_);
v___x_1144_ = l_Lean_Meta_Sym_Simp_simpNatSub(v_distrib_1129_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
if (lean_obj_tag(v_a_1145_) == 0)
{
uint8_t v_done_1146_; 
v_done_1146_ = lean_ctor_get_uint8(v_a_1145_, 0);
if (v_done_1146_ == 0)
{
uint8_t v_contextDependent_1147_; lean_object* v___x_1148_; 
lean_dec_ref_known(v___x_1144_, 1);
v_contextDependent_1147_ = lean_ctor_get_uint8(v_a_1145_, 1);
lean_dec_ref_known(v_a_1145_, 0);
lean_inc(v___y_1141_);
lean_inc_ref(v___y_1140_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
lean_inc_ref(v___y_1134_);
lean_inc(v___y_1133_);
v___x_1148_ = lean_apply_12(v___f_1130_, v___x_1143_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, lean_box(0));
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; uint8_t v___y_1151_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
if (v_contextDependent_1147_ == 0)
{
lean_dec(v_a_1149_);
return v___x_1148_;
}
else
{
if (lean_obj_tag(v_a_1149_) == 0)
{
uint8_t v_contextDependent_1161_; 
v_contextDependent_1161_ = lean_ctor_get_uint8(v_a_1149_, 1);
v___y_1151_ = v_contextDependent_1161_;
goto v___jp_1150_;
}
else
{
uint8_t v_contextDependent_1162_; 
v_contextDependent_1162_ = lean_ctor_get_uint8(v_a_1149_, sizeof(void*)*2 + 1);
v___y_1151_ = v_contextDependent_1162_;
goto v___jp_1150_;
}
}
v___jp_1150_:
{
if (v___y_1151_ == 0)
{
lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v___x_1148_, 0);
lean_dec(v_unused_1160_);
v___x_1153_ = v___x_1148_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_dec(v___x_1148_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1149_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1155_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_dec(v_a_1149_);
return v___x_1148_;
}
}
}
else
{
return v___x_1148_;
}
}
else
{
lean_dec_ref_known(v_a_1145_, 0);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v___f_1130_);
return v___x_1144_;
}
}
else
{
uint8_t v_done_1163_; 
v_done_1163_ = lean_ctor_get_uint8(v_a_1145_, sizeof(void*)*2);
if (v_done_1163_ == 0)
{
lean_object* v_e_x27_1164_; lean_object* v_proof_1165_; uint8_t v_contextDependent_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref_known(v___x_1144_, 1);
v_e_x27_1164_ = lean_ctor_get(v_a_1145_, 0);
v_proof_1165_ = lean_ctor_get(v_a_1145_, 1);
v_contextDependent_1166_ = lean_ctor_get_uint8(v_a_1145_, sizeof(void*)*2 + 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_a_1145_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1168_ = v_a_1145_;
v_isShared_1169_ = v_isSharedCheck_1216_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_proof_1165_);
lean_inc(v_e_x27_1164_);
lean_dec(v_a_1145_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1216_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; 
lean_inc(v___y_1141_);
lean_inc_ref(v___y_1140_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
lean_inc_ref(v___y_1134_);
lean_inc(v___y_1133_);
lean_inc_ref(v_e_x27_1164_);
v___x_1170_ = lean_apply_12(v___f_1130_, v___x_1143_, v_e_x27_1164_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, lean_box(0));
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1215_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1215_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1215_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
if (lean_obj_tag(v_a_1171_) == 0)
{
uint8_t v_done_1175_; uint8_t v_contextDependent_1176_; uint8_t v___y_1178_; 
lean_dec_ref(v___y_1132_);
v_done_1175_ = lean_ctor_get_uint8(v_a_1171_, 0);
v_contextDependent_1176_ = lean_ctor_get_uint8(v_a_1171_, 1);
lean_dec_ref_known(v_a_1171_, 0);
if (v_contextDependent_1166_ == 0)
{
v___y_1178_ = v_contextDependent_1176_;
goto v___jp_1177_;
}
else
{
v___y_1178_ = v_contextDependent_1166_;
goto v___jp_1177_;
}
v___jp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1169_ == 0)
{
v___x_1180_ = v___x_1168_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_e_x27_1164_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_proof_1165_);
v___x_1180_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1182_; 
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*2, v_done_1175_);
lean_ctor_set_uint8(v___x_1180_, sizeof(void*)*2 + 1, v___y_1178_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1180_);
v___x_1182_ = v___x_1173_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v_e_x27_1185_; lean_object* v_proof_1186_; uint8_t v_done_1187_; uint8_t v_contextDependent_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1214_; 
lean_del_object(v___x_1173_);
lean_del_object(v___x_1168_);
v_e_x27_1185_ = lean_ctor_get(v_a_1171_, 0);
v_proof_1186_ = lean_ctor_get(v_a_1171_, 1);
v_done_1187_ = lean_ctor_get_uint8(v_a_1171_, sizeof(void*)*2);
v_contextDependent_1188_ = lean_ctor_get_uint8(v_a_1171_, sizeof(void*)*2 + 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_a_1171_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1190_ = v_a_1171_;
v_isShared_1191_ = v_isSharedCheck_1214_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_proof_1186_);
lean_inc(v_e_x27_1185_);
lean_dec(v_a_1171_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1214_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; 
lean_inc_ref(v_e_x27_1185_);
v___x_1192_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1132_, v_e_x27_1164_, v_proof_1165_, v_e_x27_1185_, v_proof_1186_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1205_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1205_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1205_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
uint8_t v___y_1198_; 
if (v_contextDependent_1166_ == 0)
{
v___y_1198_ = v_contextDependent_1188_;
goto v___jp_1197_;
}
else
{
v___y_1198_ = v_contextDependent_1166_;
goto v___jp_1197_;
}
v___jp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v_a_1193_);
v___x_1200_ = v___x_1190_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_e_x27_1185_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_a_1193_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*2, v_done_1187_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*2 + 1, v___y_1198_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1200_);
v___x_1202_ = v___x_1195_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_del_object(v___x_1190_);
lean_dec_ref(v_e_x27_1185_);
v_a_1206_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1192_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1192_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1168_);
lean_dec_ref(v_proof_1165_);
lean_dec_ref(v_e_x27_1164_);
lean_dec_ref(v___y_1132_);
return v___x_1170_;
}
}
}
else
{
lean_dec_ref_known(v_a_1145_, 2);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v___f_1130_);
return v___x_1144_;
}
}
}
else
{
lean_dec_ref(v___y_1132_);
lean_dec_ref(v___f_1130_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed(lean_object* v_distrib_1217_, lean_object* v___f_1218_, lean_object* v_x_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v_distrib_boxed_1231_; lean_object* v_res_1232_; 
v_distrib_boxed_1231_ = lean_unbox(v_distrib_1217_);
v_res_1232_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__11(v_distrib_boxed_1231_, v___f_1218_, v_x_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12(lean_object* v___f_1233_, lean_object* v_x_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_box(0);
lean_inc_ref(v___y_1235_);
v___x_1247_ = l_Lean_Meta_Sym_Simp_simpNatRel___redArg(v___y_1235_, v___y_1239_, v___y_1242_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
if (lean_obj_tag(v_a_1248_) == 0)
{
uint8_t v_done_1249_; 
v_done_1249_ = lean_ctor_get_uint8(v_a_1248_, 0);
if (v_done_1249_ == 0)
{
uint8_t v_contextDependent_1250_; lean_object* v___x_1251_; 
lean_dec_ref_known(v___x_1247_, 1);
v_contextDependent_1250_ = lean_ctor_get_uint8(v_a_1248_, 1);
lean_dec_ref_known(v_a_1248_, 0);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc_ref(v___y_1237_);
lean_inc(v___y_1236_);
v___x_1251_ = lean_apply_12(v___f_1233_, v___x_1246_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, lean_box(0));
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; uint8_t v___y_1254_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
if (v_contextDependent_1250_ == 0)
{
lean_dec(v_a_1252_);
return v___x_1251_;
}
else
{
if (lean_obj_tag(v_a_1252_) == 0)
{
uint8_t v_contextDependent_1264_; 
v_contextDependent_1264_ = lean_ctor_get_uint8(v_a_1252_, 1);
v___y_1254_ = v_contextDependent_1264_;
goto v___jp_1253_;
}
else
{
uint8_t v_contextDependent_1265_; 
v_contextDependent_1265_ = lean_ctor_get_uint8(v_a_1252_, sizeof(void*)*2 + 1);
v___y_1254_ = v_contextDependent_1265_;
goto v___jp_1253_;
}
}
v___jp_1253_:
{
if (v___y_1254_ == 0)
{
lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1262_; 
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1251_, 0);
lean_dec(v_unused_1263_);
v___x_1256_ = v___x_1251_;
v_isShared_1257_ = v_isSharedCheck_1262_;
goto v_resetjp_1255_;
}
else
{
lean_dec(v___x_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1262_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1252_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1258_);
v___x_1260_ = v___x_1256_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_dec(v_a_1252_);
return v___x_1251_;
}
}
}
else
{
return v___x_1251_;
}
}
else
{
lean_dec_ref_known(v_a_1248_, 0);
lean_dec_ref(v___y_1235_);
lean_dec_ref(v___f_1233_);
return v___x_1247_;
}
}
else
{
uint8_t v_done_1266_; 
v_done_1266_ = lean_ctor_get_uint8(v_a_1248_, sizeof(void*)*2);
if (v_done_1266_ == 0)
{
lean_object* v_e_x27_1267_; lean_object* v_proof_1268_; uint8_t v_contextDependent_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref_known(v___x_1247_, 1);
v_e_x27_1267_ = lean_ctor_get(v_a_1248_, 0);
v_proof_1268_ = lean_ctor_get(v_a_1248_, 1);
v_contextDependent_1269_ = lean_ctor_get_uint8(v_a_1248_, sizeof(void*)*2 + 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_a_1248_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1271_ = v_a_1248_;
v_isShared_1272_ = v_isSharedCheck_1319_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_proof_1268_);
lean_inc(v_e_x27_1267_);
lean_dec(v_a_1248_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1319_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; 
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc_ref(v___y_1237_);
lean_inc(v___y_1236_);
lean_inc_ref(v_e_x27_1267_);
v___x_1273_ = lean_apply_12(v___f_1233_, v___x_1246_, v_e_x27_1267_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, lean_box(0));
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1318_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1318_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1318_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
if (lean_obj_tag(v_a_1274_) == 0)
{
uint8_t v_done_1278_; uint8_t v_contextDependent_1279_; uint8_t v___y_1281_; 
lean_dec_ref(v___y_1235_);
v_done_1278_ = lean_ctor_get_uint8(v_a_1274_, 0);
v_contextDependent_1279_ = lean_ctor_get_uint8(v_a_1274_, 1);
lean_dec_ref_known(v_a_1274_, 0);
if (v_contextDependent_1269_ == 0)
{
v___y_1281_ = v_contextDependent_1279_;
goto v___jp_1280_;
}
else
{
v___y_1281_ = v_contextDependent_1269_;
goto v___jp_1280_;
}
v___jp_1280_:
{
lean_object* v___x_1283_; 
if (v_isShared_1272_ == 0)
{
v___x_1283_ = v___x_1271_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_e_x27_1267_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_proof_1268_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1285_; 
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*2, v_done_1278_);
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*2 + 1, v___y_1281_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1283_);
v___x_1285_ = v___x_1276_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_object* v_e_x27_1288_; lean_object* v_proof_1289_; uint8_t v_done_1290_; uint8_t v_contextDependent_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1317_; 
lean_del_object(v___x_1276_);
lean_del_object(v___x_1271_);
v_e_x27_1288_ = lean_ctor_get(v_a_1274_, 0);
v_proof_1289_ = lean_ctor_get(v_a_1274_, 1);
v_done_1290_ = lean_ctor_get_uint8(v_a_1274_, sizeof(void*)*2);
v_contextDependent_1291_ = lean_ctor_get_uint8(v_a_1274_, sizeof(void*)*2 + 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_a_1274_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1293_ = v_a_1274_;
v_isShared_1294_ = v_isSharedCheck_1317_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_proof_1289_);
lean_inc(v_e_x27_1288_);
lean_dec(v_a_1274_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1317_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; 
lean_inc_ref(v_e_x27_1288_);
v___x_1295_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1235_, v_e_x27_1267_, v_proof_1268_, v_e_x27_1288_, v_proof_1289_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1308_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1308_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1308_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
uint8_t v___y_1301_; 
if (v_contextDependent_1269_ == 0)
{
v___y_1301_ = v_contextDependent_1291_;
goto v___jp_1300_;
}
else
{
v___y_1301_ = v_contextDependent_1269_;
goto v___jp_1300_;
}
v___jp_1300_:
{
lean_object* v___x_1303_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v_a_1296_);
v___x_1303_ = v___x_1293_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_e_x27_1288_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_a_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*2, v_done_1290_);
v___x_1303_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*2 + 1, v___y_1301_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1303_);
v___x_1305_ = v___x_1298_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_del_object(v___x_1293_);
lean_dec_ref(v_e_x27_1288_);
v_a_1309_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1295_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1295_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1271_);
lean_dec_ref(v_proof_1268_);
lean_dec_ref(v_e_x27_1267_);
lean_dec_ref(v___y_1235_);
return v___x_1273_;
}
}
}
else
{
lean_dec_ref_known(v_a_1248_, 2);
lean_dec_ref(v___y_1235_);
lean_dec_ref(v___f_1233_);
return v___x_1247_;
}
}
}
else
{
lean_dec_ref(v___y_1235_);
lean_dec_ref(v___f_1233_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed(lean_object* v___f_1320_, lean_object* v_x_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__12(v___f_1320_, v_x_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13(lean_object* v___f_1338_, lean_object* v_x_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__13___closed__0));
v___x_1352_ = lean_box(0);
v___x_1353_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_1340_, v___x_1351_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
if (lean_obj_tag(v_a_1354_) == 0)
{
uint8_t v_done_1355_; 
v_done_1355_ = lean_ctor_get_uint8(v_a_1354_, 0);
if (v_done_1355_ == 0)
{
uint8_t v_contextDependent_1356_; lean_object* v___x_1357_; 
lean_dec_ref_known(v___x_1353_, 1);
v_contextDependent_1356_ = lean_ctor_get_uint8(v_a_1354_, 1);
lean_dec_ref_known(v_a_1354_, 0);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
lean_inc(v___y_1347_);
lean_inc_ref(v___y_1346_);
lean_inc(v___y_1345_);
lean_inc_ref(v___y_1344_);
lean_inc(v___y_1343_);
lean_inc_ref(v___y_1342_);
lean_inc(v___y_1341_);
v___x_1357_ = lean_apply_12(v___f_1338_, v___x_1352_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, lean_box(0));
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; uint8_t v___y_1360_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
if (v_contextDependent_1356_ == 0)
{
lean_dec(v_a_1358_);
return v___x_1357_;
}
else
{
if (lean_obj_tag(v_a_1358_) == 0)
{
uint8_t v_contextDependent_1370_; 
v_contextDependent_1370_ = lean_ctor_get_uint8(v_a_1358_, 1);
v___y_1360_ = v_contextDependent_1370_;
goto v___jp_1359_;
}
else
{
uint8_t v_contextDependent_1371_; 
v_contextDependent_1371_ = lean_ctor_get_uint8(v_a_1358_, sizeof(void*)*2 + 1);
v___y_1360_ = v_contextDependent_1371_;
goto v___jp_1359_;
}
}
v___jp_1359_:
{
if (v___y_1360_ == 0)
{
lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1368_; 
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; 
v_unused_1369_ = lean_ctor_get(v___x_1357_, 0);
lean_dec(v_unused_1369_);
v___x_1362_ = v___x_1357_;
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v___x_1357_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1358_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1364_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
lean_dec(v_a_1358_);
return v___x_1357_;
}
}
}
else
{
return v___x_1357_;
}
}
else
{
lean_dec_ref_known(v_a_1354_, 0);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v___f_1338_);
return v___x_1353_;
}
}
else
{
uint8_t v_done_1372_; 
v_done_1372_ = lean_ctor_get_uint8(v_a_1354_, sizeof(void*)*2);
if (v_done_1372_ == 0)
{
lean_object* v_e_x27_1373_; lean_object* v_proof_1374_; uint8_t v_contextDependent_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref_known(v___x_1353_, 1);
v_e_x27_1373_ = lean_ctor_get(v_a_1354_, 0);
v_proof_1374_ = lean_ctor_get(v_a_1354_, 1);
v_contextDependent_1375_ = lean_ctor_get_uint8(v_a_1354_, sizeof(void*)*2 + 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_a_1354_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1377_ = v_a_1354_;
v_isShared_1378_ = v_isSharedCheck_1425_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_proof_1374_);
lean_inc(v_e_x27_1373_);
lean_dec(v_a_1354_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1425_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; 
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
lean_inc(v___y_1347_);
lean_inc_ref(v___y_1346_);
lean_inc(v___y_1345_);
lean_inc_ref(v___y_1344_);
lean_inc(v___y_1343_);
lean_inc_ref(v___y_1342_);
lean_inc(v___y_1341_);
lean_inc_ref(v_e_x27_1373_);
v___x_1379_ = lean_apply_12(v___f_1338_, v___x_1352_, v_e_x27_1373_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, lean_box(0));
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1424_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1424_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1424_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
if (lean_obj_tag(v_a_1380_) == 0)
{
uint8_t v_done_1384_; uint8_t v_contextDependent_1385_; uint8_t v___y_1387_; 
lean_dec_ref(v___y_1340_);
v_done_1384_ = lean_ctor_get_uint8(v_a_1380_, 0);
v_contextDependent_1385_ = lean_ctor_get_uint8(v_a_1380_, 1);
lean_dec_ref_known(v_a_1380_, 0);
if (v_contextDependent_1375_ == 0)
{
v___y_1387_ = v_contextDependent_1385_;
goto v___jp_1386_;
}
else
{
v___y_1387_ = v_contextDependent_1375_;
goto v___jp_1386_;
}
v___jp_1386_:
{
lean_object* v___x_1389_; 
if (v_isShared_1378_ == 0)
{
v___x_1389_ = v___x_1377_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_e_x27_1373_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_proof_1374_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*2, v_done_1384_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*2 + 1, v___y_1387_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1389_);
v___x_1391_ = v___x_1382_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
else
{
lean_object* v_e_x27_1394_; lean_object* v_proof_1395_; uint8_t v_done_1396_; uint8_t v_contextDependent_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1423_; 
lean_del_object(v___x_1382_);
lean_del_object(v___x_1377_);
v_e_x27_1394_ = lean_ctor_get(v_a_1380_, 0);
v_proof_1395_ = lean_ctor_get(v_a_1380_, 1);
v_done_1396_ = lean_ctor_get_uint8(v_a_1380_, sizeof(void*)*2);
v_contextDependent_1397_ = lean_ctor_get_uint8(v_a_1380_, sizeof(void*)*2 + 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_a_1380_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1399_ = v_a_1380_;
v_isShared_1400_ = v_isSharedCheck_1423_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_proof_1395_);
lean_inc(v_e_x27_1394_);
lean_dec(v_a_1380_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1423_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; 
lean_inc_ref(v_e_x27_1394_);
v___x_1401_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1340_, v_e_x27_1373_, v_proof_1374_, v_e_x27_1394_, v_proof_1395_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1414_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1414_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1414_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
uint8_t v___y_1407_; 
if (v_contextDependent_1375_ == 0)
{
v___y_1407_ = v_contextDependent_1397_;
goto v___jp_1406_;
}
else
{
v___y_1407_ = v_contextDependent_1375_;
goto v___jp_1406_;
}
v___jp_1406_:
{
lean_object* v___x_1409_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 1, v_a_1402_);
v___x_1409_ = v___x_1399_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_e_x27_1394_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_a_1402_);
lean_ctor_set_uint8(v_reuseFailAlloc_1413_, sizeof(void*)*2, v_done_1396_);
v___x_1409_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*2 + 1, v___y_1407_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1409_);
v___x_1411_ = v___x_1404_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_del_object(v___x_1399_);
lean_dec_ref(v_e_x27_1394_);
v_a_1415_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1401_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1401_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1377_);
lean_dec_ref(v_proof_1374_);
lean_dec_ref(v_e_x27_1373_);
lean_dec_ref(v___y_1340_);
return v___x_1379_;
}
}
}
else
{
lean_dec_ref_known(v_a_1354_, 2);
lean_dec_ref(v___y_1340_);
lean_dec_ref(v___f_1338_);
return v___x_1353_;
}
}
}
else
{
lean_dec_ref(v___y_1340_);
lean_dec_ref(v___f_1338_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed(lean_object* v___f_1426_, lean_object* v_x_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__13(v___f_1426_, v_x_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14(lean_object* v_thms_1440_, lean_object* v_d_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_pre_1454_; lean_object* v___x_1455_; 
v_pre_1454_ = lean_ctor_get(v_thms_1440_, 0);
v___x_1455_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_pre_1454_, v_d_1441_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed(lean_object* v_thms_1456_, lean_object* v_d_1457_, lean_object* v_x_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__14(v_thms_1456_, v_d_1457_, v_x_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v_thms_1456_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15(lean_object* v_maxChar_1471_, lean_object* v_d_1472_, uint8_t v_distrib_1473_, lean_object* v___f_1474_, lean_object* v_x_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
uint8_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1487_ = 1;
v___x_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1488_, 0, v_maxChar_1471_);
v___x_1489_ = lean_box(0);
lean_inc_ref(v___y_1476_);
v___x_1490_ = l_Lean_Meta_Sym_Simp_simpArith(v_d_1472_, v___x_1487_, v_distrib_1473_, v___x_1488_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec_ref_known(v___x_1488_, 1);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
if (lean_obj_tag(v_a_1491_) == 0)
{
uint8_t v_done_1492_; 
v_done_1492_ = lean_ctor_get_uint8(v_a_1491_, 0);
if (v_done_1492_ == 0)
{
uint8_t v_contextDependent_1493_; lean_object* v___x_1494_; 
lean_dec_ref_known(v___x_1490_, 1);
v_contextDependent_1493_ = lean_ctor_get_uint8(v_a_1491_, 1);
lean_dec_ref_known(v_a_1491_, 0);
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1477_);
v___x_1494_ = lean_apply_12(v___f_1474_, v___x_1489_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, lean_box(0));
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; uint8_t v___y_1497_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
if (v_contextDependent_1493_ == 0)
{
lean_dec(v_a_1495_);
return v___x_1494_;
}
else
{
if (lean_obj_tag(v_a_1495_) == 0)
{
uint8_t v_contextDependent_1507_; 
v_contextDependent_1507_ = lean_ctor_get_uint8(v_a_1495_, 1);
v___y_1497_ = v_contextDependent_1507_;
goto v___jp_1496_;
}
else
{
uint8_t v_contextDependent_1508_; 
v_contextDependent_1508_ = lean_ctor_get_uint8(v_a_1495_, sizeof(void*)*2 + 1);
v___y_1497_ = v_contextDependent_1508_;
goto v___jp_1496_;
}
}
v___jp_1496_:
{
if (v___y_1497_ == 0)
{
lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1505_; 
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v___x_1494_, 0);
lean_dec(v_unused_1506_);
v___x_1499_ = v___x_1494_;
v_isShared_1500_ = v_isSharedCheck_1505_;
goto v_resetjp_1498_;
}
else
{
lean_dec(v___x_1494_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1505_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1495_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1501_);
v___x_1503_ = v___x_1499_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
else
{
lean_dec(v_a_1495_);
return v___x_1494_;
}
}
}
else
{
return v___x_1494_;
}
}
else
{
lean_dec_ref_known(v_a_1491_, 0);
lean_dec_ref(v___y_1476_);
lean_dec_ref(v___f_1474_);
return v___x_1490_;
}
}
else
{
uint8_t v_done_1509_; 
v_done_1509_ = lean_ctor_get_uint8(v_a_1491_, sizeof(void*)*2);
if (v_done_1509_ == 0)
{
lean_object* v_e_x27_1510_; lean_object* v_proof_1511_; uint8_t v_contextDependent_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref_known(v___x_1490_, 1);
v_e_x27_1510_ = lean_ctor_get(v_a_1491_, 0);
v_proof_1511_ = lean_ctor_get(v_a_1491_, 1);
v_contextDependent_1512_ = lean_ctor_get_uint8(v_a_1491_, sizeof(void*)*2 + 1);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_a_1491_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1514_ = v_a_1491_;
v_isShared_1515_ = v_isSharedCheck_1562_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_proof_1511_);
lean_inc(v_e_x27_1510_);
lean_dec(v_a_1491_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1562_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; 
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
lean_inc_ref(v___y_1478_);
lean_inc(v___y_1477_);
lean_inc_ref(v_e_x27_1510_);
v___x_1516_ = lean_apply_12(v___f_1474_, v___x_1489_, v_e_x27_1510_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, lean_box(0));
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1561_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1561_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1561_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
if (lean_obj_tag(v_a_1517_) == 0)
{
uint8_t v_done_1521_; uint8_t v_contextDependent_1522_; uint8_t v___y_1524_; 
lean_dec_ref(v___y_1476_);
v_done_1521_ = lean_ctor_get_uint8(v_a_1517_, 0);
v_contextDependent_1522_ = lean_ctor_get_uint8(v_a_1517_, 1);
lean_dec_ref_known(v_a_1517_, 0);
if (v_contextDependent_1512_ == 0)
{
v___y_1524_ = v_contextDependent_1522_;
goto v___jp_1523_;
}
else
{
v___y_1524_ = v_contextDependent_1512_;
goto v___jp_1523_;
}
v___jp_1523_:
{
lean_object* v___x_1526_; 
if (v_isShared_1515_ == 0)
{
v___x_1526_ = v___x_1514_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_e_x27_1510_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_proof_1511_);
v___x_1526_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1528_; 
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*2, v_done_1521_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*2 + 1, v___y_1524_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1526_);
v___x_1528_ = v___x_1519_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
lean_object* v_e_x27_1531_; lean_object* v_proof_1532_; uint8_t v_done_1533_; uint8_t v_contextDependent_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1560_; 
lean_del_object(v___x_1519_);
lean_del_object(v___x_1514_);
v_e_x27_1531_ = lean_ctor_get(v_a_1517_, 0);
v_proof_1532_ = lean_ctor_get(v_a_1517_, 1);
v_done_1533_ = lean_ctor_get_uint8(v_a_1517_, sizeof(void*)*2);
v_contextDependent_1534_ = lean_ctor_get_uint8(v_a_1517_, sizeof(void*)*2 + 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_a_1517_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1536_ = v_a_1517_;
v_isShared_1537_ = v_isSharedCheck_1560_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_proof_1532_);
lean_inc(v_e_x27_1531_);
lean_dec(v_a_1517_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1560_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; 
lean_inc_ref(v_e_x27_1531_);
v___x_1538_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1476_, v_e_x27_1510_, v_proof_1511_, v_e_x27_1531_, v_proof_1532_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1551_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1551_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1551_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
uint8_t v___y_1544_; 
if (v_contextDependent_1512_ == 0)
{
v___y_1544_ = v_contextDependent_1534_;
goto v___jp_1543_;
}
else
{
v___y_1544_ = v_contextDependent_1512_;
goto v___jp_1543_;
}
v___jp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 1, v_a_1539_);
v___x_1546_ = v___x_1536_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_e_x27_1531_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_a_1539_);
lean_ctor_set_uint8(v_reuseFailAlloc_1550_, sizeof(void*)*2, v_done_1533_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
lean_ctor_set_uint8(v___x_1546_, sizeof(void*)*2 + 1, v___y_1544_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1546_);
v___x_1548_ = v___x_1541_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_del_object(v___x_1536_);
lean_dec_ref(v_e_x27_1531_);
v_a_1552_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1538_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1538_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1514_);
lean_dec_ref(v_proof_1511_);
lean_dec_ref(v_e_x27_1510_);
lean_dec_ref(v___y_1476_);
return v___x_1516_;
}
}
}
else
{
lean_dec_ref_known(v_a_1491_, 2);
lean_dec_ref(v___y_1476_);
lean_dec_ref(v___f_1474_);
return v___x_1490_;
}
}
}
else
{
lean_dec_ref(v___y_1476_);
lean_dec_ref(v___f_1474_);
return v___x_1490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed(lean_object* v_maxChar_1563_, lean_object* v_d_1564_, lean_object* v_distrib_1565_, lean_object* v___f_1566_, lean_object* v_x_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
uint8_t v_distrib_boxed_1579_; lean_object* v_res_1580_; 
v_distrib_boxed_1579_ = lean_unbox(v_distrib_1565_);
v_res_1580_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__15(v_maxChar_1563_, v_d_1564_, v_distrib_boxed_1579_, v___f_1566_, v_x_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16(lean_object* v___f_1581_, lean_object* v_x_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_box(0);
v___x_1595_ = l_Lean_Meta_Grind_NormSym_pushNot(v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
if (lean_obj_tag(v_a_1596_) == 0)
{
uint8_t v_done_1597_; 
v_done_1597_ = lean_ctor_get_uint8(v_a_1596_, 0);
if (v_done_1597_ == 0)
{
uint8_t v_contextDependent_1598_; lean_object* v___x_1599_; 
lean_dec_ref_known(v___x_1595_, 1);
v_contextDependent_1598_ = lean_ctor_get_uint8(v_a_1596_, 1);
lean_dec_ref_known(v_a_1596_, 0);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
lean_inc(v___y_1584_);
v___x_1599_ = lean_apply_12(v___f_1581_, v___x_1594_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, lean_box(0));
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; uint8_t v___y_1602_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
if (v_contextDependent_1598_ == 0)
{
lean_dec(v_a_1600_);
return v___x_1599_;
}
else
{
if (lean_obj_tag(v_a_1600_) == 0)
{
uint8_t v_contextDependent_1612_; 
v_contextDependent_1612_ = lean_ctor_get_uint8(v_a_1600_, 1);
v___y_1602_ = v_contextDependent_1612_;
goto v___jp_1601_;
}
else
{
uint8_t v_contextDependent_1613_; 
v_contextDependent_1613_ = lean_ctor_get_uint8(v_a_1600_, sizeof(void*)*2 + 1);
v___y_1602_ = v_contextDependent_1613_;
goto v___jp_1601_;
}
}
v___jp_1601_:
{
if (v___y_1602_ == 0)
{
lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1610_; 
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v___x_1599_, 0);
lean_dec(v_unused_1611_);
v___x_1604_ = v___x_1599_;
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
else
{
lean_dec(v___x_1599_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1600_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1606_);
v___x_1608_ = v___x_1604_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
else
{
lean_dec(v_a_1600_);
return v___x_1599_;
}
}
}
else
{
return v___x_1599_;
}
}
else
{
lean_dec_ref_known(v_a_1596_, 0);
lean_dec_ref(v___y_1583_);
lean_dec_ref(v___f_1581_);
return v___x_1595_;
}
}
else
{
uint8_t v_done_1614_; 
v_done_1614_ = lean_ctor_get_uint8(v_a_1596_, sizeof(void*)*2);
if (v_done_1614_ == 0)
{
lean_object* v_e_x27_1615_; lean_object* v_proof_1616_; uint8_t v_contextDependent_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref_known(v___x_1595_, 1);
v_e_x27_1615_ = lean_ctor_get(v_a_1596_, 0);
v_proof_1616_ = lean_ctor_get(v_a_1596_, 1);
v_contextDependent_1617_ = lean_ctor_get_uint8(v_a_1596_, sizeof(void*)*2 + 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_a_1596_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1619_ = v_a_1596_;
v_isShared_1620_ = v_isSharedCheck_1667_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_proof_1616_);
lean_inc(v_e_x27_1615_);
lean_dec(v_a_1596_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1667_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; 
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc_ref(v___y_1585_);
lean_inc(v___y_1584_);
lean_inc_ref(v_e_x27_1615_);
v___x_1621_ = lean_apply_12(v___f_1581_, v___x_1594_, v_e_x27_1615_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, lean_box(0));
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1666_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1666_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1666_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
if (lean_obj_tag(v_a_1622_) == 0)
{
uint8_t v_done_1626_; uint8_t v_contextDependent_1627_; uint8_t v___y_1629_; 
lean_dec_ref(v___y_1583_);
v_done_1626_ = lean_ctor_get_uint8(v_a_1622_, 0);
v_contextDependent_1627_ = lean_ctor_get_uint8(v_a_1622_, 1);
lean_dec_ref_known(v_a_1622_, 0);
if (v_contextDependent_1617_ == 0)
{
v___y_1629_ = v_contextDependent_1627_;
goto v___jp_1628_;
}
else
{
v___y_1629_ = v_contextDependent_1617_;
goto v___jp_1628_;
}
v___jp_1628_:
{
lean_object* v___x_1631_; 
if (v_isShared_1620_ == 0)
{
v___x_1631_ = v___x_1619_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_e_x27_1615_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_proof_1616_);
v___x_1631_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1633_; 
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*2, v_done_1626_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*2 + 1, v___y_1629_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1631_);
v___x_1633_ = v___x_1624_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_e_x27_1636_; lean_object* v_proof_1637_; uint8_t v_done_1638_; uint8_t v_contextDependent_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1665_; 
lean_del_object(v___x_1624_);
lean_del_object(v___x_1619_);
v_e_x27_1636_ = lean_ctor_get(v_a_1622_, 0);
v_proof_1637_ = lean_ctor_get(v_a_1622_, 1);
v_done_1638_ = lean_ctor_get_uint8(v_a_1622_, sizeof(void*)*2);
v_contextDependent_1639_ = lean_ctor_get_uint8(v_a_1622_, sizeof(void*)*2 + 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_a_1622_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1641_ = v_a_1622_;
v_isShared_1642_ = v_isSharedCheck_1665_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_proof_1637_);
lean_inc(v_e_x27_1636_);
lean_dec(v_a_1622_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1665_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; 
lean_inc_ref(v_e_x27_1636_);
v___x_1643_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1583_, v_e_x27_1615_, v_proof_1616_, v_e_x27_1636_, v_proof_1637_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1656_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1656_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1656_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
uint8_t v___y_1649_; 
if (v_contextDependent_1617_ == 0)
{
v___y_1649_ = v_contextDependent_1639_;
goto v___jp_1648_;
}
else
{
v___y_1649_ = v_contextDependent_1617_;
goto v___jp_1648_;
}
v___jp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 1, v_a_1644_);
v___x_1651_ = v___x_1641_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_e_x27_1636_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_a_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1655_, sizeof(void*)*2, v_done_1638_);
v___x_1651_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1653_; 
lean_ctor_set_uint8(v___x_1651_, sizeof(void*)*2 + 1, v___y_1649_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1651_);
v___x_1653_ = v___x_1646_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_del_object(v___x_1641_);
lean_dec_ref(v_e_x27_1636_);
v_a_1657_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1643_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1643_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1619_);
lean_dec_ref(v_proof_1616_);
lean_dec_ref(v_e_x27_1615_);
lean_dec_ref(v___y_1583_);
return v___x_1621_;
}
}
}
else
{
lean_dec_ref_known(v_a_1596_, 2);
lean_dec_ref(v___y_1583_);
lean_dec_ref(v___f_1581_);
return v___x_1595_;
}
}
}
else
{
lean_dec_ref(v___y_1583_);
lean_dec_ref(v___f_1581_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed(lean_object* v___f_1668_, lean_object* v_x_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__16(v___f_1668_, v_x_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17(lean_object* v_pre_1682_, lean_object* v___f_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = lean_box(0);
lean_inc(v___y_1693_);
lean_inc_ref(v___y_1692_);
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1688_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
v___x_1696_ = lean_apply_11(v_pre_1682_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, lean_box(0));
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
if (lean_obj_tag(v_a_1697_) == 0)
{
uint8_t v_done_1698_; 
v_done_1698_ = lean_ctor_get_uint8(v_a_1697_, 0);
if (v_done_1698_ == 0)
{
uint8_t v_contextDependent_1699_; lean_object* v___x_1700_; 
lean_dec_ref_known(v___x_1696_, 1);
v_contextDependent_1699_ = lean_ctor_get_uint8(v_a_1697_, 1);
lean_dec_ref_known(v_a_1697_, 0);
v___x_1700_ = lean_apply_12(v___f_1683_, v___x_1695_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, lean_box(0));
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; uint8_t v___y_1703_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
if (v_contextDependent_1699_ == 0)
{
lean_dec(v_a_1701_);
return v___x_1700_;
}
else
{
if (lean_obj_tag(v_a_1701_) == 0)
{
uint8_t v_contextDependent_1713_; 
v_contextDependent_1713_ = lean_ctor_get_uint8(v_a_1701_, 1);
v___y_1703_ = v_contextDependent_1713_;
goto v___jp_1702_;
}
else
{
uint8_t v_contextDependent_1714_; 
v_contextDependent_1714_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*2 + 1);
v___y_1703_ = v_contextDependent_1714_;
goto v___jp_1702_;
}
}
v___jp_1702_:
{
if (v___y_1703_ == 0)
{
lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1711_; 
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; 
v_unused_1712_ = lean_ctor_get(v___x_1700_, 0);
lean_dec(v_unused_1712_);
v___x_1705_ = v___x_1700_;
v_isShared_1706_ = v_isSharedCheck_1711_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v___x_1700_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1711_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1707_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1701_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1707_);
v___x_1709_ = v___x_1705_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
lean_dec(v_a_1701_);
return v___x_1700_;
}
}
}
else
{
return v___x_1700_;
}
}
else
{
lean_dec_ref_known(v_a_1697_, 0);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec_ref(v___f_1683_);
return v___x_1696_;
}
}
else
{
uint8_t v_done_1715_; 
v_done_1715_ = lean_ctor_get_uint8(v_a_1697_, sizeof(void*)*2);
if (v_done_1715_ == 0)
{
lean_object* v_e_x27_1716_; lean_object* v_proof_1717_; uint8_t v_contextDependent_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref_known(v___x_1696_, 1);
v_e_x27_1716_ = lean_ctor_get(v_a_1697_, 0);
v_proof_1717_ = lean_ctor_get(v_a_1697_, 1);
v_contextDependent_1718_ = lean_ctor_get_uint8(v_a_1697_, sizeof(void*)*2 + 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_a_1697_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1720_ = v_a_1697_;
v_isShared_1721_ = v_isSharedCheck_1768_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_proof_1717_);
lean_inc(v_e_x27_1716_);
lean_dec(v_a_1697_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1768_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; 
lean_inc(v___y_1693_);
lean_inc_ref(v___y_1692_);
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1688_);
lean_inc_ref(v_e_x27_1716_);
v___x_1722_ = lean_apply_12(v___f_1683_, v___x_1695_, v_e_x27_1716_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, lean_box(0));
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1767_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1767_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1767_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
if (lean_obj_tag(v_a_1723_) == 0)
{
uint8_t v_done_1727_; uint8_t v_contextDependent_1728_; uint8_t v___y_1730_; 
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec_ref(v___y_1684_);
v_done_1727_ = lean_ctor_get_uint8(v_a_1723_, 0);
v_contextDependent_1728_ = lean_ctor_get_uint8(v_a_1723_, 1);
lean_dec_ref_known(v_a_1723_, 0);
if (v_contextDependent_1718_ == 0)
{
v___y_1730_ = v_contextDependent_1728_;
goto v___jp_1729_;
}
else
{
v___y_1730_ = v_contextDependent_1718_;
goto v___jp_1729_;
}
v___jp_1729_:
{
lean_object* v___x_1732_; 
if (v_isShared_1721_ == 0)
{
v___x_1732_ = v___x_1720_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_e_x27_1716_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_proof_1717_);
v___x_1732_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1734_; 
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*2, v_done_1727_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*2 + 1, v___y_1730_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1732_);
v___x_1734_ = v___x_1725_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_object* v_e_x27_1737_; lean_object* v_proof_1738_; uint8_t v_done_1739_; uint8_t v_contextDependent_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1766_; 
lean_del_object(v___x_1725_);
lean_del_object(v___x_1720_);
v_e_x27_1737_ = lean_ctor_get(v_a_1723_, 0);
v_proof_1738_ = lean_ctor_get(v_a_1723_, 1);
v_done_1739_ = lean_ctor_get_uint8(v_a_1723_, sizeof(void*)*2);
v_contextDependent_1740_ = lean_ctor_get_uint8(v_a_1723_, sizeof(void*)*2 + 1);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_a_1723_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1742_ = v_a_1723_;
v_isShared_1743_ = v_isSharedCheck_1766_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_proof_1738_);
lean_inc(v_e_x27_1737_);
lean_dec(v_a_1723_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1766_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; 
lean_inc_ref(v_e_x27_1737_);
v___x_1744_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1684_, v_e_x27_1716_, v_proof_1717_, v_e_x27_1737_, v_proof_1738_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1757_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1757_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1757_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
uint8_t v___y_1750_; 
if (v_contextDependent_1718_ == 0)
{
v___y_1750_ = v_contextDependent_1740_;
goto v___jp_1749_;
}
else
{
v___y_1750_ = v_contextDependent_1718_;
goto v___jp_1749_;
}
v___jp_1749_:
{
lean_object* v___x_1752_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v_a_1745_);
v___x_1752_ = v___x_1742_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_e_x27_1737_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_a_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*2, v_done_1739_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*2 + 1, v___y_1750_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1752_);
v___x_1754_ = v___x_1747_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_del_object(v___x_1742_);
lean_dec_ref(v_e_x27_1737_);
v_a_1758_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1744_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1744_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1720_);
lean_dec_ref(v_proof_1717_);
lean_dec_ref(v_e_x27_1716_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec_ref(v___y_1684_);
return v___x_1722_;
}
}
}
else
{
lean_dec_ref_known(v_a_1697_, 2);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec_ref(v___f_1683_);
return v___x_1696_;
}
}
}
else
{
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec_ref(v___f_1683_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed(lean_object* v_pre_1769_, lean_object* v___f_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__17(v_pre_1769_, v___f_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18(lean_object* v_post_1783_, lean_object* v_d_1784_, lean_object* v___f_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_box(0);
lean_inc_ref(v___y_1786_);
v___x_1798_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_post_1783_, v_d_1784_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
if (lean_obj_tag(v_a_1799_) == 0)
{
uint8_t v_done_1800_; 
v_done_1800_ = lean_ctor_get_uint8(v_a_1799_, 0);
if (v_done_1800_ == 0)
{
uint8_t v_contextDependent_1801_; lean_object* v___x_1802_; 
lean_dec_ref_known(v___x_1798_, 1);
v_contextDependent_1801_ = lean_ctor_get_uint8(v_a_1799_, 1);
lean_dec_ref_known(v_a_1799_, 0);
v___x_1802_ = lean_apply_12(v___f_1785_, v___x_1797_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, lean_box(0));
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; uint8_t v___y_1805_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
if (v_contextDependent_1801_ == 0)
{
lean_dec(v_a_1803_);
return v___x_1802_;
}
else
{
if (lean_obj_tag(v_a_1803_) == 0)
{
uint8_t v_contextDependent_1815_; 
v_contextDependent_1815_ = lean_ctor_get_uint8(v_a_1803_, 1);
v___y_1805_ = v_contextDependent_1815_;
goto v___jp_1804_;
}
else
{
uint8_t v_contextDependent_1816_; 
v_contextDependent_1816_ = lean_ctor_get_uint8(v_a_1803_, sizeof(void*)*2 + 1);
v___y_1805_ = v_contextDependent_1816_;
goto v___jp_1804_;
}
}
v___jp_1804_:
{
if (v___y_1805_ == 0)
{
lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1813_; 
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v___x_1802_, 0);
lean_dec(v_unused_1814_);
v___x_1807_ = v___x_1802_;
v_isShared_1808_ = v_isSharedCheck_1813_;
goto v_resetjp_1806_;
}
else
{
lean_dec(v___x_1802_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1813_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1803_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1809_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
else
{
lean_dec(v_a_1803_);
return v___x_1802_;
}
}
}
else
{
return v___x_1802_;
}
}
else
{
lean_dec_ref_known(v_a_1799_, 0);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v___f_1785_);
return v___x_1798_;
}
}
else
{
uint8_t v_done_1817_; 
v_done_1817_ = lean_ctor_get_uint8(v_a_1799_, sizeof(void*)*2);
if (v_done_1817_ == 0)
{
lean_object* v_e_x27_1818_; lean_object* v_proof_1819_; uint8_t v_contextDependent_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref_known(v___x_1798_, 1);
v_e_x27_1818_ = lean_ctor_get(v_a_1799_, 0);
v_proof_1819_ = lean_ctor_get(v_a_1799_, 1);
v_contextDependent_1820_ = lean_ctor_get_uint8(v_a_1799_, sizeof(void*)*2 + 1);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_a_1799_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1822_ = v_a_1799_;
v_isShared_1823_ = v_isSharedCheck_1870_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_proof_1819_);
lean_inc(v_e_x27_1818_);
lean_dec(v_a_1799_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1870_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; 
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
lean_inc(v___y_1793_);
lean_inc_ref(v___y_1792_);
lean_inc(v___y_1791_);
lean_inc_ref(v___y_1790_);
lean_inc_ref(v_e_x27_1818_);
v___x_1824_ = lean_apply_12(v___f_1785_, v___x_1797_, v_e_x27_1818_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, lean_box(0));
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1869_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1869_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1869_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
if (lean_obj_tag(v_a_1825_) == 0)
{
uint8_t v_done_1829_; uint8_t v_contextDependent_1830_; uint8_t v___y_1832_; 
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___y_1786_);
v_done_1829_ = lean_ctor_get_uint8(v_a_1825_, 0);
v_contextDependent_1830_ = lean_ctor_get_uint8(v_a_1825_, 1);
lean_dec_ref_known(v_a_1825_, 0);
if (v_contextDependent_1820_ == 0)
{
v___y_1832_ = v_contextDependent_1830_;
goto v___jp_1831_;
}
else
{
v___y_1832_ = v_contextDependent_1820_;
goto v___jp_1831_;
}
v___jp_1831_:
{
lean_object* v___x_1834_; 
if (v_isShared_1823_ == 0)
{
v___x_1834_ = v___x_1822_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_e_x27_1818_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_proof_1819_);
v___x_1834_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1836_; 
lean_ctor_set_uint8(v___x_1834_, sizeof(void*)*2, v_done_1829_);
lean_ctor_set_uint8(v___x_1834_, sizeof(void*)*2 + 1, v___y_1832_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1834_);
v___x_1836_ = v___x_1827_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
else
{
lean_object* v_e_x27_1839_; lean_object* v_proof_1840_; uint8_t v_done_1841_; uint8_t v_contextDependent_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1868_; 
lean_del_object(v___x_1827_);
lean_del_object(v___x_1822_);
v_e_x27_1839_ = lean_ctor_get(v_a_1825_, 0);
v_proof_1840_ = lean_ctor_get(v_a_1825_, 1);
v_done_1841_ = lean_ctor_get_uint8(v_a_1825_, sizeof(void*)*2);
v_contextDependent_1842_ = lean_ctor_get_uint8(v_a_1825_, sizeof(void*)*2 + 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_a_1825_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1844_ = v_a_1825_;
v_isShared_1845_ = v_isSharedCheck_1868_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_proof_1840_);
lean_inc(v_e_x27_1839_);
lean_dec(v_a_1825_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1868_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; 
lean_inc_ref(v_e_x27_1839_);
v___x_1846_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1786_, v_e_x27_1818_, v_proof_1819_, v_e_x27_1839_, v_proof_1840_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1859_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1859_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1859_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
uint8_t v___y_1852_; 
if (v_contextDependent_1820_ == 0)
{
v___y_1852_ = v_contextDependent_1842_;
goto v___jp_1851_;
}
else
{
v___y_1852_ = v_contextDependent_1820_;
goto v___jp_1851_;
}
v___jp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 1, v_a_1847_);
v___x_1854_ = v___x_1844_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_e_x27_1839_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_a_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*2, v_done_1841_);
v___x_1854_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*2 + 1, v___y_1852_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1854_);
v___x_1856_ = v___x_1849_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_del_object(v___x_1844_);
lean_dec_ref(v_e_x27_1839_);
v_a_1860_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1846_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1846_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1822_);
lean_dec_ref(v_proof_1819_);
lean_dec_ref(v_e_x27_1818_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v___y_1786_);
return v___x_1824_;
}
}
}
else
{
lean_dec_ref_known(v_a_1799_, 2);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v___f_1785_);
return v___x_1798_;
}
}
}
else
{
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v___f_1785_);
return v___x_1798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__18___boxed(lean_object* v_post_1871_, lean_object* v_d_1872_, lean_object* v___f_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__18(v_post_1871_, v_d_1872_, v___f_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec_ref(v_post_1871_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__19(lean_object* v_pre_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
lean_inc(v___y_1894_);
lean_inc_ref(v___y_1893_);
lean_inc(v___y_1892_);
lean_inc_ref(v___y_1891_);
lean_inc_ref(v___y_1887_);
v___x_1898_ = lean_apply_11(v_pre_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, lean_box(0));
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
if (lean_obj_tag(v_a_1899_) == 0)
{
uint8_t v_done_1900_; 
v_done_1900_ = lean_ctor_get_uint8(v_a_1899_, 0);
if (v_done_1900_ == 0)
{
uint8_t v_contextDependent_1901_; lean_object* v___x_1902_; 
lean_dec_ref_known(v___x_1898_, 1);
v_contextDependent_1901_ = lean_ctor_get_uint8(v_a_1899_, 1);
lean_dec_ref_known(v_a_1899_, 0);
v___x_1902_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v___y_1887_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; uint8_t v___y_1905_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
if (v_contextDependent_1901_ == 0)
{
return v___x_1902_;
}
else
{
if (lean_obj_tag(v_a_1903_) == 0)
{
uint8_t v_contextDependent_1915_; 
v_contextDependent_1915_ = lean_ctor_get_uint8(v_a_1903_, 1);
v___y_1905_ = v_contextDependent_1915_;
goto v___jp_1904_;
}
else
{
uint8_t v_contextDependent_1916_; 
v_contextDependent_1916_ = lean_ctor_get_uint8(v_a_1903_, sizeof(void*)*2 + 1);
v___y_1905_ = v_contextDependent_1916_;
goto v___jp_1904_;
}
}
v___jp_1904_:
{
if (v___y_1905_ == 0)
{
lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1913_; 
lean_inc(v_a_1903_);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; 
v_unused_1914_ = lean_ctor_get(v___x_1902_, 0);
lean_dec(v_unused_1914_);
v___x_1907_ = v___x_1902_;
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
else
{
lean_dec(v___x_1902_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1903_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
else
{
return v___x_1902_;
}
}
}
else
{
return v___x_1902_;
}
}
else
{
lean_dec_ref_known(v_a_1899_, 0);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1887_);
return v___x_1898_;
}
}
else
{
uint8_t v_done_1917_; 
v_done_1917_ = lean_ctor_get_uint8(v_a_1899_, sizeof(void*)*2);
if (v_done_1917_ == 0)
{
lean_object* v_e_x27_1918_; lean_object* v_proof_1919_; uint8_t v_contextDependent_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref_known(v___x_1898_, 1);
v_e_x27_1918_ = lean_ctor_get(v_a_1899_, 0);
v_proof_1919_ = lean_ctor_get(v_a_1899_, 1);
v_contextDependent_1920_ = lean_ctor_get_uint8(v_a_1899_, sizeof(void*)*2 + 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_a_1899_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1922_ = v_a_1899_;
v_isShared_1923_ = v_isSharedCheck_1970_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_proof_1919_);
lean_inc(v_e_x27_1918_);
lean_dec(v_a_1899_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1970_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; 
lean_inc_ref(v_e_x27_1918_);
v___x_1924_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v_e_x27_1918_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1969_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1969_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1969_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
if (lean_obj_tag(v_a_1925_) == 0)
{
uint8_t v_done_1929_; uint8_t v_contextDependent_1930_; uint8_t v___y_1932_; 
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1887_);
v_done_1929_ = lean_ctor_get_uint8(v_a_1925_, 0);
v_contextDependent_1930_ = lean_ctor_get_uint8(v_a_1925_, 1);
lean_dec_ref_known(v_a_1925_, 0);
if (v_contextDependent_1920_ == 0)
{
v___y_1932_ = v_contextDependent_1930_;
goto v___jp_1931_;
}
else
{
v___y_1932_ = v_contextDependent_1920_;
goto v___jp_1931_;
}
v___jp_1931_:
{
lean_object* v___x_1934_; 
if (v_isShared_1923_ == 0)
{
v___x_1934_ = v___x_1922_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_e_x27_1918_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_proof_1919_);
v___x_1934_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1936_; 
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*2, v_done_1929_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*2 + 1, v___y_1932_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1934_);
v___x_1936_ = v___x_1927_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v_e_x27_1939_; lean_object* v_proof_1940_; uint8_t v_done_1941_; uint8_t v_contextDependent_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1968_; 
lean_del_object(v___x_1927_);
lean_del_object(v___x_1922_);
v_e_x27_1939_ = lean_ctor_get(v_a_1925_, 0);
v_proof_1940_ = lean_ctor_get(v_a_1925_, 1);
v_done_1941_ = lean_ctor_get_uint8(v_a_1925_, sizeof(void*)*2);
v_contextDependent_1942_ = lean_ctor_get_uint8(v_a_1925_, sizeof(void*)*2 + 1);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_a_1925_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1944_ = v_a_1925_;
v_isShared_1945_ = v_isSharedCheck_1968_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_proof_1940_);
lean_inc(v_e_x27_1939_);
lean_dec(v_a_1925_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1968_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; 
lean_inc_ref(v_e_x27_1939_);
v___x_1946_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1887_, v_e_x27_1918_, v_proof_1919_, v_e_x27_1939_, v_proof_1940_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1959_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1959_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1959_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
uint8_t v___y_1952_; 
if (v_contextDependent_1920_ == 0)
{
v___y_1952_ = v_contextDependent_1942_;
goto v___jp_1951_;
}
else
{
v___y_1952_ = v_contextDependent_1920_;
goto v___jp_1951_;
}
v___jp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 1, v_a_1947_);
v___x_1954_ = v___x_1944_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_e_x27_1939_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_a_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_1958_, sizeof(void*)*2, v_done_1941_);
v___x_1954_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1956_; 
lean_ctor_set_uint8(v___x_1954_, sizeof(void*)*2 + 1, v___y_1952_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1954_);
v___x_1956_ = v___x_1949_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_del_object(v___x_1944_);
lean_dec_ref(v_e_x27_1939_);
v_a_1960_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1946_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1946_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1922_);
lean_dec_ref(v_proof_1919_);
lean_dec_ref(v_e_x27_1918_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1887_);
return v___x_1924_;
}
}
}
else
{
lean_dec_ref_known(v_a_1899_, 2);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1887_);
return v___x_1898_;
}
}
}
else
{
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1887_);
return v___x_1898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__19___boxed(lean_object* v_pre_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__19(v_pre_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__20(lean_object* v___f_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_box(0);
lean_inc_ref(v___y_1985_);
v___x_1997_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_1985_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
if (lean_obj_tag(v_a_1998_) == 0)
{
uint8_t v_done_1999_; 
v_done_1999_ = lean_ctor_get_uint8(v_a_1998_, 0);
if (v_done_1999_ == 0)
{
uint8_t v_contextDependent_2000_; lean_object* v___x_2001_; 
lean_dec_ref_known(v___x_1997_, 1);
v_contextDependent_2000_ = lean_ctor_get_uint8(v_a_1998_, 1);
lean_dec_ref_known(v_a_1998_, 0);
v___x_2001_ = lean_apply_12(v___f_1984_, v___x_1996_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, lean_box(0));
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; uint8_t v___y_2004_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
if (v_contextDependent_2000_ == 0)
{
lean_dec(v_a_2002_);
return v___x_2001_;
}
else
{
if (lean_obj_tag(v_a_2002_) == 0)
{
uint8_t v_contextDependent_2014_; 
v_contextDependent_2014_ = lean_ctor_get_uint8(v_a_2002_, 1);
v___y_2004_ = v_contextDependent_2014_;
goto v___jp_2003_;
}
else
{
uint8_t v_contextDependent_2015_; 
v_contextDependent_2015_ = lean_ctor_get_uint8(v_a_2002_, sizeof(void*)*2 + 1);
v___y_2004_ = v_contextDependent_2015_;
goto v___jp_2003_;
}
}
v___jp_2003_:
{
if (v___y_2004_ == 0)
{
lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2012_; 
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v___x_2001_, 0);
lean_dec(v_unused_2013_);
v___x_2006_ = v___x_2001_;
v_isShared_2007_ = v_isSharedCheck_2012_;
goto v_resetjp_2005_;
}
else
{
lean_dec(v___x_2001_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2012_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2002_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2008_);
v___x_2010_ = v___x_2006_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
else
{
lean_dec(v_a_2002_);
return v___x_2001_;
}
}
}
else
{
return v___x_2001_;
}
}
else
{
lean_dec_ref_known(v_a_1998_, 0);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec_ref(v___f_1984_);
return v___x_1997_;
}
}
else
{
uint8_t v_done_2016_; 
v_done_2016_ = lean_ctor_get_uint8(v_a_1998_, sizeof(void*)*2);
if (v_done_2016_ == 0)
{
lean_object* v_e_x27_2017_; lean_object* v_proof_2018_; uint8_t v_contextDependent_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref_known(v___x_1997_, 1);
v_e_x27_2017_ = lean_ctor_get(v_a_1998_, 0);
v_proof_2018_ = lean_ctor_get(v_a_1998_, 1);
v_contextDependent_2019_ = lean_ctor_get_uint8(v_a_1998_, sizeof(void*)*2 + 1);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_a_1998_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2021_ = v_a_1998_;
v_isShared_2022_ = v_isSharedCheck_2069_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_proof_2018_);
lean_inc(v_e_x27_2017_);
lean_dec(v_a_1998_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2069_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; 
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1993_);
lean_inc(v___y_1992_);
lean_inc_ref(v___y_1991_);
lean_inc(v___y_1990_);
lean_inc_ref(v___y_1989_);
lean_inc_ref(v_e_x27_2017_);
v___x_2023_ = lean_apply_12(v___f_1984_, v___x_1996_, v_e_x27_2017_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, lean_box(0));
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2068_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2068_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2068_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
if (lean_obj_tag(v_a_2024_) == 0)
{
uint8_t v_done_2028_; uint8_t v_contextDependent_2029_; uint8_t v___y_2031_; 
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec_ref(v___y_1985_);
v_done_2028_ = lean_ctor_get_uint8(v_a_2024_, 0);
v_contextDependent_2029_ = lean_ctor_get_uint8(v_a_2024_, 1);
lean_dec_ref_known(v_a_2024_, 0);
if (v_contextDependent_2019_ == 0)
{
v___y_2031_ = v_contextDependent_2029_;
goto v___jp_2030_;
}
else
{
v___y_2031_ = v_contextDependent_2019_;
goto v___jp_2030_;
}
v___jp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2022_ == 0)
{
v___x_2033_ = v___x_2021_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_e_x27_2017_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_proof_2018_);
v___x_2033_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2035_; 
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2, v_done_2028_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2 + 1, v___y_2031_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2033_);
v___x_2035_ = v___x_2026_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_object* v_e_x27_2038_; lean_object* v_proof_2039_; uint8_t v_done_2040_; uint8_t v_contextDependent_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2067_; 
lean_del_object(v___x_2026_);
lean_del_object(v___x_2021_);
v_e_x27_2038_ = lean_ctor_get(v_a_2024_, 0);
v_proof_2039_ = lean_ctor_get(v_a_2024_, 1);
v_done_2040_ = lean_ctor_get_uint8(v_a_2024_, sizeof(void*)*2);
v_contextDependent_2041_ = lean_ctor_get_uint8(v_a_2024_, sizeof(void*)*2 + 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_a_2024_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2043_ = v_a_2024_;
v_isShared_2044_ = v_isSharedCheck_2067_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_proof_2039_);
lean_inc(v_e_x27_2038_);
lean_dec(v_a_2024_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2067_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; 
lean_inc_ref(v_e_x27_2038_);
v___x_2045_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1985_, v_e_x27_2017_, v_proof_2018_, v_e_x27_2038_, v_proof_2039_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2058_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2058_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2058_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
uint8_t v___y_2051_; 
if (v_contextDependent_2019_ == 0)
{
v___y_2051_ = v_contextDependent_2041_;
goto v___jp_2050_;
}
else
{
v___y_2051_ = v_contextDependent_2019_;
goto v___jp_2050_;
}
v___jp_2050_:
{
lean_object* v___x_2053_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 1, v_a_2046_);
v___x_2053_ = v___x_2043_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_e_x27_2038_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_a_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2057_, sizeof(void*)*2, v_done_2040_);
v___x_2053_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2055_; 
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*2 + 1, v___y_2051_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2053_);
v___x_2055_ = v___x_2048_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_del_object(v___x_2043_);
lean_dec_ref(v_e_x27_2038_);
v_a_2059_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2045_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2045_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2021_);
lean_dec_ref(v_proof_2018_);
lean_dec_ref(v_e_x27_2017_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec_ref(v___y_1985_);
return v___x_2023_;
}
}
}
else
{
lean_dec_ref_known(v_a_1998_, 2);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec_ref(v___f_1984_);
return v___x_1997_;
}
}
}
else
{
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec_ref(v___f_1984_);
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__20___boxed(lean_object* v___f_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__20(v___f_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__21(lean_object* v___f_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___y_2096_; lean_object* v___y_2097_; uint8_t v___y_2098_; lean_object* v___y_2102_; uint8_t v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; lean_object* v___y_2109_; lean_object* v___y_2110_; uint8_t v___y_2111_; uint8_t v___y_2112_; lean_object* v___y_2116_; lean_object* v_e_x27_2117_; lean_object* v_proof_2118_; uint8_t v_done_2119_; uint8_t v_contextDependent_2120_; lean_object* v___y_2142_; lean_object* v_a_2143_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_box(0);
lean_inc_ref(v___y_2084_);
v___x_2155_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_2084_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
if (lean_obj_tag(v_a_2156_) == 0)
{
uint8_t v_done_2157_; 
v_done_2157_ = lean_ctor_get_uint8(v_a_2156_, 0);
if (v_done_2157_ == 0)
{
uint8_t v_contextDependent_2158_; lean_object* v___x_2159_; 
lean_dec_ref_known(v___x_2155_, 1);
v_contextDependent_2158_ = lean_ctor_get_uint8(v_a_2156_, 1);
lean_dec_ref_known(v_a_2156_, 0);
lean_inc(v___y_2093_);
lean_inc_ref(v___y_2092_);
lean_inc(v___y_2091_);
lean_inc_ref(v___y_2090_);
lean_inc(v___y_2089_);
lean_inc_ref(v___y_2088_);
lean_inc_ref(v___y_2084_);
v___x_2159_ = lean_apply_12(v___f_2083_, v___x_2154_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, lean_box(0));
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; uint8_t v___y_2162_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
if (v_contextDependent_2158_ == 0)
{
v___y_2142_ = v___x_2159_;
v_a_2143_ = v_a_2160_;
goto v___jp_2141_;
}
else
{
if (lean_obj_tag(v_a_2160_) == 0)
{
uint8_t v_contextDependent_2172_; 
v_contextDependent_2172_ = lean_ctor_get_uint8(v_a_2160_, 1);
v___y_2162_ = v_contextDependent_2172_;
goto v___jp_2161_;
}
else
{
uint8_t v_contextDependent_2173_; 
v_contextDependent_2173_ = lean_ctor_get_uint8(v_a_2160_, sizeof(void*)*2 + 1);
v___y_2162_ = v_contextDependent_2173_;
goto v___jp_2161_;
}
}
v___jp_2161_:
{
if (v___y_2162_ == 0)
{
lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2170_; 
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v___x_2159_, 0);
lean_dec(v_unused_2171_);
v___x_2164_ = v___x_2159_;
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
else
{
lean_dec(v___x_2159_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2160_);
lean_inc_ref(v___x_2166_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2166_);
v___x_2168_ = v___x_2164_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
v___y_2142_ = v___x_2168_;
v_a_2143_ = v___x_2166_;
goto v___jp_2141_;
}
}
}
else
{
v___y_2142_ = v___x_2159_;
v_a_2143_ = v_a_2160_;
goto v___jp_2141_;
}
}
}
else
{
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v___y_2084_);
return v___x_2159_;
}
}
else
{
lean_dec_ref_known(v_a_2156_, 0);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec_ref(v___f_2083_);
return v___x_2155_;
}
}
else
{
uint8_t v_done_2174_; 
v_done_2174_ = lean_ctor_get_uint8(v_a_2156_, sizeof(void*)*2);
if (v_done_2174_ == 0)
{
lean_object* v_e_x27_2175_; lean_object* v_proof_2176_; uint8_t v_contextDependent_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2227_; 
lean_dec_ref_known(v___x_2155_, 1);
v_e_x27_2175_ = lean_ctor_get(v_a_2156_, 0);
v_proof_2176_ = lean_ctor_get(v_a_2156_, 1);
v_contextDependent_2177_ = lean_ctor_get_uint8(v_a_2156_, sizeof(void*)*2 + 1);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_a_2156_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2179_ = v_a_2156_;
v_isShared_2180_ = v_isSharedCheck_2227_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_proof_2176_);
lean_inc(v_e_x27_2175_);
lean_dec(v_a_2156_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2227_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; 
lean_inc(v___y_2093_);
lean_inc_ref(v___y_2092_);
lean_inc(v___y_2091_);
lean_inc_ref(v___y_2090_);
lean_inc(v___y_2089_);
lean_inc_ref(v___y_2088_);
lean_inc_ref(v_e_x27_2175_);
v___x_2181_ = lean_apply_12(v___f_2083_, v___x_2154_, v_e_x27_2175_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, lean_box(0));
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2226_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2226_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2226_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
if (lean_obj_tag(v_a_2182_) == 0)
{
uint8_t v_done_2186_; uint8_t v_contextDependent_2187_; uint8_t v___y_2189_; 
v_done_2186_ = lean_ctor_get_uint8(v_a_2182_, 0);
v_contextDependent_2187_ = lean_ctor_get_uint8(v_a_2182_, 1);
lean_dec_ref_known(v_a_2182_, 0);
if (v_contextDependent_2177_ == 0)
{
v___y_2189_ = v_contextDependent_2187_;
goto v___jp_2188_;
}
else
{
v___y_2189_ = v_contextDependent_2177_;
goto v___jp_2188_;
}
v___jp_2188_:
{
lean_object* v___x_2191_; 
lean_inc_ref(v_proof_2176_);
lean_inc_ref(v_e_x27_2175_);
if (v_isShared_2180_ == 0)
{
v___x_2191_ = v___x_2179_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_e_x27_2175_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_proof_2176_);
v___x_2191_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2193_; 
lean_ctor_set_uint8(v___x_2191_, sizeof(void*)*2, v_done_2186_);
lean_ctor_set_uint8(v___x_2191_, sizeof(void*)*2 + 1, v___y_2189_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2191_);
v___x_2193_ = v___x_2184_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
v___y_2116_ = v___x_2193_;
v_e_x27_2117_ = v_e_x27_2175_;
v_proof_2118_ = v_proof_2176_;
v_done_2119_ = v_done_2186_;
v_contextDependent_2120_ = v___y_2189_;
goto v___jp_2115_;
}
}
}
}
else
{
lean_object* v_e_x27_2196_; lean_object* v_proof_2197_; uint8_t v_done_2198_; uint8_t v_contextDependent_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2225_; 
lean_del_object(v___x_2184_);
lean_del_object(v___x_2179_);
v_e_x27_2196_ = lean_ctor_get(v_a_2182_, 0);
v_proof_2197_ = lean_ctor_get(v_a_2182_, 1);
v_done_2198_ = lean_ctor_get_uint8(v_a_2182_, sizeof(void*)*2);
v_contextDependent_2199_ = lean_ctor_get_uint8(v_a_2182_, sizeof(void*)*2 + 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_a_2182_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2201_ = v_a_2182_;
v_isShared_2202_ = v_isSharedCheck_2225_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_proof_2197_);
lean_inc(v_e_x27_2196_);
lean_dec(v_a_2182_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2225_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; 
lean_inc_ref(v_e_x27_2196_);
lean_inc_ref(v___y_2084_);
v___x_2203_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2084_, v_e_x27_2175_, v_proof_2176_, v_e_x27_2196_, v_proof_2197_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2216_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2216_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2216_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
uint8_t v___y_2209_; 
if (v_contextDependent_2177_ == 0)
{
v___y_2209_ = v_contextDependent_2199_;
goto v___jp_2208_;
}
else
{
v___y_2209_ = v_contextDependent_2177_;
goto v___jp_2208_;
}
v___jp_2208_:
{
lean_object* v___x_2211_; 
lean_inc(v_a_2204_);
lean_inc_ref(v_e_x27_2196_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 1, v_a_2204_);
v___x_2211_ = v___x_2201_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_e_x27_2196_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_a_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2215_, sizeof(void*)*2, v_done_2198_);
v___x_2211_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2213_; 
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*2 + 1, v___y_2209_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2211_);
v___x_2213_ = v___x_2206_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
v___y_2116_ = v___x_2213_;
v_e_x27_2117_ = v_e_x27_2196_;
v_proof_2118_ = v_a_2204_;
v_done_2119_ = v_done_2198_;
v_contextDependent_2120_ = v___y_2209_;
goto v___jp_2115_;
}
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_del_object(v___x_2201_);
lean_dec_ref(v_e_x27_2196_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v___y_2084_);
v_a_2217_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2203_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2203_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2179_);
lean_dec_ref(v_proof_2176_);
lean_dec_ref(v_e_x27_2175_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v___y_2084_);
return v___x_2181_;
}
}
}
else
{
lean_dec_ref_known(v_a_2156_, 2);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec_ref(v___f_2083_);
return v___x_2155_;
}
}
}
else
{
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec_ref(v___f_2083_);
return v___x_2155_;
}
v___jp_2095_:
{
if (v___y_2098_ == 0)
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec_ref(v___y_2097_);
v___x_2099_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_2096_);
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
else
{
lean_dec_ref(v___y_2096_);
return v___y_2097_;
}
}
v___jp_2101_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2106_, 0, v___y_2104_);
lean_ctor_set(v___x_2106_, 1, v___y_2102_);
lean_ctor_set_uint8(v___x_2106_, sizeof(void*)*2, v___y_2103_);
lean_ctor_set_uint8(v___x_2106_, sizeof(void*)*2 + 1, v___y_2105_);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
return v___x_2107_;
}
v___jp_2108_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2113_, 0, v___y_2110_);
lean_ctor_set(v___x_2113_, 1, v___y_2109_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*2, v___y_2111_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*2 + 1, v___y_2112_);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
v___jp_2115_:
{
if (v_done_2119_ == 0)
{
lean_object* v___x_2121_; 
lean_dec_ref(v___y_2116_);
lean_inc_ref(v_e_x27_2117_);
v___x_2121_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v_e_x27_2117_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
if (lean_obj_tag(v_a_2122_) == 0)
{
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v___y_2084_);
if (v_contextDependent_2120_ == 0)
{
uint8_t v_done_2123_; uint8_t v_contextDependent_2124_; 
v_done_2123_ = lean_ctor_get_uint8(v_a_2122_, 0);
v_contextDependent_2124_ = lean_ctor_get_uint8(v_a_2122_, 1);
lean_dec_ref_known(v_a_2122_, 0);
v___y_2109_ = v_proof_2118_;
v___y_2110_ = v_e_x27_2117_;
v___y_2111_ = v_done_2123_;
v___y_2112_ = v_contextDependent_2124_;
goto v___jp_2108_;
}
else
{
uint8_t v_done_2125_; 
v_done_2125_ = lean_ctor_get_uint8(v_a_2122_, 0);
lean_dec_ref_known(v_a_2122_, 0);
v___y_2109_ = v_proof_2118_;
v___y_2110_ = v_e_x27_2117_;
v___y_2111_ = v_done_2125_;
v___y_2112_ = v_contextDependent_2120_;
goto v___jp_2108_;
}
}
else
{
lean_object* v_e_x27_2126_; lean_object* v_proof_2127_; uint8_t v_done_2128_; uint8_t v_contextDependent_2129_; lean_object* v___x_2130_; 
v_e_x27_2126_ = lean_ctor_get(v_a_2122_, 0);
lean_inc_ref_n(v_e_x27_2126_, 2);
v_proof_2127_ = lean_ctor_get(v_a_2122_, 1);
lean_inc_ref(v_proof_2127_);
v_done_2128_ = lean_ctor_get_uint8(v_a_2122_, sizeof(void*)*2);
v_contextDependent_2129_ = lean_ctor_get_uint8(v_a_2122_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2122_, 2);
v___x_2130_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2084_, v_e_x27_2117_, v_proof_2118_, v_e_x27_2126_, v_proof_2127_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
if (lean_obj_tag(v___x_2130_) == 0)
{
if (v_contextDependent_2120_ == 0)
{
lean_object* v_a_2131_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___y_2102_ = v_a_2131_;
v___y_2103_ = v_done_2128_;
v___y_2104_ = v_e_x27_2126_;
v___y_2105_ = v_contextDependent_2129_;
goto v___jp_2101_;
}
else
{
lean_object* v_a_2132_; 
v_a_2132_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2130_, 1);
v___y_2102_ = v_a_2132_;
v___y_2103_ = v_done_2128_;
v___y_2104_ = v_e_x27_2126_;
v___y_2105_ = v_contextDependent_2120_;
goto v___jp_2101_;
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_e_x27_2126_);
v_a_2133_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2130_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2130_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_2118_);
lean_dec_ref(v_e_x27_2117_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v___y_2084_);
return v___x_2121_;
}
}
else
{
lean_dec_ref(v_proof_2118_);
lean_dec_ref(v_e_x27_2117_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v___y_2084_);
return v___y_2116_;
}
}
v___jp_2141_:
{
if (lean_obj_tag(v_a_2143_) == 0)
{
uint8_t v_done_2144_; 
v_done_2144_ = lean_ctor_get_uint8(v_a_2143_, 0);
if (v_done_2144_ == 0)
{
uint8_t v_contextDependent_2145_; lean_object* v___x_2146_; 
lean_dec_ref(v___y_2142_);
v_contextDependent_2145_ = lean_ctor_get_uint8(v_a_2143_, 1);
lean_dec_ref_known(v_a_2143_, 0);
v___x_2146_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v___y_2084_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
if (lean_obj_tag(v___x_2146_) == 0)
{
if (v_contextDependent_2145_ == 0)
{
return v___x_2146_;
}
else
{
lean_object* v_a_2147_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
if (lean_obj_tag(v_a_2147_) == 0)
{
uint8_t v_contextDependent_2148_; 
v_contextDependent_2148_ = lean_ctor_get_uint8(v_a_2147_, 1);
v___y_2096_ = v_a_2147_;
v___y_2097_ = v___x_2146_;
v___y_2098_ = v_contextDependent_2148_;
goto v___jp_2095_;
}
else
{
uint8_t v_contextDependent_2149_; 
v_contextDependent_2149_ = lean_ctor_get_uint8(v_a_2147_, sizeof(void*)*2 + 1);
v___y_2096_ = v_a_2147_;
v___y_2097_ = v___x_2146_;
v___y_2098_ = v_contextDependent_2149_;
goto v___jp_2095_;
}
}
}
else
{
return v___x_2146_;
}
}
else
{
lean_dec_ref_known(v_a_2143_, 0);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v___y_2084_);
return v___y_2142_;
}
}
else
{
lean_object* v_e_x27_2150_; lean_object* v_proof_2151_; uint8_t v_done_2152_; uint8_t v_contextDependent_2153_; 
v_e_x27_2150_ = lean_ctor_get(v_a_2143_, 0);
lean_inc_ref(v_e_x27_2150_);
v_proof_2151_ = lean_ctor_get(v_a_2143_, 1);
lean_inc_ref(v_proof_2151_);
v_done_2152_ = lean_ctor_get_uint8(v_a_2143_, sizeof(void*)*2);
v_contextDependent_2153_ = lean_ctor_get_uint8(v_a_2143_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2143_, 2);
v___y_2116_ = v___y_2142_;
v_e_x27_2117_ = v_e_x27_2150_;
v_proof_2118_ = v_proof_2151_;
v_done_2119_ = v_done_2152_;
v_contextDependent_2120_ = v_contextDependent_2153_;
goto v___jp_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___lam__21___boxed(lean_object* v___f_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_Meta_Grind_mkNormSymMethods___lam__21(v___f_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object* v_config_2266_, lean_object* v_thms_2267_){
_start:
{
uint8_t v_zetaDelta_2268_; uint8_t v_zeta_2269_; uint8_t v_distrib_2270_; lean_object* v_maxChar_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; lean_object* v___f_2274_; lean_object* v___f_2275_; lean_object* v___f_2276_; lean_object* v_d_2277_; lean_object* v___f_2278_; lean_object* v___x_2279_; lean_object* v___f_2280_; lean_object* v___f_2281_; lean_object* v_pre_2283_; lean_object* v_pre_2289_; 
v_zetaDelta_2268_ = lean_ctor_get_uint8(v_config_2266_, sizeof(void*)*18 + 19);
v_zeta_2269_ = lean_ctor_get_uint8(v_config_2266_, sizeof(void*)*18 + 20);
v_distrib_2270_ = lean_ctor_get_uint8(v_config_2266_, sizeof(void*)*18 + 21);
v_maxChar_2271_ = lean_ctor_get(v_config_2266_, 7);
lean_inc(v_maxChar_2271_);
lean_dec_ref(v_config_2266_);
v___f_2272_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__10));
v___x_2273_ = lean_box(v_distrib_2270_);
v___f_2274_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__11___boxed), 14, 2);
lean_closure_set(v___f_2274_, 0, v___x_2273_);
lean_closure_set(v___f_2274_, 1, v___f_2272_);
v___f_2275_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__12___boxed), 13, 1);
lean_closure_set(v___f_2275_, 0, v___f_2274_);
v___f_2276_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__13___boxed), 13, 1);
lean_closure_set(v___f_2276_, 0, v___f_2275_);
v_d_2277_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__11));
lean_inc_ref(v_thms_2267_);
v___f_2278_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__14___boxed), 14, 2);
lean_closure_set(v___f_2278_, 0, v_thms_2267_);
lean_closure_set(v___f_2278_, 1, v_d_2277_);
v___x_2279_ = lean_box(v_distrib_2270_);
v___f_2280_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__15___boxed), 16, 4);
lean_closure_set(v___f_2280_, 0, v_maxChar_2271_);
lean_closure_set(v___f_2280_, 1, v_d_2277_);
lean_closure_set(v___f_2280_, 2, v___x_2279_);
lean_closure_set(v___f_2280_, 3, v___f_2278_);
v___f_2281_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__16___boxed), 13, 1);
lean_closure_set(v___f_2281_, 0, v___f_2280_);
if (v_zeta_2269_ == 0)
{
lean_object* v_pre_2291_; 
v_pre_2291_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__12));
v_pre_2289_ = v_pre_2291_;
goto v___jp_2288_;
}
else
{
lean_object* v_pre_2292_; 
v_pre_2292_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___closed__13));
v_pre_2289_ = v_pre_2292_;
goto v___jp_2288_;
}
v___jp_2282_:
{
lean_object* v_post_2284_; lean_object* v_pre_2285_; lean_object* v_post_2286_; lean_object* v___x_2287_; 
v_post_2284_ = lean_ctor_get(v_thms_2267_, 1);
lean_inc_ref(v_post_2284_);
lean_dec_ref(v_thms_2267_);
v_pre_2285_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__17___boxed), 13, 2);
lean_closure_set(v_pre_2285_, 0, v_pre_2283_);
lean_closure_set(v_pre_2285_, 1, v___f_2281_);
v_post_2286_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__18___boxed), 14, 3);
lean_closure_set(v_post_2286_, 0, v_post_2284_);
lean_closure_set(v_post_2286_, 1, v_d_2277_);
lean_closure_set(v_post_2286_, 2, v___f_2276_);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_pre_2285_);
lean_ctor_set(v___x_2287_, 1, v_post_2286_);
return v___x_2287_;
}
v___jp_2288_:
{
if (v_zetaDelta_2268_ == 0)
{
lean_inc_ref(v_pre_2289_);
v_pre_2283_ = v_pre_2289_;
goto v___jp_2282_;
}
else
{
lean_object* v_pre_2290_; 
lean_inc_ref(v_pre_2289_);
v_pre_2290_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___lam__19___boxed), 12, 1);
lean_closure_set(v_pre_2290_, 0, v_pre_2289_);
v_pre_2283_ = v_pre_2290_;
goto v___jp_2282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(lean_object* v_x_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; 
lean_inc_ref(v___y_2294_);
v___x_2305_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v___y_2294_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
if (lean_obj_tag(v_a_2306_) == 0)
{
uint8_t v_done_2307_; 
v_done_2307_ = lean_ctor_get_uint8(v_a_2306_, 0);
lean_dec_ref_known(v_a_2306_, 0);
if (v_done_2307_ == 0)
{
lean_object* v___x_2308_; 
lean_dec_ref_known(v___x_2305_, 1);
v___x_2308_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_2294_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec_ref(v___y_2294_);
return v___x_2308_;
}
else
{
lean_dec_ref(v___y_2294_);
return v___x_2305_;
}
}
else
{
uint8_t v_done_2309_; 
lean_dec_ref(v___y_2294_);
v_done_2309_ = lean_ctor_get_uint8(v_a_2306_, sizeof(void*)*1);
if (v_done_2309_ == 0)
{
lean_object* v_e_x27_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref_known(v___x_2305_, 1);
v_e_x27_2310_ = lean_ctor_get(v_a_2306_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_a_2306_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2312_ = v_a_2306_;
v_isShared_2313_ = v_isSharedCheck_2328_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_e_x27_2310_);
lean_dec(v_a_2306_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2328_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_x27_2310_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
if (lean_obj_tag(v_a_2315_) == 0)
{
lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2326_; 
lean_inc_ref(v_a_2315_);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; 
v_unused_2327_ = lean_ctor_get(v___x_2314_, 0);
lean_dec(v_unused_2327_);
v___x_2317_ = v___x_2314_;
v_isShared_2318_ = v_isSharedCheck_2326_;
goto v_resetjp_2316_;
}
else
{
lean_dec(v___x_2314_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2326_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
uint8_t v_done_2319_; lean_object* v___x_2321_; 
v_done_2319_ = lean_ctor_get_uint8(v_a_2315_, 0);
lean_dec_ref_known(v_a_2315_, 0);
if (v_isShared_2313_ == 0)
{
v___x_2321_ = v___x_2312_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_e_x27_2310_);
v___x_2321_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2323_; 
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*1, v_done_2319_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___x_2321_);
v___x_2323_ = v___x_2317_;
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
lean_del_object(v___x_2312_);
lean_dec_ref(v_e_x27_2310_);
return v___x_2314_;
}
}
else
{
lean_del_object(v___x_2312_);
lean_dec_ref(v_e_x27_2310_);
return v___x_2314_;
}
}
}
else
{
lean_dec_ref_known(v_a_2306_, 1);
return v___x_2305_;
}
}
}
else
{
lean_dec_ref(v___y_2294_);
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0___boxed(lean_object* v_x_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(v_x_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(lean_object* v_x_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___closed__0));
v___x_2358_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_2357_, v___y_2346_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___boxed(lean_object* v_x_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(v_x_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(lean_object* v_dsimp_2372_, lean_object* v___f_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_box(0);
lean_inc_ref(v___y_2374_);
v___x_2386_ = l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(v_dsimp_2372_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
if (lean_obj_tag(v_a_2387_) == 0)
{
uint8_t v_done_2388_; 
v_done_2388_ = lean_ctor_get_uint8(v_a_2387_, 0);
lean_dec_ref_known(v_a_2387_, 0);
if (v_done_2388_ == 0)
{
lean_object* v___x_2389_; 
lean_dec_ref_known(v___x_2386_, 1);
v___x_2389_ = lean_apply_12(v___f_2373_, v___x_2385_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, lean_box(0));
return v___x_2389_;
}
else
{
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec_ref(v___f_2373_);
return v___x_2386_;
}
}
else
{
uint8_t v_done_2390_; 
lean_dec_ref(v___y_2374_);
v_done_2390_ = lean_ctor_get_uint8(v_a_2387_, sizeof(void*)*1);
if (v_done_2390_ == 0)
{
lean_object* v_e_x27_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref_known(v___x_2386_, 1);
v_e_x27_2391_ = lean_ctor_get(v_a_2387_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_a_2387_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2393_ = v_a_2387_;
v_isShared_2394_ = v_isSharedCheck_2409_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_e_x27_2391_);
lean_dec(v_a_2387_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2409_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; 
lean_inc_ref(v_e_x27_2391_);
v___x_2395_ = lean_apply_12(v___f_2373_, v___x_2385_, v_e_x27_2391_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, lean_box(0));
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
if (lean_obj_tag(v_a_2396_) == 0)
{
lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2407_; 
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2407_ == 0)
{
lean_object* v_unused_2408_; 
v_unused_2408_ = lean_ctor_get(v___x_2395_, 0);
lean_dec(v_unused_2408_);
v___x_2398_ = v___x_2395_;
v_isShared_2399_ = v_isSharedCheck_2407_;
goto v_resetjp_2397_;
}
else
{
lean_dec(v___x_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2407_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
uint8_t v_done_2400_; lean_object* v___x_2402_; 
v_done_2400_ = lean_ctor_get_uint8(v_a_2396_, 0);
lean_dec_ref_known(v_a_2396_, 0);
if (v_isShared_2394_ == 0)
{
v___x_2402_ = v___x_2393_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_e_x27_2391_);
v___x_2402_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
lean_object* v___x_2404_; 
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*1, v_done_2400_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2402_);
v___x_2404_ = v___x_2398_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2396_, 1);
lean_del_object(v___x_2393_);
lean_dec_ref(v_e_x27_2391_);
return v___x_2395_;
}
}
else
{
lean_del_object(v___x_2393_);
lean_dec_ref(v_e_x27_2391_);
return v___x_2395_;
}
}
}
else
{
lean_dec_ref_known(v_a_2387_, 1);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___f_2373_);
return v___x_2386_;
}
}
}
else
{
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec_ref(v___f_2373_);
return v___x_2386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed(lean_object* v_dsimp_2410_, lean_object* v___f_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(v_dsimp_2410_, v___f_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec_ref(v_dsimp_2410_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(lean_object* v_pre_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v___x_2436_; 
lean_inc(v___y_2434_);
lean_inc_ref(v___y_2433_);
lean_inc(v___y_2432_);
lean_inc_ref(v___y_2431_);
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2429_);
lean_inc_ref(v___y_2425_);
v___x_2436_ = lean_apply_11(v_pre_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, lean_box(0));
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
if (lean_obj_tag(v_a_2437_) == 0)
{
uint8_t v_done_2438_; 
v_done_2438_ = lean_ctor_get_uint8(v_a_2437_, 0);
lean_dec_ref_known(v_a_2437_, 0);
if (v_done_2438_ == 0)
{
lean_object* v___x_2439_; 
lean_dec_ref_known(v___x_2436_, 1);
v___x_2439_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_2425_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
return v___x_2439_;
}
else
{
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec_ref(v___y_2425_);
return v___x_2436_;
}
}
else
{
uint8_t v_done_2440_; 
lean_dec_ref(v___y_2425_);
v_done_2440_ = lean_ctor_get_uint8(v_a_2437_, sizeof(void*)*1);
if (v_done_2440_ == 0)
{
lean_object* v_e_x27_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2459_; 
lean_dec_ref_known(v___x_2436_, 1);
v_e_x27_2441_ = lean_ctor_get(v_a_2437_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v_a_2437_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2443_ = v_a_2437_;
v_isShared_2444_ = v_isSharedCheck_2459_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_e_x27_2441_);
lean_dec(v_a_2437_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2459_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; 
lean_inc_ref(v_e_x27_2441_);
v___x_2445_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_x27_2441_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
if (lean_obj_tag(v_a_2446_) == 0)
{
lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2457_; 
lean_inc_ref(v_a_2446_);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2457_ == 0)
{
lean_object* v_unused_2458_; 
v_unused_2458_ = lean_ctor_get(v___x_2445_, 0);
lean_dec(v_unused_2458_);
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2457_;
goto v_resetjp_2447_;
}
else
{
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2457_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
uint8_t v_done_2450_; lean_object* v___x_2452_; 
v_done_2450_ = lean_ctor_get_uint8(v_a_2446_, 0);
lean_dec_ref_known(v_a_2446_, 0);
if (v_isShared_2444_ == 0)
{
v___x_2452_ = v___x_2443_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_e_x27_2441_);
v___x_2452_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2454_; 
lean_ctor_set_uint8(v___x_2452_, sizeof(void*)*1, v_done_2450_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2452_);
v___x_2454_ = v___x_2448_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_del_object(v___x_2443_);
lean_dec_ref(v_e_x27_2441_);
return v___x_2445_;
}
}
else
{
lean_del_object(v___x_2443_);
lean_dec_ref(v_e_x27_2441_);
return v___x_2445_;
}
}
}
else
{
lean_dec_ref_known(v_a_2437_, 1);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
return v___x_2436_;
}
}
}
else
{
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec_ref(v___y_2425_);
return v___x_2436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed(lean_object* v_pre_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(v_pre_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(lean_object* v___f_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_box(0);
lean_inc_ref(v___y_2474_);
v___x_2486_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_2474_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
if (lean_obj_tag(v_a_2487_) == 0)
{
uint8_t v_done_2488_; 
v_done_2488_ = lean_ctor_get_uint8(v_a_2487_, 0);
lean_dec_ref_known(v_a_2487_, 0);
if (v_done_2488_ == 0)
{
lean_object* v___x_2489_; 
lean_dec_ref_known(v___x_2486_, 1);
v___x_2489_ = lean_apply_12(v___f_2473_, v___x_2485_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, lean_box(0));
return v___x_2489_;
}
else
{
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v___f_2473_);
return v___x_2486_;
}
}
else
{
uint8_t v_done_2490_; 
lean_dec_ref(v___y_2474_);
v_done_2490_ = lean_ctor_get_uint8(v_a_2487_, sizeof(void*)*1);
if (v_done_2490_ == 0)
{
lean_object* v_e_x27_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2509_; 
lean_dec_ref_known(v___x_2486_, 1);
v_e_x27_2491_ = lean_ctor_get(v_a_2487_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_a_2487_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2493_ = v_a_2487_;
v_isShared_2494_ = v_isSharedCheck_2509_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_e_x27_2491_);
lean_dec(v_a_2487_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2509_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2495_; 
lean_inc_ref(v_e_x27_2491_);
v___x_2495_ = lean_apply_12(v___f_2473_, v___x_2485_, v_e_x27_2491_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, lean_box(0));
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
if (lean_obj_tag(v_a_2496_) == 0)
{
lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2507_; 
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v___x_2495_, 0);
lean_dec(v_unused_2508_);
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2507_;
goto v_resetjp_2497_;
}
else
{
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2507_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
uint8_t v_done_2500_; lean_object* v___x_2502_; 
v_done_2500_ = lean_ctor_get_uint8(v_a_2496_, 0);
lean_dec_ref_known(v_a_2496_, 0);
if (v_isShared_2494_ == 0)
{
v___x_2502_ = v___x_2493_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_e_x27_2491_);
v___x_2502_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2504_; 
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*1, v_done_2500_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2502_);
v___x_2504_ = v___x_2498_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2496_, 1);
lean_del_object(v___x_2493_);
lean_dec_ref(v_e_x27_2491_);
return v___x_2495_;
}
}
else
{
lean_del_object(v___x_2493_);
lean_dec_ref(v_e_x27_2491_);
return v___x_2495_;
}
}
}
else
{
lean_dec_ref_known(v_a_2487_, 1);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___f_2473_);
return v___x_2486_;
}
}
}
else
{
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v___f_2473_);
return v___x_2486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4___boxed(lean_object* v___f_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(v___f_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(lean_object* v___f_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___y_2536_; lean_object* v_e_x27_2537_; uint8_t v_done_2538_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_box(0);
lean_inc_ref(v___y_2524_);
v___x_2552_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_2524_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
if (lean_obj_tag(v_a_2553_) == 0)
{
uint8_t v_done_2554_; 
v_done_2554_ = lean_ctor_get_uint8(v_a_2553_, 0);
lean_dec_ref_known(v_a_2553_, 0);
if (v_done_2554_ == 0)
{
lean_object* v___x_2555_; 
lean_dec_ref_known(v___x_2552_, 1);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc_ref(v___y_2524_);
v___x_2555_ = lean_apply_12(v___f_2523_, v___x_2551_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, lean_box(0));
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
if (lean_obj_tag(v_a_2556_) == 0)
{
uint8_t v_done_2557_; 
v_done_2557_ = lean_ctor_get_uint8(v_a_2556_, 0);
lean_dec_ref_known(v_a_2556_, 0);
if (v_done_2557_ == 0)
{
lean_object* v___x_2558_; 
lean_dec_ref_known(v___x_2555_, 1);
v___x_2558_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_2524_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
return v___x_2558_;
}
else
{
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec_ref(v___y_2524_);
return v___x_2555_;
}
}
else
{
lean_object* v_e_x27_2559_; uint8_t v_done_2560_; 
lean_dec_ref(v___y_2524_);
v_e_x27_2559_ = lean_ctor_get(v_a_2556_, 0);
lean_inc_ref(v_e_x27_2559_);
v_done_2560_ = lean_ctor_get_uint8(v_a_2556_, sizeof(void*)*1);
lean_dec_ref_known(v_a_2556_, 1);
v___y_2536_ = v___x_2555_;
v_e_x27_2537_ = v_e_x27_2559_;
v_done_2538_ = v_done_2560_;
goto v___jp_2535_;
}
}
else
{
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec_ref(v___y_2524_);
return v___x_2555_;
}
}
else
{
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___f_2523_);
return v___x_2552_;
}
}
else
{
uint8_t v_done_2561_; 
lean_dec_ref(v___y_2524_);
v_done_2561_ = lean_ctor_get_uint8(v_a_2553_, sizeof(void*)*1);
if (v_done_2561_ == 0)
{
lean_object* v_e_x27_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2582_; 
lean_dec_ref_known(v___x_2552_, 1);
v_e_x27_2562_ = lean_ctor_get(v_a_2553_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_a_2553_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2564_ = v_a_2553_;
v_isShared_2565_ = v_isSharedCheck_2582_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_e_x27_2562_);
lean_dec(v_a_2553_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2582_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2566_; 
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc_ref(v_e_x27_2562_);
v___x_2566_ = lean_apply_12(v___f_2523_, v___x_2551_, v_e_x27_2562_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, lean_box(0));
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
if (lean_obj_tag(v_a_2567_) == 0)
{
lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2578_; 
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2578_ == 0)
{
lean_object* v_unused_2579_; 
v_unused_2579_ = lean_ctor_get(v___x_2566_, 0);
lean_dec(v_unused_2579_);
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2578_;
goto v_resetjp_2568_;
}
else
{
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2578_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
uint8_t v_done_2571_; lean_object* v___x_2573_; 
v_done_2571_ = lean_ctor_get_uint8(v_a_2567_, 0);
lean_dec_ref_known(v_a_2567_, 0);
lean_inc_ref(v_e_x27_2562_);
if (v_isShared_2565_ == 0)
{
v___x_2573_ = v___x_2564_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_e_x27_2562_);
v___x_2573_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2575_; 
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*1, v_done_2571_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2573_);
v___x_2575_ = v___x_2569_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
v___y_2536_ = v___x_2575_;
v_e_x27_2537_ = v_e_x27_2562_;
v_done_2538_ = v_done_2571_;
goto v___jp_2535_;
}
}
}
}
else
{
lean_object* v_e_x27_2580_; uint8_t v_done_2581_; 
lean_del_object(v___x_2564_);
lean_dec_ref(v_e_x27_2562_);
v_e_x27_2580_ = lean_ctor_get(v_a_2567_, 0);
lean_inc_ref(v_e_x27_2580_);
v_done_2581_ = lean_ctor_get_uint8(v_a_2567_, sizeof(void*)*1);
lean_dec_ref_known(v_a_2567_, 1);
v___y_2536_ = v___x_2566_;
v_e_x27_2537_ = v_e_x27_2580_;
v_done_2538_ = v_done_2581_;
goto v___jp_2535_;
}
}
else
{
lean_del_object(v___x_2564_);
lean_dec_ref(v_e_x27_2562_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
return v___x_2566_;
}
}
}
else
{
lean_dec_ref_known(v_a_2553_, 1);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___f_2523_);
return v___x_2552_;
}
}
}
else
{
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___f_2523_);
return v___x_2552_;
}
v___jp_2535_:
{
if (v_done_2538_ == 0)
{
lean_object* v___x_2539_; 
lean_dec_ref(v___y_2536_);
lean_inc_ref(v_e_x27_2537_);
v___x_2539_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_x27_2537_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
if (lean_obj_tag(v_a_2540_) == 0)
{
lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2549_; 
lean_inc_ref(v_a_2540_);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; 
v_unused_2550_ = lean_ctor_get(v___x_2539_, 0);
lean_dec(v_unused_2550_);
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2549_;
goto v_resetjp_2541_;
}
else
{
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2549_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
uint8_t v_done_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
v_done_2544_ = lean_ctor_get_uint8(v_a_2540_, 0);
lean_dec_ref_known(v_a_2540_, 0);
v___x_2545_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2545_, 0, v_e_x27_2537_);
lean_ctor_set_uint8(v___x_2545_, sizeof(void*)*1, v_done_2544_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v___x_2545_);
v___x_2547_ = v___x_2542_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
else
{
lean_dec_ref(v_e_x27_2537_);
return v___x_2539_;
}
}
else
{
lean_dec_ref(v_e_x27_2537_);
return v___x_2539_;
}
}
else
{
lean_dec_ref(v_e_x27_2537_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
return v___y_2536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5___boxed(lean_object* v___f_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(v___f_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods(lean_object* v_config_2602_, lean_object* v_thms_2603_){
_start:
{
uint8_t v_zetaDelta_2604_; uint8_t v_zeta_2605_; lean_object* v___f_2606_; lean_object* v_pre_2608_; lean_object* v_pre_2613_; 
v_zetaDelta_2604_ = lean_ctor_get_uint8(v_config_2602_, sizeof(void*)*18 + 19);
v_zeta_2605_ = lean_ctor_get_uint8(v_config_2602_, sizeof(void*)*18 + 20);
v___f_2606_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__1));
if (v_zeta_2605_ == 0)
{
lean_object* v_pre_2615_; 
v_pre_2615_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__2));
v_pre_2613_ = v_pre_2615_;
goto v___jp_2612_;
}
else
{
lean_object* v_pre_2616_; 
v_pre_2616_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__3));
v_pre_2613_ = v_pre_2616_;
goto v___jp_2612_;
}
v___jp_2607_:
{
lean_object* v_dsimp_2609_; lean_object* v_post_2610_; lean_object* v___x_2611_; 
v_dsimp_2609_ = lean_ctor_get(v_thms_2603_, 2);
lean_inc_ref(v_dsimp_2609_);
lean_dec_ref(v_thms_2603_);
v_post_2610_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed), 13, 2);
lean_closure_set(v_post_2610_, 0, v_dsimp_2609_);
lean_closure_set(v_post_2610_, 1, v___f_2606_);
v___x_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2611_, 0, v_pre_2608_);
lean_ctor_set(v___x_2611_, 1, v_post_2610_);
return v___x_2611_;
}
v___jp_2612_:
{
if (v_zetaDelta_2604_ == 0)
{
lean_inc_ref(v_pre_2613_);
v_pre_2608_ = v_pre_2613_;
goto v___jp_2607_;
}
else
{
lean_object* v_pre_2614_; 
lean_inc_ref(v_pre_2613_);
v_pre_2614_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed), 12, 1);
lean_closure_set(v_pre_2614_, 0, v_pre_2613_);
v_pre_2608_ = v_pre_2614_;
goto v___jp_2607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___boxed(lean_object* v_config_2617_, lean_object* v_thms_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_config_2617_, v_thms_2618_);
lean_dec_ref(v_config_2617_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(lean_object* v_e_2620_, lean_object* v___y_2621_){
_start:
{
uint8_t v___x_2623_; 
v___x_2623_ = l_Lean_Expr_hasMVar(v_e_2620_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v_e_2620_);
return v___x_2624_;
}
else
{
lean_object* v___x_2625_; lean_object* v_mctx_2626_; lean_object* v___x_2627_; lean_object* v_fst_2628_; lean_object* v_snd_2629_; lean_object* v___x_2630_; lean_object* v_cache_2631_; lean_object* v_zetaDeltaFVarIds_2632_; lean_object* v_postponed_2633_; lean_object* v_diag_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2643_; 
v___x_2625_ = lean_st_ref_get(v___y_2621_);
v_mctx_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc_ref(v_mctx_2626_);
lean_dec(v___x_2625_);
v___x_2627_ = l_Lean_instantiateMVarsCore(v_mctx_2626_, v_e_2620_);
v_fst_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_fst_2628_);
v_snd_2629_ = lean_ctor_get(v___x_2627_, 1);
lean_inc(v_snd_2629_);
lean_dec_ref(v___x_2627_);
v___x_2630_ = lean_st_ref_take(v___y_2621_);
v_cache_2631_ = lean_ctor_get(v___x_2630_, 1);
v_zetaDeltaFVarIds_2632_ = lean_ctor_get(v___x_2630_, 2);
v_postponed_2633_ = lean_ctor_get(v___x_2630_, 3);
v_diag_2634_ = lean_ctor_get(v___x_2630_, 4);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; 
v_unused_2644_ = lean_ctor_get(v___x_2630_, 0);
lean_dec(v_unused_2644_);
v___x_2636_ = v___x_2630_;
v_isShared_2637_ = v_isSharedCheck_2643_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_diag_2634_);
lean_inc(v_postponed_2633_);
lean_inc(v_zetaDeltaFVarIds_2632_);
lean_inc(v_cache_2631_);
lean_dec(v___x_2630_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2643_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v_snd_2629_);
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_snd_2629_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_cache_2631_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_zetaDeltaFVarIds_2632_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v_postponed_2633_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v_diag_2634_);
v___x_2639_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_st_ref_put(v___y_2621_, v___x_2639_);
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_fst_2628_);
return v___x_2641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg___boxed(lean_object* v_e_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2645_, v___y_2646_);
lean_dec(v___y_2646_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(lean_object* v_e_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2649_, v___y_2656_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___boxed(lean_object* v_e_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(v_e_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy(lean_object* v_e_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v___x_2684_; lean_object* v_a_2685_; lean_object* v___x_2686_; 
v___x_2684_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2673_, v_a_2680_);
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref(v___x_2684_);
v___x_2686_ = l_Lean_Meta_Grind_simpCore(v_a_2685_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v_expr_2688_; lean_object* v_proof_x3f_2689_; uint8_t v_cache_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2714_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2686_, 1);
v_expr_2688_ = lean_ctor_get(v_a_2687_, 0);
v_proof_x3f_2689_ = lean_ctor_get(v_a_2687_, 1);
v_cache_2690_ = lean_ctor_get_uint8(v_a_2687_, sizeof(void*)*2);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_a_2687_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2692_ = v_a_2687_;
v_isShared_2693_ = v_isSharedCheck_2714_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_proof_x3f_2689_);
lean_inc(v_expr_2688_);
lean_dec(v_a_2687_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2714_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_expr_2688_, v_a_2681_, v_a_2682_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2705_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2705_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2705_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v_a_2695_);
v___x_2700_ = v___x_2692_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2695_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_proof_x3f_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, sizeof(void*)*2, v_cache_2690_);
v___x_2700_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2702_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2700_);
v___x_2702_ = v___x_2697_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_del_object(v___x_2692_);
lean_dec(v_proof_x3f_2689_);
v_a_2706_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2694_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2694_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
else
{
return v___x_2686_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy___boxed(lean_object* v_e_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_Meta_Grind_normLegacy(v_e_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
return v_res_2726_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__0(void){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2727_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__1(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__0, &l_Lean_Meta_Grind_normSym___redArg___closed__0_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__0);
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
return v___x_2729_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__2(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__1, &l_Lean_Meta_Grind_normSym___redArg___closed__1_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__1);
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
lean_ctor_set(v___x_2732_, 1, v___x_2730_);
lean_ctor_set(v___x_2732_, 2, v___x_2730_);
lean_ctor_set(v___x_2732_, 3, v___x_2730_);
return v___x_2732_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__3(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__1, &l_Lean_Meta_Grind_normSym___redArg___closed__1_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__1);
v___x_2734_ = lean_unsigned_to_nat(0u);
v___x_2735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
lean_ctor_set(v___x_2735_, 1, v___x_2733_);
lean_ctor_set(v___x_2735_, 2, v___x_2733_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg(lean_object* v_e_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v___x_2745_; lean_object* v_a_2746_; lean_object* v___x_2747_; 
v___x_2745_ = l_Lean_Meta_Grind_getNormSymTheorems___redArg(v_a_2743_);
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref(v___x_2745_);
v___x_2747_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2737_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc_n(v_a_2748_, 2);
lean_dec_ref_known(v___x_2747_, 1);
lean_inc(v_a_2746_);
v___x_2749_ = l_Lean_Meta_Grind_mkNormSymMethods(v_a_2748_, v_a_2746_);
v___x_2750_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_a_2748_, v_a_2746_);
lean_dec(v_a_2748_);
v___x_2751_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__2, &l_Lean_Meta_Grind_normSym___redArg___closed__2_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__2);
v___x_2752_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__3, &l_Lean_Meta_Grind_normSym___redArg___closed__3_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__3);
v___x_2753_ = l_Lean_Meta_Grind_symNorm(v_e_2736_, v___x_2749_, v___x_2750_, v___x_2751_, v___x_2752_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2762_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v_fst_2758_; lean_object* v___x_2760_; 
v_fst_2758_ = lean_ctor_get(v_a_2754_, 0);
lean_inc(v_fst_2758_);
lean_dec(v_a_2754_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v_fst_2758_);
v___x_2760_ = v___x_2756_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_fst_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
v_a_2763_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2753_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2753_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_a_2746_);
lean_dec_ref(v_e_2736_);
v_a_2771_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2747_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2747_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg___boxed(lean_object* v_e_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_Meta_Grind_normSym___redArg(v_e_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
lean_dec_ref(v_a_2780_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym(lean_object* v_e_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Meta_Grind_normSym___redArg(v_e_2789_, v_a_2791_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___boxed(lean_object* v_e_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean_Meta_Grind_normSym(v_e_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
return v_res_2812_;
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
