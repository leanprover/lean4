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
lean_object* l_Lean_Meta_Grind_NormSym_pushNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_reduceControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpExistsPropDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_reduceProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_etaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedNormSymTheorems_default;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Meta_Grind_normSymExt;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpNatSub(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_NormSym_simpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpNatRel___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpArith(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)(((size_t)(65536) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__15___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__15___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__20(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__0_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__2___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__1_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__3___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__2_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__4___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__3_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__5___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__4_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__6___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__5_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__6_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__7___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__5_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__7_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__9___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__8_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__10___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__8_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__9_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__11___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__9_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__10_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__12___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__10_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__11_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__13___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__11_value)} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__12_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__15___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__16_value;
static const lean_string_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(184, 238, 182, 216, 107, 45, 243, 168)}};
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19_value;
static const lean_closure_object l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__20_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__0(lean_object* v_x_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__0___boxed(lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__0(v_x_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__1(lean_object* v___f_122_, lean_object* v_x_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__1___boxed(lean_object* v___f_209_, lean_object* v_x_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__1(v___f_209_, v_x_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__2(lean_object* v___f_223_, lean_object* v_x_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__2___boxed(lean_object* v___f_310_, lean_object* v_x_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__2(v___f_310_, v_x_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__3(lean_object* v___f_324_, lean_object* v_x_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__3___boxed(lean_object* v___f_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__3(v___f_411_, v_x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__4(lean_object* v___f_425_, lean_object* v_x_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__4___boxed(lean_object* v___f_512_, lean_object* v_x_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__4(v___f_512_, v_x_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__5(lean_object* v___f_526_, lean_object* v_x_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__5___boxed(lean_object* v___f_613_, lean_object* v_x_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__5(v___f_613_, v_x_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__6(lean_object* v___f_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_box(0);
lean_inc_ref(v___y_628_);
v___x_640_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_628_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
if (lean_obj_tag(v_a_641_) == 0)
{
uint8_t v_done_642_; 
v_done_642_ = lean_ctor_get_uint8(v_a_641_, 0);
if (v_done_642_ == 0)
{
uint8_t v_contextDependent_643_; lean_object* v___x_644_; 
lean_dec_ref_known(v___x_640_, 1);
v_contextDependent_643_ = lean_ctor_get_uint8(v_a_641_, 1);
lean_dec_ref_known(v_a_641_, 0);
v___x_644_ = lean_apply_12(v___f_627_, v___x_639_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, lean_box(0));
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; uint8_t v___y_647_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
if (v_contextDependent_643_ == 0)
{
lean_dec(v_a_645_);
return v___x_644_;
}
else
{
if (lean_obj_tag(v_a_645_) == 0)
{
uint8_t v_contextDependent_657_; 
v_contextDependent_657_ = lean_ctor_get_uint8(v_a_645_, 1);
v___y_647_ = v_contextDependent_657_;
goto v___jp_646_;
}
else
{
uint8_t v_contextDependent_658_; 
v_contextDependent_658_ = lean_ctor_get_uint8(v_a_645_, sizeof(void*)*2 + 1);
v___y_647_ = v_contextDependent_658_;
goto v___jp_646_;
}
}
v___jp_646_:
{
if (v___y_647_ == 0)
{
lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_655_; 
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v___x_644_, 0);
lean_dec(v_unused_656_);
v___x_649_ = v___x_644_;
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
else
{
lean_dec(v___x_644_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_645_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_651_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
else
{
lean_dec(v_a_645_);
return v___x_644_;
}
}
}
else
{
return v___x_644_;
}
}
else
{
lean_dec_ref_known(v_a_641_, 0);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec_ref(v___f_627_);
return v___x_640_;
}
}
else
{
uint8_t v_done_659_; 
v_done_659_ = lean_ctor_get_uint8(v_a_641_, sizeof(void*)*2);
if (v_done_659_ == 0)
{
lean_object* v_e_x27_660_; lean_object* v_proof_661_; uint8_t v_contextDependent_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref_known(v___x_640_, 1);
v_e_x27_660_ = lean_ctor_get(v_a_641_, 0);
v_proof_661_ = lean_ctor_get(v_a_641_, 1);
v_contextDependent_662_ = lean_ctor_get_uint8(v_a_641_, sizeof(void*)*2 + 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_a_641_);
if (v_isSharedCheck_712_ == 0)
{
v___x_664_ = v_a_641_;
v_isShared_665_ = v_isSharedCheck_712_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_proof_661_);
lean_inc(v_e_x27_660_);
lean_dec(v_a_641_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_712_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; 
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc(v___y_633_);
lean_inc_ref(v___y_632_);
lean_inc_ref(v_e_x27_660_);
v___x_666_ = lean_apply_12(v___f_627_, v___x_639_, v_e_x27_660_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, lean_box(0));
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_711_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_711_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_711_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_711_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
if (lean_obj_tag(v_a_667_) == 0)
{
uint8_t v_done_671_; uint8_t v_contextDependent_672_; uint8_t v___y_674_; 
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___y_628_);
v_done_671_ = lean_ctor_get_uint8(v_a_667_, 0);
v_contextDependent_672_ = lean_ctor_get_uint8(v_a_667_, 1);
lean_dec_ref_known(v_a_667_, 0);
if (v_contextDependent_662_ == 0)
{
v___y_674_ = v_contextDependent_672_;
goto v___jp_673_;
}
else
{
v___y_674_ = v_contextDependent_662_;
goto v___jp_673_;
}
v___jp_673_:
{
lean_object* v___x_676_; 
if (v_isShared_665_ == 0)
{
v___x_676_ = v___x_664_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_e_x27_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_proof_661_);
v___x_676_ = v_reuseFailAlloc_680_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_678_; 
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*2, v_done_671_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*2 + 1, v___y_674_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_676_);
v___x_678_ = v___x_669_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_e_x27_681_; lean_object* v_proof_682_; uint8_t v_done_683_; uint8_t v_contextDependent_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_710_; 
lean_del_object(v___x_669_);
lean_del_object(v___x_664_);
v_e_x27_681_ = lean_ctor_get(v_a_667_, 0);
v_proof_682_ = lean_ctor_get(v_a_667_, 1);
v_done_683_ = lean_ctor_get_uint8(v_a_667_, sizeof(void*)*2);
v_contextDependent_684_ = lean_ctor_get_uint8(v_a_667_, sizeof(void*)*2 + 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_a_667_);
if (v_isSharedCheck_710_ == 0)
{
v___x_686_ = v_a_667_;
v_isShared_687_ = v_isSharedCheck_710_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_proof_682_);
lean_inc(v_e_x27_681_);
lean_dec(v_a_667_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_710_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; 
lean_inc_ref(v_e_x27_681_);
v___x_688_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_628_, v_e_x27_660_, v_proof_661_, v_e_x27_681_, v_proof_682_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_701_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_701_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___y_694_; 
if (v_contextDependent_662_ == 0)
{
v___y_694_ = v_contextDependent_684_;
goto v___jp_693_;
}
else
{
v___y_694_ = v_contextDependent_662_;
goto v___jp_693_;
}
v___jp_693_:
{
lean_object* v___x_696_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_a_689_);
v___x_696_ = v___x_686_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_e_x27_681_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_a_689_);
lean_ctor_set_uint8(v_reuseFailAlloc_700_, sizeof(void*)*2, v_done_683_);
v___x_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*2 + 1, v___y_694_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_696_);
v___x_698_ = v___x_691_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_del_object(v___x_686_);
lean_dec_ref(v_e_x27_681_);
v_a_702_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_688_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_688_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_664_);
lean_dec_ref(v_proof_661_);
lean_dec_ref(v_e_x27_660_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___y_628_);
return v___x_666_;
}
}
}
else
{
lean_dec_ref_known(v_a_641_, 2);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec_ref(v___f_627_);
return v___x_640_;
}
}
}
else
{
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec_ref(v___f_627_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__6___boxed(lean_object* v___f_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__6(v___f_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__7(lean_object* v___f_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___y_739_; lean_object* v___y_740_; uint8_t v___y_741_; lean_object* v___y_745_; lean_object* v___y_746_; uint8_t v___y_747_; uint8_t v___y_748_; uint8_t v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; uint8_t v___y_755_; lean_object* v___y_759_; lean_object* v_e_x27_760_; lean_object* v_proof_761_; uint8_t v_done_762_; uint8_t v_contextDependent_763_; lean_object* v___y_785_; lean_object* v_a_786_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_box(0);
lean_inc_ref(v___y_727_);
v___x_798_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v___y_727_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
if (lean_obj_tag(v_a_799_) == 0)
{
uint8_t v_done_800_; 
v_done_800_ = lean_ctor_get_uint8(v_a_799_, 0);
if (v_done_800_ == 0)
{
uint8_t v_contextDependent_801_; lean_object* v___x_802_; 
lean_dec_ref_known(v___x_798_, 1);
v_contextDependent_801_ = lean_ctor_get_uint8(v_a_799_, 1);
lean_dec_ref_known(v_a_799_, 0);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc_ref(v___y_727_);
v___x_802_ = lean_apply_12(v___f_726_, v___x_797_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, lean_box(0));
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; uint8_t v___y_805_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
if (v_contextDependent_801_ == 0)
{
v___y_785_ = v___x_802_;
v_a_786_ = v_a_803_;
goto v___jp_784_;
}
else
{
if (lean_obj_tag(v_a_803_) == 0)
{
uint8_t v_contextDependent_815_; 
v_contextDependent_815_ = lean_ctor_get_uint8(v_a_803_, 1);
v___y_805_ = v_contextDependent_815_;
goto v___jp_804_;
}
else
{
uint8_t v_contextDependent_816_; 
v_contextDependent_816_ = lean_ctor_get_uint8(v_a_803_, sizeof(void*)*2 + 1);
v___y_805_ = v_contextDependent_816_;
goto v___jp_804_;
}
}
v___jp_804_:
{
if (v___y_805_ == 0)
{
lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v___x_802_, 0);
lean_dec(v_unused_814_);
v___x_807_ = v___x_802_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_dec(v___x_802_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_803_);
lean_inc_ref(v___x_809_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
v___y_785_ = v___x_811_;
v_a_786_ = v___x_809_;
goto v___jp_784_;
}
}
}
else
{
v___y_785_ = v___x_802_;
v_a_786_ = v_a_803_;
goto v___jp_784_;
}
}
}
else
{
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_727_);
return v___x_802_;
}
}
else
{
lean_dec_ref_known(v_a_799_, 0);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec_ref(v___f_726_);
return v___x_798_;
}
}
else
{
uint8_t v_done_817_; 
v_done_817_ = lean_ctor_get_uint8(v_a_799_, sizeof(void*)*2);
if (v_done_817_ == 0)
{
lean_object* v_e_x27_818_; lean_object* v_proof_819_; uint8_t v_contextDependent_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref_known(v___x_798_, 1);
v_e_x27_818_ = lean_ctor_get(v_a_799_, 0);
v_proof_819_ = lean_ctor_get(v_a_799_, 1);
v_contextDependent_820_ = lean_ctor_get_uint8(v_a_799_, sizeof(void*)*2 + 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_a_799_);
if (v_isSharedCheck_870_ == 0)
{
v___x_822_ = v_a_799_;
v_isShared_823_ = v_isSharedCheck_870_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_proof_819_);
lean_inc(v_e_x27_818_);
lean_dec(v_a_799_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_870_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; 
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
lean_inc(v___y_734_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
lean_inc_ref(v___y_731_);
lean_inc_ref(v_e_x27_818_);
v___x_824_ = lean_apply_12(v___f_726_, v___x_797_, v_e_x27_818_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, lean_box(0));
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_869_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_869_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_869_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_869_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
if (lean_obj_tag(v_a_825_) == 0)
{
uint8_t v_done_829_; uint8_t v_contextDependent_830_; uint8_t v___y_832_; 
v_done_829_ = lean_ctor_get_uint8(v_a_825_, 0);
v_contextDependent_830_ = lean_ctor_get_uint8(v_a_825_, 1);
lean_dec_ref_known(v_a_825_, 0);
if (v_contextDependent_820_ == 0)
{
v___y_832_ = v_contextDependent_830_;
goto v___jp_831_;
}
else
{
v___y_832_ = v_contextDependent_820_;
goto v___jp_831_;
}
v___jp_831_:
{
lean_object* v___x_834_; 
lean_inc_ref(v_proof_819_);
lean_inc_ref(v_e_x27_818_);
if (v_isShared_823_ == 0)
{
v___x_834_ = v___x_822_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_e_x27_818_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_proof_819_);
v___x_834_ = v_reuseFailAlloc_838_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_836_; 
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*2, v_done_829_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*2 + 1, v___y_832_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_834_);
v___x_836_ = v___x_827_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
v___y_759_ = v___x_836_;
v_e_x27_760_ = v_e_x27_818_;
v_proof_761_ = v_proof_819_;
v_done_762_ = v_done_829_;
v_contextDependent_763_ = v___y_832_;
goto v___jp_758_;
}
}
}
}
else
{
lean_object* v_e_x27_839_; lean_object* v_proof_840_; uint8_t v_done_841_; uint8_t v_contextDependent_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_868_; 
lean_del_object(v___x_827_);
lean_del_object(v___x_822_);
v_e_x27_839_ = lean_ctor_get(v_a_825_, 0);
v_proof_840_ = lean_ctor_get(v_a_825_, 1);
v_done_841_ = lean_ctor_get_uint8(v_a_825_, sizeof(void*)*2);
v_contextDependent_842_ = lean_ctor_get_uint8(v_a_825_, sizeof(void*)*2 + 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_a_825_);
if (v_isSharedCheck_868_ == 0)
{
v___x_844_ = v_a_825_;
v_isShared_845_ = v_isSharedCheck_868_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_proof_840_);
lean_inc(v_e_x27_839_);
lean_dec(v_a_825_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_868_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; 
lean_inc_ref(v_e_x27_839_);
lean_inc_ref(v___y_727_);
v___x_846_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_727_, v_e_x27_818_, v_proof_819_, v_e_x27_839_, v_proof_840_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_859_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_859_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_859_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_859_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
uint8_t v___y_852_; 
if (v_contextDependent_820_ == 0)
{
v___y_852_ = v_contextDependent_842_;
goto v___jp_851_;
}
else
{
v___y_852_ = v_contextDependent_820_;
goto v___jp_851_;
}
v___jp_851_:
{
lean_object* v___x_854_; 
lean_inc(v_a_847_);
lean_inc_ref(v_e_x27_839_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_a_847_);
v___x_854_ = v___x_844_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_e_x27_839_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_a_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_858_, sizeof(void*)*2, v_done_841_);
v___x_854_ = v_reuseFailAlloc_858_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
lean_ctor_set_uint8(v___x_854_, sizeof(void*)*2 + 1, v___y_852_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_854_);
v___x_856_ = v___x_849_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
v___y_759_ = v___x_856_;
v_e_x27_760_ = v_e_x27_839_;
v_proof_761_ = v_a_847_;
v_done_762_ = v_done_841_;
v_contextDependent_763_ = v___y_852_;
goto v___jp_758_;
}
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_del_object(v___x_844_);
lean_dec_ref(v_e_x27_839_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_727_);
v_a_860_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_846_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_846_);
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
}
else
{
lean_del_object(v___x_822_);
lean_dec_ref(v_proof_819_);
lean_dec_ref(v_e_x27_818_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_727_);
return v___x_824_;
}
}
}
else
{
lean_dec_ref_known(v_a_799_, 2);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec_ref(v___f_726_);
return v___x_798_;
}
}
}
else
{
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec_ref(v___f_726_);
return v___x_798_;
}
v___jp_738_:
{
if (v___y_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec_ref(v___y_739_);
v___x_742_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_740_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
else
{
lean_dec_ref(v___y_740_);
return v___y_739_;
}
}
v___jp_744_:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_749_, 0, v___y_746_);
lean_ctor_set(v___x_749_, 1, v___y_745_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*2, v___y_747_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*2 + 1, v___y_748_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
v___jp_751_:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_756_, 0, v___y_754_);
lean_ctor_set(v___x_756_, 1, v___y_753_);
lean_ctor_set_uint8(v___x_756_, sizeof(void*)*2, v___y_752_);
lean_ctor_set_uint8(v___x_756_, sizeof(void*)*2 + 1, v___y_755_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
v___jp_758_:
{
if (v_done_762_ == 0)
{
lean_object* v___x_764_; 
lean_dec_ref(v___y_759_);
lean_inc_ref(v_e_x27_760_);
v___x_764_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v_e_x27_760_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
if (lean_obj_tag(v_a_765_) == 0)
{
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_727_);
if (v_contextDependent_763_ == 0)
{
uint8_t v_done_766_; uint8_t v_contextDependent_767_; 
v_done_766_ = lean_ctor_get_uint8(v_a_765_, 0);
v_contextDependent_767_ = lean_ctor_get_uint8(v_a_765_, 1);
lean_dec_ref_known(v_a_765_, 0);
v___y_752_ = v_done_766_;
v___y_753_ = v_proof_761_;
v___y_754_ = v_e_x27_760_;
v___y_755_ = v_contextDependent_767_;
goto v___jp_751_;
}
else
{
uint8_t v_done_768_; 
v_done_768_ = lean_ctor_get_uint8(v_a_765_, 0);
lean_dec_ref_known(v_a_765_, 0);
v___y_752_ = v_done_768_;
v___y_753_ = v_proof_761_;
v___y_754_ = v_e_x27_760_;
v___y_755_ = v_contextDependent_763_;
goto v___jp_751_;
}
}
else
{
lean_object* v_e_x27_769_; lean_object* v_proof_770_; uint8_t v_done_771_; uint8_t v_contextDependent_772_; lean_object* v___x_773_; 
v_e_x27_769_ = lean_ctor_get(v_a_765_, 0);
lean_inc_ref_n(v_e_x27_769_, 2);
v_proof_770_ = lean_ctor_get(v_a_765_, 1);
lean_inc_ref(v_proof_770_);
v_done_771_ = lean_ctor_get_uint8(v_a_765_, sizeof(void*)*2);
v_contextDependent_772_ = lean_ctor_get_uint8(v_a_765_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_765_, 2);
v___x_773_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_727_, v_e_x27_760_, v_proof_761_, v_e_x27_769_, v_proof_770_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
if (lean_obj_tag(v___x_773_) == 0)
{
if (v_contextDependent_763_ == 0)
{
lean_object* v_a_774_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
v___y_745_ = v_a_774_;
v___y_746_ = v_e_x27_769_;
v___y_747_ = v_done_771_;
v___y_748_ = v_contextDependent_772_;
goto v___jp_744_;
}
else
{
lean_object* v_a_775_; 
v_a_775_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_773_, 1);
v___y_745_ = v_a_775_;
v___y_746_ = v_e_x27_769_;
v___y_747_ = v_done_771_;
v___y_748_ = v_contextDependent_763_;
goto v___jp_744_;
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_e_x27_769_);
v_a_776_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_773_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_773_);
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
}
else
{
lean_dec_ref(v_proof_761_);
lean_dec_ref(v_e_x27_760_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_727_);
return v___x_764_;
}
}
else
{
lean_dec_ref(v_proof_761_);
lean_dec_ref(v_e_x27_760_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_727_);
return v___y_759_;
}
}
v___jp_784_:
{
if (lean_obj_tag(v_a_786_) == 0)
{
uint8_t v_done_787_; 
v_done_787_ = lean_ctor_get_uint8(v_a_786_, 0);
if (v_done_787_ == 0)
{
uint8_t v_contextDependent_788_; lean_object* v___x_789_; 
lean_dec_ref(v___y_785_);
v_contextDependent_788_ = lean_ctor_get_uint8(v_a_786_, 1);
lean_dec_ref_known(v_a_786_, 0);
v___x_789_ = l_Lean_Meta_Sym_Simp_zeta___redArg(v___y_727_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
if (lean_obj_tag(v___x_789_) == 0)
{
if (v_contextDependent_788_ == 0)
{
return v___x_789_;
}
else
{
lean_object* v_a_790_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
if (lean_obj_tag(v_a_790_) == 0)
{
uint8_t v_contextDependent_791_; 
v_contextDependent_791_ = lean_ctor_get_uint8(v_a_790_, 1);
v___y_739_ = v___x_789_;
v___y_740_ = v_a_790_;
v___y_741_ = v_contextDependent_791_;
goto v___jp_738_;
}
else
{
uint8_t v_contextDependent_792_; 
v_contextDependent_792_ = lean_ctor_get_uint8(v_a_790_, sizeof(void*)*2 + 1);
v___y_739_ = v___x_789_;
v___y_740_ = v_a_790_;
v___y_741_ = v_contextDependent_792_;
goto v___jp_738_;
}
}
}
else
{
return v___x_789_;
}
}
else
{
lean_dec_ref_known(v_a_786_, 0);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_727_);
return v___y_785_;
}
}
else
{
lean_object* v_e_x27_793_; lean_object* v_proof_794_; uint8_t v_done_795_; uint8_t v_contextDependent_796_; 
v_e_x27_793_ = lean_ctor_get(v_a_786_, 0);
lean_inc_ref(v_e_x27_793_);
v_proof_794_ = lean_ctor_get(v_a_786_, 1);
lean_inc_ref(v_proof_794_);
v_done_795_ = lean_ctor_get_uint8(v_a_786_, sizeof(void*)*2);
v_contextDependent_796_ = lean_ctor_get_uint8(v_a_786_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_786_, 2);
v___y_759_ = v___y_785_;
v_e_x27_760_ = v_e_x27_793_;
v_proof_761_ = v_proof_794_;
v_done_762_ = v_done_795_;
v_contextDependent_763_ = v_contextDependent_796_;
goto v___jp_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__7___boxed(lean_object* v___f_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__7(v___f_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__8(lean_object* v_config_884_, lean_object* v_x_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v_distrib_897_; lean_object* v___x_898_; 
v_distrib_897_ = lean_ctor_get_uint8(v_config_884_, sizeof(void*)*18 + 21);
v___x_898_ = l_Lean_Meta_Sym_Simp_simpNatSub(v_distrib_897_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__8___boxed(lean_object* v_config_899_, lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__8(v_config_899_, v_x_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v_config_899_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__9(lean_object* v_x_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
lean_inc_ref(v___y_914_);
v___x_925_ = l_Lean_Meta_Grind_NormSym_simpForall(v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
if (lean_obj_tag(v_a_926_) == 0)
{
uint8_t v_done_927_; 
v_done_927_ = lean_ctor_get_uint8(v_a_926_, 0);
if (v_done_927_ == 0)
{
uint8_t v_contextDependent_928_; lean_object* v___x_929_; 
lean_dec_ref_known(v___x_925_, 1);
v_contextDependent_928_ = lean_ctor_get_uint8(v_a_926_, 1);
lean_dec_ref_known(v_a_926_, 0);
v___x_929_ = l_Lean_Meta_Grind_NormSym_simpExists___redArg(v___y_914_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec_ref(v___y_914_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; uint8_t v___y_932_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
if (v_contextDependent_928_ == 0)
{
return v___x_929_;
}
else
{
if (lean_obj_tag(v_a_930_) == 0)
{
uint8_t v_contextDependent_942_; 
v_contextDependent_942_ = lean_ctor_get_uint8(v_a_930_, 1);
v___y_932_ = v_contextDependent_942_;
goto v___jp_931_;
}
else
{
uint8_t v_contextDependent_943_; 
v_contextDependent_943_ = lean_ctor_get_uint8(v_a_930_, sizeof(void*)*2 + 1);
v___y_932_ = v_contextDependent_943_;
goto v___jp_931_;
}
}
v___jp_931_:
{
if (v___y_932_ == 0)
{
lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
lean_inc(v_a_930_);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v___x_929_, 0);
lean_dec(v_unused_941_);
v___x_934_ = v___x_929_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_dec(v___x_929_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_930_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
return v___x_929_;
}
}
}
else
{
return v___x_929_;
}
}
else
{
lean_dec_ref_known(v_a_926_, 0);
lean_dec_ref(v___y_914_);
return v___x_925_;
}
}
else
{
uint8_t v_done_944_; 
v_done_944_ = lean_ctor_get_uint8(v_a_926_, sizeof(void*)*2);
if (v_done_944_ == 0)
{
lean_object* v_e_x27_945_; lean_object* v_proof_946_; uint8_t v_contextDependent_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref_known(v___x_925_, 1);
v_e_x27_945_ = lean_ctor_get(v_a_926_, 0);
v_proof_946_ = lean_ctor_get(v_a_926_, 1);
v_contextDependent_947_ = lean_ctor_get_uint8(v_a_926_, sizeof(void*)*2 + 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_a_926_);
if (v_isSharedCheck_997_ == 0)
{
v___x_949_ = v_a_926_;
v_isShared_950_ = v_isSharedCheck_997_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_proof_946_);
lean_inc(v_e_x27_945_);
lean_dec(v_a_926_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_997_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_Grind_NormSym_simpExists___redArg(v_e_x27_945_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_996_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_996_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_996_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_996_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
if (lean_obj_tag(v_a_952_) == 0)
{
uint8_t v_done_956_; uint8_t v_contextDependent_957_; uint8_t v___y_959_; 
lean_dec_ref(v___y_914_);
v_done_956_ = lean_ctor_get_uint8(v_a_952_, 0);
v_contextDependent_957_ = lean_ctor_get_uint8(v_a_952_, 1);
lean_dec_ref_known(v_a_952_, 0);
if (v_contextDependent_947_ == 0)
{
v___y_959_ = v_contextDependent_957_;
goto v___jp_958_;
}
else
{
v___y_959_ = v_contextDependent_947_;
goto v___jp_958_;
}
v___jp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_950_ == 0)
{
v___x_961_ = v___x_949_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_e_x27_945_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_proof_946_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; 
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*2, v_done_956_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*2 + 1, v___y_959_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_961_);
v___x_963_ = v___x_954_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v_e_x27_966_; lean_object* v_proof_967_; uint8_t v_done_968_; uint8_t v_contextDependent_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_995_; 
lean_del_object(v___x_954_);
lean_del_object(v___x_949_);
v_e_x27_966_ = lean_ctor_get(v_a_952_, 0);
v_proof_967_ = lean_ctor_get(v_a_952_, 1);
v_done_968_ = lean_ctor_get_uint8(v_a_952_, sizeof(void*)*2);
v_contextDependent_969_ = lean_ctor_get_uint8(v_a_952_, sizeof(void*)*2 + 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_a_952_);
if (v_isSharedCheck_995_ == 0)
{
v___x_971_ = v_a_952_;
v_isShared_972_ = v_isSharedCheck_995_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_proof_967_);
lean_inc(v_e_x27_966_);
lean_dec(v_a_952_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_995_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; 
lean_inc_ref(v_e_x27_966_);
v___x_973_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_914_, v_e_x27_945_, v_proof_946_, v_e_x27_966_, v_proof_967_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_986_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_986_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_986_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_986_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
uint8_t v___y_979_; 
if (v_contextDependent_947_ == 0)
{
v___y_979_ = v_contextDependent_969_;
goto v___jp_978_;
}
else
{
v___y_979_ = v_contextDependent_947_;
goto v___jp_978_;
}
v___jp_978_:
{
lean_object* v___x_981_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v_a_974_);
v___x_981_ = v___x_971_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_e_x27_966_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_a_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*2, v_done_968_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*2 + 1, v___y_979_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_981_);
v___x_983_ = v___x_976_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_del_object(v___x_971_);
lean_dec_ref(v_e_x27_966_);
v_a_987_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_973_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_973_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_949_);
lean_dec_ref(v_proof_946_);
lean_dec_ref(v_e_x27_945_);
lean_dec_ref(v___y_914_);
return v___x_951_;
}
}
}
else
{
lean_dec_ref_known(v_a_926_, 2);
lean_dec_ref(v___y_914_);
return v___x_925_;
}
}
}
else
{
lean_dec_ref(v___y_914_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__9___boxed(lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__9(v_x_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__10(lean_object* v___f_1011_, lean_object* v_x_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_box(0);
lean_inc_ref(v___y_1013_);
v___x_1025_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
if (lean_obj_tag(v_a_1026_) == 0)
{
uint8_t v_done_1027_; 
v_done_1027_ = lean_ctor_get_uint8(v_a_1026_, 0);
if (v_done_1027_ == 0)
{
uint8_t v_contextDependent_1028_; lean_object* v___x_1029_; 
lean_dec_ref_known(v___x_1025_, 1);
v_contextDependent_1028_ = lean_ctor_get_uint8(v_a_1026_, 1);
lean_dec_ref_known(v_a_1026_, 0);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
lean_inc(v___y_1014_);
v___x_1029_ = lean_apply_12(v___f_1011_, v___x_1024_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; uint8_t v___y_1032_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
if (v_contextDependent_1028_ == 0)
{
lean_dec(v_a_1030_);
return v___x_1029_;
}
else
{
if (lean_obj_tag(v_a_1030_) == 0)
{
uint8_t v_contextDependent_1042_; 
v_contextDependent_1042_ = lean_ctor_get_uint8(v_a_1030_, 1);
v___y_1032_ = v_contextDependent_1042_;
goto v___jp_1031_;
}
else
{
uint8_t v_contextDependent_1043_; 
v_contextDependent_1043_ = lean_ctor_get_uint8(v_a_1030_, sizeof(void*)*2 + 1);
v___y_1032_ = v_contextDependent_1043_;
goto v___jp_1031_;
}
}
v___jp_1031_:
{
if (v___y_1032_ == 0)
{
lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v___x_1029_, 0);
lean_dec(v_unused_1041_);
v___x_1034_ = v___x_1029_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_dec(v___x_1029_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1030_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
else
{
lean_dec(v_a_1030_);
return v___x_1029_;
}
}
}
else
{
return v___x_1029_;
}
}
else
{
lean_dec_ref_known(v_a_1026_, 0);
lean_dec_ref(v___y_1013_);
lean_dec_ref(v___f_1011_);
return v___x_1025_;
}
}
else
{
uint8_t v_done_1044_; 
v_done_1044_ = lean_ctor_get_uint8(v_a_1026_, sizeof(void*)*2);
if (v_done_1044_ == 0)
{
lean_object* v_e_x27_1045_; lean_object* v_proof_1046_; uint8_t v_contextDependent_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref_known(v___x_1025_, 1);
v_e_x27_1045_ = lean_ctor_get(v_a_1026_, 0);
v_proof_1046_ = lean_ctor_get(v_a_1026_, 1);
v_contextDependent_1047_ = lean_ctor_get_uint8(v_a_1026_, sizeof(void*)*2 + 1);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_a_1026_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1049_ = v_a_1026_;
v_isShared_1050_ = v_isSharedCheck_1097_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_proof_1046_);
lean_inc(v_e_x27_1045_);
lean_dec(v_a_1026_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1097_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; 
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
lean_inc(v___y_1014_);
lean_inc_ref(v_e_x27_1045_);
v___x_1051_ = lean_apply_12(v___f_1011_, v___x_1024_, v_e_x27_1045_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1096_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1096_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1096_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
if (lean_obj_tag(v_a_1052_) == 0)
{
uint8_t v_done_1056_; uint8_t v_contextDependent_1057_; uint8_t v___y_1059_; 
lean_dec_ref(v___y_1013_);
v_done_1056_ = lean_ctor_get_uint8(v_a_1052_, 0);
v_contextDependent_1057_ = lean_ctor_get_uint8(v_a_1052_, 1);
lean_dec_ref_known(v_a_1052_, 0);
if (v_contextDependent_1047_ == 0)
{
v___y_1059_ = v_contextDependent_1057_;
goto v___jp_1058_;
}
else
{
v___y_1059_ = v_contextDependent_1047_;
goto v___jp_1058_;
}
v___jp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1050_ == 0)
{
v___x_1061_ = v___x_1049_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_e_x27_1045_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_proof_1046_);
v___x_1061_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*2, v_done_1056_);
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*2 + 1, v___y_1059_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1061_);
v___x_1063_ = v___x_1054_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_e_x27_1066_; lean_object* v_proof_1067_; uint8_t v_done_1068_; uint8_t v_contextDependent_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1095_; 
lean_del_object(v___x_1054_);
lean_del_object(v___x_1049_);
v_e_x27_1066_ = lean_ctor_get(v_a_1052_, 0);
v_proof_1067_ = lean_ctor_get(v_a_1052_, 1);
v_done_1068_ = lean_ctor_get_uint8(v_a_1052_, sizeof(void*)*2);
v_contextDependent_1069_ = lean_ctor_get_uint8(v_a_1052_, sizeof(void*)*2 + 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_a_1052_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1071_ = v_a_1052_;
v_isShared_1072_ = v_isSharedCheck_1095_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_proof_1067_);
lean_inc(v_e_x27_1066_);
lean_dec(v_a_1052_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1095_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; 
lean_inc_ref(v_e_x27_1066_);
v___x_1073_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1013_, v_e_x27_1045_, v_proof_1046_, v_e_x27_1066_, v_proof_1067_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1086_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1086_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1086_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
uint8_t v___y_1079_; 
if (v_contextDependent_1047_ == 0)
{
v___y_1079_ = v_contextDependent_1069_;
goto v___jp_1078_;
}
else
{
v___y_1079_ = v_contextDependent_1047_;
goto v___jp_1078_;
}
v___jp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v_a_1074_);
v___x_1081_ = v___x_1071_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_e_x27_1066_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_a_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*2, v_done_1068_);
v___x_1081_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1083_; 
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*2 + 1, v___y_1079_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1081_);
v___x_1083_ = v___x_1076_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_del_object(v___x_1071_);
lean_dec_ref(v_e_x27_1066_);
v_a_1087_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1073_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1073_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1049_);
lean_dec_ref(v_proof_1046_);
lean_dec_ref(v_e_x27_1045_);
lean_dec_ref(v___y_1013_);
return v___x_1051_;
}
}
}
else
{
lean_dec_ref_known(v_a_1026_, 2);
lean_dec_ref(v___y_1013_);
lean_dec_ref(v___f_1011_);
return v___x_1025_;
}
}
}
else
{
lean_dec_ref(v___y_1013_);
lean_dec_ref(v___f_1011_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__10___boxed(lean_object* v___f_1098_, lean_object* v_x_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__10(v___f_1098_, v_x_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__11(lean_object* v___f_1112_, lean_object* v_x_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_box(0);
v___x_1126_ = l_Lean_Meta_Grind_NormSym_simpDIte(v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
if (lean_obj_tag(v_a_1127_) == 0)
{
uint8_t v_done_1128_; 
v_done_1128_ = lean_ctor_get_uint8(v_a_1127_, 0);
if (v_done_1128_ == 0)
{
uint8_t v_contextDependent_1129_; lean_object* v___x_1130_; 
lean_dec_ref_known(v___x_1126_, 1);
v_contextDependent_1129_ = lean_ctor_get_uint8(v_a_1127_, 1);
lean_dec_ref_known(v_a_1127_, 0);
lean_inc(v___y_1123_);
lean_inc_ref(v___y_1122_);
lean_inc(v___y_1121_);
lean_inc_ref(v___y_1120_);
lean_inc(v___y_1119_);
lean_inc_ref(v___y_1118_);
lean_inc(v___y_1117_);
lean_inc_ref(v___y_1116_);
lean_inc(v___y_1115_);
v___x_1130_ = lean_apply_12(v___f_1112_, v___x_1125_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, lean_box(0));
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; uint8_t v___y_1133_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
if (v_contextDependent_1129_ == 0)
{
lean_dec(v_a_1131_);
return v___x_1130_;
}
else
{
if (lean_obj_tag(v_a_1131_) == 0)
{
uint8_t v_contextDependent_1143_; 
v_contextDependent_1143_ = lean_ctor_get_uint8(v_a_1131_, 1);
v___y_1133_ = v_contextDependent_1143_;
goto v___jp_1132_;
}
else
{
uint8_t v_contextDependent_1144_; 
v_contextDependent_1144_ = lean_ctor_get_uint8(v_a_1131_, sizeof(void*)*2 + 1);
v___y_1133_ = v_contextDependent_1144_;
goto v___jp_1132_;
}
}
v___jp_1132_:
{
if (v___y_1133_ == 0)
{
lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v___x_1130_, 0);
lean_dec(v_unused_1142_);
v___x_1135_ = v___x_1130_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_dec(v___x_1130_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1131_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
lean_dec(v_a_1131_);
return v___x_1130_;
}
}
}
else
{
return v___x_1130_;
}
}
else
{
lean_dec_ref_known(v_a_1127_, 0);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v___f_1112_);
return v___x_1126_;
}
}
else
{
uint8_t v_done_1145_; 
v_done_1145_ = lean_ctor_get_uint8(v_a_1127_, sizeof(void*)*2);
if (v_done_1145_ == 0)
{
lean_object* v_e_x27_1146_; lean_object* v_proof_1147_; uint8_t v_contextDependent_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref_known(v___x_1126_, 1);
v_e_x27_1146_ = lean_ctor_get(v_a_1127_, 0);
v_proof_1147_ = lean_ctor_get(v_a_1127_, 1);
v_contextDependent_1148_ = lean_ctor_get_uint8(v_a_1127_, sizeof(void*)*2 + 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_a_1127_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1150_ = v_a_1127_;
v_isShared_1151_ = v_isSharedCheck_1198_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_proof_1147_);
lean_inc(v_e_x27_1146_);
lean_dec(v_a_1127_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1198_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; 
lean_inc(v___y_1123_);
lean_inc_ref(v___y_1122_);
lean_inc(v___y_1121_);
lean_inc_ref(v___y_1120_);
lean_inc(v___y_1119_);
lean_inc_ref(v___y_1118_);
lean_inc(v___y_1117_);
lean_inc_ref(v___y_1116_);
lean_inc(v___y_1115_);
lean_inc_ref(v_e_x27_1146_);
v___x_1152_ = lean_apply_12(v___f_1112_, v___x_1125_, v_e_x27_1146_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, lean_box(0));
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1197_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1197_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1197_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
if (lean_obj_tag(v_a_1153_) == 0)
{
uint8_t v_done_1157_; uint8_t v_contextDependent_1158_; uint8_t v___y_1160_; 
lean_dec_ref(v___y_1114_);
v_done_1157_ = lean_ctor_get_uint8(v_a_1153_, 0);
v_contextDependent_1158_ = lean_ctor_get_uint8(v_a_1153_, 1);
lean_dec_ref_known(v_a_1153_, 0);
if (v_contextDependent_1148_ == 0)
{
v___y_1160_ = v_contextDependent_1158_;
goto v___jp_1159_;
}
else
{
v___y_1160_ = v_contextDependent_1148_;
goto v___jp_1159_;
}
v___jp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_1151_ == 0)
{
v___x_1162_ = v___x_1150_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_e_x27_1146_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_proof_1147_);
v___x_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; 
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*2, v_done_1157_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*2 + 1, v___y_1160_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1162_);
v___x_1164_ = v___x_1155_;
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
else
{
lean_object* v_e_x27_1167_; lean_object* v_proof_1168_; uint8_t v_done_1169_; uint8_t v_contextDependent_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1196_; 
lean_del_object(v___x_1155_);
lean_del_object(v___x_1150_);
v_e_x27_1167_ = lean_ctor_get(v_a_1153_, 0);
v_proof_1168_ = lean_ctor_get(v_a_1153_, 1);
v_done_1169_ = lean_ctor_get_uint8(v_a_1153_, sizeof(void*)*2);
v_contextDependent_1170_ = lean_ctor_get_uint8(v_a_1153_, sizeof(void*)*2 + 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_a_1153_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1172_ = v_a_1153_;
v_isShared_1173_ = v_isSharedCheck_1196_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_proof_1168_);
lean_inc(v_e_x27_1167_);
lean_dec(v_a_1153_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1196_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; 
lean_inc_ref(v_e_x27_1167_);
v___x_1174_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1114_, v_e_x27_1146_, v_proof_1147_, v_e_x27_1167_, v_proof_1168_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1187_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1187_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1187_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
uint8_t v___y_1180_; 
if (v_contextDependent_1148_ == 0)
{
v___y_1180_ = v_contextDependent_1170_;
goto v___jp_1179_;
}
else
{
v___y_1180_ = v_contextDependent_1148_;
goto v___jp_1179_;
}
v___jp_1179_:
{
lean_object* v___x_1182_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_a_1175_);
v___x_1182_ = v___x_1172_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_e_x27_1167_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_a_1175_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*2, v_done_1169_);
v___x_1182_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; 
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*2 + 1, v___y_1180_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1182_);
v___x_1184_ = v___x_1177_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_del_object(v___x_1172_);
lean_dec_ref(v_e_x27_1167_);
v_a_1188_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1174_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1174_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1150_);
lean_dec_ref(v_proof_1147_);
lean_dec_ref(v_e_x27_1146_);
lean_dec_ref(v___y_1114_);
return v___x_1152_;
}
}
}
else
{
lean_dec_ref_known(v_a_1127_, 2);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v___f_1112_);
return v___x_1126_;
}
}
}
else
{
lean_dec_ref(v___y_1114_);
lean_dec_ref(v___f_1112_);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__11___boxed(lean_object* v___f_1199_, lean_object* v_x_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__11(v___f_1199_, v_x_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__12(lean_object* v___f_1213_, lean_object* v_x_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v___y_1215_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
if (lean_obj_tag(v_a_1228_) == 0)
{
uint8_t v_done_1229_; 
v_done_1229_ = lean_ctor_get_uint8(v_a_1228_, 0);
if (v_done_1229_ == 0)
{
uint8_t v_contextDependent_1230_; lean_object* v___x_1231_; 
lean_dec_ref_known(v___x_1227_, 1);
v_contextDependent_1230_ = lean_ctor_get_uint8(v_a_1228_, 1);
lean_dec_ref_known(v_a_1228_, 0);
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
lean_inc(v___y_1216_);
v___x_1231_ = lean_apply_12(v___f_1213_, v___x_1226_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, lean_box(0));
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; uint8_t v___y_1234_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
if (v_contextDependent_1230_ == 0)
{
lean_dec(v_a_1232_);
return v___x_1231_;
}
else
{
if (lean_obj_tag(v_a_1232_) == 0)
{
uint8_t v_contextDependent_1244_; 
v_contextDependent_1244_ = lean_ctor_get_uint8(v_a_1232_, 1);
v___y_1234_ = v_contextDependent_1244_;
goto v___jp_1233_;
}
else
{
uint8_t v_contextDependent_1245_; 
v_contextDependent_1245_ = lean_ctor_get_uint8(v_a_1232_, sizeof(void*)*2 + 1);
v___y_1234_ = v_contextDependent_1245_;
goto v___jp_1233_;
}
}
v___jp_1233_:
{
if (v___y_1234_ == 0)
{
lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1242_; 
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1231_, 0);
lean_dec(v_unused_1243_);
v___x_1236_ = v___x_1231_;
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
else
{
lean_dec(v___x_1231_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1232_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1238_);
v___x_1240_ = v___x_1236_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
else
{
lean_dec(v_a_1232_);
return v___x_1231_;
}
}
}
else
{
return v___x_1231_;
}
}
else
{
lean_dec_ref_known(v_a_1228_, 0);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___f_1213_);
return v___x_1227_;
}
}
else
{
uint8_t v_done_1246_; 
v_done_1246_ = lean_ctor_get_uint8(v_a_1228_, sizeof(void*)*2);
if (v_done_1246_ == 0)
{
lean_object* v_e_x27_1247_; lean_object* v_proof_1248_; uint8_t v_contextDependent_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref_known(v___x_1227_, 1);
v_e_x27_1247_ = lean_ctor_get(v_a_1228_, 0);
v_proof_1248_ = lean_ctor_get(v_a_1228_, 1);
v_contextDependent_1249_ = lean_ctor_get_uint8(v_a_1228_, sizeof(void*)*2 + 1);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_a_1228_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1251_ = v_a_1228_;
v_isShared_1252_ = v_isSharedCheck_1299_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_proof_1248_);
lean_inc(v_e_x27_1247_);
lean_dec(v_a_1228_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1299_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; 
lean_inc(v___y_1224_);
lean_inc_ref(v___y_1223_);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc_ref(v_e_x27_1247_);
v___x_1253_ = lean_apply_12(v___f_1213_, v___x_1226_, v_e_x27_1247_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, lean_box(0));
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1298_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1298_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1298_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
if (lean_obj_tag(v_a_1254_) == 0)
{
uint8_t v_done_1258_; uint8_t v_contextDependent_1259_; uint8_t v___y_1261_; 
lean_dec_ref(v___y_1215_);
v_done_1258_ = lean_ctor_get_uint8(v_a_1254_, 0);
v_contextDependent_1259_ = lean_ctor_get_uint8(v_a_1254_, 1);
lean_dec_ref_known(v_a_1254_, 0);
if (v_contextDependent_1249_ == 0)
{
v___y_1261_ = v_contextDependent_1259_;
goto v___jp_1260_;
}
else
{
v___y_1261_ = v_contextDependent_1249_;
goto v___jp_1260_;
}
v___jp_1260_:
{
lean_object* v___x_1263_; 
if (v_isShared_1252_ == 0)
{
v___x_1263_ = v___x_1251_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_e_x27_1247_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_proof_1248_);
v___x_1263_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1265_; 
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*2, v_done_1258_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*2 + 1, v___y_1261_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1263_);
v___x_1265_ = v___x_1256_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v_e_x27_1268_; lean_object* v_proof_1269_; uint8_t v_done_1270_; uint8_t v_contextDependent_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1297_; 
lean_del_object(v___x_1256_);
lean_del_object(v___x_1251_);
v_e_x27_1268_ = lean_ctor_get(v_a_1254_, 0);
v_proof_1269_ = lean_ctor_get(v_a_1254_, 1);
v_done_1270_ = lean_ctor_get_uint8(v_a_1254_, sizeof(void*)*2);
v_contextDependent_1271_ = lean_ctor_get_uint8(v_a_1254_, sizeof(void*)*2 + 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_a_1254_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1273_ = v_a_1254_;
v_isShared_1274_ = v_isSharedCheck_1297_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_proof_1269_);
lean_inc(v_e_x27_1268_);
lean_dec(v_a_1254_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1297_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; 
lean_inc_ref(v_e_x27_1268_);
v___x_1275_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1215_, v_e_x27_1247_, v_proof_1248_, v_e_x27_1268_, v_proof_1269_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1288_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1288_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1288_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
uint8_t v___y_1281_; 
if (v_contextDependent_1249_ == 0)
{
v___y_1281_ = v_contextDependent_1271_;
goto v___jp_1280_;
}
else
{
v___y_1281_ = v_contextDependent_1249_;
goto v___jp_1280_;
}
v___jp_1280_:
{
lean_object* v___x_1283_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v_a_1276_);
v___x_1283_ = v___x_1273_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_e_x27_1268_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_a_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1287_, sizeof(void*)*2, v_done_1270_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1285_; 
lean_ctor_set_uint8(v___x_1283_, sizeof(void*)*2 + 1, v___y_1281_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1283_);
v___x_1285_ = v___x_1278_;
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
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_del_object(v___x_1273_);
lean_dec_ref(v_e_x27_1268_);
v_a_1289_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1275_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1275_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1251_);
lean_dec_ref(v_proof_1248_);
lean_dec_ref(v_e_x27_1247_);
lean_dec_ref(v___y_1215_);
return v___x_1253_;
}
}
}
else
{
lean_dec_ref_known(v_a_1228_, 2);
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___f_1213_);
return v___x_1227_;
}
}
}
else
{
lean_dec_ref(v___y_1215_);
lean_dec_ref(v___f_1213_);
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__12___boxed(lean_object* v___f_1300_, lean_object* v_x_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__12(v___f_1300_, v_x_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__13(lean_object* v___f_1314_, lean_object* v_x_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_box(0);
v___x_1328_ = l_Lean_Meta_Grind_NormSym_simpEq(v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
if (lean_obj_tag(v_a_1329_) == 0)
{
uint8_t v_done_1330_; 
v_done_1330_ = lean_ctor_get_uint8(v_a_1329_, 0);
if (v_done_1330_ == 0)
{
uint8_t v_contextDependent_1331_; lean_object* v___x_1332_; 
lean_dec_ref_known(v___x_1328_, 1);
v_contextDependent_1331_ = lean_ctor_get_uint8(v_a_1329_, 1);
lean_dec_ref_known(v_a_1329_, 0);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc(v___y_1319_);
lean_inc_ref(v___y_1318_);
lean_inc(v___y_1317_);
v___x_1332_ = lean_apply_12(v___f_1314_, v___x_1327_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, lean_box(0));
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; uint8_t v___y_1335_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
if (v_contextDependent_1331_ == 0)
{
lean_dec(v_a_1333_);
return v___x_1332_;
}
else
{
if (lean_obj_tag(v_a_1333_) == 0)
{
uint8_t v_contextDependent_1345_; 
v_contextDependent_1345_ = lean_ctor_get_uint8(v_a_1333_, 1);
v___y_1335_ = v_contextDependent_1345_;
goto v___jp_1334_;
}
else
{
uint8_t v_contextDependent_1346_; 
v_contextDependent_1346_ = lean_ctor_get_uint8(v_a_1333_, sizeof(void*)*2 + 1);
v___y_1335_ = v_contextDependent_1346_;
goto v___jp_1334_;
}
}
v___jp_1334_:
{
if (v___y_1335_ == 0)
{
lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v___x_1332_, 0);
lean_dec(v_unused_1344_);
v___x_1337_ = v___x_1332_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_dec(v___x_1332_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1333_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
lean_dec(v_a_1333_);
return v___x_1332_;
}
}
}
else
{
return v___x_1332_;
}
}
else
{
lean_dec_ref_known(v_a_1329_, 0);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___f_1314_);
return v___x_1328_;
}
}
else
{
uint8_t v_done_1347_; 
v_done_1347_ = lean_ctor_get_uint8(v_a_1329_, sizeof(void*)*2);
if (v_done_1347_ == 0)
{
lean_object* v_e_x27_1348_; lean_object* v_proof_1349_; uint8_t v_contextDependent_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref_known(v___x_1328_, 1);
v_e_x27_1348_ = lean_ctor_get(v_a_1329_, 0);
v_proof_1349_ = lean_ctor_get(v_a_1329_, 1);
v_contextDependent_1350_ = lean_ctor_get_uint8(v_a_1329_, sizeof(void*)*2 + 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_a_1329_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1352_ = v_a_1329_;
v_isShared_1353_ = v_isSharedCheck_1400_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_proof_1349_);
lean_inc(v_e_x27_1348_);
lean_dec(v_a_1329_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1400_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; 
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc(v___y_1319_);
lean_inc_ref(v___y_1318_);
lean_inc(v___y_1317_);
lean_inc_ref(v_e_x27_1348_);
v___x_1354_ = lean_apply_12(v___f_1314_, v___x_1327_, v_e_x27_1348_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, lean_box(0));
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1399_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1399_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1399_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
if (lean_obj_tag(v_a_1355_) == 0)
{
uint8_t v_done_1359_; uint8_t v_contextDependent_1360_; uint8_t v___y_1362_; 
lean_dec_ref(v___y_1316_);
v_done_1359_ = lean_ctor_get_uint8(v_a_1355_, 0);
v_contextDependent_1360_ = lean_ctor_get_uint8(v_a_1355_, 1);
lean_dec_ref_known(v_a_1355_, 0);
if (v_contextDependent_1350_ == 0)
{
v___y_1362_ = v_contextDependent_1360_;
goto v___jp_1361_;
}
else
{
v___y_1362_ = v_contextDependent_1350_;
goto v___jp_1361_;
}
v___jp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1353_ == 0)
{
v___x_1364_ = v___x_1352_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_e_x27_1348_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_proof_1349_);
v___x_1364_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1366_; 
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*2, v_done_1359_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*2 + 1, v___y_1362_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1364_);
v___x_1366_ = v___x_1357_;
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
}
else
{
lean_object* v_e_x27_1369_; lean_object* v_proof_1370_; uint8_t v_done_1371_; uint8_t v_contextDependent_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1398_; 
lean_del_object(v___x_1357_);
lean_del_object(v___x_1352_);
v_e_x27_1369_ = lean_ctor_get(v_a_1355_, 0);
v_proof_1370_ = lean_ctor_get(v_a_1355_, 1);
v_done_1371_ = lean_ctor_get_uint8(v_a_1355_, sizeof(void*)*2);
v_contextDependent_1372_ = lean_ctor_get_uint8(v_a_1355_, sizeof(void*)*2 + 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_a_1355_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1374_ = v_a_1355_;
v_isShared_1375_ = v_isSharedCheck_1398_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_proof_1370_);
lean_inc(v_e_x27_1369_);
lean_dec(v_a_1355_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1398_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; 
lean_inc_ref(v_e_x27_1369_);
v___x_1376_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1316_, v_e_x27_1348_, v_proof_1349_, v_e_x27_1369_, v_proof_1370_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1389_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1389_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1389_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
uint8_t v___y_1382_; 
if (v_contextDependent_1350_ == 0)
{
v___y_1382_ = v_contextDependent_1372_;
goto v___jp_1381_;
}
else
{
v___y_1382_ = v_contextDependent_1350_;
goto v___jp_1381_;
}
v___jp_1381_:
{
lean_object* v___x_1384_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v_a_1377_);
v___x_1384_ = v___x_1374_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_e_x27_1369_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_a_1377_);
lean_ctor_set_uint8(v_reuseFailAlloc_1388_, sizeof(void*)*2, v_done_1371_);
v___x_1384_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1386_; 
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*2 + 1, v___y_1382_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1384_);
v___x_1386_ = v___x_1379_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_del_object(v___x_1374_);
lean_dec_ref(v_e_x27_1369_);
v_a_1390_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1376_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1376_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1352_);
lean_dec_ref(v_proof_1349_);
lean_dec_ref(v_e_x27_1348_);
lean_dec_ref(v___y_1316_);
return v___x_1354_;
}
}
}
else
{
lean_dec_ref_known(v_a_1329_, 2);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___f_1314_);
return v___x_1328_;
}
}
}
else
{
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___f_1314_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__13___boxed(lean_object* v___f_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__13(v___f_1401_, v_x_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__14(lean_object* v_post_1415_, lean_object* v___f_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_box(0);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
lean_inc(v___y_1420_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
v___x_1429_ = lean_apply_11(v_post_1415_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, lean_box(0));
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
if (lean_obj_tag(v_a_1430_) == 0)
{
uint8_t v_done_1431_; 
v_done_1431_ = lean_ctor_get_uint8(v_a_1430_, 0);
if (v_done_1431_ == 0)
{
uint8_t v_contextDependent_1432_; lean_object* v___x_1433_; 
lean_dec_ref_known(v___x_1429_, 1);
v_contextDependent_1432_ = lean_ctor_get_uint8(v_a_1430_, 1);
lean_dec_ref_known(v_a_1430_, 0);
v___x_1433_ = lean_apply_12(v___f_1416_, v___x_1428_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, lean_box(0));
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; uint8_t v___y_1436_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
if (v_contextDependent_1432_ == 0)
{
lean_dec(v_a_1434_);
return v___x_1433_;
}
else
{
if (lean_obj_tag(v_a_1434_) == 0)
{
uint8_t v_contextDependent_1446_; 
v_contextDependent_1446_ = lean_ctor_get_uint8(v_a_1434_, 1);
v___y_1436_ = v_contextDependent_1446_;
goto v___jp_1435_;
}
else
{
uint8_t v_contextDependent_1447_; 
v_contextDependent_1447_ = lean_ctor_get_uint8(v_a_1434_, sizeof(void*)*2 + 1);
v___y_1436_ = v_contextDependent_1447_;
goto v___jp_1435_;
}
}
v___jp_1435_:
{
if (v___y_1436_ == 0)
{
lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1444_; 
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v___x_1433_, 0);
lean_dec(v_unused_1445_);
v___x_1438_ = v___x_1433_;
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
else
{
lean_dec(v___x_1433_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1434_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1440_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
else
{
lean_dec(v_a_1434_);
return v___x_1433_;
}
}
}
else
{
return v___x_1433_;
}
}
else
{
lean_dec_ref_known(v_a_1430_, 0);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec_ref(v___f_1416_);
return v___x_1429_;
}
}
else
{
uint8_t v_done_1448_; 
v_done_1448_ = lean_ctor_get_uint8(v_a_1430_, sizeof(void*)*2);
if (v_done_1448_ == 0)
{
lean_object* v_e_x27_1449_; lean_object* v_proof_1450_; uint8_t v_contextDependent_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref_known(v___x_1429_, 1);
v_e_x27_1449_ = lean_ctor_get(v_a_1430_, 0);
v_proof_1450_ = lean_ctor_get(v_a_1430_, 1);
v_contextDependent_1451_ = lean_ctor_get_uint8(v_a_1430_, sizeof(void*)*2 + 1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_a_1430_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1453_ = v_a_1430_;
v_isShared_1454_ = v_isSharedCheck_1501_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_proof_1450_);
lean_inc(v_e_x27_1449_);
lean_dec(v_a_1430_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1501_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; 
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
lean_inc_ref(v_e_x27_1449_);
v___x_1455_ = lean_apply_12(v___f_1416_, v___x_1428_, v_e_x27_1449_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, lean_box(0));
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1500_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1500_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1500_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
if (lean_obj_tag(v_a_1456_) == 0)
{
uint8_t v_done_1460_; uint8_t v_contextDependent_1461_; uint8_t v___y_1463_; 
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec_ref(v___y_1417_);
v_done_1460_ = lean_ctor_get_uint8(v_a_1456_, 0);
v_contextDependent_1461_ = lean_ctor_get_uint8(v_a_1456_, 1);
lean_dec_ref_known(v_a_1456_, 0);
if (v_contextDependent_1451_ == 0)
{
v___y_1463_ = v_contextDependent_1461_;
goto v___jp_1462_;
}
else
{
v___y_1463_ = v_contextDependent_1451_;
goto v___jp_1462_;
}
v___jp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1454_ == 0)
{
v___x_1465_ = v___x_1453_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_e_x27_1449_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_proof_1450_);
v___x_1465_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1467_; 
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*2, v_done_1460_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*2 + 1, v___y_1463_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1465_);
v___x_1467_ = v___x_1458_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v_e_x27_1470_; lean_object* v_proof_1471_; uint8_t v_done_1472_; uint8_t v_contextDependent_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1499_; 
lean_del_object(v___x_1458_);
lean_del_object(v___x_1453_);
v_e_x27_1470_ = lean_ctor_get(v_a_1456_, 0);
v_proof_1471_ = lean_ctor_get(v_a_1456_, 1);
v_done_1472_ = lean_ctor_get_uint8(v_a_1456_, sizeof(void*)*2);
v_contextDependent_1473_ = lean_ctor_get_uint8(v_a_1456_, sizeof(void*)*2 + 1);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_a_1456_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1475_ = v_a_1456_;
v_isShared_1476_ = v_isSharedCheck_1499_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_proof_1471_);
lean_inc(v_e_x27_1470_);
lean_dec(v_a_1456_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1499_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; 
lean_inc_ref(v_e_x27_1470_);
v___x_1477_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1417_, v_e_x27_1449_, v_proof_1450_, v_e_x27_1470_, v_proof_1471_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1490_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1490_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1490_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
uint8_t v___y_1483_; 
if (v_contextDependent_1451_ == 0)
{
v___y_1483_ = v_contextDependent_1473_;
goto v___jp_1482_;
}
else
{
v___y_1483_ = v_contextDependent_1451_;
goto v___jp_1482_;
}
v___jp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v_a_1478_);
v___x_1485_ = v___x_1475_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_e_x27_1470_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_a_1478_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, sizeof(void*)*2, v_done_1472_);
v___x_1485_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1487_; 
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*2 + 1, v___y_1483_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1485_);
v___x_1487_ = v___x_1480_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_del_object(v___x_1475_);
lean_dec_ref(v_e_x27_1470_);
v_a_1491_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1477_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1477_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1453_);
lean_dec_ref(v_proof_1450_);
lean_dec_ref(v_e_x27_1449_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec_ref(v___y_1417_);
return v___x_1455_;
}
}
}
else
{
lean_dec_ref_known(v_a_1430_, 2);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec_ref(v___f_1416_);
return v___x_1429_;
}
}
}
else
{
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec_ref(v___f_1416_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__14___boxed(lean_object* v_post_1502_, lean_object* v___f_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__14(v_post_1502_, v___f_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__15(lean_object* v_x_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__15___closed__0));
v___x_1533_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_1521_, v___x_1532_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
if (lean_obj_tag(v_a_1534_) == 0)
{
uint8_t v_done_1535_; 
v_done_1535_ = lean_ctor_get_uint8(v_a_1534_, 0);
if (v_done_1535_ == 0)
{
uint8_t v_contextDependent_1536_; lean_object* v___x_1537_; 
lean_dec_ref_known(v___x_1533_, 1);
v_contextDependent_1536_ = lean_ctor_get_uint8(v_a_1534_, 1);
lean_dec_ref_known(v_a_1534_, 0);
v___x_1537_ = l_Lean_Meta_Sym_Simp_simpNatRel___redArg(v___y_1521_, v___y_1525_, v___y_1528_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; uint8_t v___y_1540_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
if (v_contextDependent_1536_ == 0)
{
return v___x_1537_;
}
else
{
if (lean_obj_tag(v_a_1538_) == 0)
{
uint8_t v_contextDependent_1550_; 
v_contextDependent_1550_ = lean_ctor_get_uint8(v_a_1538_, 1);
v___y_1540_ = v_contextDependent_1550_;
goto v___jp_1539_;
}
else
{
uint8_t v_contextDependent_1551_; 
v_contextDependent_1551_ = lean_ctor_get_uint8(v_a_1538_, sizeof(void*)*2 + 1);
v___y_1540_ = v_contextDependent_1551_;
goto v___jp_1539_;
}
}
v___jp_1539_:
{
if (v___y_1540_ == 0)
{
lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1548_; 
lean_inc(v_a_1538_);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v___x_1537_, 0);
lean_dec(v_unused_1549_);
v___x_1542_ = v___x_1537_;
v_isShared_1543_ = v_isSharedCheck_1548_;
goto v_resetjp_1541_;
}
else
{
lean_dec(v___x_1537_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1548_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1544_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1538_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1544_);
v___x_1546_ = v___x_1542_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
else
{
return v___x_1537_;
}
}
}
else
{
return v___x_1537_;
}
}
else
{
lean_dec_ref_known(v_a_1534_, 0);
lean_dec_ref(v___y_1521_);
return v___x_1533_;
}
}
else
{
uint8_t v_done_1552_; 
v_done_1552_ = lean_ctor_get_uint8(v_a_1534_, sizeof(void*)*2);
if (v_done_1552_ == 0)
{
lean_object* v_e_x27_1553_; lean_object* v_proof_1554_; uint8_t v_contextDependent_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1605_; 
lean_dec_ref_known(v___x_1533_, 1);
v_e_x27_1553_ = lean_ctor_get(v_a_1534_, 0);
v_proof_1554_ = lean_ctor_get(v_a_1534_, 1);
v_contextDependent_1555_ = lean_ctor_get_uint8(v_a_1534_, sizeof(void*)*2 + 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_a_1534_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1557_ = v_a_1534_;
v_isShared_1558_ = v_isSharedCheck_1605_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_proof_1554_);
lean_inc(v_e_x27_1553_);
lean_dec(v_a_1534_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1605_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; 
lean_inc_ref(v_e_x27_1553_);
v___x_1559_ = l_Lean_Meta_Sym_Simp_simpNatRel___redArg(v_e_x27_1553_, v___y_1525_, v___y_1528_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1604_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1604_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1604_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
if (lean_obj_tag(v_a_1560_) == 0)
{
uint8_t v_done_1564_; uint8_t v_contextDependent_1565_; uint8_t v___y_1567_; 
lean_dec_ref(v___y_1521_);
v_done_1564_ = lean_ctor_get_uint8(v_a_1560_, 0);
v_contextDependent_1565_ = lean_ctor_get_uint8(v_a_1560_, 1);
lean_dec_ref_known(v_a_1560_, 0);
if (v_contextDependent_1555_ == 0)
{
v___y_1567_ = v_contextDependent_1565_;
goto v___jp_1566_;
}
else
{
v___y_1567_ = v_contextDependent_1555_;
goto v___jp_1566_;
}
v___jp_1566_:
{
lean_object* v___x_1569_; 
if (v_isShared_1558_ == 0)
{
v___x_1569_ = v___x_1557_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_e_x27_1553_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_proof_1554_);
v___x_1569_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1571_; 
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*2, v_done_1564_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*2 + 1, v___y_1567_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1569_);
v___x_1571_ = v___x_1562_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
else
{
lean_object* v_e_x27_1574_; lean_object* v_proof_1575_; uint8_t v_done_1576_; uint8_t v_contextDependent_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1603_; 
lean_del_object(v___x_1562_);
lean_del_object(v___x_1557_);
v_e_x27_1574_ = lean_ctor_get(v_a_1560_, 0);
v_proof_1575_ = lean_ctor_get(v_a_1560_, 1);
v_done_1576_ = lean_ctor_get_uint8(v_a_1560_, sizeof(void*)*2);
v_contextDependent_1577_ = lean_ctor_get_uint8(v_a_1560_, sizeof(void*)*2 + 1);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_a_1560_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1579_ = v_a_1560_;
v_isShared_1580_ = v_isSharedCheck_1603_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_proof_1575_);
lean_inc(v_e_x27_1574_);
lean_dec(v_a_1560_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1603_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; 
lean_inc_ref(v_e_x27_1574_);
v___x_1581_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1521_, v_e_x27_1553_, v_proof_1554_, v_e_x27_1574_, v_proof_1575_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1594_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1594_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1594_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
uint8_t v___y_1587_; 
if (v_contextDependent_1555_ == 0)
{
v___y_1587_ = v_contextDependent_1577_;
goto v___jp_1586_;
}
else
{
v___y_1587_ = v_contextDependent_1555_;
goto v___jp_1586_;
}
v___jp_1586_:
{
lean_object* v___x_1589_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v_a_1582_);
v___x_1589_ = v___x_1579_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_e_x27_1574_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1582_);
lean_ctor_set_uint8(v_reuseFailAlloc_1593_, sizeof(void*)*2, v_done_1576_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; 
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*2 + 1, v___y_1587_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1589_);
v___x_1591_ = v___x_1584_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_del_object(v___x_1579_);
lean_dec_ref(v_e_x27_1574_);
v_a_1595_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1581_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1581_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1557_);
lean_dec_ref(v_proof_1554_);
lean_dec_ref(v_e_x27_1553_);
lean_dec_ref(v___y_1521_);
return v___x_1559_;
}
}
}
else
{
lean_dec_ref_known(v_a_1534_, 2);
lean_dec_ref(v___y_1521_);
return v___x_1533_;
}
}
}
else
{
lean_dec_ref(v___y_1521_);
return v___x_1533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__15___boxed(lean_object* v_x_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__15(v_x_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__16(lean_object* v_thms_1619_, lean_object* v___x_1620_, lean_object* v_x_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_pre_1633_; lean_object* v___x_1634_; 
v_pre_1633_ = lean_ctor_get(v_thms_1619_, 0);
v___x_1634_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_pre_1633_, v___x_1620_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__16___boxed(lean_object* v_thms_1635_, lean_object* v___x_1636_, lean_object* v_x_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__16(v_thms_1635_, v___x_1636_, v_x_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v_thms_1635_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__17(lean_object* v_pre_1650_, lean_object* v___f_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = lean_box(0);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1654_);
lean_inc(v___y_1653_);
lean_inc_ref(v___y_1652_);
v___x_1664_ = lean_apply_11(v_pre_1650_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, lean_box(0));
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
if (lean_obj_tag(v_a_1665_) == 0)
{
uint8_t v_done_1666_; 
v_done_1666_ = lean_ctor_get_uint8(v_a_1665_, 0);
if (v_done_1666_ == 0)
{
uint8_t v_contextDependent_1667_; lean_object* v___x_1668_; 
lean_dec_ref_known(v___x_1664_, 1);
v_contextDependent_1667_ = lean_ctor_get_uint8(v_a_1665_, 1);
lean_dec_ref_known(v_a_1665_, 0);
v___x_1668_ = lean_apply_12(v___f_1651_, v___x_1663_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, lean_box(0));
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; uint8_t v___y_1671_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
if (v_contextDependent_1667_ == 0)
{
lean_dec(v_a_1669_);
return v___x_1668_;
}
else
{
if (lean_obj_tag(v_a_1669_) == 0)
{
uint8_t v_contextDependent_1681_; 
v_contextDependent_1681_ = lean_ctor_get_uint8(v_a_1669_, 1);
v___y_1671_ = v_contextDependent_1681_;
goto v___jp_1670_;
}
else
{
uint8_t v_contextDependent_1682_; 
v_contextDependent_1682_ = lean_ctor_get_uint8(v_a_1669_, sizeof(void*)*2 + 1);
v___y_1671_ = v_contextDependent_1682_;
goto v___jp_1670_;
}
}
v___jp_1670_:
{
if (v___y_1671_ == 0)
{
lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1679_; 
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1679_ == 0)
{
lean_object* v_unused_1680_; 
v_unused_1680_ = lean_ctor_get(v___x_1668_, 0);
lean_dec(v_unused_1680_);
v___x_1673_ = v___x_1668_;
v_isShared_1674_ = v_isSharedCheck_1679_;
goto v_resetjp_1672_;
}
else
{
lean_dec(v___x_1668_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1679_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1675_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1669_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1675_);
v___x_1677_ = v___x_1673_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_dec(v_a_1669_);
return v___x_1668_;
}
}
}
else
{
return v___x_1668_;
}
}
else
{
lean_dec_ref_known(v_a_1665_, 0);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v___f_1651_);
return v___x_1664_;
}
}
else
{
uint8_t v_done_1683_; 
v_done_1683_ = lean_ctor_get_uint8(v_a_1665_, sizeof(void*)*2);
if (v_done_1683_ == 0)
{
lean_object* v_e_x27_1684_; lean_object* v_proof_1685_; uint8_t v_contextDependent_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref_known(v___x_1664_, 1);
v_e_x27_1684_ = lean_ctor_get(v_a_1665_, 0);
v_proof_1685_ = lean_ctor_get(v_a_1665_, 1);
v_contextDependent_1686_ = lean_ctor_get_uint8(v_a_1665_, sizeof(void*)*2 + 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_a_1665_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1688_ = v_a_1665_;
v_isShared_1689_ = v_isSharedCheck_1736_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_proof_1685_);
lean_inc(v_e_x27_1684_);
lean_dec(v_a_1665_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1736_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; 
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
lean_inc_ref(v_e_x27_1684_);
v___x_1690_ = lean_apply_12(v___f_1651_, v___x_1663_, v_e_x27_1684_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, lean_box(0));
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1735_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1735_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1735_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
if (lean_obj_tag(v_a_1691_) == 0)
{
uint8_t v_done_1695_; uint8_t v_contextDependent_1696_; uint8_t v___y_1698_; 
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec_ref(v___y_1652_);
v_done_1695_ = lean_ctor_get_uint8(v_a_1691_, 0);
v_contextDependent_1696_ = lean_ctor_get_uint8(v_a_1691_, 1);
lean_dec_ref_known(v_a_1691_, 0);
if (v_contextDependent_1686_ == 0)
{
v___y_1698_ = v_contextDependent_1696_;
goto v___jp_1697_;
}
else
{
v___y_1698_ = v_contextDependent_1686_;
goto v___jp_1697_;
}
v___jp_1697_:
{
lean_object* v___x_1700_; 
if (v_isShared_1689_ == 0)
{
v___x_1700_ = v___x_1688_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_e_x27_1684_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_proof_1685_);
v___x_1700_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1702_; 
lean_ctor_set_uint8(v___x_1700_, sizeof(void*)*2, v_done_1695_);
lean_ctor_set_uint8(v___x_1700_, sizeof(void*)*2 + 1, v___y_1698_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1700_);
v___x_1702_ = v___x_1693_;
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
}
else
{
lean_object* v_e_x27_1705_; lean_object* v_proof_1706_; uint8_t v_done_1707_; uint8_t v_contextDependent_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1734_; 
lean_del_object(v___x_1693_);
lean_del_object(v___x_1688_);
v_e_x27_1705_ = lean_ctor_get(v_a_1691_, 0);
v_proof_1706_ = lean_ctor_get(v_a_1691_, 1);
v_done_1707_ = lean_ctor_get_uint8(v_a_1691_, sizeof(void*)*2);
v_contextDependent_1708_ = lean_ctor_get_uint8(v_a_1691_, sizeof(void*)*2 + 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_a_1691_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1710_ = v_a_1691_;
v_isShared_1711_ = v_isSharedCheck_1734_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_proof_1706_);
lean_inc(v_e_x27_1705_);
lean_dec(v_a_1691_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1734_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; 
lean_inc_ref(v_e_x27_1705_);
v___x_1712_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1652_, v_e_x27_1684_, v_proof_1685_, v_e_x27_1705_, v_proof_1706_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1725_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1725_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1725_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
uint8_t v___y_1718_; 
if (v_contextDependent_1686_ == 0)
{
v___y_1718_ = v_contextDependent_1708_;
goto v___jp_1717_;
}
else
{
v___y_1718_ = v_contextDependent_1686_;
goto v___jp_1717_;
}
v___jp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 1, v_a_1713_);
v___x_1720_ = v___x_1710_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_e_x27_1705_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_a_1713_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*2, v_done_1707_);
v___x_1720_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1722_; 
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*2 + 1, v___y_1718_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1720_);
v___x_1722_ = v___x_1715_;
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
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_del_object(v___x_1710_);
lean_dec_ref(v_e_x27_1705_);
v_a_1726_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1712_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1712_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1688_);
lean_dec_ref(v_proof_1685_);
lean_dec_ref(v_e_x27_1684_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec_ref(v___y_1652_);
return v___x_1690_;
}
}
}
else
{
lean_dec_ref_known(v_a_1665_, 2);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v___f_1651_);
return v___x_1664_;
}
}
}
else
{
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v___f_1651_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__17___boxed(lean_object* v_pre_1737_, lean_object* v___f_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__17(v_pre_1737_, v___f_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__18(lean_object* v_post_1751_, lean_object* v___x_1752_, lean_object* v___f_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_box(0);
lean_inc_ref(v___y_1754_);
v___x_1766_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_post_1751_, v___x_1752_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
if (lean_obj_tag(v_a_1767_) == 0)
{
uint8_t v_done_1768_; 
v_done_1768_ = lean_ctor_get_uint8(v_a_1767_, 0);
if (v_done_1768_ == 0)
{
uint8_t v_contextDependent_1769_; lean_object* v___x_1770_; 
lean_dec_ref_known(v___x_1766_, 1);
v_contextDependent_1769_ = lean_ctor_get_uint8(v_a_1767_, 1);
lean_dec_ref_known(v_a_1767_, 0);
v___x_1770_ = lean_apply_12(v___f_1753_, v___x_1765_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, lean_box(0));
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; uint8_t v___y_1773_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
if (v_contextDependent_1769_ == 0)
{
lean_dec(v_a_1771_);
return v___x_1770_;
}
else
{
if (lean_obj_tag(v_a_1771_) == 0)
{
uint8_t v_contextDependent_1783_; 
v_contextDependent_1783_ = lean_ctor_get_uint8(v_a_1771_, 1);
v___y_1773_ = v_contextDependent_1783_;
goto v___jp_1772_;
}
else
{
uint8_t v_contextDependent_1784_; 
v_contextDependent_1784_ = lean_ctor_get_uint8(v_a_1771_, sizeof(void*)*2 + 1);
v___y_1773_ = v_contextDependent_1784_;
goto v___jp_1772_;
}
}
v___jp_1772_:
{
if (v___y_1773_ == 0)
{
lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1781_; 
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v___x_1770_, 0);
lean_dec(v_unused_1782_);
v___x_1775_ = v___x_1770_;
v_isShared_1776_ = v_isSharedCheck_1781_;
goto v_resetjp_1774_;
}
else
{
lean_dec(v___x_1770_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1781_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1777_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1771_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1777_);
v___x_1779_ = v___x_1775_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
else
{
lean_dec(v_a_1771_);
return v___x_1770_;
}
}
}
else
{
return v___x_1770_;
}
}
else
{
lean_dec_ref_known(v_a_1767_, 0);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec_ref(v___f_1753_);
return v___x_1766_;
}
}
else
{
uint8_t v_done_1785_; 
v_done_1785_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*2);
if (v_done_1785_ == 0)
{
lean_object* v_e_x27_1786_; lean_object* v_proof_1787_; uint8_t v_contextDependent_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref_known(v___x_1766_, 1);
v_e_x27_1786_ = lean_ctor_get(v_a_1767_, 0);
v_proof_1787_ = lean_ctor_get(v_a_1767_, 1);
v_contextDependent_1788_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*2 + 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1790_ = v_a_1767_;
v_isShared_1791_ = v_isSharedCheck_1838_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_proof_1787_);
lean_inc(v_e_x27_1786_);
lean_dec(v_a_1767_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1838_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; 
lean_inc(v___y_1763_);
lean_inc_ref(v___y_1762_);
lean_inc(v___y_1761_);
lean_inc_ref(v___y_1760_);
lean_inc(v___y_1759_);
lean_inc_ref(v___y_1758_);
lean_inc_ref(v_e_x27_1786_);
v___x_1792_ = lean_apply_12(v___f_1753_, v___x_1765_, v_e_x27_1786_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, lean_box(0));
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1837_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1795_ = v___x_1792_;
v_isShared_1796_ = v_isSharedCheck_1837_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1792_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1837_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
if (lean_obj_tag(v_a_1793_) == 0)
{
uint8_t v_done_1797_; uint8_t v_contextDependent_1798_; uint8_t v___y_1800_; 
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v___y_1754_);
v_done_1797_ = lean_ctor_get_uint8(v_a_1793_, 0);
v_contextDependent_1798_ = lean_ctor_get_uint8(v_a_1793_, 1);
lean_dec_ref_known(v_a_1793_, 0);
if (v_contextDependent_1788_ == 0)
{
v___y_1800_ = v_contextDependent_1798_;
goto v___jp_1799_;
}
else
{
v___y_1800_ = v_contextDependent_1788_;
goto v___jp_1799_;
}
v___jp_1799_:
{
lean_object* v___x_1802_; 
if (v_isShared_1791_ == 0)
{
v___x_1802_ = v___x_1790_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_e_x27_1786_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_proof_1787_);
v___x_1802_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1804_; 
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*2, v_done_1797_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*2 + 1, v___y_1800_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1802_);
v___x_1804_ = v___x_1795_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
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
else
{
lean_object* v_e_x27_1807_; lean_object* v_proof_1808_; uint8_t v_done_1809_; uint8_t v_contextDependent_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1836_; 
lean_del_object(v___x_1795_);
lean_del_object(v___x_1790_);
v_e_x27_1807_ = lean_ctor_get(v_a_1793_, 0);
v_proof_1808_ = lean_ctor_get(v_a_1793_, 1);
v_done_1809_ = lean_ctor_get_uint8(v_a_1793_, sizeof(void*)*2);
v_contextDependent_1810_ = lean_ctor_get_uint8(v_a_1793_, sizeof(void*)*2 + 1);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_a_1793_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1812_ = v_a_1793_;
v_isShared_1813_ = v_isSharedCheck_1836_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_proof_1808_);
lean_inc(v_e_x27_1807_);
lean_dec(v_a_1793_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1836_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; 
lean_inc_ref(v_e_x27_1807_);
v___x_1814_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1754_, v_e_x27_1786_, v_proof_1787_, v_e_x27_1807_, v_proof_1808_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1827_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1827_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1827_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
uint8_t v___y_1820_; 
if (v_contextDependent_1788_ == 0)
{
v___y_1820_ = v_contextDependent_1810_;
goto v___jp_1819_;
}
else
{
v___y_1820_ = v_contextDependent_1788_;
goto v___jp_1819_;
}
v___jp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 1, v_a_1815_);
v___x_1822_ = v___x_1812_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_e_x27_1807_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_a_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*2, v_done_1809_);
v___x_1822_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
lean_ctor_set_uint8(v___x_1822_, sizeof(void*)*2 + 1, v___y_1820_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1822_);
v___x_1824_ = v___x_1817_;
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
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_del_object(v___x_1812_);
lean_dec_ref(v_e_x27_1807_);
v_a_1828_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1814_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1814_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1790_);
lean_dec_ref(v_proof_1787_);
lean_dec_ref(v_e_x27_1786_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v___y_1754_);
return v___x_1792_;
}
}
}
else
{
lean_dec_ref_known(v_a_1767_, 2);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec_ref(v___f_1753_);
return v___x_1766_;
}
}
}
else
{
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec_ref(v___f_1753_);
return v___x_1766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__18___boxed(lean_object* v_post_1839_, lean_object* v___x_1840_, lean_object* v___f_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__18(v_post_1839_, v___x_1840_, v___f_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec_ref(v_post_1839_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__19(lean_object* v___f_1854_, lean_object* v_post_1855_, lean_object* v___x_1856_, lean_object* v___f_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___y_1870_; uint8_t v___y_1871_; lean_object* v___y_1872_; uint8_t v___y_1873_; lean_object* v___y_1877_; uint8_t v___y_1878_; lean_object* v___y_1879_; uint8_t v___y_1880_; lean_object* v___y_1884_; lean_object* v___y_1885_; uint8_t v___y_1886_; lean_object* v___x_1889_; lean_object* v___y_1891_; lean_object* v_e_x27_1892_; lean_object* v_proof_1893_; uint8_t v_done_1894_; uint8_t v_contextDependent_1895_; lean_object* v___y_1917_; lean_object* v_a_1918_; lean_object* v___x_1929_; 
v___x_1889_ = lean_box(0);
lean_inc_ref(v___y_1858_);
v___x_1929_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_post_1855_, v___x_1856_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
if (lean_obj_tag(v_a_1930_) == 0)
{
uint8_t v_done_1931_; 
v_done_1931_ = lean_ctor_get_uint8(v_a_1930_, 0);
if (v_done_1931_ == 0)
{
uint8_t v_contextDependent_1932_; lean_object* v___x_1933_; 
lean_dec_ref_known(v___x_1929_, 1);
v_contextDependent_1932_ = lean_ctor_get_uint8(v_a_1930_, 1);
lean_dec_ref_known(v_a_1930_, 0);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
lean_inc(v___y_1861_);
lean_inc_ref(v___y_1860_);
lean_inc(v___y_1859_);
lean_inc_ref(v___y_1858_);
v___x_1933_ = lean_apply_12(v___f_1857_, v___x_1889_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, lean_box(0));
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; uint8_t v___y_1936_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
if (v_contextDependent_1932_ == 0)
{
v___y_1917_ = v___x_1933_;
v_a_1918_ = v_a_1934_;
goto v___jp_1916_;
}
else
{
if (lean_obj_tag(v_a_1934_) == 0)
{
uint8_t v_contextDependent_1946_; 
v_contextDependent_1946_ = lean_ctor_get_uint8(v_a_1934_, 1);
v___y_1936_ = v_contextDependent_1946_;
goto v___jp_1935_;
}
else
{
uint8_t v_contextDependent_1947_; 
v_contextDependent_1947_ = lean_ctor_get_uint8(v_a_1934_, sizeof(void*)*2 + 1);
v___y_1936_ = v_contextDependent_1947_;
goto v___jp_1935_;
}
}
v___jp_1935_:
{
if (v___y_1936_ == 0)
{
lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1944_; 
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v___x_1933_, 0);
lean_dec(v_unused_1945_);
v___x_1938_ = v___x_1933_;
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
else
{
lean_dec(v___x_1933_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1934_);
lean_inc_ref(v___x_1940_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v___y_1917_ = v___x_1942_;
v_a_1918_ = v___x_1940_;
goto v___jp_1916_;
}
}
}
else
{
v___y_1917_ = v___x_1933_;
v_a_1918_ = v_a_1934_;
goto v___jp_1916_;
}
}
}
else
{
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v___f_1854_);
return v___x_1933_;
}
}
else
{
lean_dec_ref_known(v_a_1930_, 0);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v___f_1857_);
lean_dec_ref(v___f_1854_);
return v___x_1929_;
}
}
else
{
uint8_t v_done_1948_; 
v_done_1948_ = lean_ctor_get_uint8(v_a_1930_, sizeof(void*)*2);
if (v_done_1948_ == 0)
{
lean_object* v_e_x27_1949_; lean_object* v_proof_1950_; uint8_t v_contextDependent_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref_known(v___x_1929_, 1);
v_e_x27_1949_ = lean_ctor_get(v_a_1930_, 0);
v_proof_1950_ = lean_ctor_get(v_a_1930_, 1);
v_contextDependent_1951_ = lean_ctor_get_uint8(v_a_1930_, sizeof(void*)*2 + 1);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_a_1930_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1953_ = v_a_1930_;
v_isShared_1954_ = v_isSharedCheck_2001_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_proof_1950_);
lean_inc(v_e_x27_1949_);
lean_dec(v_a_1930_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_2001_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; 
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
lean_inc(v___y_1861_);
lean_inc_ref(v___y_1860_);
lean_inc(v___y_1859_);
lean_inc_ref(v_e_x27_1949_);
v___x_1955_ = lean_apply_12(v___f_1857_, v___x_1889_, v_e_x27_1949_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, lean_box(0));
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_2000_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_2000_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_2000_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
if (lean_obj_tag(v_a_1956_) == 0)
{
uint8_t v_done_1960_; uint8_t v_contextDependent_1961_; uint8_t v___y_1963_; 
v_done_1960_ = lean_ctor_get_uint8(v_a_1956_, 0);
v_contextDependent_1961_ = lean_ctor_get_uint8(v_a_1956_, 1);
lean_dec_ref_known(v_a_1956_, 0);
if (v_contextDependent_1951_ == 0)
{
v___y_1963_ = v_contextDependent_1961_;
goto v___jp_1962_;
}
else
{
v___y_1963_ = v_contextDependent_1951_;
goto v___jp_1962_;
}
v___jp_1962_:
{
lean_object* v___x_1965_; 
lean_inc_ref(v_proof_1950_);
lean_inc_ref(v_e_x27_1949_);
if (v_isShared_1954_ == 0)
{
v___x_1965_ = v___x_1953_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_e_x27_1949_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_proof_1950_);
v___x_1965_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1967_; 
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*2, v_done_1960_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*2 + 1, v___y_1963_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1965_);
v___x_1967_ = v___x_1958_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
v___y_1891_ = v___x_1967_;
v_e_x27_1892_ = v_e_x27_1949_;
v_proof_1893_ = v_proof_1950_;
v_done_1894_ = v_done_1960_;
v_contextDependent_1895_ = v___y_1963_;
goto v___jp_1890_;
}
}
}
}
else
{
lean_object* v_e_x27_1970_; lean_object* v_proof_1971_; uint8_t v_done_1972_; uint8_t v_contextDependent_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1999_; 
lean_del_object(v___x_1958_);
lean_del_object(v___x_1953_);
v_e_x27_1970_ = lean_ctor_get(v_a_1956_, 0);
v_proof_1971_ = lean_ctor_get(v_a_1956_, 1);
v_done_1972_ = lean_ctor_get_uint8(v_a_1956_, sizeof(void*)*2);
v_contextDependent_1973_ = lean_ctor_get_uint8(v_a_1956_, sizeof(void*)*2 + 1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_a_1956_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1975_ = v_a_1956_;
v_isShared_1976_ = v_isSharedCheck_1999_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_proof_1971_);
lean_inc(v_e_x27_1970_);
lean_dec(v_a_1956_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1999_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; 
lean_inc_ref(v_e_x27_1970_);
lean_inc_ref(v___y_1858_);
v___x_1977_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1858_, v_e_x27_1949_, v_proof_1950_, v_e_x27_1970_, v_proof_1971_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1990_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1990_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1990_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
uint8_t v___y_1983_; 
if (v_contextDependent_1951_ == 0)
{
v___y_1983_ = v_contextDependent_1973_;
goto v___jp_1982_;
}
else
{
v___y_1983_ = v_contextDependent_1951_;
goto v___jp_1982_;
}
v___jp_1982_:
{
lean_object* v___x_1985_; 
lean_inc(v_a_1978_);
lean_inc_ref(v_e_x27_1970_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v_a_1978_);
v___x_1985_ = v___x_1975_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_e_x27_1970_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_a_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1989_, sizeof(void*)*2, v_done_1972_);
v___x_1985_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1987_; 
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*2 + 1, v___y_1983_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1985_);
v___x_1987_ = v___x_1980_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
v___y_1891_ = v___x_1987_;
v_e_x27_1892_ = v_e_x27_1970_;
v_proof_1893_ = v_a_1978_;
v_done_1894_ = v_done_1972_;
v_contextDependent_1895_ = v___y_1983_;
goto v___jp_1890_;
}
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_del_object(v___x_1975_);
lean_dec_ref(v_e_x27_1970_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v___f_1854_);
v_a_1991_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1977_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1977_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1953_);
lean_dec_ref(v_proof_1950_);
lean_dec_ref(v_e_x27_1949_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v___f_1854_);
return v___x_1955_;
}
}
}
else
{
lean_dec_ref_known(v_a_1930_, 2);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v___f_1857_);
lean_dec_ref(v___f_1854_);
return v___x_1929_;
}
}
}
else
{
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v___f_1857_);
lean_dec_ref(v___f_1854_);
return v___x_1929_;
}
v___jp_1869_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1874_, 0, v___y_1872_);
lean_ctor_set(v___x_1874_, 1, v___y_1870_);
lean_ctor_set_uint8(v___x_1874_, sizeof(void*)*2, v___y_1871_);
lean_ctor_set_uint8(v___x_1874_, sizeof(void*)*2 + 1, v___y_1873_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
v___jp_1876_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1881_, 0, v___y_1877_);
lean_ctor_set(v___x_1881_, 1, v___y_1879_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*2, v___y_1878_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*2 + 1, v___y_1880_);
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
v___jp_1883_:
{
if (v___y_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec_ref(v___y_1884_);
v___x_1887_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1885_);
v___x_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
return v___x_1888_;
}
else
{
lean_dec_ref(v___y_1885_);
return v___y_1884_;
}
}
v___jp_1890_:
{
if (v_done_1894_ == 0)
{
lean_object* v___x_1896_; 
lean_dec_ref(v___y_1891_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
lean_inc_ref(v_e_x27_1892_);
v___x_1896_ = lean_apply_12(v___f_1854_, v___x_1889_, v_e_x27_1892_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, lean_box(0));
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
if (lean_obj_tag(v_a_1897_) == 0)
{
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1858_);
if (v_contextDependent_1895_ == 0)
{
uint8_t v_done_1898_; uint8_t v_contextDependent_1899_; 
v_done_1898_ = lean_ctor_get_uint8(v_a_1897_, 0);
v_contextDependent_1899_ = lean_ctor_get_uint8(v_a_1897_, 1);
lean_dec_ref_known(v_a_1897_, 0);
v___y_1870_ = v_proof_1893_;
v___y_1871_ = v_done_1898_;
v___y_1872_ = v_e_x27_1892_;
v___y_1873_ = v_contextDependent_1899_;
goto v___jp_1869_;
}
else
{
uint8_t v_done_1900_; 
v_done_1900_ = lean_ctor_get_uint8(v_a_1897_, 0);
lean_dec_ref_known(v_a_1897_, 0);
v___y_1870_ = v_proof_1893_;
v___y_1871_ = v_done_1900_;
v___y_1872_ = v_e_x27_1892_;
v___y_1873_ = v_contextDependent_1895_;
goto v___jp_1869_;
}
}
else
{
lean_object* v_e_x27_1901_; lean_object* v_proof_1902_; uint8_t v_done_1903_; uint8_t v_contextDependent_1904_; lean_object* v___x_1905_; 
v_e_x27_1901_ = lean_ctor_get(v_a_1897_, 0);
lean_inc_ref_n(v_e_x27_1901_, 2);
v_proof_1902_ = lean_ctor_get(v_a_1897_, 1);
lean_inc_ref(v_proof_1902_);
v_done_1903_ = lean_ctor_get_uint8(v_a_1897_, sizeof(void*)*2);
v_contextDependent_1904_ = lean_ctor_get_uint8(v_a_1897_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1897_, 2);
v___x_1905_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_1858_, v_e_x27_1892_, v_proof_1893_, v_e_x27_1901_, v_proof_1902_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
if (lean_obj_tag(v___x_1905_) == 0)
{
if (v_contextDependent_1895_ == 0)
{
lean_object* v_a_1906_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v___y_1877_ = v_e_x27_1901_;
v___y_1878_ = v_done_1903_;
v___y_1879_ = v_a_1906_;
v___y_1880_ = v_contextDependent_1904_;
goto v___jp_1876_;
}
else
{
lean_object* v_a_1907_; 
v_a_1907_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1905_, 1);
v___y_1877_ = v_e_x27_1901_;
v___y_1878_ = v_done_1903_;
v___y_1879_ = v_a_1907_;
v___y_1880_ = v_contextDependent_1895_;
goto v___jp_1876_;
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v_e_x27_1901_);
v_a_1908_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1905_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1905_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_1893_);
lean_dec_ref(v_e_x27_1892_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1858_);
return v___x_1896_;
}
}
else
{
lean_dec_ref(v_proof_1893_);
lean_dec_ref(v_e_x27_1892_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v___f_1854_);
return v___y_1891_;
}
}
v___jp_1916_:
{
if (lean_obj_tag(v_a_1918_) == 0)
{
uint8_t v_done_1919_; 
v_done_1919_ = lean_ctor_get_uint8(v_a_1918_, 0);
if (v_done_1919_ == 0)
{
uint8_t v_contextDependent_1920_; lean_object* v___x_1921_; 
lean_dec_ref(v___y_1917_);
v_contextDependent_1920_ = lean_ctor_get_uint8(v_a_1918_, 1);
lean_dec_ref_known(v_a_1918_, 0);
v___x_1921_ = lean_apply_12(v___f_1854_, v___x_1889_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, lean_box(0));
if (lean_obj_tag(v___x_1921_) == 0)
{
if (v_contextDependent_1920_ == 0)
{
return v___x_1921_;
}
else
{
lean_object* v_a_1922_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
if (lean_obj_tag(v_a_1922_) == 0)
{
uint8_t v_contextDependent_1923_; 
v_contextDependent_1923_ = lean_ctor_get_uint8(v_a_1922_, 1);
v___y_1884_ = v___x_1921_;
v___y_1885_ = v_a_1922_;
v___y_1886_ = v_contextDependent_1923_;
goto v___jp_1883_;
}
else
{
uint8_t v_contextDependent_1924_; 
v_contextDependent_1924_ = lean_ctor_get_uint8(v_a_1922_, sizeof(void*)*2 + 1);
v___y_1884_ = v___x_1921_;
v___y_1885_ = v_a_1922_;
v___y_1886_ = v_contextDependent_1924_;
goto v___jp_1883_;
}
}
}
else
{
return v___x_1921_;
}
}
else
{
lean_dec_ref_known(v_a_1918_, 0);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v___f_1854_);
return v___y_1917_;
}
}
else
{
lean_object* v_e_x27_1925_; lean_object* v_proof_1926_; uint8_t v_done_1927_; uint8_t v_contextDependent_1928_; 
v_e_x27_1925_ = lean_ctor_get(v_a_1918_, 0);
lean_inc_ref(v_e_x27_1925_);
v_proof_1926_ = lean_ctor_get(v_a_1918_, 1);
lean_inc_ref(v_proof_1926_);
v_done_1927_ = lean_ctor_get_uint8(v_a_1918_, sizeof(void*)*2);
v_contextDependent_1928_ = lean_ctor_get_uint8(v_a_1918_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1918_, 2);
v___y_1891_ = v___y_1917_;
v_e_x27_1892_ = v_e_x27_1925_;
v_proof_1893_ = v_proof_1926_;
v_done_1894_ = v_done_1927_;
v_contextDependent_1895_ = v_contextDependent_1928_;
goto v___jp_1890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__19___boxed(lean_object* v___f_2002_, lean_object* v_post_2003_, lean_object* v___x_2004_, lean_object* v___f_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__19(v___f_2002_, v_post_2003_, v___x_2004_, v___f_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec_ref(v_post_2003_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__20(lean_object* v_maxChar_2018_, lean_object* v___x_2019_, uint8_t v___x_2020_, uint8_t v_distrib_2021_, lean_object* v_x_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_maxChar_2018_);
v___x_2035_ = l_Lean_Meta_Sym_Simp_simpArith(v___x_2019_, v___x_2020_, v_distrib_2021_, v___x_2034_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec_ref_known(v___x_2034_, 1);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__20___boxed(lean_object* v_maxChar_2036_, lean_object* v___x_2037_, lean_object* v___x_2038_, lean_object* v_distrib_2039_, lean_object* v_x_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
uint8_t v___x_11818__boxed_2052_; uint8_t v_distrib_boxed_2053_; lean_object* v_res_2054_; 
v___x_11818__boxed_2052_ = lean_unbox(v___x_2038_);
v_distrib_boxed_2053_ = lean_unbox(v_distrib_2039_);
v_res_2054_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__20(v_maxChar_2036_, v___x_2037_, v___x_11818__boxed_2052_, v_distrib_boxed_2053_, v_x_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__21(lean_object* v_pre_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; 
lean_inc(v___y_2065_);
lean_inc_ref(v___y_2064_);
lean_inc(v___y_2063_);
lean_inc_ref(v___y_2062_);
lean_inc(v___y_2061_);
lean_inc_ref(v___y_2060_);
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2058_);
lean_inc(v___y_2057_);
lean_inc_ref(v___y_2056_);
v___x_2067_ = lean_apply_11(v_pre_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, lean_box(0));
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
if (lean_obj_tag(v_a_2068_) == 0)
{
uint8_t v_done_2069_; 
v_done_2069_ = lean_ctor_get_uint8(v_a_2068_, 0);
if (v_done_2069_ == 0)
{
uint8_t v_contextDependent_2070_; lean_object* v___x_2071_; 
lean_dec_ref_known(v___x_2067_, 1);
v_contextDependent_2070_ = lean_ctor_get_uint8(v_a_2068_, 1);
lean_dec_ref_known(v_a_2068_, 0);
v___x_2071_ = l_Lean_Meta_Grind_NormSym_pushNot(v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; uint8_t v___y_2074_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
if (v_contextDependent_2070_ == 0)
{
return v___x_2071_;
}
else
{
if (lean_obj_tag(v_a_2072_) == 0)
{
uint8_t v_contextDependent_2084_; 
v_contextDependent_2084_ = lean_ctor_get_uint8(v_a_2072_, 1);
v___y_2074_ = v_contextDependent_2084_;
goto v___jp_2073_;
}
else
{
uint8_t v_contextDependent_2085_; 
v_contextDependent_2085_ = lean_ctor_get_uint8(v_a_2072_, sizeof(void*)*2 + 1);
v___y_2074_ = v_contextDependent_2085_;
goto v___jp_2073_;
}
}
v___jp_2073_:
{
if (v___y_2074_ == 0)
{
lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2082_; 
lean_inc(v_a_2072_);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v___x_2071_, 0);
lean_dec(v_unused_2083_);
v___x_2076_ = v___x_2071_;
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
else
{
lean_dec(v___x_2071_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2072_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
else
{
return v___x_2071_;
}
}
}
else
{
return v___x_2071_;
}
}
else
{
lean_dec_ref_known(v_a_2068_, 0);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v___x_2067_;
}
}
else
{
uint8_t v_done_2086_; 
v_done_2086_ = lean_ctor_get_uint8(v_a_2068_, sizeof(void*)*2);
if (v_done_2086_ == 0)
{
lean_object* v_e_x27_2087_; lean_object* v_proof_2088_; uint8_t v_contextDependent_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref_known(v___x_2067_, 1);
v_e_x27_2087_ = lean_ctor_get(v_a_2068_, 0);
v_proof_2088_ = lean_ctor_get(v_a_2068_, 1);
v_contextDependent_2089_ = lean_ctor_get_uint8(v_a_2068_, sizeof(void*)*2 + 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_a_2068_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2091_ = v_a_2068_;
v_isShared_2092_ = v_isSharedCheck_2139_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_proof_2088_);
lean_inc(v_e_x27_2087_);
lean_dec(v_a_2068_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2139_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_Meta_Grind_NormSym_pushNot(v_e_x27_2087_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2138_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2138_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2138_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
if (lean_obj_tag(v_a_2094_) == 0)
{
uint8_t v_done_2098_; uint8_t v_contextDependent_2099_; uint8_t v___y_2101_; 
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec_ref(v___y_2056_);
v_done_2098_ = lean_ctor_get_uint8(v_a_2094_, 0);
v_contextDependent_2099_ = lean_ctor_get_uint8(v_a_2094_, 1);
lean_dec_ref_known(v_a_2094_, 0);
if (v_contextDependent_2089_ == 0)
{
v___y_2101_ = v_contextDependent_2099_;
goto v___jp_2100_;
}
else
{
v___y_2101_ = v_contextDependent_2089_;
goto v___jp_2100_;
}
v___jp_2100_:
{
lean_object* v___x_2103_; 
if (v_isShared_2092_ == 0)
{
v___x_2103_ = v___x_2091_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_e_x27_2087_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_proof_2088_);
v___x_2103_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2105_; 
lean_ctor_set_uint8(v___x_2103_, sizeof(void*)*2, v_done_2098_);
lean_ctor_set_uint8(v___x_2103_, sizeof(void*)*2 + 1, v___y_2101_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2103_);
v___x_2105_ = v___x_2096_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v_e_x27_2108_; lean_object* v_proof_2109_; uint8_t v_done_2110_; uint8_t v_contextDependent_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2137_; 
lean_del_object(v___x_2096_);
lean_del_object(v___x_2091_);
v_e_x27_2108_ = lean_ctor_get(v_a_2094_, 0);
v_proof_2109_ = lean_ctor_get(v_a_2094_, 1);
v_done_2110_ = lean_ctor_get_uint8(v_a_2094_, sizeof(void*)*2);
v_contextDependent_2111_ = lean_ctor_get_uint8(v_a_2094_, sizeof(void*)*2 + 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_a_2094_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2113_ = v_a_2094_;
v_isShared_2114_ = v_isSharedCheck_2137_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_proof_2109_);
lean_inc(v_e_x27_2108_);
lean_dec(v_a_2094_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2137_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; 
lean_inc_ref(v_e_x27_2108_);
v___x_2115_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2056_, v_e_x27_2087_, v_proof_2088_, v_e_x27_2108_, v_proof_2109_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2128_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2128_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2128_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
uint8_t v___y_2121_; 
if (v_contextDependent_2089_ == 0)
{
v___y_2121_ = v_contextDependent_2111_;
goto v___jp_2120_;
}
else
{
v___y_2121_ = v_contextDependent_2089_;
goto v___jp_2120_;
}
v___jp_2120_:
{
lean_object* v___x_2123_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 1, v_a_2116_);
v___x_2123_ = v___x_2113_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_e_x27_2108_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_a_2116_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*2, v_done_2110_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*2 + 1, v___y_2121_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2123_);
v___x_2125_ = v___x_2118_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_del_object(v___x_2113_);
lean_dec_ref(v_e_x27_2108_);
v_a_2129_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2115_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2115_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2091_);
lean_dec_ref(v_proof_2088_);
lean_dec_ref(v_e_x27_2087_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec_ref(v___y_2056_);
return v___x_2093_;
}
}
}
else
{
lean_dec_ref_known(v_a_2068_, 2);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v___x_2067_;
}
}
}
else
{
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v___x_2067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__21___boxed(lean_object* v_pre_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__21(v_pre_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__22(lean_object* v___f_2153_, lean_object* v_pre_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; uint8_t v___y_2170_; lean_object* v___y_2174_; uint8_t v___y_2175_; lean_object* v___y_2176_; uint8_t v___y_2177_; lean_object* v___y_2181_; lean_object* v___y_2182_; uint8_t v___y_2183_; lean_object* v___x_2186_; lean_object* v___y_2188_; lean_object* v_e_x27_2189_; lean_object* v_proof_2190_; uint8_t v_done_2191_; uint8_t v_contextDependent_2192_; lean_object* v___y_2214_; lean_object* v_a_2215_; lean_object* v___x_2226_; 
v___x_2186_ = lean_box(0);
lean_inc(v___y_2164_);
lean_inc_ref(v___y_2163_);
lean_inc(v___y_2162_);
lean_inc_ref(v___y_2161_);
lean_inc(v___y_2160_);
lean_inc_ref(v___y_2159_);
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
lean_inc(v___y_2156_);
lean_inc_ref(v___y_2155_);
v___x_2226_ = lean_apply_11(v_pre_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, lean_box(0));
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
if (lean_obj_tag(v_a_2227_) == 0)
{
uint8_t v_done_2228_; 
v_done_2228_ = lean_ctor_get_uint8(v_a_2227_, 0);
if (v_done_2228_ == 0)
{
uint8_t v_contextDependent_2229_; lean_object* v___x_2230_; 
lean_dec_ref_known(v___x_2226_, 1);
v_contextDependent_2229_ = lean_ctor_get_uint8(v_a_2227_, 1);
lean_dec_ref_known(v_a_2227_, 0);
v___x_2230_ = l_Lean_Meta_Grind_NormSym_pushNot(v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; uint8_t v___y_2233_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
if (v_contextDependent_2229_ == 0)
{
v___y_2214_ = v___x_2230_;
v_a_2215_ = v_a_2231_;
goto v___jp_2213_;
}
else
{
if (lean_obj_tag(v_a_2231_) == 0)
{
uint8_t v_contextDependent_2243_; 
v_contextDependent_2243_ = lean_ctor_get_uint8(v_a_2231_, 1);
v___y_2233_ = v_contextDependent_2243_;
goto v___jp_2232_;
}
else
{
uint8_t v_contextDependent_2244_; 
v_contextDependent_2244_ = lean_ctor_get_uint8(v_a_2231_, sizeof(void*)*2 + 1);
v___y_2233_ = v_contextDependent_2244_;
goto v___jp_2232_;
}
}
v___jp_2232_:
{
if (v___y_2233_ == 0)
{
lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2241_; 
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; 
v_unused_2242_ = lean_ctor_get(v___x_2230_, 0);
lean_dec(v_unused_2242_);
v___x_2235_ = v___x_2230_;
v_isShared_2236_ = v_isSharedCheck_2241_;
goto v_resetjp_2234_;
}
else
{
lean_dec(v___x_2230_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2241_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2231_);
lean_inc_ref(v___x_2237_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2237_);
v___x_2239_ = v___x_2235_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
v___y_2214_ = v___x_2239_;
v_a_2215_ = v___x_2237_;
goto v___jp_2213_;
}
}
}
else
{
v___y_2214_ = v___x_2230_;
v_a_2215_ = v_a_2231_;
goto v___jp_2213_;
}
}
}
else
{
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___f_2153_);
return v___x_2230_;
}
}
else
{
lean_dec_ref_known(v_a_2227_, 0);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___f_2153_);
return v___x_2226_;
}
}
else
{
uint8_t v_done_2245_; 
v_done_2245_ = lean_ctor_get_uint8(v_a_2227_, sizeof(void*)*2);
if (v_done_2245_ == 0)
{
lean_object* v_e_x27_2246_; lean_object* v_proof_2247_; uint8_t v_contextDependent_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref_known(v___x_2226_, 1);
v_e_x27_2246_ = lean_ctor_get(v_a_2227_, 0);
v_proof_2247_ = lean_ctor_get(v_a_2227_, 1);
v_contextDependent_2248_ = lean_ctor_get_uint8(v_a_2227_, sizeof(void*)*2 + 1);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_a_2227_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2250_ = v_a_2227_;
v_isShared_2251_ = v_isSharedCheck_2298_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_proof_2247_);
lean_inc(v_e_x27_2246_);
lean_dec(v_a_2227_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2298_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lean_Meta_Grind_NormSym_pushNot(v_e_x27_2246_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2297_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2297_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2297_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
if (lean_obj_tag(v_a_2253_) == 0)
{
uint8_t v_done_2257_; uint8_t v_contextDependent_2258_; uint8_t v___y_2260_; 
v_done_2257_ = lean_ctor_get_uint8(v_a_2253_, 0);
v_contextDependent_2258_ = lean_ctor_get_uint8(v_a_2253_, 1);
lean_dec_ref_known(v_a_2253_, 0);
if (v_contextDependent_2248_ == 0)
{
v___y_2260_ = v_contextDependent_2258_;
goto v___jp_2259_;
}
else
{
v___y_2260_ = v_contextDependent_2248_;
goto v___jp_2259_;
}
v___jp_2259_:
{
lean_object* v___x_2262_; 
lean_inc_ref(v_proof_2247_);
lean_inc_ref(v_e_x27_2246_);
if (v_isShared_2251_ == 0)
{
v___x_2262_ = v___x_2250_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_e_x27_2246_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_proof_2247_);
v___x_2262_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2264_; 
lean_ctor_set_uint8(v___x_2262_, sizeof(void*)*2, v_done_2257_);
lean_ctor_set_uint8(v___x_2262_, sizeof(void*)*2 + 1, v___y_2260_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2262_);
v___x_2264_ = v___x_2255_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
v___y_2188_ = v___x_2264_;
v_e_x27_2189_ = v_e_x27_2246_;
v_proof_2190_ = v_proof_2247_;
v_done_2191_ = v_done_2257_;
v_contextDependent_2192_ = v___y_2260_;
goto v___jp_2187_;
}
}
}
}
else
{
lean_object* v_e_x27_2267_; lean_object* v_proof_2268_; uint8_t v_done_2269_; uint8_t v_contextDependent_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2296_; 
lean_del_object(v___x_2255_);
lean_del_object(v___x_2250_);
v_e_x27_2267_ = lean_ctor_get(v_a_2253_, 0);
v_proof_2268_ = lean_ctor_get(v_a_2253_, 1);
v_done_2269_ = lean_ctor_get_uint8(v_a_2253_, sizeof(void*)*2);
v_contextDependent_2270_ = lean_ctor_get_uint8(v_a_2253_, sizeof(void*)*2 + 1);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_a_2253_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2272_ = v_a_2253_;
v_isShared_2273_ = v_isSharedCheck_2296_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_proof_2268_);
lean_inc(v_e_x27_2267_);
lean_dec(v_a_2253_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2296_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; 
lean_inc_ref(v_e_x27_2267_);
lean_inc_ref(v___y_2155_);
v___x_2274_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2155_, v_e_x27_2246_, v_proof_2247_, v_e_x27_2267_, v_proof_2268_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2287_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2287_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2287_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
uint8_t v___y_2280_; 
if (v_contextDependent_2248_ == 0)
{
v___y_2280_ = v_contextDependent_2270_;
goto v___jp_2279_;
}
else
{
v___y_2280_ = v_contextDependent_2248_;
goto v___jp_2279_;
}
v___jp_2279_:
{
lean_object* v___x_2282_; 
lean_inc(v_a_2275_);
lean_inc_ref(v_e_x27_2267_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 1, v_a_2275_);
v___x_2282_ = v___x_2272_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_e_x27_2267_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_a_2275_);
lean_ctor_set_uint8(v_reuseFailAlloc_2286_, sizeof(void*)*2, v_done_2269_);
v___x_2282_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2284_; 
lean_ctor_set_uint8(v___x_2282_, sizeof(void*)*2 + 1, v___y_2280_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2282_);
v___x_2284_ = v___x_2277_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
v___y_2188_ = v___x_2284_;
v_e_x27_2189_ = v_e_x27_2267_;
v_proof_2190_ = v_a_2275_;
v_done_2191_ = v_done_2269_;
v_contextDependent_2192_ = v___y_2280_;
goto v___jp_2187_;
}
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_del_object(v___x_2272_);
lean_dec_ref(v_e_x27_2267_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___f_2153_);
v_a_2288_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2274_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2274_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2250_);
lean_dec_ref(v_proof_2247_);
lean_dec_ref(v_e_x27_2246_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___f_2153_);
return v___x_2252_;
}
}
}
else
{
lean_dec_ref_known(v_a_2227_, 2);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___f_2153_);
return v___x_2226_;
}
}
}
else
{
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___f_2153_);
return v___x_2226_;
}
v___jp_2166_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2171_, 0, v___y_2168_);
lean_ctor_set(v___x_2171_, 1, v___y_2169_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*2, v___y_2167_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*2 + 1, v___y_2170_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
v___jp_2173_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2178_, 0, v___y_2174_);
lean_ctor_set(v___x_2178_, 1, v___y_2176_);
lean_ctor_set_uint8(v___x_2178_, sizeof(void*)*2, v___y_2175_);
lean_ctor_set_uint8(v___x_2178_, sizeof(void*)*2 + 1, v___y_2177_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
return v___x_2179_;
}
v___jp_2180_:
{
if (v___y_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec_ref(v___y_2181_);
v___x_2184_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_2182_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
else
{
lean_dec_ref(v___y_2182_);
return v___y_2181_;
}
}
v___jp_2187_:
{
if (v_done_2191_ == 0)
{
lean_object* v___x_2193_; 
lean_dec_ref(v___y_2188_);
lean_inc(v___y_2164_);
lean_inc_ref(v___y_2163_);
lean_inc(v___y_2162_);
lean_inc_ref(v___y_2161_);
lean_inc(v___y_2160_);
lean_inc_ref(v___y_2159_);
lean_inc_ref(v_e_x27_2189_);
v___x_2193_ = lean_apply_12(v___f_2153_, v___x_2186_, v_e_x27_2189_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, lean_box(0));
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2193_, 1);
if (lean_obj_tag(v_a_2194_) == 0)
{
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v___y_2155_);
if (v_contextDependent_2192_ == 0)
{
uint8_t v_done_2195_; uint8_t v_contextDependent_2196_; 
v_done_2195_ = lean_ctor_get_uint8(v_a_2194_, 0);
v_contextDependent_2196_ = lean_ctor_get_uint8(v_a_2194_, 1);
lean_dec_ref_known(v_a_2194_, 0);
v___y_2167_ = v_done_2195_;
v___y_2168_ = v_e_x27_2189_;
v___y_2169_ = v_proof_2190_;
v___y_2170_ = v_contextDependent_2196_;
goto v___jp_2166_;
}
else
{
uint8_t v_done_2197_; 
v_done_2197_ = lean_ctor_get_uint8(v_a_2194_, 0);
lean_dec_ref_known(v_a_2194_, 0);
v___y_2167_ = v_done_2197_;
v___y_2168_ = v_e_x27_2189_;
v___y_2169_ = v_proof_2190_;
v___y_2170_ = v_contextDependent_2192_;
goto v___jp_2166_;
}
}
else
{
lean_object* v_e_x27_2198_; lean_object* v_proof_2199_; uint8_t v_done_2200_; uint8_t v_contextDependent_2201_; lean_object* v___x_2202_; 
v_e_x27_2198_ = lean_ctor_get(v_a_2194_, 0);
lean_inc_ref_n(v_e_x27_2198_, 2);
v_proof_2199_ = lean_ctor_get(v_a_2194_, 1);
lean_inc_ref(v_proof_2199_);
v_done_2200_ = lean_ctor_get_uint8(v_a_2194_, sizeof(void*)*2);
v_contextDependent_2201_ = lean_ctor_get_uint8(v_a_2194_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2194_, 2);
v___x_2202_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2155_, v_e_x27_2189_, v_proof_2190_, v_e_x27_2198_, v_proof_2199_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
if (lean_obj_tag(v___x_2202_) == 0)
{
if (v_contextDependent_2192_ == 0)
{
lean_object* v_a_2203_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___y_2174_ = v_e_x27_2198_;
v___y_2175_ = v_done_2200_;
v___y_2176_ = v_a_2203_;
v___y_2177_ = v_contextDependent_2201_;
goto v___jp_2173_;
}
else
{
lean_object* v_a_2204_; 
v_a_2204_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2202_, 1);
v___y_2174_ = v_e_x27_2198_;
v___y_2175_ = v_done_2200_;
v___y_2176_ = v_a_2204_;
v___y_2177_ = v_contextDependent_2192_;
goto v___jp_2173_;
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec_ref(v_e_x27_2198_);
v_a_2205_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2202_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2202_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_2190_);
lean_dec_ref(v_e_x27_2189_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec_ref(v___y_2155_);
return v___x_2193_;
}
}
else
{
lean_dec_ref(v_proof_2190_);
lean_dec_ref(v_e_x27_2189_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___f_2153_);
return v___y_2188_;
}
}
v___jp_2213_:
{
if (lean_obj_tag(v_a_2215_) == 0)
{
uint8_t v_done_2216_; 
v_done_2216_ = lean_ctor_get_uint8(v_a_2215_, 0);
if (v_done_2216_ == 0)
{
uint8_t v_contextDependent_2217_; lean_object* v___x_2218_; 
lean_dec_ref(v___y_2214_);
v_contextDependent_2217_ = lean_ctor_get_uint8(v_a_2215_, 1);
lean_dec_ref_known(v_a_2215_, 0);
v___x_2218_ = lean_apply_12(v___f_2153_, v___x_2186_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, lean_box(0));
if (lean_obj_tag(v___x_2218_) == 0)
{
if (v_contextDependent_2217_ == 0)
{
return v___x_2218_;
}
else
{
lean_object* v_a_2219_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
if (lean_obj_tag(v_a_2219_) == 0)
{
uint8_t v_contextDependent_2220_; 
v_contextDependent_2220_ = lean_ctor_get_uint8(v_a_2219_, 1);
v___y_2181_ = v___x_2218_;
v___y_2182_ = v_a_2219_;
v___y_2183_ = v_contextDependent_2220_;
goto v___jp_2180_;
}
else
{
uint8_t v_contextDependent_2221_; 
v_contextDependent_2221_ = lean_ctor_get_uint8(v_a_2219_, sizeof(void*)*2 + 1);
v___y_2181_ = v___x_2218_;
v___y_2182_ = v_a_2219_;
v___y_2183_ = v_contextDependent_2221_;
goto v___jp_2180_;
}
}
}
else
{
return v___x_2218_;
}
}
else
{
lean_dec_ref_known(v_a_2215_, 0);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___f_2153_);
return v___y_2214_;
}
}
else
{
lean_object* v_e_x27_2222_; lean_object* v_proof_2223_; uint8_t v_done_2224_; uint8_t v_contextDependent_2225_; 
v_e_x27_2222_ = lean_ctor_get(v_a_2215_, 0);
lean_inc_ref(v_e_x27_2222_);
v_proof_2223_ = lean_ctor_get(v_a_2215_, 1);
lean_inc_ref(v_proof_2223_);
v_done_2224_ = lean_ctor_get_uint8(v_a_2215_, sizeof(void*)*2);
v_contextDependent_2225_ = lean_ctor_get_uint8(v_a_2215_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2215_, 2);
v___y_2188_ = v___y_2214_;
v_e_x27_2189_ = v_e_x27_2222_;
v_proof_2190_ = v_proof_2223_;
v_done_2191_ = v_done_2224_;
v_contextDependent_2192_ = v_contextDependent_2225_;
goto v___jp_2187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__22___boxed(lean_object* v___f_2299_, lean_object* v_pre_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__22(v___f_2299_, v_pre_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__23(lean_object* v_pre_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
lean_inc(v___y_2323_);
lean_inc_ref(v___y_2322_);
lean_inc(v___y_2321_);
lean_inc_ref(v___y_2320_);
lean_inc(v___y_2319_);
lean_inc_ref(v___y_2318_);
lean_inc_ref(v___y_2314_);
v___x_2325_ = lean_apply_11(v_pre_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, lean_box(0));
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
if (lean_obj_tag(v_a_2326_) == 0)
{
uint8_t v_done_2327_; 
v_done_2327_ = lean_ctor_get_uint8(v_a_2326_, 0);
if (v_done_2327_ == 0)
{
uint8_t v_contextDependent_2328_; lean_object* v___x_2329_; 
lean_dec_ref_known(v___x_2325_, 1);
v_contextDependent_2328_ = lean_ctor_get_uint8(v_a_2326_, 1);
lean_dec_ref_known(v_a_2326_, 0);
v___x_2329_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v___y_2314_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v___y_2332_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
if (v_contextDependent_2328_ == 0)
{
return v___x_2329_;
}
else
{
if (lean_obj_tag(v_a_2330_) == 0)
{
uint8_t v_contextDependent_2342_; 
v_contextDependent_2342_ = lean_ctor_get_uint8(v_a_2330_, 1);
v___y_2332_ = v_contextDependent_2342_;
goto v___jp_2331_;
}
else
{
uint8_t v_contextDependent_2343_; 
v_contextDependent_2343_ = lean_ctor_get_uint8(v_a_2330_, sizeof(void*)*2 + 1);
v___y_2332_ = v_contextDependent_2343_;
goto v___jp_2331_;
}
}
v___jp_2331_:
{
if (v___y_2332_ == 0)
{
lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2340_; 
lean_inc(v_a_2330_);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; 
v_unused_2341_ = lean_ctor_get(v___x_2329_, 0);
lean_dec(v_unused_2341_);
v___x_2334_ = v___x_2329_;
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
else
{
lean_dec(v___x_2329_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2336_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2330_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2336_);
v___x_2338_ = v___x_2334_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
return v___x_2329_;
}
}
}
else
{
return v___x_2329_;
}
}
else
{
lean_dec_ref_known(v_a_2326_, 0);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v___y_2314_);
return v___x_2325_;
}
}
else
{
uint8_t v_done_2344_; 
v_done_2344_ = lean_ctor_get_uint8(v_a_2326_, sizeof(void*)*2);
if (v_done_2344_ == 0)
{
lean_object* v_e_x27_2345_; lean_object* v_proof_2346_; uint8_t v_contextDependent_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref_known(v___x_2325_, 1);
v_e_x27_2345_ = lean_ctor_get(v_a_2326_, 0);
v_proof_2346_ = lean_ctor_get(v_a_2326_, 1);
v_contextDependent_2347_ = lean_ctor_get_uint8(v_a_2326_, sizeof(void*)*2 + 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_a_2326_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2349_ = v_a_2326_;
v_isShared_2350_ = v_isSharedCheck_2397_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_proof_2346_);
lean_inc(v_e_x27_2345_);
lean_dec(v_a_2326_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2397_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; 
lean_inc_ref(v_e_x27_2345_);
v___x_2351_ = l_Lean_Meta_Sym_Simp_zetaDeltaAll___redArg(v_e_x27_2345_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2396_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2396_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2396_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
if (lean_obj_tag(v_a_2352_) == 0)
{
uint8_t v_done_2356_; uint8_t v_contextDependent_2357_; uint8_t v___y_2359_; 
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v___y_2314_);
v_done_2356_ = lean_ctor_get_uint8(v_a_2352_, 0);
v_contextDependent_2357_ = lean_ctor_get_uint8(v_a_2352_, 1);
lean_dec_ref_known(v_a_2352_, 0);
if (v_contextDependent_2347_ == 0)
{
v___y_2359_ = v_contextDependent_2357_;
goto v___jp_2358_;
}
else
{
v___y_2359_ = v_contextDependent_2347_;
goto v___jp_2358_;
}
v___jp_2358_:
{
lean_object* v___x_2361_; 
if (v_isShared_2350_ == 0)
{
v___x_2361_ = v___x_2349_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_e_x27_2345_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_proof_2346_);
v___x_2361_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*2, v_done_2356_);
lean_ctor_set_uint8(v___x_2361_, sizeof(void*)*2 + 1, v___y_2359_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2361_);
v___x_2363_ = v___x_2354_;
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
return v___x_2363_;
}
}
}
}
else
{
lean_object* v_e_x27_2366_; lean_object* v_proof_2367_; uint8_t v_done_2368_; uint8_t v_contextDependent_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2395_; 
lean_del_object(v___x_2354_);
lean_del_object(v___x_2349_);
v_e_x27_2366_ = lean_ctor_get(v_a_2352_, 0);
v_proof_2367_ = lean_ctor_get(v_a_2352_, 1);
v_done_2368_ = lean_ctor_get_uint8(v_a_2352_, sizeof(void*)*2);
v_contextDependent_2369_ = lean_ctor_get_uint8(v_a_2352_, sizeof(void*)*2 + 1);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_a_2352_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2371_ = v_a_2352_;
v_isShared_2372_ = v_isSharedCheck_2395_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_proof_2367_);
lean_inc(v_e_x27_2366_);
lean_dec(v_a_2352_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2395_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; 
lean_inc_ref(v_e_x27_2366_);
v___x_2373_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_2314_, v_e_x27_2345_, v_proof_2346_, v_e_x27_2366_, v_proof_2367_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2386_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2376_ = v___x_2373_;
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
uint8_t v___y_2379_; 
if (v_contextDependent_2347_ == 0)
{
v___y_2379_ = v_contextDependent_2369_;
goto v___jp_2378_;
}
else
{
v___y_2379_ = v_contextDependent_2347_;
goto v___jp_2378_;
}
v___jp_2378_:
{
lean_object* v___x_2381_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 1, v_a_2374_);
v___x_2381_ = v___x_2371_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_e_x27_2366_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2374_);
lean_ctor_set_uint8(v_reuseFailAlloc_2385_, sizeof(void*)*2, v_done_2368_);
v___x_2381_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2383_; 
lean_ctor_set_uint8(v___x_2381_, sizeof(void*)*2 + 1, v___y_2379_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v___x_2381_);
v___x_2383_ = v___x_2376_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_del_object(v___x_2371_);
lean_dec_ref(v_e_x27_2366_);
v_a_2387_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2373_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2373_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
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
}
}
}
else
{
lean_del_object(v___x_2349_);
lean_dec_ref(v_proof_2346_);
lean_dec_ref(v_e_x27_2345_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v___y_2314_);
return v___x_2351_;
}
}
}
else
{
lean_dec_ref_known(v_a_2326_, 2);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v___y_2314_);
return v___x_2325_;
}
}
}
else
{
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v___y_2314_);
return v___x_2325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__23___boxed(lean_object* v_pre_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__23(v_pre_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg(lean_object* v_config_2448_, lean_object* v_thms_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v___f_2452_; lean_object* v___f_2453_; lean_object* v___f_2454_; lean_object* v___f_2455_; lean_object* v___y_2457_; lean_object* v_post_2458_; lean_object* v___f_2462_; lean_object* v___x_2463_; lean_object* v_env_2464_; uint8_t v_zetaDelta_2465_; uint8_t v_zeta_2466_; uint8_t v_distrib_2467_; lean_object* v_maxChar_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; uint8_t v___x_2471_; lean_object* v___x_2472_; lean_object* v___f_2473_; lean_object* v_pre_2475_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___f_2482_; lean_object* v_pre_2484_; lean_object* v_pre_2488_; 
v___f_2452_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__6));
v___f_2453_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__7));
lean_inc_ref(v_config_2448_);
v___f_2454_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__8___boxed), 13, 1);
lean_closure_set(v___f_2454_, 0, v_config_2448_);
v___f_2455_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__12));
v___f_2462_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__13));
v___x_2463_ = lean_st_ref_get(v_a_2450_);
v_env_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc_ref(v_env_2464_);
lean_dec(v___x_2463_);
v_zetaDelta_2465_ = lean_ctor_get_uint8(v_config_2448_, sizeof(void*)*18 + 19);
v_zeta_2466_ = lean_ctor_get_uint8(v_config_2448_, sizeof(void*)*18 + 20);
v_distrib_2467_ = lean_ctor_get_uint8(v_config_2448_, sizeof(void*)*18 + 21);
v_maxChar_2468_ = lean_ctor_get(v_config_2448_, 7);
lean_inc(v_maxChar_2468_);
lean_dec_ref(v_config_2448_);
v___x_2469_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__19));
v___x_2470_ = 1;
v___x_2471_ = l_Lean_Environment_contains(v_env_2464_, v___x_2469_, v___x_2470_);
v___x_2472_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___closed__20));
lean_inc_ref(v_thms_2449_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__16___boxed), 14, 2);
lean_closure_set(v___f_2473_, 0, v_thms_2449_);
lean_closure_set(v___f_2473_, 1, v___x_2472_);
v___x_2480_ = lean_box(v___x_2470_);
v___x_2481_ = lean_box(v_distrib_2467_);
v___f_2482_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__20___boxed), 16, 4);
lean_closure_set(v___f_2482_, 0, v_maxChar_2468_);
lean_closure_set(v___f_2482_, 1, v___x_2472_);
lean_closure_set(v___f_2482_, 2, v___x_2480_);
lean_closure_set(v___f_2482_, 3, v___x_2481_);
if (v_zeta_2466_ == 0)
{
v_pre_2488_ = v___f_2452_;
goto v___jp_2487_;
}
else
{
v_pre_2488_ = v___f_2453_;
goto v___jp_2487_;
}
v___jp_2456_:
{
lean_object* v___f_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___f_2459_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__14___boxed), 13, 2);
lean_closure_set(v___f_2459_, 0, v_post_2458_);
lean_closure_set(v___f_2459_, 1, v___f_2455_);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___y_2457_);
lean_ctor_set(v___x_2460_, 1, v___f_2459_);
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
return v___x_2461_;
}
v___jp_2474_:
{
lean_object* v_post_2476_; lean_object* v___f_2477_; 
v_post_2476_ = lean_ctor_get(v_thms_2449_, 1);
lean_inc_ref(v_post_2476_);
lean_dec_ref(v_thms_2449_);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__17___boxed), 13, 2);
lean_closure_set(v___f_2477_, 0, v_pre_2475_);
lean_closure_set(v___f_2477_, 1, v___f_2473_);
if (v___x_2471_ == 0)
{
lean_object* v___f_2478_; 
lean_dec_ref(v___f_2454_);
v___f_2478_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__18___boxed), 14, 3);
lean_closure_set(v___f_2478_, 0, v_post_2476_);
lean_closure_set(v___f_2478_, 1, v___x_2472_);
lean_closure_set(v___f_2478_, 2, v___f_2462_);
v___y_2457_ = v___f_2477_;
v_post_2458_ = v___f_2478_;
goto v___jp_2456_;
}
else
{
lean_object* v___f_2479_; 
v___f_2479_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__19___boxed), 15, 4);
lean_closure_set(v___f_2479_, 0, v___f_2454_);
lean_closure_set(v___f_2479_, 1, v_post_2476_);
lean_closure_set(v___f_2479_, 2, v___x_2472_);
lean_closure_set(v___f_2479_, 3, v___f_2462_);
v___y_2457_ = v___f_2477_;
v_post_2458_ = v___f_2479_;
goto v___jp_2456_;
}
}
v___jp_2483_:
{
if (v___x_2471_ == 0)
{
lean_object* v___f_2485_; 
lean_dec_ref(v___f_2482_);
v___f_2485_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__21___boxed), 12, 1);
lean_closure_set(v___f_2485_, 0, v_pre_2484_);
v_pre_2475_ = v___f_2485_;
goto v___jp_2474_;
}
else
{
lean_object* v___f_2486_; 
v___f_2486_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__22___boxed), 13, 2);
lean_closure_set(v___f_2486_, 0, v___f_2482_);
lean_closure_set(v___f_2486_, 1, v_pre_2484_);
v_pre_2475_ = v___f_2486_;
goto v___jp_2474_;
}
}
v___jp_2487_:
{
if (v_zetaDelta_2465_ == 0)
{
lean_inc_ref(v_pre_2488_);
v_pre_2484_ = v_pre_2488_;
goto v___jp_2483_;
}
else
{
lean_object* v___f_2489_; 
lean_inc_ref(v_pre_2488_);
v___f_2489_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymMethods___redArg___lam__23___boxed), 12, 1);
lean_closure_set(v___f_2489_, 0, v_pre_2488_);
v_pre_2484_ = v___f_2489_;
goto v___jp_2483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg___boxed(lean_object* v_config_2490_, lean_object* v_thms_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg(v_config_2490_, v_thms_2491_, v_a_2492_);
lean_dec(v_a_2492_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object* v_config_2495_, lean_object* v_thms_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg(v_config_2495_, v_thms_2496_, v_a_2498_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymMethods___boxed(lean_object* v_config_2501_, lean_object* v_thms_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_Meta_Grind_mkNormSymMethods(v_config_2501_, v_thms_2502_, v_a_2503_, v_a_2504_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(lean_object* v_x_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; 
lean_inc_ref(v___y_2508_);
v___x_2519_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v___y_2508_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
if (lean_obj_tag(v_a_2520_) == 0)
{
uint8_t v_done_2521_; 
v_done_2521_ = lean_ctor_get_uint8(v_a_2520_, 0);
lean_dec_ref_known(v_a_2520_, 0);
if (v_done_2521_ == 0)
{
lean_object* v___x_2522_; 
lean_dec_ref_known(v___x_2519_, 1);
v___x_2522_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_2508_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec_ref(v___y_2508_);
return v___x_2522_;
}
else
{
lean_dec_ref(v___y_2508_);
return v___x_2519_;
}
}
else
{
uint8_t v_done_2523_; 
lean_dec_ref(v___y_2508_);
v_done_2523_ = lean_ctor_get_uint8(v_a_2520_, sizeof(void*)*1);
if (v_done_2523_ == 0)
{
lean_object* v_e_x27_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref_known(v___x_2519_, 1);
v_e_x27_2524_ = lean_ctor_get(v_a_2520_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_a_2520_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2526_ = v_a_2520_;
v_isShared_2527_ = v_isSharedCheck_2542_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_e_x27_2524_);
lean_dec(v_a_2520_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2542_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v_e_x27_2524_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
if (lean_obj_tag(v_a_2529_) == 0)
{
lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2540_; 
lean_inc_ref(v_a_2529_);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; 
v_unused_2541_ = lean_ctor_get(v___x_2528_, 0);
lean_dec(v_unused_2541_);
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2540_;
goto v_resetjp_2530_;
}
else
{
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2540_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
uint8_t v_done_2533_; lean_object* v___x_2535_; 
v_done_2533_ = lean_ctor_get_uint8(v_a_2529_, 0);
lean_dec_ref_known(v_a_2529_, 0);
if (v_isShared_2527_ == 0)
{
v___x_2535_ = v___x_2526_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_e_x27_2524_);
v___x_2535_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2537_; 
lean_ctor_set_uint8(v___x_2535_, sizeof(void*)*1, v_done_2533_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v___x_2535_);
v___x_2537_ = v___x_2531_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_del_object(v___x_2526_);
lean_dec_ref(v_e_x27_2524_);
return v___x_2528_;
}
}
else
{
lean_del_object(v___x_2526_);
lean_dec_ref(v_e_x27_2524_);
return v___x_2528_;
}
}
}
else
{
lean_dec_ref_known(v_a_2520_, 1);
return v___x_2519_;
}
}
}
else
{
lean_dec_ref(v___y_2508_);
return v___x_2519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0___boxed(lean_object* v_x_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__0(v_x_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(lean_object* v_x_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___closed__0));
v___x_2572_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_2571_, v___y_2560_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1___boxed(lean_object* v_x_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__1(v_x_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(lean_object* v_dsimp_2586_, lean_object* v___f_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = lean_box(0);
lean_inc_ref(v___y_2588_);
v___x_2600_ = l_Lean_Meta_Sym_DSimp_Decls_toDSimproc(v_dsimp_2586_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
if (lean_obj_tag(v_a_2601_) == 0)
{
uint8_t v_done_2602_; 
v_done_2602_ = lean_ctor_get_uint8(v_a_2601_, 0);
lean_dec_ref_known(v_a_2601_, 0);
if (v_done_2602_ == 0)
{
lean_object* v___x_2603_; 
lean_dec_ref_known(v___x_2600_, 1);
v___x_2603_ = lean_apply_12(v___f_2587_, v___x_2599_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, lean_box(0));
return v___x_2603_;
}
else
{
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec_ref(v___f_2587_);
return v___x_2600_;
}
}
else
{
uint8_t v_done_2604_; 
lean_dec_ref(v___y_2588_);
v_done_2604_ = lean_ctor_get_uint8(v_a_2601_, sizeof(void*)*1);
if (v_done_2604_ == 0)
{
lean_object* v_e_x27_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref_known(v___x_2600_, 1);
v_e_x27_2605_ = lean_ctor_get(v_a_2601_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_a_2601_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2607_ = v_a_2601_;
v_isShared_2608_ = v_isSharedCheck_2623_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_e_x27_2605_);
lean_dec(v_a_2601_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2623_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; 
lean_inc_ref(v_e_x27_2605_);
v___x_2609_ = lean_apply_12(v___f_2587_, v___x_2599_, v_e_x27_2605_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, lean_box(0));
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
if (lean_obj_tag(v_a_2610_) == 0)
{
lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2621_; 
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; 
v_unused_2622_ = lean_ctor_get(v___x_2609_, 0);
lean_dec(v_unused_2622_);
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2621_;
goto v_resetjp_2611_;
}
else
{
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2621_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
uint8_t v_done_2614_; lean_object* v___x_2616_; 
v_done_2614_ = lean_ctor_get_uint8(v_a_2610_, 0);
lean_dec_ref_known(v_a_2610_, 0);
if (v_isShared_2608_ == 0)
{
v___x_2616_ = v___x_2607_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_e_x27_2605_);
v___x_2616_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2618_; 
lean_ctor_set_uint8(v___x_2616_, sizeof(void*)*1, v_done_2614_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___x_2616_);
v___x_2618_ = v___x_2612_;
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
else
{
lean_dec_ref_known(v_a_2610_, 1);
lean_del_object(v___x_2607_);
lean_dec_ref(v_e_x27_2605_);
return v___x_2609_;
}
}
else
{
lean_del_object(v___x_2607_);
lean_dec_ref(v_e_x27_2605_);
return v___x_2609_;
}
}
}
else
{
lean_dec_ref_known(v_a_2601_, 1);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___f_2587_);
return v___x_2600_;
}
}
}
else
{
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec_ref(v___f_2587_);
return v___x_2600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed(lean_object* v_dsimp_2624_, lean_object* v___f_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2(v_dsimp_2624_, v___f_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec_ref(v_dsimp_2624_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(lean_object* v_pre_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___x_2650_; 
lean_inc(v___y_2648_);
lean_inc_ref(v___y_2647_);
lean_inc(v___y_2646_);
lean_inc_ref(v___y_2645_);
lean_inc(v___y_2644_);
lean_inc_ref(v___y_2643_);
lean_inc_ref(v___y_2639_);
v___x_2650_ = lean_apply_11(v_pre_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, lean_box(0));
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
if (lean_obj_tag(v_a_2651_) == 0)
{
uint8_t v_done_2652_; 
v_done_2652_ = lean_ctor_get_uint8(v_a_2651_, 0);
lean_dec_ref_known(v_a_2651_, 0);
if (v_done_2652_ == 0)
{
lean_object* v___x_2653_; 
lean_dec_ref_known(v___x_2650_, 1);
v___x_2653_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_2639_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
return v___x_2653_;
}
else
{
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec_ref(v___y_2639_);
return v___x_2650_;
}
}
else
{
uint8_t v_done_2654_; 
lean_dec_ref(v___y_2639_);
v_done_2654_ = lean_ctor_get_uint8(v_a_2651_, sizeof(void*)*1);
if (v_done_2654_ == 0)
{
lean_object* v_e_x27_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref_known(v___x_2650_, 1);
v_e_x27_2655_ = lean_ctor_get(v_a_2651_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_a_2651_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2657_ = v_a_2651_;
v_isShared_2658_ = v_isSharedCheck_2673_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_e_x27_2655_);
lean_dec(v_a_2651_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2673_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; 
lean_inc_ref(v_e_x27_2655_);
v___x_2659_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_x27_2655_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
if (lean_obj_tag(v_a_2660_) == 0)
{
lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2671_; 
lean_inc_ref(v_a_2660_);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; 
v_unused_2672_ = lean_ctor_get(v___x_2659_, 0);
lean_dec(v_unused_2672_);
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2671_;
goto v_resetjp_2661_;
}
else
{
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2671_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
uint8_t v_done_2664_; lean_object* v___x_2666_; 
v_done_2664_ = lean_ctor_get_uint8(v_a_2660_, 0);
lean_dec_ref_known(v_a_2660_, 0);
if (v_isShared_2658_ == 0)
{
v___x_2666_ = v___x_2657_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_e_x27_2655_);
v___x_2666_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2668_; 
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*1, v_done_2664_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2666_);
v___x_2668_ = v___x_2662_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
else
{
lean_del_object(v___x_2657_);
lean_dec_ref(v_e_x27_2655_);
return v___x_2659_;
}
}
else
{
lean_del_object(v___x_2657_);
lean_dec_ref(v_e_x27_2655_);
return v___x_2659_;
}
}
}
else
{
lean_dec_ref_known(v_a_2651_, 1);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
return v___x_2650_;
}
}
}
else
{
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec_ref(v___y_2639_);
return v___x_2650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed(lean_object* v_pre_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3(v_pre_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(lean_object* v___f_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_box(0);
lean_inc_ref(v___y_2688_);
v___x_2700_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_2688_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
if (lean_obj_tag(v_a_2701_) == 0)
{
uint8_t v_done_2702_; 
v_done_2702_ = lean_ctor_get_uint8(v_a_2701_, 0);
lean_dec_ref_known(v_a_2701_, 0);
if (v_done_2702_ == 0)
{
lean_object* v___x_2703_; 
lean_dec_ref_known(v___x_2700_, 1);
v___x_2703_ = lean_apply_12(v___f_2687_, v___x_2699_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
return v___x_2703_;
}
else
{
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec_ref(v___f_2687_);
return v___x_2700_;
}
}
else
{
uint8_t v_done_2704_; 
lean_dec_ref(v___y_2688_);
v_done_2704_ = lean_ctor_get_uint8(v_a_2701_, sizeof(void*)*1);
if (v_done_2704_ == 0)
{
lean_object* v_e_x27_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2723_; 
lean_dec_ref_known(v___x_2700_, 1);
v_e_x27_2705_ = lean_ctor_get(v_a_2701_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_a_2701_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2707_ = v_a_2701_;
v_isShared_2708_ = v_isSharedCheck_2723_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_e_x27_2705_);
lean_dec(v_a_2701_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2723_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; 
lean_inc_ref(v_e_x27_2705_);
v___x_2709_ = lean_apply_12(v___f_2687_, v___x_2699_, v_e_x27_2705_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, lean_box(0));
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
if (lean_obj_tag(v_a_2710_) == 0)
{
lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2721_; 
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2721_ == 0)
{
lean_object* v_unused_2722_; 
v_unused_2722_ = lean_ctor_get(v___x_2709_, 0);
lean_dec(v_unused_2722_);
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2721_;
goto v_resetjp_2711_;
}
else
{
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2721_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
uint8_t v_done_2714_; lean_object* v___x_2716_; 
v_done_2714_ = lean_ctor_get_uint8(v_a_2710_, 0);
lean_dec_ref_known(v_a_2710_, 0);
if (v_isShared_2708_ == 0)
{
v___x_2716_ = v___x_2707_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_e_x27_2705_);
v___x_2716_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_object* v___x_2718_; 
lean_ctor_set_uint8(v___x_2716_, sizeof(void*)*1, v_done_2714_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2716_);
v___x_2718_ = v___x_2712_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2710_, 1);
lean_del_object(v___x_2707_);
lean_dec_ref(v_e_x27_2705_);
return v___x_2709_;
}
}
else
{
lean_del_object(v___x_2707_);
lean_dec_ref(v_e_x27_2705_);
return v___x_2709_;
}
}
}
else
{
lean_dec_ref_known(v_a_2701_, 1);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___f_2687_);
return v___x_2700_;
}
}
}
else
{
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec_ref(v___f_2687_);
return v___x_2700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4___boxed(lean_object* v___f_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__4(v___f_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(lean_object* v___f_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v___y_2750_; lean_object* v_e_x27_2751_; uint8_t v_done_2752_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = lean_box(0);
lean_inc_ref(v___y_2738_);
v___x_2766_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_2738_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
if (lean_obj_tag(v_a_2767_) == 0)
{
uint8_t v_done_2768_; 
v_done_2768_ = lean_ctor_get_uint8(v_a_2767_, 0);
lean_dec_ref_known(v_a_2767_, 0);
if (v_done_2768_ == 0)
{
lean_object* v___x_2769_; 
lean_dec_ref_known(v___x_2766_, 1);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2744_);
lean_inc(v___y_2743_);
lean_inc_ref(v___y_2742_);
lean_inc_ref(v___y_2738_);
v___x_2769_ = lean_apply_12(v___f_2737_, v___x_2765_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, lean_box(0));
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
if (lean_obj_tag(v_a_2770_) == 0)
{
uint8_t v_done_2771_; 
v_done_2771_ = lean_ctor_get_uint8(v_a_2770_, 0);
lean_dec_ref_known(v_a_2770_, 0);
if (v_done_2771_ == 0)
{
lean_object* v___x_2772_; 
lean_dec_ref_known(v___x_2769_, 1);
v___x_2772_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_2738_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v___x_2772_;
}
else
{
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v___y_2738_);
return v___x_2769_;
}
}
else
{
lean_object* v_e_x27_2773_; uint8_t v_done_2774_; 
lean_dec_ref(v___y_2738_);
v_e_x27_2773_ = lean_ctor_get(v_a_2770_, 0);
lean_inc_ref(v_e_x27_2773_);
v_done_2774_ = lean_ctor_get_uint8(v_a_2770_, sizeof(void*)*1);
lean_dec_ref_known(v_a_2770_, 1);
v___y_2750_ = v___x_2769_;
v_e_x27_2751_ = v_e_x27_2773_;
v_done_2752_ = v_done_2774_;
goto v___jp_2749_;
}
}
else
{
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v___y_2738_);
return v___x_2769_;
}
}
else
{
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v___f_2737_);
return v___x_2766_;
}
}
else
{
uint8_t v_done_2775_; 
lean_dec_ref(v___y_2738_);
v_done_2775_ = lean_ctor_get_uint8(v_a_2767_, sizeof(void*)*1);
if (v_done_2775_ == 0)
{
lean_object* v_e_x27_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2796_; 
lean_dec_ref_known(v___x_2766_, 1);
v_e_x27_2776_ = lean_ctor_get(v_a_2767_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_a_2767_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2778_ = v_a_2767_;
v_isShared_2779_ = v_isSharedCheck_2796_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_e_x27_2776_);
lean_dec(v_a_2767_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2796_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; 
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2744_);
lean_inc(v___y_2743_);
lean_inc_ref(v___y_2742_);
lean_inc_ref(v_e_x27_2776_);
v___x_2780_ = lean_apply_12(v___f_2737_, v___x_2765_, v_e_x27_2776_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, lean_box(0));
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
if (lean_obj_tag(v_a_2781_) == 0)
{
lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2792_; 
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; 
v_unused_2793_ = lean_ctor_get(v___x_2780_, 0);
lean_dec(v_unused_2793_);
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2792_;
goto v_resetjp_2782_;
}
else
{
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2792_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
uint8_t v_done_2785_; lean_object* v___x_2787_; 
v_done_2785_ = lean_ctor_get_uint8(v_a_2781_, 0);
lean_dec_ref_known(v_a_2781_, 0);
lean_inc_ref(v_e_x27_2776_);
if (v_isShared_2779_ == 0)
{
v___x_2787_ = v___x_2778_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_e_x27_2776_);
v___x_2787_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; 
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*1, v_done_2785_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2787_);
v___x_2789_ = v___x_2783_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
v___y_2750_ = v___x_2789_;
v_e_x27_2751_ = v_e_x27_2776_;
v_done_2752_ = v_done_2785_;
goto v___jp_2749_;
}
}
}
}
else
{
lean_object* v_e_x27_2794_; uint8_t v_done_2795_; 
lean_del_object(v___x_2778_);
lean_dec_ref(v_e_x27_2776_);
v_e_x27_2794_ = lean_ctor_get(v_a_2781_, 0);
lean_inc_ref(v_e_x27_2794_);
v_done_2795_ = lean_ctor_get_uint8(v_a_2781_, sizeof(void*)*1);
lean_dec_ref_known(v_a_2781_, 1);
v___y_2750_ = v___x_2780_;
v_e_x27_2751_ = v_e_x27_2794_;
v_done_2752_ = v_done_2795_;
goto v___jp_2749_;
}
}
else
{
lean_del_object(v___x_2778_);
lean_dec_ref(v_e_x27_2776_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v___x_2780_;
}
}
}
else
{
lean_dec_ref_known(v_a_2767_, 1);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___f_2737_);
return v___x_2766_;
}
}
}
else
{
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v___f_2737_);
return v___x_2766_;
}
v___jp_2749_:
{
if (v_done_2752_ == 0)
{
lean_object* v___x_2753_; 
lean_dec_ref(v___y_2750_);
lean_inc_ref(v_e_x27_2751_);
v___x_2753_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v_e_x27_2751_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
if (lean_obj_tag(v_a_2754_) == 0)
{
lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2763_; 
lean_inc_ref(v_a_2754_);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2763_ == 0)
{
lean_object* v_unused_2764_; 
v_unused_2764_ = lean_ctor_get(v___x_2753_, 0);
lean_dec(v_unused_2764_);
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2763_;
goto v_resetjp_2755_;
}
else
{
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2763_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
uint8_t v_done_2758_; lean_object* v___x_2759_; lean_object* v___x_2761_; 
v_done_2758_ = lean_ctor_get_uint8(v_a_2754_, 0);
lean_dec_ref_known(v_a_2754_, 0);
v___x_2759_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_2759_, 0, v_e_x27_2751_);
lean_ctor_set_uint8(v___x_2759_, sizeof(void*)*1, v_done_2758_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___x_2759_);
v___x_2761_ = v___x_2756_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
else
{
lean_dec_ref(v_e_x27_2751_);
return v___x_2753_;
}
}
else
{
lean_dec_ref(v_e_x27_2751_);
return v___x_2753_;
}
}
else
{
lean_dec_ref(v_e_x27_2751_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v___y_2750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5___boxed(lean_object* v___f_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__5(v___f_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods(lean_object* v_config_2816_, lean_object* v_thms_2817_){
_start:
{
uint8_t v_zetaDelta_2818_; uint8_t v_zeta_2819_; lean_object* v___f_2820_; lean_object* v_pre_2822_; lean_object* v_pre_2827_; 
v_zetaDelta_2818_ = lean_ctor_get_uint8(v_config_2816_, sizeof(void*)*18 + 19);
v_zeta_2819_ = lean_ctor_get_uint8(v_config_2816_, sizeof(void*)*18 + 20);
v___f_2820_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__1));
if (v_zeta_2819_ == 0)
{
lean_object* v_pre_2829_; 
v_pre_2829_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__2));
v_pre_2827_ = v_pre_2829_;
goto v___jp_2826_;
}
else
{
lean_object* v_pre_2830_; 
v_pre_2830_ = ((lean_object*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___closed__3));
v_pre_2827_ = v_pre_2830_;
goto v___jp_2826_;
}
v___jp_2821_:
{
lean_object* v_dsimp_2823_; lean_object* v_post_2824_; lean_object* v___x_2825_; 
v_dsimp_2823_ = lean_ctor_get(v_thms_2817_, 2);
lean_inc_ref(v_dsimp_2823_);
lean_dec_ref(v_thms_2817_);
v_post_2824_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__2___boxed), 13, 2);
lean_closure_set(v_post_2824_, 0, v_dsimp_2823_);
lean_closure_set(v_post_2824_, 1, v___f_2820_);
v___x_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2825_, 0, v_pre_2822_);
lean_ctor_set(v___x_2825_, 1, v_post_2824_);
return v___x_2825_;
}
v___jp_2826_:
{
if (v_zetaDelta_2818_ == 0)
{
lean_inc_ref(v_pre_2827_);
v_pre_2822_ = v_pre_2827_;
goto v___jp_2821_;
}
else
{
lean_object* v_pre_2828_; 
lean_inc_ref(v_pre_2827_);
v_pre_2828_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkNormSymDSimpMethods___lam__3___boxed), 12, 1);
lean_closure_set(v_pre_2828_, 0, v_pre_2827_);
v_pre_2822_ = v_pre_2828_;
goto v___jp_2821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkNormSymDSimpMethods___boxed(lean_object* v_config_2831_, lean_object* v_thms_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_config_2831_, v_thms_2832_);
lean_dec_ref(v_config_2831_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(lean_object* v_e_2834_, lean_object* v___y_2835_){
_start:
{
uint8_t v___x_2837_; 
v___x_2837_ = l_Lean_Expr_hasMVar(v_e_2834_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; 
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_e_2834_);
return v___x_2838_;
}
else
{
lean_object* v___x_2839_; lean_object* v_mctx_2840_; lean_object* v___x_2841_; lean_object* v_fst_2842_; lean_object* v_snd_2843_; lean_object* v___x_2844_; lean_object* v_cache_2845_; lean_object* v_zetaDeltaFVarIds_2846_; lean_object* v_postponed_2847_; lean_object* v_diag_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2857_; 
v___x_2839_ = lean_st_ref_get(v___y_2835_);
v_mctx_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc_ref(v_mctx_2840_);
lean_dec(v___x_2839_);
v___x_2841_ = l_Lean_instantiateMVarsCore(v_mctx_2840_, v_e_2834_);
v_fst_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_fst_2842_);
v_snd_2843_ = lean_ctor_get(v___x_2841_, 1);
lean_inc(v_snd_2843_);
lean_dec_ref(v___x_2841_);
v___x_2844_ = lean_st_ref_take(v___y_2835_);
v_cache_2845_ = lean_ctor_get(v___x_2844_, 1);
v_zetaDeltaFVarIds_2846_ = lean_ctor_get(v___x_2844_, 2);
v_postponed_2847_ = lean_ctor_get(v___x_2844_, 3);
v_diag_2848_ = lean_ctor_get(v___x_2844_, 4);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v___x_2844_, 0);
lean_dec(v_unused_2858_);
v___x_2850_ = v___x_2844_;
v_isShared_2851_ = v_isSharedCheck_2857_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_diag_2848_);
lean_inc(v_postponed_2847_);
lean_inc(v_zetaDeltaFVarIds_2846_);
lean_inc(v_cache_2845_);
lean_dec(v___x_2844_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2857_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v_snd_2843_);
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_snd_2843_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_cache_2845_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_zetaDeltaFVarIds_2846_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_postponed_2847_);
lean_ctor_set(v_reuseFailAlloc_2856_, 4, v_diag_2848_);
v___x_2853_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_st_ref_put(v___y_2835_, v___x_2853_);
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v_fst_2842_);
return v___x_2855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg___boxed(lean_object* v_e_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2859_, v___y_2860_);
lean_dec(v___y_2860_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(lean_object* v_e_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2863_, v___y_2870_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___boxed(lean_object* v_e_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0(v_e_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy(lean_object* v_e_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v_a_2899_; lean_object* v___x_2900_; 
v___x_2898_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_normLegacy_spec__0___redArg(v_e_2887_, v_a_2894_);
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref(v___x_2898_);
v___x_2900_ = l_Lean_Meta_Grind_simpCore(v_a_2899_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v_expr_2902_; lean_object* v_proof_x3f_2903_; uint8_t v_cache_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2928_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2900_, 1);
v_expr_2902_ = lean_ctor_get(v_a_2901_, 0);
v_proof_x3f_2903_ = lean_ctor_get(v_a_2901_, 1);
v_cache_2904_ = lean_ctor_get_uint8(v_a_2901_, sizeof(void*)*2);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_a_2901_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2906_ = v_a_2901_;
v_isShared_2907_ = v_isSharedCheck_2928_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_proof_x3f_2903_);
lean_inc(v_expr_2902_);
lean_dec(v_a_2901_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2928_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_expr_2902_, v_a_2895_, v_a_2896_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2919_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2911_ = v___x_2908_;
v_isShared_2912_ = v_isSharedCheck_2919_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2908_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2919_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v_a_2909_);
v___x_2914_ = v___x_2906_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2909_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_proof_x3f_2903_);
lean_ctor_set_uint8(v_reuseFailAlloc_2918_, sizeof(void*)*2, v_cache_2904_);
v___x_2914_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2916_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v___x_2914_);
v___x_2916_ = v___x_2911_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_del_object(v___x_2906_);
lean_dec(v_proof_x3f_2903_);
v_a_2920_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2908_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2908_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
else
{
return v___x_2900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normLegacy___boxed(lean_object* v_e_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Lean_Meta_Grind_normLegacy(v_e_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
lean_dec(v_a_2930_);
return v_res_2940_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__0(void){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2941_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__1(void){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__0, &l_Lean_Meta_Grind_normSym___redArg___closed__0_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__0);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
return v___x_2943_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__2(void){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__1, &l_Lean_Meta_Grind_normSym___redArg___closed__1_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__1);
v___x_2945_ = lean_unsigned_to_nat(0u);
v___x_2946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
lean_ctor_set(v___x_2946_, 1, v___x_2944_);
lean_ctor_set(v___x_2946_, 2, v___x_2944_);
lean_ctor_set(v___x_2946_, 3, v___x_2944_);
return v___x_2946_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normSym___redArg___closed__3(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__1, &l_Lean_Meta_Grind_normSym___redArg___closed__1_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__1);
v___x_2948_ = lean_unsigned_to_nat(0u);
v___x_2949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v___x_2947_);
lean_ctor_set(v___x_2949_, 2, v___x_2947_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg(lean_object* v_e_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v___x_2959_; lean_object* v_a_2960_; lean_object* v___x_2961_; 
v___x_2959_ = l_Lean_Meta_Grind_getNormSymTheorems___redArg(v_a_2957_);
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref(v___x_2959_);
v___x_2961_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2951_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2963_; lean_object* v_a_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc_n(v_a_2962_, 2);
lean_dec_ref_known(v___x_2961_, 1);
lean_inc(v_a_2960_);
v___x_2963_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg(v_a_2962_, v_a_2960_, v_a_2957_);
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref(v___x_2963_);
v___x_2965_ = l_Lean_Meta_Grind_mkNormSymDSimpMethods(v_a_2962_, v_a_2960_);
lean_dec(v_a_2962_);
v___x_2966_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__2, &l_Lean_Meta_Grind_normSym___redArg___closed__2_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__2);
v___x_2967_ = lean_obj_once(&l_Lean_Meta_Grind_normSym___redArg___closed__3, &l_Lean_Meta_Grind_normSym___redArg___closed__3_once, _init_l_Lean_Meta_Grind_normSym___redArg___closed__3);
v___x_2968_ = l_Lean_Meta_Grind_symNorm(v_e_2950_, v_a_2964_, v___x_2965_, v___x_2966_, v___x_2967_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2977_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2971_ = v___x_2968_;
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v_fst_2973_; lean_object* v___x_2975_; 
v_fst_2973_ = lean_ctor_get(v_a_2969_, 0);
lean_inc(v_fst_2973_);
lean_dec(v_a_2969_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 0, v_fst_2973_);
v___x_2975_ = v___x_2971_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_fst_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
v_a_2978_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2968_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2968_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec(v_a_2960_);
lean_dec_ref(v_e_2950_);
v_a_2986_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2961_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2961_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___redArg___boxed(lean_object* v_e_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_Meta_Grind_normSym___redArg(v_e_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_);
lean_dec(v_a_3001_);
lean_dec_ref(v_a_3000_);
lean_dec(v_a_2999_);
lean_dec_ref(v_a_2998_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec_ref(v_a_2995_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym(lean_object* v_e_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_Meta_Grind_normSym___redArg(v_e_3004_, v_a_3006_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normSym___boxed(lean_object* v_e_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_Meta_Grind_normSym(v_e_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
return v_res_3027_;
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
