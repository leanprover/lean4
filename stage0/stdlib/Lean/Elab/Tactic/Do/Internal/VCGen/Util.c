// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Util
// Imports: public import Lean.Meta.Tactic.Grind.Main public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.Reduce public import Lean.Meta.Sym.AlphaShareBuilder public import Lean.Meta.Sym.Intro public import Lean.Meta.Sym.Simp.Goal public import Lean.Meta.Sym.Simp.Telescope public import Lean.Meta.Sym.Util
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
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqS(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_processHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "[mvcgen' +debug] BackwardRule "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " failed to apply to:"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "\nbut succeeded after `unfoldReducible`-normalization to:"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 116, .m_capacity = 116, .m_length = 115, .m_data = "\nAn earlier step is missing a normalization. Re-run with `set_option pp.all true` to see the structural difference."};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "<rule constructed from expression>"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Util_0__Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_collectBinders(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___boxed(lean_object**);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simpTelescope___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "solveTrivialConjuncts: failed to apply "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " to"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__14;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "left"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(12, 252, 227, 83, 88, 185, 40, 148)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__17;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "right"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(18, 204, 165, 192, 253, 41, 237, 145)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__20;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__22;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(lean_object* v___y_1_, lean_object* v_mctx_2_, lean_object* v_cache_3_, lean_object* v_a_x3f_4_){
_start:
{
lean_object* v___x_6_; lean_object* v_zetaDeltaFVarIds_7_; lean_object* v_postponed_8_; lean_object* v_diag_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_19_; 
v___x_6_ = lean_st_ref_take(v___y_1_);
v_zetaDeltaFVarIds_7_ = lean_ctor_get(v___x_6_, 2);
v_postponed_8_ = lean_ctor_get(v___x_6_, 3);
v_diag_9_ = lean_ctor_get(v___x_6_, 4);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_6_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; lean_object* v_unused_21_; 
v_unused_20_ = lean_ctor_get(v___x_6_, 1);
lean_dec(v_unused_20_);
v_unused_21_ = lean_ctor_get(v___x_6_, 0);
lean_dec(v_unused_21_);
v___x_11_ = v___x_6_;
v_isShared_12_ = v_isSharedCheck_19_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_diag_9_);
lean_inc(v_postponed_8_);
lean_inc(v_zetaDeltaFVarIds_7_);
lean_dec(v___x_6_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_19_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v_cache_3_);
lean_ctor_set(v___x_11_, 0, v_mctx_2_);
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_mctx_2_);
lean_ctor_set(v_reuseFailAlloc_18_, 1, v_cache_3_);
lean_ctor_set(v_reuseFailAlloc_18_, 2, v_zetaDeltaFVarIds_7_);
lean_ctor_set(v_reuseFailAlloc_18_, 3, v_postponed_8_);
lean_ctor_set(v_reuseFailAlloc_18_, 4, v_diag_9_);
v___x_14_ = v_reuseFailAlloc_18_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_st_ref_set(v___y_1_, v___x_14_);
v___x_16_ = lean_box(0);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(lean_object* v___y_22_, lean_object* v_mctx_23_, lean_object* v_cache_24_, lean_object* v_a_x3f_25_, lean_object* v___y_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_22_, v_mctx_23_, v_cache_24_, v_a_x3f_25_);
lean_dec(v_a_x3f_25_);
lean_dec(v___y_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(lean_object* v_x_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v_mctx_43_; lean_object* v_cache_44_; lean_object* v___x_45_; 
v___x_41_ = lean_st_ref_get(v___y_37_);
v___x_42_ = lean_st_ref_get(v___y_37_);
v_mctx_43_ = lean_ctor_get(v___x_41_, 0);
lean_inc_ref(v_mctx_43_);
lean_dec(v___x_41_);
v_cache_44_ = lean_ctor_get(v___x_42_, 1);
lean_inc_ref(v_cache_44_);
lean_dec(v___x_42_);
lean_inc(v___y_39_);
lean_inc_ref(v___y_38_);
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
lean_inc(v___y_31_);
lean_inc(v___y_30_);
lean_inc_ref(v___y_29_);
v___x_45_ = lean_apply_12(v_x_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, lean_box(0));
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_62_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_62_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_62_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_62_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
lean_inc(v_a_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 1);
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_61_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
v___x_52_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_37_, v_mctx_43_, v_cache_44_, v___x_51_);
lean_dec_ref(v___x_51_);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_59_ == 0)
{
lean_object* v_unused_60_; 
v_unused_60_ = lean_ctor_get(v___x_52_, 0);
lean_dec(v_unused_60_);
v___x_54_ = v___x_52_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_dec(v___x_52_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v_a_46_);
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_46_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
}
else
{
lean_object* v_a_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
v_a_63_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_a_63_);
lean_dec_ref_known(v___x_45_, 1);
v___x_64_ = lean_box(0);
v___x_65_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_37_, v_mctx_43_, v_cache_44_, v___x_64_);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_72_ == 0)
{
lean_object* v_unused_73_; 
v_unused_73_ = lean_ctor_get(v___x_65_, 0);
lean_dec(v_unused_73_);
v___x_67_ = v___x_65_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_dec(v___x_65_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set_tag(v___x_67_, 1);
lean_ctor_set(v___x_67_, 0, v_a_63_);
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_63_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(lean_object* v_x_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_object* v_00_u03b1_88_, lean_object* v_x_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(lean_object* v_00_u03b1_103_, lean_object* v_x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(v_00_u03b1_103_, v_x_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(lean_object* v_a_118_, lean_object* v___x_119_, lean_object* v_rule_120_, uint8_t v___x_121_, uint8_t v_debug_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_118_, v___x_119_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
v___x_137_ = l_Lean_Expr_mvarId_x21(v_a_136_);
lean_dec(v_a_136_);
v___x_138_ = l_Lean_Meta_Sym_BackwardRule_apply(v___x_137_, v_rule_120_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_151_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_151_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
if (lean_obj_tag(v_a_139_) == 0)
{
lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_143_ = lean_box(v___x_121_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_143_);
v___x_145_ = v___x_141_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec_ref_known(v_a_139_, 1);
v___x_147_ = lean_box(v_debug_122_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_147_);
v___x_149_ = v___x_141_;
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
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_138_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_138_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec_ref(v_rule_120_);
v_a_160_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_135_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_135_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(lean_object** _args){
lean_object* v_a_168_ = _args[0];
lean_object* v___x_169_ = _args[1];
lean_object* v_rule_170_ = _args[2];
lean_object* v___x_171_ = _args[3];
lean_object* v_debug_172_ = _args[4];
lean_object* v___y_173_ = _args[5];
lean_object* v___y_174_ = _args[6];
lean_object* v___y_175_ = _args[7];
lean_object* v___y_176_ = _args[8];
lean_object* v___y_177_ = _args[9];
lean_object* v___y_178_ = _args[10];
lean_object* v___y_179_ = _args[11];
lean_object* v___y_180_ = _args[12];
lean_object* v___y_181_ = _args[13];
lean_object* v___y_182_ = _args[14];
lean_object* v___y_183_ = _args[15];
lean_object* v___y_184_ = _args[16];
_start:
{
uint8_t v___x_43892__boxed_185_; uint8_t v_debug_boxed_186_; lean_object* v_res_187_; 
v___x_43892__boxed_185_ = lean_unbox(v___x_171_);
v_debug_boxed_186_ = lean_unbox(v_debug_172_);
v_res_187_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(v_a_168_, v___x_169_, v_rule_170_, v___x_43892__boxed_185_, v_debug_boxed_186_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(lean_object* v_msgData_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; lean_object* v_env_195_; lean_object* v___x_196_; lean_object* v_mctx_197_; lean_object* v_lctx_198_; lean_object* v_options_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_194_ = lean_st_ref_get(v___y_192_);
v_env_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc_ref(v_env_195_);
lean_dec(v___x_194_);
v___x_196_ = lean_st_ref_get(v___y_190_);
v_mctx_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc_ref(v_mctx_197_);
lean_dec(v___x_196_);
v_lctx_198_ = lean_ctor_get(v___y_189_, 2);
v_options_199_ = lean_ctor_get(v___y_191_, 2);
lean_inc_ref(v_options_199_);
lean_inc_ref(v_lctx_198_);
v___x_200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_200_, 0, v_env_195_);
lean_ctor_set(v___x_200_, 1, v_mctx_197_);
lean_ctor_set(v___x_200_, 2, v_lctx_198_);
lean_ctor_set(v___x_200_, 3, v_options_199_);
v___x_201_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v_msgData_188_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1___boxed(lean_object* v_msgData_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msgData_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(lean_object* v_msg_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_ref_216_; lean_object* v___x_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_226_; 
v_ref_216_ = lean_ctor_get(v___y_213_, 5);
v___x_217_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msg_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_226_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
lean_inc(v_ref_216_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_ref_216_);
lean_ctor_set(v___x_222_, 1, v_a_218_);
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 1);
lean_ctor_set(v___x_220_, 0, v___x_222_);
v___x_224_ = v___x_220_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
return v_res_233_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0));
v___x_236_ = l_Lean_stringToMessageData(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2));
v___x_239_ = l_Lean_stringToMessageData(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4));
v___x_242_ = l_Lean_stringToMessageData(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6));
v___x_245_ = l_Lean_stringToMessageData(v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8));
v___x_248_ = l_Lean_stringToMessageData(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object* v_rule_252_, lean_object* v_goal_253_, lean_object* v_ruleDesc_x3f_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; 
lean_inc_ref(v_rule_252_);
lean_inc(v_goal_253_);
v___x_267_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_253_, v_rule_252_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
if (lean_obj_tag(v_a_268_) == 0)
{
uint8_t v_debug_269_; 
v_debug_269_ = lean_ctor_get_uint8(v_a_255_, sizeof(void*)*4 + 3);
if (v_debug_269_ == 0)
{
lean_dec(v_ruleDesc_x3f_254_);
lean_dec(v_goal_253_);
lean_dec_ref(v_rule_252_);
return v___x_267_;
}
else
{
lean_object* v___x_270_; 
lean_dec_ref_known(v___x_267_, 1);
v___x_270_ = l_Lean_MVarId_getType(v_goal_253_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_n(v_a_271_, 2);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = l_Lean_Meta_Sym_unfoldReducible(v_a_271_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_335_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_335_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_335_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_335_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
uint8_t v___x_277_; 
v___x_277_ = lean_expr_eqv(v_a_273_, v_a_271_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___f_281_; lean_object* v___x_282_; 
lean_del_object(v___x_275_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_box(v___x_277_);
v___x_280_ = lean_box(v_debug_269_);
lean_inc_ref(v_rule_252_);
lean_inc(v_a_273_);
v___f_281_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed), 17, 5);
lean_closure_set(v___f_281_, 0, v_a_273_);
lean_closure_set(v___f_281_, 1, v___x_278_);
lean_closure_set(v___f_281_, 2, v_rule_252_);
lean_closure_set(v___f_281_, 3, v___x_279_);
lean_closure_set(v___f_281_, 4, v___x_280_);
v___x_282_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v___f_281_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_323_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_323_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_323_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_323_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___y_288_; uint8_t v___x_310_; 
v___x_310_ = lean_unbox(v_a_283_);
lean_dec(v_a_283_);
if (v___x_310_ == 0)
{
lean_object* v___x_312_; 
lean_dec(v_a_273_);
lean_dec(v_a_271_);
lean_dec(v_ruleDesc_x3f_254_);
lean_dec_ref(v_rule_252_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v_a_268_);
v___x_312_ = v___x_285_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_268_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_del_object(v___x_285_);
if (lean_obj_tag(v_ruleDesc_x3f_254_) == 0)
{
lean_object* v_expr_314_; lean_object* v___x_315_; 
v_expr_314_ = lean_ctor_get(v_rule_252_, 0);
lean_inc_ref(v_expr_314_);
lean_dec_ref(v_rule_252_);
v___x_315_ = l_Lean_Expr_getAppFn(v_expr_314_);
lean_dec_ref(v_expr_314_);
if (lean_obj_tag(v___x_315_) == 4)
{
lean_object* v_declName_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_declName_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_declName_316_);
lean_dec_ref_known(v___x_315_, 2);
v___x_317_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9);
v___x_318_ = l_Lean_MessageData_ofConstName(v_declName_316_, v___x_277_);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_317_);
v___y_288_ = v___x_320_;
goto v___jp_287_;
}
else
{
lean_object* v___x_321_; 
lean_dec_ref(v___x_315_);
v___x_321_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11);
v___y_288_ = v___x_321_;
goto v___jp_287_;
}
}
else
{
lean_object* v_val_322_; 
lean_dec_ref(v_rule_252_);
v_val_322_ = lean_ctor_get(v_ruleDesc_x3f_254_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v_ruleDesc_x3f_254_, 1);
v___y_288_ = v_val_322_;
goto v___jp_287_;
}
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v___x_289_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1);
v___x_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___y_288_);
v___x_291_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = l_Lean_indentExpr(v_a_271_);
v___x_294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_indentExpr(v_a_273_);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_300_, v_a_262_, v_a_263_, v_a_264_, v_a_265_);
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_a_273_);
lean_dec(v_a_271_);
lean_dec(v_ruleDesc_x3f_254_);
lean_dec_ref(v_rule_252_);
v_a_324_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_282_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_282_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v___x_333_; 
lean_dec(v_a_273_);
lean_dec(v_a_271_);
lean_dec(v_ruleDesc_x3f_254_);
lean_dec_ref(v_rule_252_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v_a_268_);
v___x_333_ = v___x_275_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_268_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v_a_271_);
lean_dec(v_ruleDesc_x3f_254_);
lean_dec_ref(v_rule_252_);
v_a_336_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_272_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_272_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_ruleDesc_x3f_254_);
lean_dec_ref(v_rule_252_);
v_a_344_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_270_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_270_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_a_268_, 1);
lean_dec(v_ruleDesc_x3f_254_);
lean_dec(v_goal_253_);
lean_dec_ref(v_rule_252_);
return v___x_267_;
}
}
else
{
lean_dec(v_ruleDesc_x3f_254_);
lean_dec(v_goal_253_);
lean_dec_ref(v_rule_252_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object* v_rule_352_, lean_object* v_goal_353_, lean_object* v_ruleDesc_x3f_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_352_, v_goal_353_, v_ruleDesc_x3f_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object* v_00_u03b1_368_, lean_object* v_msg_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_369_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object* v_00_u03b1_383_, lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(v_00_u03b1_383_, v_msg_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(lean_object* v_goal_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
uint8_t v_internalize_410_; 
v_internalize_410_ = lean_ctor_get_uint8(v_a_399_, sizeof(void*)*4 + 4);
if (v_internalize_410_ == 0)
{
lean_object* v___x_411_; 
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v_goal_398_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_box(0);
v___x_413_ = l_Lean_Meta_Grind_processHypotheses(v_goal_398_, v___x_412_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg___boxed(lean_object* v_goal_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(v_goal_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses(lean_object* v_goal_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(v_goal_427_, v_a_428_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___boxed(lean_object* v_goal_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses(v_goal_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Util_0__Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_collectBinders(lean_object* v_type_455_, lean_object* v_acc_456_){
_start:
{
switch(lean_obj_tag(v_type_455_))
{
case 7:
{
lean_object* v_binderName_457_; lean_object* v_body_458_; lean_object* v___x_459_; 
v_binderName_457_ = lean_ctor_get(v_type_455_, 0);
lean_inc(v_binderName_457_);
v_body_458_ = lean_ctor_get(v_type_455_, 2);
lean_inc_ref(v_body_458_);
lean_dec_ref_known(v_type_455_, 3);
v___x_459_ = lean_array_push(v_acc_456_, v_binderName_457_);
v_type_455_ = v_body_458_;
v_acc_456_ = v___x_459_;
goto _start;
}
case 8:
{
lean_object* v_declName_461_; lean_object* v_body_462_; lean_object* v___x_463_; 
v_declName_461_ = lean_ctor_get(v_type_455_, 0);
lean_inc(v_declName_461_);
v_body_462_ = lean_ctor_get(v_type_455_, 3);
lean_inc_ref(v_body_462_);
lean_dec_ref_known(v_type_455_, 4);
v___x_463_ = lean_array_push(v_acc_456_, v_declName_461_);
v_type_455_ = v_body_462_;
v_acc_456_ = v___x_463_;
goto _start;
}
default: 
{
lean_dec_ref(v_type_455_);
return v_acc_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___lam__0(lean_object* v_x_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; 
lean_inc(v___y_472_);
lean_inc_ref(v___y_471_);
lean_inc(v___y_470_);
lean_inc_ref(v___y_469_);
lean_inc(v___y_468_);
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
v___x_478_ = lean_apply_12(v_x_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, lean_box(0));
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___lam__0___boxed(lean_object* v_x_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___lam__0(v_x_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(lean_object* v_mvarId_493_, lean_object* v_x_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___f_507_; lean_object* v___x_508_; 
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v___y_497_);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
v___f_507_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_507_, 0, v_x_494_);
lean_closure_set(v___f_507_, 1, v___y_495_);
lean_closure_set(v___f_507_, 2, v___y_496_);
lean_closure_set(v___f_507_, 3, v___y_497_);
lean_closure_set(v___f_507_, 4, v___y_498_);
lean_closure_set(v___f_507_, 5, v___y_499_);
lean_closure_set(v___f_507_, 6, v___y_500_);
lean_closure_set(v___f_507_, 7, v___y_501_);
v___x_508_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_493_, v___f_507_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_508_) == 0)
{
return v___x_508_;
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___boxed(lean_object* v_mvarId_517_, lean_object* v_x_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(v_mvarId_517_, v_x_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1(lean_object* v_00_u03b1_532_, lean_object* v_mvarId_533_, lean_object* v_x_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(v_mvarId_533_, v_x_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___boxed(lean_object* v_00_u03b1_548_, lean_object* v_mvarId_549_, lean_object* v_x_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1(v_00_u03b1_548_, v_mvarId_549_, v_x_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg(lean_object* v_upperBound_564_, lean_object* v_overrides_565_, lean_object* v_binderNames_566_, lean_object* v_a_567_, lean_object* v_b_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___y_574_; uint8_t v___x_589_; 
v___x_589_ = lean_nat_dec_lt(v_a_567_, v_upperBound_564_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
lean_dec(v_a_567_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v_b_568_);
return v___x_590_;
}
else
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_array_get_size(v_overrides_565_);
v___x_592_ = lean_nat_dec_lt(v_a_567_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_array_fget_borrowed(v_binderNames_566_, v_a_567_);
lean_inc(v___x_593_);
v___y_574_ = v___x_593_;
goto v___jp_573_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = lean_array_fget_borrowed(v_overrides_565_, v_a_567_);
lean_inc(v___x_594_);
v___y_574_ = v___x_594_;
goto v___jp_573_;
}
}
v___jp_573_:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v___y_574_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = lean_array_push(v_b_568_, v_a_576_);
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_a_567_, v___x_578_);
lean_dec(v_a_567_);
v_a_567_ = v___x_579_;
v_b_568_ = v___x_577_;
goto _start;
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v_b_568_);
lean_dec(v_a_567_);
v_a_581_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_575_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_575_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg___boxed(lean_object* v_upperBound_595_, lean_object* v_overrides_596_, lean_object* v_binderNames_597_, lean_object* v_a_598_, lean_object* v_b_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg(v_upperBound_595_, v_overrides_596_, v_binderNames_597_, v_a_598_, v_b_599_, v___y_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec_ref(v_binderNames_597_);
lean_dec_ref(v_overrides_596_);
lean_dec(v_upperBound_595_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0(lean_object* v_goal_607_, lean_object* v_overrides_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___x_621_; 
lean_inc(v_goal_607_);
v___x_621_ = l_Lean_MVarId_getType(v_goal_607_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_665_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_665_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_665_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_665_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v_names_627_; lean_object* v_binderNames_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v_names_627_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___closed__0));
v_binderNames_628_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Util_0__Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_collectBinders(v_a_622_, v_names_627_);
v___x_629_ = lean_array_get_size(v_binderNames_628_);
v___x_630_ = lean_nat_dec_eq(v___x_629_, v___x_626_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
lean_del_object(v___x_624_);
v___x_631_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg(v___x_629_, v_overrides_608_, v_binderNames_628_, v___x_626_, v_names_627_, v___y_616_, v___y_618_, v___y_619_);
lean_dec_ref(v_binderNames_628_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
lean_inc(v_goal_607_);
v___x_633_ = l_Lean_Meta_Sym_intros(v_goal_607_, v_a_632_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_645_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_645_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
if (lean_obj_tag(v_a_634_) == 1)
{
lean_object* v_mvarId_638_; lean_object* v___x_640_; 
lean_dec(v_goal_607_);
v_mvarId_638_ = lean_ctor_get(v_a_634_, 1);
lean_inc(v_mvarId_638_);
lean_dec_ref_known(v_a_634_, 2);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v_mvarId_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_mvarId_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
else
{
lean_object* v___x_643_; 
lean_dec(v_a_634_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v_goal_607_);
v___x_643_ = v___x_636_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_goal_607_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_goal_607_);
v_a_646_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_633_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_633_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
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
lean_dec(v_goal_607_);
v_a_654_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_631_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_631_);
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
else
{
lean_object* v___x_663_; 
lean_dec_ref(v_binderNames_628_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v_goal_607_);
v___x_663_ = v___x_624_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_goal_607_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec(v_goal_607_);
v_a_666_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_621_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_621_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___boxed(lean_object* v_goal_674_, lean_object* v_overrides_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0(v_goal_674_, v_overrides_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec_ref(v_overrides_675_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(lean_object* v_goal_689_, lean_object* v_overrides_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___f_703_; lean_object* v___x_704_; 
lean_inc(v_goal_689_);
v___f_703_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___boxed), 14, 2);
lean_closure_set(v___f_703_, 0, v_goal_689_);
lean_closure_set(v___f_703_, 1, v_overrides_690_);
v___x_704_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(v_goal_689_, v___f_703_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___boxed(lean_object* v_goal_705_, lean_object* v_overrides_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(v_goal_705_, v_overrides_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0(lean_object* v_upperBound_720_, lean_object* v_overrides_721_, lean_object* v_binderNames_722_, lean_object* v_inst_723_, lean_object* v_R_724_, lean_object* v_a_725_, lean_object* v_b_726_, lean_object* v_c_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg(v_upperBound_720_, v_overrides_721_, v_binderNames_722_, v_a_725_, v_b_726_, v___y_735_, v___y_737_, v___y_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_741_ = _args[0];
lean_object* v_overrides_742_ = _args[1];
lean_object* v_binderNames_743_ = _args[2];
lean_object* v_inst_744_ = _args[3];
lean_object* v_R_745_ = _args[4];
lean_object* v_a_746_ = _args[5];
lean_object* v_b_747_ = _args[6];
lean_object* v_c_748_ = _args[7];
lean_object* v___y_749_ = _args[8];
lean_object* v___y_750_ = _args[9];
lean_object* v___y_751_ = _args[10];
lean_object* v___y_752_ = _args[11];
lean_object* v___y_753_ = _args[12];
lean_object* v___y_754_ = _args[13];
lean_object* v___y_755_ = _args[14];
lean_object* v___y_756_ = _args[15];
lean_object* v___y_757_ = _args[16];
lean_object* v___y_758_ = _args[17];
lean_object* v___y_759_ = _args[18];
lean_object* v___y_760_ = _args[19];
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0(v_upperBound_741_, v_overrides_742_, v_binderNames_743_, v_inst_744_, v_R_745_, v_a_746_, v_b_747_, v_c_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec_ref(v_binderNames_743_);
lean_dec_ref(v_overrides_742_);
lean_dec(v_upperBound_741_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(lean_object* v_goal_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_hypSimpMethods_776_; 
v_hypSimpMethods_776_ = lean_ctor_get(v_a_767_, 1);
if (lean_obj_tag(v_hypSimpMethods_776_) == 1)
{
lean_object* v_val_777_; lean_object* v___x_778_; 
v_val_777_ = lean_ctor_get(v_hypSimpMethods_776_, 0);
lean_inc(v_goal_766_);
v___x_778_ = l_Lean_MVarId_getType(v_goal_766_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v_post_781_; lean_object* v_simpState_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v___x_780_ = lean_st_ref_get(v_a_768_);
v_post_781_ = lean_ctor_get(v_val_777_, 1);
v_simpState_782_ = lean_ctor_get(v___x_780_, 5);
lean_inc_ref(v_simpState_782_);
lean_dec(v___x_780_);
v___x_783_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___closed__0));
lean_inc_ref(v_post_781_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v_post_781_);
v___x_785_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_785_, 0, v_a_779_);
v___x_786_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___closed__1));
v___x_787_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_785_, v___x_784_, v___x_786_, v_simpState_782_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v_fst_789_; lean_object* v_snd_790_; lean_object* v___x_791_; lean_object* v_specBackwardRuleCache_792_; lean_object* v_splitBackwardRuleCache_793_; lean_object* v_latticeBackwardRuleCache_794_; lean_object* v_invariants_795_; lean_object* v_vcs_796_; lean_object* v_fuel_797_; lean_object* v_inlineHandledInvariants_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_807_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
v_fst_789_ = lean_ctor_get(v_a_788_, 0);
lean_inc(v_fst_789_);
v_snd_790_ = lean_ctor_get(v_a_788_, 1);
lean_inc(v_snd_790_);
lean_dec(v_a_788_);
v___x_791_ = lean_st_ref_take(v_a_768_);
v_specBackwardRuleCache_792_ = lean_ctor_get(v___x_791_, 0);
v_splitBackwardRuleCache_793_ = lean_ctor_get(v___x_791_, 1);
v_latticeBackwardRuleCache_794_ = lean_ctor_get(v___x_791_, 2);
v_invariants_795_ = lean_ctor_get(v___x_791_, 3);
v_vcs_796_ = lean_ctor_get(v___x_791_, 4);
v_fuel_797_ = lean_ctor_get(v___x_791_, 6);
v_inlineHandledInvariants_798_ = lean_ctor_get(v___x_791_, 7);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v___x_791_, 5);
lean_dec(v_unused_808_);
v___x_800_ = v___x_791_;
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_inlineHandledInvariants_798_);
lean_inc(v_fuel_797_);
lean_inc(v_vcs_796_);
lean_inc(v_invariants_795_);
lean_inc(v_latticeBackwardRuleCache_794_);
lean_inc(v_splitBackwardRuleCache_793_);
lean_inc(v_specBackwardRuleCache_792_);
lean_dec(v___x_791_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 5, v_snd_790_);
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_specBackwardRuleCache_792_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_splitBackwardRuleCache_793_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_latticeBackwardRuleCache_794_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_invariants_795_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_vcs_796_);
lean_ctor_set(v_reuseFailAlloc_806_, 5, v_snd_790_);
lean_ctor_set(v_reuseFailAlloc_806_, 6, v_fuel_797_);
lean_ctor_set(v_reuseFailAlloc_806_, 7, v_inlineHandledInvariants_798_);
v___x_803_ = v_reuseFailAlloc_806_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_st_ref_set(v_a_768_, v___x_803_);
v___x_805_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_789_, v_goal_766_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
return v___x_805_;
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec(v_goal_766_);
v_a_809_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_787_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_787_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_goal_766_);
v_a_817_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_778_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_778_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec(v_goal_766_);
v___x_825_ = lean_box(0);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___boxed(lean_object* v_goal_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_goal_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope(lean_object* v_goal_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_goal_838_, v_a_839_, v_a_840_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___boxed(lean_object* v_goal_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope(v_goal_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0(lean_object* v_goal_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
lean_inc(v_goal_875_);
v___x_888_ = l_Lean_MVarId_getType(v_goal_875_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_957_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_957_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_957_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_957_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_893_ = l_Lean_Expr_cleanupAnnotations(v_a_889_);
v___x_894_ = l_Lean_Expr_isApp(v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v___x_893_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_goal_875_);
v___x_896_ = v___x_891_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_goal_875_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
else
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = l_Lean_Expr_appFnCleanup___redArg(v___x_893_);
v___x_899_ = l_Lean_Expr_isApp(v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_901_; 
lean_dec_ref(v___x_898_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_goal_875_);
v___x_901_ = v___x_891_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_goal_875_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
else
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = l_Lean_Expr_appFnCleanup___redArg(v___x_898_);
v___x_904_ = l_Lean_Expr_isApp(v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_906_; 
lean_dec_ref(v___x_903_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_goal_875_);
v___x_906_ = v___x_891_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_goal_875_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
else
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = l_Lean_Expr_appFnCleanup___redArg(v___x_903_);
v___x_909_ = l_Lean_Expr_isApp(v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_911_; 
lean_dec_ref(v___x_908_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_goal_875_);
v___x_911_ = v___x_891_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_goal_875_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
else
{
lean_object* v_arg_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_arg_913_ = lean_ctor_get(v___x_908_, 1);
lean_inc_ref(v_arg_913_);
v___x_914_ = l_Lean_Expr_appFnCleanup___redArg(v___x_908_);
v___x_915_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__4));
v___x_916_ = l_Lean_Expr_isConstOf(v___x_914_, v___x_915_);
lean_dec_ref(v___x_914_);
if (v___x_916_ == 0)
{
lean_object* v___x_918_; 
lean_dec_ref(v_arg_913_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_goal_875_);
v___x_918_ = v___x_891_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_goal_875_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
else
{
uint8_t v___x_920_; 
v___x_920_ = l_Lean_Expr_isForall(v_arg_913_);
lean_dec_ref(v_arg_913_);
if (v___x_920_ == 0)
{
lean_object* v___x_922_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_goal_875_);
v___x_922_ = v___x_891_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_goal_875_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
lean_object* v_backwardRules_924_; lean_object* v_stateArgIntro_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_del_object(v___x_891_);
v_backwardRules_924_ = lean_ctor_get(v___y_876_, 0);
v_stateArgIntro_925_ = lean_ctor_get(v_backwardRules_924_, 1);
v___x_926_ = lean_box(0);
lean_inc(v_goal_875_);
lean_inc_ref(v_stateArgIntro_925_);
v___x_927_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_stateArgIntro_925_, v_goal_875_, v___x_926_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_948_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_948_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_948_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_948_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
if (lean_obj_tag(v_a_928_) == 1)
{
lean_object* v_mvarIds_932_; 
v_mvarIds_932_ = lean_ctor_get(v_a_928_, 0);
lean_inc(v_mvarIds_932_);
lean_dec_ref_known(v_a_928_, 1);
if (lean_obj_tag(v_mvarIds_932_) == 1)
{
lean_object* v_tail_933_; 
v_tail_933_ = lean_ctor_get(v_mvarIds_932_, 1);
if (lean_obj_tag(v_tail_933_) == 0)
{
lean_object* v_head_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_del_object(v___x_930_);
lean_dec(v_goal_875_);
v_head_934_ = lean_ctor_get(v_mvarIds_932_, 0);
lean_inc(v_head_934_);
lean_dec_ref_known(v_mvarIds_932_, 2);
v___x_935_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___closed__0));
v___x_936_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(v_head_934_, v___x_935_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 1);
v___x_938_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(v_a_937_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_938_;
}
else
{
return v___x_936_;
}
}
else
{
lean_object* v___x_940_; 
lean_dec_ref_known(v_mvarIds_932_, 2);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v_goal_875_);
v___x_940_ = v___x_930_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_goal_875_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
else
{
lean_object* v___x_943_; 
lean_dec(v_mvarIds_932_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v_goal_875_);
v___x_943_ = v___x_930_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_goal_875_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
else
{
lean_object* v___x_946_; 
lean_dec(v_a_928_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v_goal_875_);
v___x_946_ = v___x_930_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_goal_875_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_goal_875_);
v_a_949_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_927_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_927_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_goal_875_);
v_a_958_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_888_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_888_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___boxed(lean_object* v_goal_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0(v_goal_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(lean_object* v_goal_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___f_993_; lean_object* v___x_994_; 
lean_inc(v_goal_980_);
v___f_993_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_993_, 0, v_goal_980_);
v___x_994_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(v_goal_980_, v___f_993_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___boxed(lean_object* v_goal_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(v_goal_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg(lean_object* v_e_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_Expr_hasMVar(v_e_1009_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_e_1009_);
return v___x_1013_;
}
else
{
lean_object* v___x_1014_; lean_object* v_mctx_1015_; lean_object* v___x_1016_; lean_object* v_fst_1017_; lean_object* v_snd_1018_; lean_object* v___x_1019_; lean_object* v_cache_1020_; lean_object* v_zetaDeltaFVarIds_1021_; lean_object* v_postponed_1022_; lean_object* v_diag_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1032_; 
v___x_1014_ = lean_st_ref_get(v___y_1010_);
v_mctx_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc_ref(v_mctx_1015_);
lean_dec(v___x_1014_);
v___x_1016_ = l_Lean_instantiateMVarsCore(v_mctx_1015_, v_e_1009_);
v_fst_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_fst_1017_);
v_snd_1018_ = lean_ctor_get(v___x_1016_, 1);
lean_inc(v_snd_1018_);
lean_dec_ref(v___x_1016_);
v___x_1019_ = lean_st_ref_take(v___y_1010_);
v_cache_1020_ = lean_ctor_get(v___x_1019_, 1);
v_zetaDeltaFVarIds_1021_ = lean_ctor_get(v___x_1019_, 2);
v_postponed_1022_ = lean_ctor_get(v___x_1019_, 3);
v_diag_1023_ = lean_ctor_get(v___x_1019_, 4);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v___x_1019_, 0);
lean_dec(v_unused_1033_);
v___x_1025_ = v___x_1019_;
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_diag_1023_);
lean_inc(v_postponed_1022_);
lean_inc(v_zetaDeltaFVarIds_1021_);
lean_inc(v_cache_1020_);
lean_dec(v___x_1019_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1032_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v_snd_1018_);
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_snd_1018_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_cache_1020_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_zetaDeltaFVarIds_1021_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v_postponed_1022_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v_diag_1023_);
v___x_1028_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_st_ref_set(v___y_1010_, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v_fst_1017_);
return v___x_1030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg___boxed(lean_object* v_e_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg(v_e_1034_, v___y_1035_);
lean_dec(v___y_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0(lean_object* v_e_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg(v_e_1038_, v___y_1047_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___boxed(lean_object* v_e_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0(v_e_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
lean_object* v_ks_1070_; lean_object* v_vs_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1095_; 
v_ks_1070_ = lean_ctor_get(v_x_1066_, 0);
v_vs_1071_ = lean_ctor_get(v_x_1066_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_x_1066_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1073_ = v_x_1066_;
v_isShared_1074_ = v_isSharedCheck_1095_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_vs_1071_);
lean_inc(v_ks_1070_);
lean_dec(v_x_1066_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1095_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = lean_array_get_size(v_ks_1070_);
v___x_1076_ = lean_nat_dec_lt(v_x_1067_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
lean_dec(v_x_1067_);
v___x_1077_ = lean_array_push(v_ks_1070_, v_x_1068_);
v___x_1078_ = lean_array_push(v_vs_1071_, v_x_1069_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v___x_1078_);
lean_ctor_set(v___x_1073_, 0, v___x_1077_);
v___x_1080_ = v___x_1073_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
else
{
lean_object* v_k_x27_1082_; uint8_t v___x_1083_; 
v_k_x27_1082_ = lean_array_fget_borrowed(v_ks_1070_, v_x_1067_);
v___x_1083_ = l_Lean_instBEqMVarId_beq(v_x_1068_, v_k_x27_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1085_; 
if (v_isShared_1074_ == 0)
{
v___x_1085_ = v___x_1073_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_ks_1070_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_vs_1071_);
v___x_1085_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_nat_add(v_x_1067_, v___x_1086_);
lean_dec(v_x_1067_);
v_x_1066_ = v___x_1085_;
v_x_1067_ = v___x_1087_;
goto _start;
}
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1090_ = lean_array_fset(v_ks_1070_, v_x_1067_, v_x_1068_);
v___x_1091_ = lean_array_fset(v_vs_1071_, v_x_1067_, v_x_1069_);
lean_dec(v_x_1067_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 1, v___x_1091_);
lean_ctor_set(v___x_1073_, 0, v___x_1090_);
v___x_1093_ = v___x_1073_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_1096_, lean_object* v_k_1097_, lean_object* v_v_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_1096_, v___x_1099_, v_k_1097_, v_v_1098_);
return v___x_1100_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; 
v___x_1101_ = ((size_t)5ULL);
v___x_1102_ = ((size_t)1ULL);
v___x_1103_ = lean_usize_shift_left(v___x_1102_, v___x_1101_);
return v___x_1103_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; 
v___x_1104_ = ((size_t)1ULL);
v___x_1105_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_1106_ = lean_usize_sub(v___x_1105_, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1108_, size_t v_x_1109_, size_t v_x_1110_, lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1108_) == 0)
{
lean_object* v_es_1113_; size_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; lean_object* v_j_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v_es_1113_ = lean_ctor_get(v_x_1108_, 0);
v___x_1114_ = ((size_t)5ULL);
v___x_1115_ = ((size_t)1ULL);
v___x_1116_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_1117_ = lean_usize_land(v_x_1109_, v___x_1116_);
v_j_1118_ = lean_usize_to_nat(v___x_1117_);
v___x_1119_ = lean_array_get_size(v_es_1113_);
v___x_1120_ = lean_nat_dec_lt(v_j_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_dec(v_j_1118_);
lean_dec(v_x_1112_);
lean_dec(v_x_1111_);
return v_x_1108_;
}
else
{
lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1157_; 
lean_inc_ref(v_es_1113_);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_x_1108_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v_x_1108_, 0);
lean_dec(v_unused_1158_);
v___x_1122_ = v_x_1108_;
v_isShared_1123_ = v_isSharedCheck_1157_;
goto v_resetjp_1121_;
}
else
{
lean_dec(v_x_1108_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1157_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v_v_1124_; lean_object* v___x_1125_; lean_object* v_xs_x27_1126_; lean_object* v___y_1128_; 
v_v_1124_ = lean_array_fget(v_es_1113_, v_j_1118_);
v___x_1125_ = lean_box(0);
v_xs_x27_1126_ = lean_array_fset(v_es_1113_, v_j_1118_, v___x_1125_);
switch(lean_obj_tag(v_v_1124_))
{
case 0:
{
lean_object* v_key_1133_; lean_object* v_val_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1144_; 
v_key_1133_ = lean_ctor_get(v_v_1124_, 0);
v_val_1134_ = lean_ctor_get(v_v_1124_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_v_1124_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1136_ = v_v_1124_;
v_isShared_1137_ = v_isSharedCheck_1144_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_val_1134_);
lean_inc(v_key_1133_);
lean_dec(v_v_1124_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1144_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
uint8_t v___x_1138_; 
v___x_1138_ = l_Lean_instBEqMVarId_beq(v_x_1111_, v_key_1133_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_del_object(v___x_1136_);
v___x_1139_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1133_, v_val_1134_, v_x_1111_, v_x_1112_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
v___y_1128_ = v___x_1140_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1142_; 
lean_dec(v_val_1134_);
lean_dec(v_key_1133_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v_x_1112_);
lean_ctor_set(v___x_1136_, 0, v_x_1111_);
v___x_1142_ = v___x_1136_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_x_1111_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_x_1112_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
v___y_1128_ = v___x_1142_;
goto v___jp_1127_;
}
}
}
}
case 1:
{
lean_object* v_node_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1155_; 
v_node_1145_ = lean_ctor_get(v_v_1124_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_v_1124_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1147_ = v_v_1124_;
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_node_1145_);
lean_dec(v_v_1124_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1149_ = lean_usize_shift_right(v_x_1109_, v___x_1114_);
v___x_1150_ = lean_usize_add(v_x_1110_, v___x_1115_);
v___x_1151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(v_node_1145_, v___x_1149_, v___x_1150_, v_x_1111_, v_x_1112_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1151_);
v___x_1153_ = v___x_1147_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
v___y_1128_ = v___x_1153_;
goto v___jp_1127_;
}
}
}
default: 
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v_x_1111_);
lean_ctor_set(v___x_1156_, 1, v_x_1112_);
v___y_1128_ = v___x_1156_;
goto v___jp_1127_;
}
}
v___jp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = lean_array_fset(v_xs_x27_1126_, v_j_1118_, v___y_1128_);
lean_dec(v_j_1118_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1129_);
v___x_1131_ = v___x_1122_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
else
{
lean_object* v_ks_1159_; lean_object* v_vs_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1180_; 
v_ks_1159_ = lean_ctor_get(v_x_1108_, 0);
v_vs_1160_ = lean_ctor_get(v_x_1108_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_x_1108_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1162_ = v_x_1108_;
v_isShared_1163_ = v_isSharedCheck_1180_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_vs_1160_);
lean_inc(v_ks_1159_);
lean_dec(v_x_1108_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1180_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_ks_1159_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_vs_1160_);
v___x_1165_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v_newNode_1166_; uint8_t v___y_1168_; size_t v___x_1174_; uint8_t v___x_1175_; 
v_newNode_1166_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3___redArg(v___x_1165_, v_x_1111_, v_x_1112_);
v___x_1174_ = ((size_t)7ULL);
v___x_1175_ = lean_usize_dec_le(v___x_1174_, v_x_1110_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1176_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1166_);
v___x_1177_ = lean_unsigned_to_nat(4u);
v___x_1178_ = lean_nat_dec_lt(v___x_1176_, v___x_1177_);
lean_dec(v___x_1176_);
v___y_1168_ = v___x_1178_;
goto v___jp_1167_;
}
else
{
v___y_1168_ = v___x_1175_;
goto v___jp_1167_;
}
v___jp_1167_:
{
if (v___y_1168_ == 0)
{
lean_object* v_ks_1169_; lean_object* v_vs_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v_ks_1169_ = lean_ctor_get(v_newNode_1166_, 0);
lean_inc_ref(v_ks_1169_);
v_vs_1170_ = lean_ctor_get(v_newNode_1166_, 1);
lean_inc_ref(v_vs_1170_);
lean_dec_ref(v_newNode_1166_);
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_1173_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg(v_x_1110_, v_ks_1169_, v_vs_1170_, v___x_1171_, v___x_1172_);
lean_dec_ref(v_vs_1170_);
lean_dec_ref(v_ks_1169_);
return v___x_1173_;
}
else
{
return v_newNode_1166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_1181_, lean_object* v_keys_1182_, lean_object* v_vals_1183_, lean_object* v_i_1184_, lean_object* v_entries_1185_){
_start:
{
lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = lean_array_get_size(v_keys_1182_);
v___x_1187_ = lean_nat_dec_lt(v_i_1184_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_dec(v_i_1184_);
return v_entries_1185_;
}
else
{
lean_object* v_k_1188_; lean_object* v_v_1189_; uint64_t v___x_1190_; size_t v_h_1191_; size_t v___x_1192_; lean_object* v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; size_t v_h_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_k_1188_ = lean_array_fget_borrowed(v_keys_1182_, v_i_1184_);
v_v_1189_ = lean_array_fget_borrowed(v_vals_1183_, v_i_1184_);
v___x_1190_ = l_Lean_instHashableMVarId_hash(v_k_1188_);
v_h_1191_ = lean_uint64_to_usize(v___x_1190_);
v___x_1192_ = ((size_t)5ULL);
v___x_1193_ = lean_unsigned_to_nat(1u);
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_sub(v_depth_1181_, v___x_1194_);
v___x_1196_ = lean_usize_mul(v___x_1192_, v___x_1195_);
v_h_1197_ = lean_usize_shift_right(v_h_1191_, v___x_1196_);
v___x_1198_ = lean_nat_add(v_i_1184_, v___x_1193_);
lean_dec(v_i_1184_);
lean_inc(v_v_1189_);
lean_inc(v_k_1188_);
v___x_1199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(v_entries_1185_, v_h_1197_, v_depth_1181_, v_k_1188_, v_v_1189_);
v_i_1184_ = v___x_1198_;
v_entries_1185_ = v___x_1199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_1201_, lean_object* v_keys_1202_, lean_object* v_vals_1203_, lean_object* v_i_1204_, lean_object* v_entries_1205_){
_start:
{
size_t v_depth_boxed_1206_; lean_object* v_res_1207_; 
v_depth_boxed_1206_ = lean_unbox_usize(v_depth_1201_);
lean_dec(v_depth_1201_);
v_res_1207_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_1206_, v_keys_1202_, v_vals_1203_, v_i_1204_, v_entries_1205_);
lean_dec_ref(v_vals_1203_);
lean_dec_ref(v_keys_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_, lean_object* v_x_1211_, lean_object* v_x_1212_){
_start:
{
size_t v_x_59189__boxed_1213_; size_t v_x_59190__boxed_1214_; lean_object* v_res_1215_; 
v_x_59189__boxed_1213_ = lean_unbox_usize(v_x_1209_);
lean_dec(v_x_1209_);
v_x_59190__boxed_1214_ = lean_unbox_usize(v_x_1210_);
lean_dec(v_x_1210_);
v_res_1215_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(v_x_1208_, v_x_59189__boxed_1213_, v_x_59190__boxed_1214_, v_x_1211_, v_x_1212_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1___redArg(lean_object* v_x_1216_, lean_object* v_x_1217_, lean_object* v_x_1218_){
_start:
{
uint64_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v___x_1219_ = l_Lean_instHashableMVarId_hash(v_x_1217_);
v___x_1220_ = lean_uint64_to_usize(v___x_1219_);
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(v_x_1216_, v___x_1220_, v___x_1221_, v_x_1217_, v_x_1218_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(lean_object* v_mvarId_1223_, lean_object* v_val_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; lean_object* v_mctx_1228_; lean_object* v_cache_1229_; lean_object* v_zetaDeltaFVarIds_1230_; lean_object* v_postponed_1231_; lean_object* v_diag_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1260_; 
v___x_1227_ = lean_st_ref_take(v___y_1225_);
v_mctx_1228_ = lean_ctor_get(v___x_1227_, 0);
v_cache_1229_ = lean_ctor_get(v___x_1227_, 1);
v_zetaDeltaFVarIds_1230_ = lean_ctor_get(v___x_1227_, 2);
v_postponed_1231_ = lean_ctor_get(v___x_1227_, 3);
v_diag_1232_ = lean_ctor_get(v___x_1227_, 4);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1234_ = v___x_1227_;
v_isShared_1235_ = v_isSharedCheck_1260_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_diag_1232_);
lean_inc(v_postponed_1231_);
lean_inc(v_zetaDeltaFVarIds_1230_);
lean_inc(v_cache_1229_);
lean_inc(v_mctx_1228_);
lean_dec(v___x_1227_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1260_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v_depth_1236_; lean_object* v_levelAssignDepth_1237_; lean_object* v_lmvarCounter_1238_; lean_object* v_mvarCounter_1239_; lean_object* v_lDecls_1240_; lean_object* v_decls_1241_; lean_object* v_userNames_1242_; lean_object* v_lAssignment_1243_; lean_object* v_eAssignment_1244_; lean_object* v_dAssignment_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1259_; 
v_depth_1236_ = lean_ctor_get(v_mctx_1228_, 0);
v_levelAssignDepth_1237_ = lean_ctor_get(v_mctx_1228_, 1);
v_lmvarCounter_1238_ = lean_ctor_get(v_mctx_1228_, 2);
v_mvarCounter_1239_ = lean_ctor_get(v_mctx_1228_, 3);
v_lDecls_1240_ = lean_ctor_get(v_mctx_1228_, 4);
v_decls_1241_ = lean_ctor_get(v_mctx_1228_, 5);
v_userNames_1242_ = lean_ctor_get(v_mctx_1228_, 6);
v_lAssignment_1243_ = lean_ctor_get(v_mctx_1228_, 7);
v_eAssignment_1244_ = lean_ctor_get(v_mctx_1228_, 8);
v_dAssignment_1245_ = lean_ctor_get(v_mctx_1228_, 9);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_mctx_1228_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1247_ = v_mctx_1228_;
v_isShared_1248_ = v_isSharedCheck_1259_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_dAssignment_1245_);
lean_inc(v_eAssignment_1244_);
lean_inc(v_lAssignment_1243_);
lean_inc(v_userNames_1242_);
lean_inc(v_decls_1241_);
lean_inc(v_lDecls_1240_);
lean_inc(v_mvarCounter_1239_);
lean_inc(v_lmvarCounter_1238_);
lean_inc(v_levelAssignDepth_1237_);
lean_inc(v_depth_1236_);
lean_dec(v_mctx_1228_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1259_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1___redArg(v_eAssignment_1244_, v_mvarId_1223_, v_val_1224_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 8, v___x_1249_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_depth_1236_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_levelAssignDepth_1237_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_lmvarCounter_1238_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_mvarCounter_1239_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v_lDecls_1240_);
lean_ctor_set(v_reuseFailAlloc_1258_, 5, v_decls_1241_);
lean_ctor_set(v_reuseFailAlloc_1258_, 6, v_userNames_1242_);
lean_ctor_set(v_reuseFailAlloc_1258_, 7, v_lAssignment_1243_);
lean_ctor_set(v_reuseFailAlloc_1258_, 8, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1258_, 9, v_dAssignment_1245_);
v___x_1251_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1253_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1251_);
v___x_1253_ = v___x_1234_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_cache_1229_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_zetaDeltaFVarIds_1230_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_postponed_1231_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_diag_1232_);
v___x_1253_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_st_ref_set(v___y_1225_, v___x_1253_);
v___x_1255_ = lean_box(0);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg___boxed(lean_object* v_mvarId_1261_, lean_object* v_val_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_mvarId_1261_, v_val_1262_, v___y_1263_);
lean_dec(v___y_1263_);
return v_res_1265_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__8));
v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__12));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__14(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_box(0);
v___x_1290_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__3));
v___x_1291_ = l_Lean_mkConst(v___x_1290_, v___x_1289_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__17(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__16));
v___x_1298_ = l_Lean_mkConst(v___x_1297_, v___x_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__20(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_box(0);
v___x_1304_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__19));
v___x_1305_ = l_Lean_mkConst(v___x_1304_, v___x_1303_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__22(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__21));
v___x_1311_ = l_Lean_mkConst(v___x_1310_, v___x_1309_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0(lean_object* v_goal_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
lean_inc(v_goal_1312_);
v___x_1325_ = l_Lean_MVarId_getType(v_goal_1312_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg(v_a_1326_, v___y_1321_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1590_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1590_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1590_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__1));
v___x_1333_ = l_Lean_Expr_isAppOf(v_a_1328_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__3));
v___x_1335_ = l_Lean_Expr_isAppOf(v_a_1328_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1336_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__5));
v___x_1337_ = lean_unsigned_to_nat(3u);
v___x_1338_ = l_Lean_Expr_isAppOfArity(v_a_1328_, v___x_1336_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
lean_dec(v_a_1328_);
v___x_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_goal_1312_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1339_);
v___x_1341_ = v___x_1330_;
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
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_del_object(v___x_1330_);
v___x_1343_ = l_Lean_Expr_appFn_x21(v_a_1328_);
v___x_1344_ = l_Lean_Expr_appArg_x21(v___x_1343_);
v___x_1345_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v___x_1344_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = l_Lean_Expr_appArg_x21(v_a_1328_);
lean_dec(v_a_1328_);
v___x_1348_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v___x_1347_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = l_Lean_Expr_appFn_x21(v___x_1343_);
lean_dec_ref(v___x_1343_);
v___x_1351_ = l_Lean_Expr_appArg_x21(v___x_1350_);
lean_dec_ref(v___x_1350_);
lean_inc_ref(v___x_1351_);
v___x_1352_ = l_Lean_Meta_getLevel(v___x_1351_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_a_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_mkConst(v___x_1336_, v___x_1355_);
lean_inc(v_a_1349_);
lean_inc(v_a_1346_);
lean_inc_ref(v___x_1351_);
v___x_1357_ = l_Lean_mkApp3(v___x_1356_, v___x_1351_, v_a_1346_, v_a_1349_);
v___x_1358_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_1312_, v___x_1357_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___closed__0));
lean_inc(v_a_1346_);
v___x_1361_ = l_Lean_Meta_Sym_isDefEqS(v_a_1346_, v_a_1349_, v___x_1338_, v___x_1338_, v___x_1360_, v___x_1360_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1403_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1403_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1403_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_unbox(v_a_1362_);
lean_dec(v_a_1362_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
lean_dec_ref(v___x_1351_);
lean_dec(v_a_1346_);
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_a_1359_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1367_);
v___x_1369_ = v___x_1364_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
else
{
lean_object* v___x_1371_; 
lean_del_object(v___x_1364_);
lean_inc_ref(v___x_1351_);
v___x_1371_ = l_Lean_Meta_getLevel(v___x_1351_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1373_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__7));
v___x_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_a_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1354_);
v___x_1375_ = l_Lean_mkConst(v___x_1373_, v___x_1374_);
v___x_1376_ = l_Lean_mkAppB(v___x_1375_, v___x_1351_, v_a_1346_);
v___x_1377_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_a_1359_, v___x_1376_, v___y_1321_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1385_; 
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; 
v_unused_1386_ = lean_ctor_get(v___x_1377_, 0);
lean_dec(v_unused_1386_);
v___x_1379_ = v___x_1377_;
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
else
{
lean_dec(v___x_1377_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1385_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1381_ = lean_box(0);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1381_);
v___x_1383_ = v___x_1379_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_a_1387_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1377_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1377_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_a_1359_);
lean_dec_ref(v___x_1351_);
lean_dec(v_a_1346_);
v_a_1395_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1371_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1371_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec(v_a_1359_);
lean_dec_ref(v___x_1351_);
lean_dec(v_a_1346_);
v_a_1404_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1361_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1361_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec_ref(v___x_1351_);
lean_dec(v_a_1349_);
lean_dec(v_a_1346_);
v_a_1412_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1358_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1358_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec_ref(v___x_1351_);
lean_dec(v_a_1349_);
lean_dec(v_a_1346_);
lean_dec(v_goal_1312_);
v_a_1420_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1352_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1352_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec(v_a_1346_);
lean_dec_ref(v___x_1343_);
lean_dec(v_goal_1312_);
v_a_1428_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1348_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1348_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v___x_1343_);
lean_dec(v_a_1328_);
lean_dec(v_goal_1312_);
v_a_1436_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1345_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1345_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
else
{
lean_object* v_backwardRules_1444_; lean_object* v_andIntro_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_del_object(v___x_1330_);
v_backwardRules_1444_ = lean_ctor_get(v___y_1313_, 0);
v_andIntro_1445_ = lean_ctor_get(v_backwardRules_1444_, 6);
v___x_1446_ = lean_box(0);
lean_inc_ref(v_andIntro_1445_);
v___x_1447_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_andIntro_1445_, v_goal_1312_, v___x_1446_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
if (lean_obj_tag(v_a_1448_) == 1)
{
lean_object* v_mvarIds_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1562_; 
v_mvarIds_1463_ = lean_ctor_get(v_a_1448_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_a_1448_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1465_ = v_a_1448_;
v_isShared_1466_ = v_isSharedCheck_1562_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_mvarIds_1463_);
lean_dec(v_a_1448_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1562_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
if (lean_obj_tag(v_mvarIds_1463_) == 1)
{
lean_object* v_tail_1467_; 
v_tail_1467_ = lean_ctor_get(v_mvarIds_1463_, 1);
lean_inc(v_tail_1467_);
if (lean_obj_tag(v_tail_1467_) == 1)
{
lean_object* v_tail_1468_; 
v_tail_1468_ = lean_ctor_get(v_tail_1467_, 1);
if (lean_obj_tag(v_tail_1468_) == 0)
{
lean_object* v_head_1469_; lean_object* v_head_1470_; lean_object* v___x_1471_; 
lean_dec(v_a_1328_);
v_head_1469_ = lean_ctor_get(v_mvarIds_1463_, 0);
lean_inc(v_head_1469_);
lean_dec_ref_known(v_mvarIds_1463_, 2);
v_head_1470_ = lean_ctor_get(v_tail_1467_, 0);
lean_inc(v_head_1470_);
lean_dec_ref_known(v_tail_1467_, 2);
v___x_1471_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(v_head_1469_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1561_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1474_ = v___x_1471_;
v_isShared_1475_ = v_isSharedCheck_1561_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1561_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(v_head_1470_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v_g_1479_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
if (lean_obj_tag(v_a_1472_) == 0)
{
if (lean_obj_tag(v_a_1477_) == 0)
{
lean_del_object(v___x_1474_);
lean_del_object(v___x_1465_);
return v___x_1476_;
}
else
{
lean_object* v_val_1486_; 
lean_dec_ref_known(v___x_1476_, 1);
v_val_1486_ = lean_ctor_get(v_a_1477_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v_a_1477_, 1);
v_g_1479_ = v_val_1486_;
goto v___jp_1478_;
}
}
else
{
lean_dec_ref_known(v___x_1476_, 1);
if (lean_obj_tag(v_a_1477_) == 0)
{
lean_object* v_val_1487_; 
v_val_1487_ = lean_ctor_get(v_a_1472_, 0);
lean_inc(v_val_1487_);
lean_dec_ref_known(v_a_1472_, 1);
v_g_1479_ = v_val_1487_;
goto v___jp_1478_;
}
else
{
lean_object* v_val_1488_; lean_object* v_val_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1560_; 
lean_del_object(v___x_1474_);
lean_del_object(v___x_1465_);
v_val_1488_ = lean_ctor_get(v_a_1472_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v_a_1472_, 1);
v_val_1489_ = lean_ctor_get(v_a_1477_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_a_1477_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1491_ = v_a_1477_;
v_isShared_1492_ = v_isSharedCheck_1560_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_val_1489_);
lean_dec(v_a_1477_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1560_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; 
lean_inc(v_val_1488_);
v___x_1493_ = l_Lean_MVarId_getType(v_val_1488_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1495_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
lean_inc(v_val_1489_);
v___x_1495_ = l_Lean_MVarId_getType(v_val_1489_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc_n(v_a_1496_, 2);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1497_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__14, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__14_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__14);
lean_inc(v_a_1494_);
v___x_1498_ = l_Lean_mkAppB(v___x_1497_, v_a_1494_, v_a_1496_);
v___x_1499_ = lean_box(0);
v___x_1500_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1498_, v___x_1499_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc_n(v_a_1501_, 2);
lean_dec_ref_known(v___x_1500_, 1);
v___x_1502_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__17, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__17);
lean_inc(v_a_1496_);
lean_inc(v_a_1494_);
v___x_1503_ = l_Lean_mkApp3(v___x_1502_, v_a_1494_, v_a_1496_, v_a_1501_);
v___x_1504_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_val_1488_, v___x_1503_, v___y_1321_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec_ref_known(v___x_1504_, 1);
v___x_1505_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__20, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__20_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__20);
lean_inc(v_a_1501_);
v___x_1506_ = l_Lean_mkApp3(v___x_1505_, v_a_1494_, v_a_1496_, v_a_1501_);
v___x_1507_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_val_1489_, v___x_1506_, v___y_1321_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1518_; 
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; 
v_unused_1519_ = lean_ctor_get(v___x_1507_, 0);
lean_dec(v_unused_1519_);
v___x_1509_ = v___x_1507_;
v_isShared_1510_ = v_isSharedCheck_1518_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v___x_1507_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1518_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = l_Lean_Expr_mvarId_x21(v_a_1501_);
lean_dec(v_a_1501_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1511_);
v___x_1513_ = v___x_1491_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1515_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1513_);
v___x_1515_ = v___x_1509_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_a_1501_);
lean_del_object(v___x_1491_);
v_a_1520_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1507_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1507_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
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
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_a_1501_);
lean_dec(v_a_1496_);
lean_dec(v_a_1494_);
lean_del_object(v___x_1491_);
lean_dec(v_val_1489_);
v_a_1528_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1504_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1504_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec(v_a_1496_);
lean_dec(v_a_1494_);
lean_del_object(v___x_1491_);
lean_dec(v_val_1489_);
lean_dec(v_val_1488_);
v_a_1536_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1500_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1500_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_a_1494_);
lean_del_object(v___x_1491_);
lean_dec(v_val_1489_);
lean_dec(v_val_1488_);
v_a_1544_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1495_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1495_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_del_object(v___x_1491_);
lean_dec(v_val_1489_);
lean_dec(v_val_1488_);
v_a_1552_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1493_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1493_);
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
v___jp_1478_:
{
lean_object* v___x_1481_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v_g_1479_);
v___x_1481_ = v___x_1465_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_g_1479_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v___x_1481_);
v___x_1483_ = v___x_1474_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_del_object(v___x_1474_);
lean_dec(v_a_1472_);
lean_del_object(v___x_1465_);
return v___x_1476_;
}
}
}
else
{
lean_dec(v_head_1470_);
lean_del_object(v___x_1465_);
return v___x_1471_;
}
}
else
{
lean_dec_ref_known(v_tail_1467_, 2);
lean_dec_ref_known(v_mvarIds_1463_, 2);
lean_del_object(v___x_1465_);
v___y_1450_ = v___y_1320_;
v___y_1451_ = v___y_1321_;
v___y_1452_ = v___y_1322_;
v___y_1453_ = v___y_1323_;
goto v___jp_1449_;
}
}
else
{
lean_dec_ref_known(v_mvarIds_1463_, 2);
lean_dec(v_tail_1467_);
lean_del_object(v___x_1465_);
v___y_1450_ = v___y_1320_;
v___y_1451_ = v___y_1321_;
v___y_1452_ = v___y_1322_;
v___y_1453_ = v___y_1323_;
goto v___jp_1449_;
}
}
else
{
lean_del_object(v___x_1465_);
lean_dec(v_mvarIds_1463_);
v___y_1450_ = v___y_1320_;
v___y_1451_ = v___y_1321_;
v___y_1452_ = v___y_1322_;
v___y_1453_ = v___y_1323_;
goto v___jp_1449_;
}
}
}
else
{
lean_dec(v_a_1448_);
v___y_1450_ = v___y_1320_;
v___y_1451_ = v___y_1321_;
v___y_1452_ = v___y_1322_;
v___y_1453_ = v___y_1323_;
goto v___jp_1449_;
}
v___jp_1449_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1454_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__9, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__9);
v___x_1455_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__11));
v___x_1456_ = l_Lean_MessageData_ofConstName(v___x_1455_, v___x_1333_);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1454_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__13, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__13);
v___x_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = l_Lean_indentExpr(v_a_1328_);
v___x_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1461_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1462_;
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v_a_1328_);
v_a_1563_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1447_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1447_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_del_object(v___x_1330_);
lean_dec(v_a_1328_);
v___x_1571_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__22, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__22);
v___x_1572_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_goal_1312_, v___x_1571_, v___y_1321_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1580_; 
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v___x_1572_, 0);
lean_dec(v_unused_1581_);
v___x_1574_ = v___x_1572_;
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
else
{
lean_dec(v___x_1572_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = lean_box(0);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1576_);
v___x_1578_ = v___x_1574_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_a_1582_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1572_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1572_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_goal_1312_);
v_a_1591_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1327_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1327_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_goal_1312_);
v_a_1599_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1325_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1325_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___boxed(lean_object* v_goal_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0(v_goal_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(lean_object* v_goal_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___f_1634_; lean_object* v___x_1635_; 
lean_inc(v_goal_1621_);
v___f_1634_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1634_, 0, v_goal_1621_);
v___x_1635_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(v_goal_1621_, v___f_1634_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___boxed(lean_object* v_goal_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(v_goal_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1(lean_object* v_mvarId_1650_, lean_object* v_val_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_mvarId_1650_, v_val_1651_, v___y_1660_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___boxed(lean_object* v_mvarId_1665_, lean_object* v_val_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1(v_mvarId_1665_, v_val_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1(lean_object* v_00_u03b2_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1___redArg(v_x_1681_, v_x_1682_, v_x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1685_, lean_object* v_x_1686_, size_t v_x_1687_, size_t v_x_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(v_x_1686_, v_x_1687_, v_x_1688_, v_x_1689_, v_x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1692_, lean_object* v_x_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_, lean_object* v_x_1697_){
_start:
{
size_t v_x_60203__boxed_1698_; size_t v_x_60204__boxed_1699_; lean_object* v_res_1700_; 
v_x_60203__boxed_1698_ = lean_unbox_usize(v_x_1694_);
lean_dec(v_x_1694_);
v_x_60204__boxed_1699_ = lean_unbox_usize(v_x_1695_);
lean_dec(v_x_1695_);
v_res_1700_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2(v_00_u03b2_1692_, v_x_1693_, v_x_60203__boxed_1698_, v_x_60204__boxed_1699_, v_x_1696_, v_x_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1701_, lean_object* v_n_1702_, lean_object* v_k_1703_, lean_object* v_v_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1702_, v_k_1703_, v_v_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1706_, size_t v_depth_1707_, lean_object* v_keys_1708_, lean_object* v_vals_1709_, lean_object* v_heq_1710_, lean_object* v_i_1711_, lean_object* v_entries_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1707_, v_keys_1708_, v_vals_1709_, v_i_1711_, v_entries_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1714_, lean_object* v_depth_1715_, lean_object* v_keys_1716_, lean_object* v_vals_1717_, lean_object* v_heq_1718_, lean_object* v_i_1719_, lean_object* v_entries_1720_){
_start:
{
size_t v_depth_boxed_1721_; lean_object* v_res_1722_; 
v_depth_boxed_1721_ = lean_unbox_usize(v_depth_1715_);
lean_dec(v_depth_1715_);
v_res_1722_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1714_, v_depth_boxed_1721_, v_keys_1716_, v_vals_1717_, v_heq_1718_, v_i_1719_, v_entries_1720_);
lean_dec_ref(v_vals_1717_);
lean_dec_ref(v_keys_1716_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1723_, lean_object* v_x_1724_, lean_object* v_x_1725_, lean_object* v_x_1726_, lean_object* v_x_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1724_, v_x_1725_, v_x_1726_, v_x_1727_);
return v___x_1728_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Telescope(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Telescope(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
}
#ifdef __cplusplus
}
#endif
