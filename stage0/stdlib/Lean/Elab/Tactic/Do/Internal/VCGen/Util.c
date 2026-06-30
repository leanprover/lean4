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
lean_object* l_Lean_Meta_Sym_Pattern_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "[vcgen +debug] BackwardRule "};
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
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " to goal"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "le_of_forall_le"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(101, 62, 242, 60, 214, 49, 44, 186)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "failed to apply "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__13;
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object* v_rule_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_expr_9_; lean_object* v_pattern_10_; lean_object* v_resultPos_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_35_; 
v_expr_9_ = lean_ctor_get(v_rule_1_, 0);
v_pattern_10_ = lean_ctor_get(v_rule_1_, 1);
v_resultPos_11_ = lean_ctor_get(v_rule_1_, 2);
v_isSharedCheck_35_ = !lean_is_exclusive(v_rule_1_);
if (v_isSharedCheck_35_ == 0)
{
v___x_13_ = v_rule_1_;
v_isShared_14_ = v_isSharedCheck_35_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_resultPos_11_);
lean_inc(v_pattern_10_);
lean_inc(v_expr_9_);
lean_dec(v_rule_1_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_35_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_Sym_Pattern_shareCommon(v_pattern_10_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_26_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_26_ == 0)
{
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_26_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_a_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_26_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_21_; 
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v_a_16_);
v___x_21_ = v___x_13_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_expr_9_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_a_16_);
lean_ctor_set(v_reuseFailAlloc_25_, 2, v_resultPos_11_);
v___x_21_ = v_reuseFailAlloc_25_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_23_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_21_);
v___x_23_ = v___x_18_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
else
{
lean_object* v_a_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_34_; 
lean_del_object(v___x_13_);
lean_dec(v_resultPos_11_);
lean_dec_ref(v_expr_9_);
v_a_27_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_34_ == 0)
{
v___x_29_ = v___x_15_;
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_a_27_);
lean_dec(v___x_15_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_34_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_32_; 
if (v_isShared_30_ == 0)
{
v___x_32_ = v___x_29_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_a_27_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon___boxed(lean_object* v_rule_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(lean_object* v___y_45_, lean_object* v_mctx_46_, lean_object* v_cache_47_, lean_object* v_a_x3f_48_){
_start:
{
lean_object* v___x_50_; lean_object* v_zetaDeltaFVarIds_51_; lean_object* v_postponed_52_; lean_object* v_diag_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_63_; 
v___x_50_ = lean_st_ref_take(v___y_45_);
v_zetaDeltaFVarIds_51_ = lean_ctor_get(v___x_50_, 2);
v_postponed_52_ = lean_ctor_get(v___x_50_, 3);
v_diag_53_ = lean_ctor_get(v___x_50_, 4);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_63_ == 0)
{
lean_object* v_unused_64_; lean_object* v_unused_65_; 
v_unused_64_ = lean_ctor_get(v___x_50_, 1);
lean_dec(v_unused_64_);
v_unused_65_ = lean_ctor_get(v___x_50_, 0);
lean_dec(v_unused_65_);
v___x_55_ = v___x_50_;
v_isShared_56_ = v_isSharedCheck_63_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_diag_53_);
lean_inc(v_postponed_52_);
lean_inc(v_zetaDeltaFVarIds_51_);
lean_dec(v___x_50_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_63_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v_cache_47_);
lean_ctor_set(v___x_55_, 0, v_mctx_46_);
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_mctx_46_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_cache_47_);
lean_ctor_set(v_reuseFailAlloc_62_, 2, v_zetaDeltaFVarIds_51_);
lean_ctor_set(v_reuseFailAlloc_62_, 3, v_postponed_52_);
lean_ctor_set(v_reuseFailAlloc_62_, 4, v_diag_53_);
v___x_58_ = v_reuseFailAlloc_62_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_st_ref_set(v___y_45_, v___x_58_);
v___x_60_ = lean_box(0);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(lean_object* v___y_66_, lean_object* v_mctx_67_, lean_object* v_cache_68_, lean_object* v_a_x3f_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_66_, v_mctx_67_, v_cache_68_, v_a_x3f_69_);
lean_dec(v_a_x3f_69_);
lean_dec(v___y_66_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(lean_object* v_x_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_mctx_87_; lean_object* v_cache_88_; lean_object* v___x_89_; 
v___x_85_ = lean_st_ref_get(v___y_81_);
v___x_86_ = lean_st_ref_get(v___y_81_);
v_mctx_87_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref(v_mctx_87_);
lean_dec(v___x_85_);
v_cache_88_ = lean_ctor_get(v___x_86_, 1);
lean_inc_ref(v_cache_88_);
lean_dec(v___x_86_);
lean_inc(v___y_83_);
lean_inc_ref(v___y_82_);
lean_inc(v___y_81_);
lean_inc_ref(v___y_80_);
lean_inc(v___y_79_);
lean_inc_ref(v___y_78_);
lean_inc(v___y_77_);
lean_inc_ref(v___y_76_);
lean_inc(v___y_75_);
lean_inc(v___y_74_);
lean_inc_ref(v___y_73_);
v___x_89_ = lean_apply_12(v_x_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, lean_box(0));
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_106_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_106_ == 0)
{
v___x_92_ = v___x_89_;
v_isShared_93_ = v_isSharedCheck_106_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_106_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
lean_inc(v_a_90_);
if (v_isShared_93_ == 0)
{
lean_ctor_set_tag(v___x_92_, 1);
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_105_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v___x_96_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_81_, v_mctx_87_, v_cache_88_, v___x_95_);
lean_dec_ref(v___x_95_);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_103_ == 0)
{
lean_object* v_unused_104_; 
v_unused_104_ = lean_ctor_get(v___x_96_, 0);
lean_dec(v_unused_104_);
v___x_98_ = v___x_96_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_dec(v___x_96_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v_a_90_);
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_90_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
v_a_107_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_89_, 1);
v___x_108_ = lean_box(0);
v___x_109_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_81_, v_mctx_87_, v_cache_88_, v___x_108_);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; 
v_unused_117_ = lean_ctor_get(v___x_109_, 0);
lean_dec(v_unused_117_);
v___x_111_ = v___x_109_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_dec(v___x_109_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set_tag(v___x_111_, 1);
lean_ctor_set(v___x_111_, 0, v_a_107_);
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_107_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(lean_object* v_x_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(lean_object* v_00_u03b1_132_, lean_object* v_x_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(lean_object* v_00_u03b1_147_, lean_object* v_x_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(v_00_u03b1_147_, v_x_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(lean_object* v_a_162_, lean_object* v___x_163_, lean_object* v_rule_164_, uint8_t v___x_165_, uint8_t v_debug_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_162_, v___x_163_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = l_Lean_Expr_mvarId_x21(v_a_180_);
lean_dec(v_a_180_);
v___x_182_ = l_Lean_Meta_Sym_BackwardRule_apply(v___x_181_, v_rule_164_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_195_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_195_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
if (lean_obj_tag(v_a_183_) == 0)
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_box(v___x_165_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
else
{
lean_object* v___x_191_; lean_object* v___x_193_; 
lean_dec_ref_known(v_a_183_, 1);
v___x_191_ = lean_box(v_debug_166_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_191_);
v___x_193_ = v___x_185_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_182_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_182_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec_ref(v_rule_164_);
v_a_204_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_179_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_179_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(lean_object** _args){
lean_object* v_a_212_ = _args[0];
lean_object* v___x_213_ = _args[1];
lean_object* v_rule_214_ = _args[2];
lean_object* v___x_215_ = _args[3];
lean_object* v_debug_216_ = _args[4];
lean_object* v___y_217_ = _args[5];
lean_object* v___y_218_ = _args[6];
lean_object* v___y_219_ = _args[7];
lean_object* v___y_220_ = _args[8];
lean_object* v___y_221_ = _args[9];
lean_object* v___y_222_ = _args[10];
lean_object* v___y_223_ = _args[11];
lean_object* v___y_224_ = _args[12];
lean_object* v___y_225_ = _args[13];
lean_object* v___y_226_ = _args[14];
lean_object* v___y_227_ = _args[15];
lean_object* v___y_228_ = _args[16];
_start:
{
uint8_t v___x_43892__boxed_229_; uint8_t v_debug_boxed_230_; lean_object* v_res_231_; 
v___x_43892__boxed_229_ = lean_unbox(v___x_215_);
v_debug_boxed_230_ = lean_unbox(v_debug_216_);
v_res_231_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(v_a_212_, v___x_213_, v_rule_214_, v___x_43892__boxed_229_, v_debug_boxed_230_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(lean_object* v_msgData_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_238_; lean_object* v_env_239_; lean_object* v___x_240_; lean_object* v_mctx_241_; lean_object* v_lctx_242_; lean_object* v_options_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_238_ = lean_st_ref_get(v___y_236_);
v_env_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc_ref(v_env_239_);
lean_dec(v___x_238_);
v___x_240_ = lean_st_ref_get(v___y_234_);
v_mctx_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc_ref(v_mctx_241_);
lean_dec(v___x_240_);
v_lctx_242_ = lean_ctor_get(v___y_233_, 2);
v_options_243_ = lean_ctor_get(v___y_235_, 2);
lean_inc_ref(v_options_243_);
lean_inc_ref(v_lctx_242_);
v___x_244_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_244_, 0, v_env_239_);
lean_ctor_set(v___x_244_, 1, v_mctx_241_);
lean_ctor_set(v___x_244_, 2, v_lctx_242_);
lean_ctor_set(v___x_244_, 3, v_options_243_);
v___x_245_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v_msgData_232_);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1___boxed(lean_object* v_msgData_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msgData_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(lean_object* v_msg_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_ref_260_; lean_object* v___x_261_; lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_270_; 
v_ref_260_ = lean_ctor_get(v___y_257_, 5);
v___x_261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msg_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_270_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_270_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
lean_inc(v_ref_260_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_ref_260_);
lean_ctor_set(v___x_266_, 1, v_a_262_);
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 1);
lean_ctor_set(v___x_264_, 0, v___x_266_);
v___x_268_ = v___x_264_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(lean_object* v_msg_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_277_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0));
v___x_280_ = l_Lean_stringToMessageData(v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2));
v___x_283_ = l_Lean_stringToMessageData(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6));
v___x_289_ = l_Lean_stringToMessageData(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8));
v___x_292_ = l_Lean_stringToMessageData(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10));
v___x_295_ = l_Lean_stringToMessageData(v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object* v_rule_296_, lean_object* v_goal_297_, lean_object* v_ruleDesc_x3f_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_311_; 
lean_inc_ref(v_rule_296_);
lean_inc(v_goal_297_);
v___x_311_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_297_, v_rule_296_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
if (lean_obj_tag(v_a_312_) == 0)
{
uint8_t v_debug_313_; 
v_debug_313_ = lean_ctor_get_uint8(v_a_299_, sizeof(void*)*4 + 3);
if (v_debug_313_ == 0)
{
lean_dec(v_ruleDesc_x3f_298_);
lean_dec(v_goal_297_);
lean_dec_ref(v_rule_296_);
return v___x_311_;
}
else
{
lean_object* v___x_314_; 
lean_dec_ref_known(v___x_311_, 1);
v___x_314_ = l_Lean_MVarId_getType(v_goal_297_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_316_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc_n(v_a_315_, 2);
lean_dec_ref_known(v___x_314_, 1);
v___x_316_ = l_Lean_Meta_Sym_unfoldReducible(v_a_315_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_379_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_379_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_379_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_379_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
uint8_t v___x_321_; 
v___x_321_ = lean_expr_eqv(v_a_317_, v_a_315_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___f_325_; lean_object* v___x_326_; 
lean_del_object(v___x_319_);
v___x_322_ = lean_box(0);
v___x_323_ = lean_box(v___x_321_);
v___x_324_ = lean_box(v_debug_313_);
lean_inc_ref(v_rule_296_);
lean_inc(v_a_317_);
v___f_325_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed), 17, 5);
lean_closure_set(v___f_325_, 0, v_a_317_);
lean_closure_set(v___f_325_, 1, v___x_322_);
lean_closure_set(v___f_325_, 2, v_rule_296_);
lean_closure_set(v___f_325_, 3, v___x_323_);
lean_closure_set(v___f_325_, 4, v___x_324_);
v___x_326_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v___f_325_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_367_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_367_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_367_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_367_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___y_332_; uint8_t v___x_354_; 
v___x_354_ = lean_unbox(v_a_327_);
lean_dec(v_a_327_);
if (v___x_354_ == 0)
{
lean_object* v___x_356_; 
lean_dec(v_a_317_);
lean_dec(v_a_315_);
lean_dec(v_ruleDesc_x3f_298_);
lean_dec_ref(v_rule_296_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v_a_312_);
v___x_356_ = v___x_329_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_312_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
else
{
lean_del_object(v___x_329_);
if (lean_obj_tag(v_ruleDesc_x3f_298_) == 0)
{
lean_object* v_expr_358_; lean_object* v___x_359_; 
v_expr_358_ = lean_ctor_get(v_rule_296_, 0);
lean_inc_ref(v_expr_358_);
lean_dec_ref(v_rule_296_);
v___x_359_ = l_Lean_Expr_getAppFn(v_expr_358_);
lean_dec_ref(v_expr_358_);
if (lean_obj_tag(v___x_359_) == 4)
{
lean_object* v_declName_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_declName_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_declName_360_);
lean_dec_ref_known(v___x_359_, 2);
v___x_361_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9);
v___x_362_ = l_Lean_MessageData_ofConstName(v_declName_360_, v___x_321_);
v___x_363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_361_);
v___y_332_ = v___x_364_;
goto v___jp_331_;
}
else
{
lean_object* v___x_365_; 
lean_dec_ref(v___x_359_);
v___x_365_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11);
v___y_332_ = v___x_365_;
goto v___jp_331_;
}
}
else
{
lean_object* v_val_366_; 
lean_dec_ref(v_rule_296_);
v_val_366_ = lean_ctor_get(v_ruleDesc_x3f_298_, 0);
lean_inc(v_val_366_);
lean_dec_ref_known(v_ruleDesc_x3f_298_, 1);
v___y_332_ = v_val_366_;
goto v___jp_331_;
}
}
v___jp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v___x_333_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___y_332_);
v___x_335_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = l_Lean_indentExpr(v_a_315_);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5);
v___x_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = l_Lean_indentExpr(v_a_317_);
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7, &l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7);
v___x_344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_344_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v_a_317_);
lean_dec(v_a_315_);
lean_dec(v_ruleDesc_x3f_298_);
lean_dec_ref(v_rule_296_);
v_a_368_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_326_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_326_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_object* v___x_377_; 
lean_dec(v_a_317_);
lean_dec(v_a_315_);
lean_dec(v_ruleDesc_x3f_298_);
lean_dec_ref(v_rule_296_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v_a_312_);
v___x_377_ = v___x_319_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_312_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec(v_a_315_);
lean_dec(v_ruleDesc_x3f_298_);
lean_dec_ref(v_rule_296_);
v_a_380_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_316_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_316_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_ruleDesc_x3f_298_);
lean_dec_ref(v_rule_296_);
v_a_388_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_314_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_314_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_a_312_, 1);
lean_dec(v_ruleDesc_x3f_298_);
lean_dec(v_goal_297_);
lean_dec_ref(v_rule_296_);
return v___x_311_;
}
}
else
{
lean_dec(v_ruleDesc_x3f_298_);
lean_dec(v_goal_297_);
lean_dec_ref(v_rule_296_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(lean_object* v_rule_396_, lean_object* v_goal_397_, lean_object* v_ruleDesc_x3f_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_396_, v_goal_397_, v_ruleDesc_x3f_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(lean_object* v_00_u03b1_412_, lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_413_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(lean_object* v_00_u03b1_427_, lean_object* v_msg_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(v_00_u03b1_427_, v_msg_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(lean_object* v_goal_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
uint8_t v_internalize_454_; 
v_internalize_454_ = lean_ctor_get_uint8(v_a_443_, sizeof(void*)*4 + 4);
if (v_internalize_454_ == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v_goal_442_);
return v___x_455_;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_box(0);
v___x_457_ = l_Lean_Meta_Grind_processHypotheses(v_goal_442_, v___x_456_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg___boxed(lean_object* v_goal_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(v_goal_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses(lean_object* v_goal_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___redArg(v_goal_471_, v_a_472_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses___boxed(lean_object* v_goal_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_processHypotheses(v_goal_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Util_0__Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_collectBinders(lean_object* v_type_499_, lean_object* v_acc_500_){
_start:
{
switch(lean_obj_tag(v_type_499_))
{
case 7:
{
lean_object* v_binderName_501_; lean_object* v_body_502_; lean_object* v___x_503_; 
v_binderName_501_ = lean_ctor_get(v_type_499_, 0);
lean_inc(v_binderName_501_);
v_body_502_ = lean_ctor_get(v_type_499_, 2);
lean_inc_ref(v_body_502_);
lean_dec_ref_known(v_type_499_, 3);
v___x_503_ = lean_array_push(v_acc_500_, v_binderName_501_);
v_type_499_ = v_body_502_;
v_acc_500_ = v___x_503_;
goto _start;
}
case 8:
{
lean_object* v_declName_505_; lean_object* v_body_506_; lean_object* v___x_507_; 
v_declName_505_ = lean_ctor_get(v_type_499_, 0);
lean_inc(v_declName_505_);
v_body_506_ = lean_ctor_get(v_type_499_, 3);
lean_inc_ref(v_body_506_);
lean_dec_ref_known(v_type_499_, 4);
v___x_507_ = lean_array_push(v_acc_500_, v_declName_505_);
v_type_499_ = v_body_506_;
v_acc_500_ = v___x_507_;
goto _start;
}
default: 
{
lean_dec_ref(v_type_499_);
return v_acc_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___lam__0(lean_object* v_x_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
lean_inc(v___y_514_);
lean_inc_ref(v___y_513_);
lean_inc(v___y_512_);
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
v___x_522_ = lean_apply_12(v_x_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, lean_box(0));
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___lam__0___boxed(lean_object* v_x_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___lam__0(v_x_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(lean_object* v_mvarId_537_, lean_object* v_x_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___f_551_; lean_object* v___x_552_; 
lean_inc(v___y_545_);
lean_inc_ref(v___y_544_);
lean_inc(v___y_543_);
lean_inc_ref(v___y_542_);
lean_inc(v___y_541_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
v___f_551_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_551_, 0, v_x_538_);
lean_closure_set(v___f_551_, 1, v___y_539_);
lean_closure_set(v___f_551_, 2, v___y_540_);
lean_closure_set(v___f_551_, 3, v___y_541_);
lean_closure_set(v___f_551_, 4, v___y_542_);
lean_closure_set(v___f_551_, 5, v___y_543_);
lean_closure_set(v___f_551_, 6, v___y_544_);
lean_closure_set(v___f_551_, 7, v___y_545_);
v___x_552_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_537_, v___f_551_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
if (lean_obj_tag(v___x_552_) == 0)
{
return v___x_552_;
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg___boxed(lean_object* v_mvarId_561_, lean_object* v_x_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(v_mvarId_561_, v_x_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1(lean_object* v_00_u03b1_576_, lean_object* v_mvarId_577_, lean_object* v_x_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(v_mvarId_577_, v_x_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___boxed(lean_object* v_00_u03b1_592_, lean_object* v_mvarId_593_, lean_object* v_x_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1(v_00_u03b1_592_, v_mvarId_593_, v_x_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg(lean_object* v_upperBound_608_, lean_object* v_overrides_609_, lean_object* v_binderNames_610_, lean_object* v_a_611_, lean_object* v_b_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___y_618_; uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_lt(v_a_611_, v_upperBound_608_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
lean_dec(v_a_611_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v_b_612_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_array_get_size(v_overrides_609_);
v___x_636_ = lean_nat_dec_lt(v_a_611_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
v___x_637_ = lean_array_fget_borrowed(v_binderNames_610_, v_a_611_);
lean_inc(v___x_637_);
v___y_618_ = v___x_637_;
goto v___jp_617_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_array_fget_borrowed(v_overrides_609_, v_a_611_);
lean_inc(v___x_638_);
v___y_618_ = v___x_638_;
goto v___jp_617_;
}
}
v___jp_617_:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v___y_618_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 1);
v___x_621_ = lean_array_push(v_b_612_, v_a_620_);
v___x_622_ = lean_unsigned_to_nat(1u);
v___x_623_ = lean_nat_add(v_a_611_, v___x_622_);
lean_dec(v_a_611_);
v_a_611_ = v___x_623_;
v_b_612_ = v___x_621_;
goto _start;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v_b_612_);
lean_dec(v_a_611_);
v_a_625_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_619_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_619_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg___boxed(lean_object* v_upperBound_639_, lean_object* v_overrides_640_, lean_object* v_binderNames_641_, lean_object* v_a_642_, lean_object* v_b_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg(v_upperBound_639_, v_overrides_640_, v_binderNames_641_, v_a_642_, v_b_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v_binderNames_641_);
lean_dec_ref(v_overrides_640_);
lean_dec(v_upperBound_639_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0(lean_object* v_goal_651_, lean_object* v_overrides_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
lean_inc(v_goal_651_);
v___x_665_ = l_Lean_MVarId_getType(v_goal_651_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_709_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_709_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_709_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_709_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v_names_671_; lean_object* v_binderNames_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_670_ = lean_unsigned_to_nat(0u);
v_names_671_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___closed__0));
v_binderNames_672_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Util_0__Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_collectBinders(v_a_666_, v_names_671_);
v___x_673_ = lean_array_get_size(v_binderNames_672_);
v___x_674_ = lean_nat_dec_eq(v___x_673_, v___x_670_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_del_object(v___x_668_);
v___x_675_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg(v___x_673_, v_overrides_652_, v_binderNames_672_, v___x_670_, v_names_671_, v___y_660_, v___y_662_, v___y_663_);
lean_dec_ref(v_binderNames_672_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
lean_inc(v_goal_651_);
v___x_677_ = l_Lean_Meta_Sym_intros(v_goal_651_, v_a_676_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_689_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_689_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_689_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_689_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
if (lean_obj_tag(v_a_678_) == 1)
{
lean_object* v_mvarId_682_; lean_object* v___x_684_; 
lean_dec(v_goal_651_);
v_mvarId_682_ = lean_ctor_get(v_a_678_, 1);
lean_inc(v_mvarId_682_);
lean_dec_ref_known(v_a_678_, 2);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v_mvarId_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_mvarId_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
else
{
lean_object* v___x_687_; 
lean_dec(v_a_678_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v_goal_651_);
v___x_687_ = v___x_680_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_goal_651_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec(v_goal_651_);
v_a_690_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_677_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_677_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_goal_651_);
v_a_698_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_675_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_675_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v___x_707_; 
lean_dec_ref(v_binderNames_672_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v_goal_651_);
v___x_707_ = v___x_668_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_goal_651_);
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
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v_goal_651_);
v_a_710_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_665_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_665_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___boxed(lean_object* v_goal_718_, lean_object* v_overrides_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0(v_goal_718_, v_overrides_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec_ref(v_overrides_719_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(lean_object* v_goal_733_, lean_object* v_overrides_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___f_747_; lean_object* v___x_748_; 
lean_inc(v_goal_733_);
v___f_747_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___boxed), 14, 2);
lean_closure_set(v___f_747_, 0, v_goal_733_);
lean_closure_set(v___f_747_, 1, v_overrides_734_);
v___x_748_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(v_goal_733_, v___f_747_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___boxed(lean_object* v_goal_749_, lean_object* v_overrides_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(v_goal_749_, v_overrides_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0(lean_object* v_upperBound_764_, lean_object* v_overrides_765_, lean_object* v_binderNames_766_, lean_object* v_inst_767_, lean_object* v_R_768_, lean_object* v_a_769_, lean_object* v_b_770_, lean_object* v_c_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___redArg(v_upperBound_764_, v_overrides_765_, v_binderNames_766_, v_a_769_, v_b_770_, v___y_779_, v___y_781_, v___y_782_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_785_ = _args[0];
lean_object* v_overrides_786_ = _args[1];
lean_object* v_binderNames_787_ = _args[2];
lean_object* v_inst_788_ = _args[3];
lean_object* v_R_789_ = _args[4];
lean_object* v_a_790_ = _args[5];
lean_object* v_b_791_ = _args[6];
lean_object* v_c_792_ = _args[7];
lean_object* v___y_793_ = _args[8];
lean_object* v___y_794_ = _args[9];
lean_object* v___y_795_ = _args[10];
lean_object* v___y_796_ = _args[11];
lean_object* v___y_797_ = _args[12];
lean_object* v___y_798_ = _args[13];
lean_object* v___y_799_ = _args[14];
lean_object* v___y_800_ = _args[15];
lean_object* v___y_801_ = _args[16];
lean_object* v___y_802_ = _args[17];
lean_object* v___y_803_ = _args[18];
lean_object* v___y_804_ = _args[19];
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__0(v_upperBound_785_, v_overrides_786_, v_binderNames_787_, v_inst_788_, v_R_789_, v_a_790_, v_b_791_, v_c_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec_ref(v_binderNames_787_);
lean_dec_ref(v_overrides_786_);
lean_dec(v_upperBound_785_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(lean_object* v_goal_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_hypSimpMethods_820_; 
v_hypSimpMethods_820_ = lean_ctor_get(v_a_811_, 1);
if (lean_obj_tag(v_hypSimpMethods_820_) == 1)
{
lean_object* v_val_821_; lean_object* v___x_822_; 
v_val_821_ = lean_ctor_get(v_hypSimpMethods_820_, 0);
lean_inc(v_goal_810_);
v___x_822_ = l_Lean_MVarId_getType(v_goal_810_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_824_; lean_object* v_post_825_; lean_object* v_simpState_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = lean_st_ref_get(v_a_812_);
v_post_825_ = lean_ctor_get(v_val_821_, 1);
v_simpState_826_ = lean_ctor_get(v___x_824_, 6);
lean_inc_ref(v_simpState_826_);
lean_dec(v___x_824_);
v___x_827_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___closed__0));
lean_inc_ref(v_post_825_);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_post_825_);
v___x_829_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_829_, 0, v_a_823_);
v___x_830_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___closed__1));
v___x_831_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_829_, v___x_828_, v___x_830_, v_simpState_826_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v_fst_833_; lean_object* v_snd_834_; lean_object* v___x_835_; lean_object* v_specBackwardRuleCache_836_; lean_object* v_splitBackwardRuleCache_837_; lean_object* v_latticeBackwardRuleCache_838_; lean_object* v_frameDB_x3f_839_; lean_object* v_invariants_840_; lean_object* v_vcs_841_; lean_object* v_fuel_842_; lean_object* v_inlineHandledInvariants_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_852_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
v_fst_833_ = lean_ctor_get(v_a_832_, 0);
lean_inc(v_fst_833_);
v_snd_834_ = lean_ctor_get(v_a_832_, 1);
lean_inc(v_snd_834_);
lean_dec(v_a_832_);
v___x_835_ = lean_st_ref_take(v_a_812_);
v_specBackwardRuleCache_836_ = lean_ctor_get(v___x_835_, 0);
v_splitBackwardRuleCache_837_ = lean_ctor_get(v___x_835_, 1);
v_latticeBackwardRuleCache_838_ = lean_ctor_get(v___x_835_, 2);
v_frameDB_x3f_839_ = lean_ctor_get(v___x_835_, 3);
v_invariants_840_ = lean_ctor_get(v___x_835_, 4);
v_vcs_841_ = lean_ctor_get(v___x_835_, 5);
v_fuel_842_ = lean_ctor_get(v___x_835_, 7);
v_inlineHandledInvariants_843_ = lean_ctor_get(v___x_835_, 8);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v___x_835_, 6);
lean_dec(v_unused_853_);
v___x_845_ = v___x_835_;
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_inlineHandledInvariants_843_);
lean_inc(v_fuel_842_);
lean_inc(v_vcs_841_);
lean_inc(v_invariants_840_);
lean_inc(v_frameDB_x3f_839_);
lean_inc(v_latticeBackwardRuleCache_838_);
lean_inc(v_splitBackwardRuleCache_837_);
lean_inc(v_specBackwardRuleCache_836_);
lean_dec(v___x_835_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 6, v_snd_834_);
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_specBackwardRuleCache_836_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_splitBackwardRuleCache_837_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_latticeBackwardRuleCache_838_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_frameDB_x3f_839_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v_invariants_840_);
lean_ctor_set(v_reuseFailAlloc_851_, 5, v_vcs_841_);
lean_ctor_set(v_reuseFailAlloc_851_, 6, v_snd_834_);
lean_ctor_set(v_reuseFailAlloc_851_, 7, v_fuel_842_);
lean_ctor_set(v_reuseFailAlloc_851_, 8, v_inlineHandledInvariants_843_);
v___x_848_ = v_reuseFailAlloc_851_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_st_ref_set(v_a_812_, v___x_848_);
v___x_850_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_fst_833_, v_goal_810_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
return v___x_850_;
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_goal_810_);
v_a_854_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_831_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_831_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_goal_810_);
v_a_862_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_822_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_822_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec(v_goal_810_);
v___x_870_ = lean_box(0);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg___boxed(lean_object* v_goal_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_goal_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope(lean_object* v_goal_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_goal_883_, v_a_884_, v_a_885_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___boxed(lean_object* v_goal_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope(v_goal_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
return v_res_910_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__12(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__11));
v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
return v___x_922_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__9(void){
_start:
{
uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = 0;
v___x_929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__8));
v___x_930_ = l_Lean_MessageData_ofConstName(v___x_929_, v___x_928_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__6(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__5));
v___x_933_ = l_Lean_stringToMessageData(v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__10(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__9, &l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__9);
v___x_935_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__6);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__13(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__12, &l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__12_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__12);
v___x_938_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__10, &l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__10_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__10);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_937_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0(lean_object* v_goal_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
lean_inc(v_goal_940_);
v___x_953_ = l_Lean_MVarId_getType(v_goal_940_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1031_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_1031_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1031_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_963_; uint8_t v___x_964_; 
lean_inc(v_a_954_);
v___x_963_ = l_Lean_Expr_cleanupAnnotations(v_a_954_);
v___x_964_ = l_Lean_Expr_isApp(v___x_963_);
if (v___x_964_ == 0)
{
lean_dec_ref(v___x_963_);
lean_dec(v_a_954_);
lean_dec(v_goal_940_);
goto v___jp_958_;
}
else
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_963_);
v___x_966_ = l_Lean_Expr_isApp(v___x_965_);
if (v___x_966_ == 0)
{
lean_dec_ref(v___x_965_);
lean_dec(v_a_954_);
lean_dec(v_goal_940_);
goto v___jp_958_;
}
else
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_965_);
v___x_968_ = l_Lean_Expr_isApp(v___x_967_);
if (v___x_968_ == 0)
{
lean_dec_ref(v___x_967_);
lean_dec(v_a_954_);
lean_dec(v_goal_940_);
goto v___jp_958_;
}
else
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = l_Lean_Expr_appFnCleanup___redArg(v___x_967_);
v___x_970_ = l_Lean_Expr_isApp(v___x_969_);
if (v___x_970_ == 0)
{
lean_dec_ref(v___x_969_);
lean_dec(v_a_954_);
lean_dec(v_goal_940_);
goto v___jp_958_;
}
else
{
lean_object* v_arg_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_arg_971_ = lean_ctor_get(v___x_969_, 1);
lean_inc_ref(v_arg_971_);
v___x_972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_969_);
v___x_973_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__4));
v___x_974_ = l_Lean_Expr_isConstOf(v___x_972_, v___x_973_);
lean_dec_ref(v___x_972_);
if (v___x_974_ == 0)
{
lean_dec_ref(v_arg_971_);
lean_dec(v_a_954_);
lean_dec(v_goal_940_);
goto v___jp_958_;
}
else
{
uint8_t v___x_975_; 
lean_del_object(v___x_956_);
v___x_975_ = l_Lean_Expr_isForall(v_arg_971_);
lean_dec_ref(v_arg_971_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; 
lean_dec(v_a_954_);
lean_dec(v_goal_940_);
v___x_976_ = lean_box(0);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
else
{
lean_object* v_backwardRules_978_; lean_object* v_stateArgIntro_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_backwardRules_978_ = lean_ctor_get(v___y_941_, 0);
v_stateArgIntro_979_ = lean_ctor_get(v_backwardRules_978_, 1);
v___x_980_ = lean_box(0);
lean_inc_ref(v_stateArgIntro_979_);
v___x_981_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_stateArgIntro_979_, v_goal_940_, v___x_980_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
if (lean_obj_tag(v_a_982_) == 1)
{
lean_object* v_mvarIds_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1022_; 
v_mvarIds_992_ = lean_ctor_get(v_a_982_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_a_982_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_994_ = v_a_982_;
v_isShared_995_ = v_isSharedCheck_1022_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_mvarIds_992_);
lean_dec(v_a_982_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1022_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
if (lean_obj_tag(v_mvarIds_992_) == 1)
{
lean_object* v_tail_996_; 
v_tail_996_ = lean_ctor_get(v_mvarIds_992_, 1);
if (lean_obj_tag(v_tail_996_) == 0)
{
lean_object* v_head_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
lean_dec(v_a_954_);
v_head_997_ = lean_ctor_get(v_mvarIds_992_, 0);
lean_inc(v_head_997_);
lean_dec_ref_known(v_mvarIds_992_, 2);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___closed__0));
v___x_999_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(v_head_997_, v___x_998_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc_n(v_a_1000_, 2);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(v_a_1000_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
if (lean_obj_tag(v_a_1002_) == 0)
{
lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1012_; 
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v___x_1001_, 0);
lean_dec(v_unused_1013_);
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1012_;
goto v_resetjp_1003_;
}
else
{
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1012_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v_a_1000_);
v___x_1007_ = v___x_994_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1000_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1007_);
v___x_1009_ = v___x_1004_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_1002_, 1);
lean_dec(v_a_1000_);
lean_del_object(v___x_994_);
return v___x_1001_;
}
}
else
{
lean_dec(v_a_1000_);
lean_del_object(v___x_994_);
return v___x_1001_;
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_del_object(v___x_994_);
v_a_1014_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_999_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_999_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_992_, 2);
lean_del_object(v___x_994_);
v___y_984_ = v___y_948_;
v___y_985_ = v___y_949_;
v___y_986_ = v___y_950_;
v___y_987_ = v___y_951_;
goto v___jp_983_;
}
}
else
{
lean_del_object(v___x_994_);
lean_dec(v_mvarIds_992_);
v___y_984_ = v___y_948_;
v___y_985_ = v___y_949_;
v___y_986_ = v___y_950_;
v___y_987_ = v___y_951_;
goto v___jp_983_;
}
}
}
else
{
lean_dec(v_a_982_);
v___y_984_ = v___y_948_;
v___y_985_ = v___y_949_;
v___y_986_ = v___y_950_;
v___y_987_ = v___y_951_;
goto v___jp_983_;
}
v___jp_983_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_988_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__13, &l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___closed__13);
v___x_989_ = l_Lean_indentExpr(v_a_954_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_990_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
return v___x_991_;
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_a_954_);
v_a_1023_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_981_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_981_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
}
}
}
v___jp_958_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_box(0);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_959_);
v___x_961_ = v___x_956_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_goal_940_);
v_a_1032_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_953_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_953_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___boxed(lean_object* v_goal_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0(v_goal_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(lean_object* v_goal_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___f_1067_; lean_object* v___x_1068_; 
lean_inc(v_goal_1054_);
v___f_1067_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1067_, 0, v_goal_1054_);
v___x_1068_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(v_goal_1054_, v___f_1067_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs___boxed(lean_object* v_goal_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(v_goal_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg(lean_object* v_e_1083_, lean_object* v___y_1084_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = l_Lean_Expr_hasMVar(v_e_1083_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_e_1083_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; lean_object* v_mctx_1089_; lean_object* v___x_1090_; lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v___x_1093_; lean_object* v_cache_1094_; lean_object* v_zetaDeltaFVarIds_1095_; lean_object* v_postponed_1096_; lean_object* v_diag_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1106_; 
v___x_1088_ = lean_st_ref_get(v___y_1084_);
v_mctx_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc_ref(v_mctx_1089_);
lean_dec(v___x_1088_);
v___x_1090_ = l_Lean_instantiateMVarsCore(v_mctx_1089_, v_e_1083_);
v_fst_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_fst_1091_);
v_snd_1092_ = lean_ctor_get(v___x_1090_, 1);
lean_inc(v_snd_1092_);
lean_dec_ref(v___x_1090_);
v___x_1093_ = lean_st_ref_take(v___y_1084_);
v_cache_1094_ = lean_ctor_get(v___x_1093_, 1);
v_zetaDeltaFVarIds_1095_ = lean_ctor_get(v___x_1093_, 2);
v_postponed_1096_ = lean_ctor_get(v___x_1093_, 3);
v_diag_1097_ = lean_ctor_get(v___x_1093_, 4);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; 
v_unused_1107_ = lean_ctor_get(v___x_1093_, 0);
lean_dec(v_unused_1107_);
v___x_1099_ = v___x_1093_;
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_diag_1097_);
lean_inc(v_postponed_1096_);
lean_inc(v_zetaDeltaFVarIds_1095_);
lean_inc(v_cache_1094_);
lean_dec(v___x_1093_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_snd_1092_);
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_snd_1092_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_cache_1094_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_zetaDeltaFVarIds_1095_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_postponed_1096_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_diag_1097_);
v___x_1102_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_st_ref_set(v___y_1084_, v___x_1102_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_fst_1091_);
return v___x_1104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg___boxed(lean_object* v_e_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg(v_e_1108_, v___y_1109_);
lean_dec(v___y_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0(lean_object* v_e_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg(v_e_1112_, v___y_1121_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___boxed(lean_object* v_e_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0(v_e_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_){
_start:
{
lean_object* v_ks_1144_; lean_object* v_vs_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1169_; 
v_ks_1144_ = lean_ctor_get(v_x_1140_, 0);
v_vs_1145_ = lean_ctor_get(v_x_1140_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1147_ = v_x_1140_;
v_isShared_1148_ = v_isSharedCheck_1169_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_vs_1145_);
lean_inc(v_ks_1144_);
lean_dec(v_x_1140_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1169_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = lean_array_get_size(v_ks_1144_);
v___x_1150_ = lean_nat_dec_lt(v_x_1141_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
lean_dec(v_x_1141_);
v___x_1151_ = lean_array_push(v_ks_1144_, v_x_1142_);
v___x_1152_ = lean_array_push(v_vs_1145_, v_x_1143_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___x_1152_);
lean_ctor_set(v___x_1147_, 0, v___x_1151_);
v___x_1154_ = v___x_1147_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
else
{
lean_object* v_k_x27_1156_; uint8_t v___x_1157_; 
v_k_x27_1156_ = lean_array_fget_borrowed(v_ks_1144_, v_x_1141_);
v___x_1157_ = l_Lean_instBEqMVarId_beq(v_x_1142_, v_k_x27_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1159_; 
if (v_isShared_1148_ == 0)
{
v___x_1159_ = v___x_1147_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_ks_1144_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_vs_1145_);
v___x_1159_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_add(v_x_1141_, v___x_1160_);
lean_dec(v_x_1141_);
v_x_1140_ = v___x_1159_;
v_x_1141_ = v___x_1161_;
goto _start;
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1164_ = lean_array_fset(v_ks_1144_, v_x_1141_, v_x_1142_);
v___x_1165_ = lean_array_fset(v_vs_1145_, v_x_1141_, v_x_1143_);
lean_dec(v_x_1141_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___x_1165_);
lean_ctor_set(v___x_1147_, 0, v___x_1164_);
v___x_1167_ = v___x_1147_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1165_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_1170_, lean_object* v_k_1171_, lean_object* v_v_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_1170_, v___x_1173_, v_k_1171_, v_v_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1176_, size_t v_x_1177_, size_t v_x_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
if (lean_obj_tag(v_x_1176_) == 0)
{
lean_object* v_es_1181_; size_t v___x_1182_; size_t v___x_1183_; lean_object* v_j_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v_es_1181_ = lean_ctor_get(v_x_1176_, 0);
v___x_1182_ = ((size_t)31ULL);
v___x_1183_ = lean_usize_land(v_x_1177_, v___x_1182_);
v_j_1184_ = lean_usize_to_nat(v___x_1183_);
v___x_1185_ = lean_array_get_size(v_es_1181_);
v___x_1186_ = lean_nat_dec_lt(v_j_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_dec(v_j_1184_);
lean_dec(v_x_1180_);
lean_dec(v_x_1179_);
return v_x_1176_;
}
else
{
lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1225_; 
lean_inc_ref(v_es_1181_);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v_x_1176_, 0);
lean_dec(v_unused_1226_);
v___x_1188_ = v_x_1176_;
v_isShared_1189_ = v_isSharedCheck_1225_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v_x_1176_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1225_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_v_1190_; lean_object* v___x_1191_; lean_object* v_xs_x27_1192_; lean_object* v___y_1194_; 
v_v_1190_ = lean_array_fget(v_es_1181_, v_j_1184_);
v___x_1191_ = lean_box(0);
v_xs_x27_1192_ = lean_array_fset(v_es_1181_, v_j_1184_, v___x_1191_);
switch(lean_obj_tag(v_v_1190_))
{
case 0:
{
lean_object* v_key_1199_; lean_object* v_val_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1210_; 
v_key_1199_ = lean_ctor_get(v_v_1190_, 0);
v_val_1200_ = lean_ctor_get(v_v_1190_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_v_1190_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1202_ = v_v_1190_;
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_val_1200_);
lean_inc(v_key_1199_);
lean_dec(v_v_1190_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
uint8_t v___x_1204_; 
v___x_1204_ = l_Lean_instBEqMVarId_beq(v_x_1179_, v_key_1199_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_del_object(v___x_1202_);
v___x_1205_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1199_, v_val_1200_, v_x_1179_, v_x_1180_);
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
v___y_1194_ = v___x_1206_;
goto v___jp_1193_;
}
else
{
lean_object* v___x_1208_; 
lean_dec(v_val_1200_);
lean_dec(v_key_1199_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v_x_1180_);
lean_ctor_set(v___x_1202_, 0, v_x_1179_);
v___x_1208_ = v___x_1202_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_x_1179_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_x_1180_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
v___y_1194_ = v___x_1208_;
goto v___jp_1193_;
}
}
}
}
case 1:
{
lean_object* v_node_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1223_; 
v_node_1211_ = lean_ctor_get(v_v_1190_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_v_1190_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1213_ = v_v_1190_;
v_isShared_1214_ = v_isSharedCheck_1223_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_node_1211_);
lean_dec(v_v_1190_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1223_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
size_t v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1215_ = ((size_t)5ULL);
v___x_1216_ = lean_usize_shift_right(v_x_1177_, v___x_1215_);
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_x_1178_, v___x_1217_);
v___x_1219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(v_node_1211_, v___x_1216_, v___x_1218_, v_x_1179_, v_x_1180_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1219_);
v___x_1221_ = v___x_1213_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v___y_1194_ = v___x_1221_;
goto v___jp_1193_;
}
}
}
default: 
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_x_1179_);
lean_ctor_set(v___x_1224_, 1, v_x_1180_);
v___y_1194_ = v___x_1224_;
goto v___jp_1193_;
}
}
v___jp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_array_fset(v_xs_x27_1192_, v_j_1184_, v___y_1194_);
lean_dec(v_j_1184_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1195_);
v___x_1197_ = v___x_1188_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
else
{
lean_object* v_ks_1227_; lean_object* v_vs_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1248_; 
v_ks_1227_ = lean_ctor_get(v_x_1176_, 0);
v_vs_1228_ = lean_ctor_get(v_x_1176_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1230_ = v_x_1176_;
v_isShared_1231_ = v_isSharedCheck_1248_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_vs_1228_);
lean_inc(v_ks_1227_);
lean_dec(v_x_1176_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1248_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_ks_1227_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_vs_1228_);
v___x_1233_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v_newNode_1234_; uint8_t v___y_1236_; size_t v___x_1242_; uint8_t v___x_1243_; 
v_newNode_1234_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3___redArg(v___x_1233_, v_x_1179_, v_x_1180_);
v___x_1242_ = ((size_t)7ULL);
v___x_1243_ = lean_usize_dec_le(v___x_1242_, v_x_1178_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1244_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1234_);
v___x_1245_ = lean_unsigned_to_nat(4u);
v___x_1246_ = lean_nat_dec_lt(v___x_1244_, v___x_1245_);
lean_dec(v___x_1244_);
v___y_1236_ = v___x_1246_;
goto v___jp_1235_;
}
else
{
v___y_1236_ = v___x_1243_;
goto v___jp_1235_;
}
v___jp_1235_:
{
if (v___y_1236_ == 0)
{
lean_object* v_ks_1237_; lean_object* v_vs_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_ks_1237_ = lean_ctor_get(v_newNode_1234_, 0);
lean_inc_ref(v_ks_1237_);
v_vs_1238_ = lean_ctor_get(v_newNode_1234_, 1);
lean_inc_ref(v_vs_1238_);
lean_dec_ref(v_newNode_1234_);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_1241_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg(v_x_1178_, v_ks_1237_, v_vs_1238_, v___x_1239_, v___x_1240_);
lean_dec_ref(v_vs_1238_);
lean_dec_ref(v_ks_1237_);
return v___x_1241_;
}
else
{
return v_newNode_1234_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_1249_, lean_object* v_keys_1250_, lean_object* v_vals_1251_, lean_object* v_i_1252_, lean_object* v_entries_1253_){
_start:
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_array_get_size(v_keys_1250_);
v___x_1255_ = lean_nat_dec_lt(v_i_1252_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec(v_i_1252_);
return v_entries_1253_;
}
else
{
lean_object* v_k_1256_; lean_object* v_v_1257_; uint64_t v___x_1258_; size_t v_h_1259_; size_t v___x_1260_; lean_object* v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; size_t v_h_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_k_1256_ = lean_array_fget_borrowed(v_keys_1250_, v_i_1252_);
v_v_1257_ = lean_array_fget_borrowed(v_vals_1251_, v_i_1252_);
v___x_1258_ = l_Lean_instHashableMVarId_hash(v_k_1256_);
v_h_1259_ = lean_uint64_to_usize(v___x_1258_);
v___x_1260_ = ((size_t)5ULL);
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = ((size_t)1ULL);
v___x_1263_ = lean_usize_sub(v_depth_1249_, v___x_1262_);
v___x_1264_ = lean_usize_mul(v___x_1260_, v___x_1263_);
v_h_1265_ = lean_usize_shift_right(v_h_1259_, v___x_1264_);
v___x_1266_ = lean_nat_add(v_i_1252_, v___x_1261_);
lean_dec(v_i_1252_);
lean_inc(v_v_1257_);
lean_inc(v_k_1256_);
v___x_1267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(v_entries_1253_, v_h_1265_, v_depth_1249_, v_k_1256_, v_v_1257_);
v_i_1252_ = v___x_1266_;
v_entries_1253_ = v___x_1267_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_1269_, lean_object* v_keys_1270_, lean_object* v_vals_1271_, lean_object* v_i_1272_, lean_object* v_entries_1273_){
_start:
{
size_t v_depth_boxed_1274_; lean_object* v_res_1275_; 
v_depth_boxed_1274_ = lean_unbox_usize(v_depth_1269_);
lean_dec(v_depth_1269_);
v_res_1275_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_1274_, v_keys_1270_, v_vals_1271_, v_i_1272_, v_entries_1273_);
lean_dec_ref(v_vals_1271_);
lean_dec_ref(v_keys_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
size_t v_x_59175__boxed_1281_; size_t v_x_59176__boxed_1282_; lean_object* v_res_1283_; 
v_x_59175__boxed_1281_ = lean_unbox_usize(v_x_1277_);
lean_dec(v_x_1277_);
v_x_59176__boxed_1282_ = lean_unbox_usize(v_x_1278_);
lean_dec(v_x_1278_);
v_res_1283_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(v_x_1276_, v_x_59175__boxed_1281_, v_x_59176__boxed_1282_, v_x_1279_, v_x_1280_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1___redArg(lean_object* v_x_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_){
_start:
{
uint64_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1287_ = l_Lean_instHashableMVarId_hash(v_x_1285_);
v___x_1288_ = lean_uint64_to_usize(v___x_1287_);
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(v_x_1284_, v___x_1288_, v___x_1289_, v_x_1285_, v_x_1286_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(lean_object* v_mvarId_1291_, lean_object* v_val_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; lean_object* v_mctx_1296_; lean_object* v_cache_1297_; lean_object* v_zetaDeltaFVarIds_1298_; lean_object* v_postponed_1299_; lean_object* v_diag_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1328_; 
v___x_1295_ = lean_st_ref_take(v___y_1293_);
v_mctx_1296_ = lean_ctor_get(v___x_1295_, 0);
v_cache_1297_ = lean_ctor_get(v___x_1295_, 1);
v_zetaDeltaFVarIds_1298_ = lean_ctor_get(v___x_1295_, 2);
v_postponed_1299_ = lean_ctor_get(v___x_1295_, 3);
v_diag_1300_ = lean_ctor_get(v___x_1295_, 4);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1302_ = v___x_1295_;
v_isShared_1303_ = v_isSharedCheck_1328_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_diag_1300_);
lean_inc(v_postponed_1299_);
lean_inc(v_zetaDeltaFVarIds_1298_);
lean_inc(v_cache_1297_);
lean_inc(v_mctx_1296_);
lean_dec(v___x_1295_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1328_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v_depth_1304_; lean_object* v_levelAssignDepth_1305_; lean_object* v_lmvarCounter_1306_; lean_object* v_mvarCounter_1307_; lean_object* v_lDecls_1308_; lean_object* v_decls_1309_; lean_object* v_userNames_1310_; lean_object* v_lAssignment_1311_; lean_object* v_eAssignment_1312_; lean_object* v_dAssignment_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1327_; 
v_depth_1304_ = lean_ctor_get(v_mctx_1296_, 0);
v_levelAssignDepth_1305_ = lean_ctor_get(v_mctx_1296_, 1);
v_lmvarCounter_1306_ = lean_ctor_get(v_mctx_1296_, 2);
v_mvarCounter_1307_ = lean_ctor_get(v_mctx_1296_, 3);
v_lDecls_1308_ = lean_ctor_get(v_mctx_1296_, 4);
v_decls_1309_ = lean_ctor_get(v_mctx_1296_, 5);
v_userNames_1310_ = lean_ctor_get(v_mctx_1296_, 6);
v_lAssignment_1311_ = lean_ctor_get(v_mctx_1296_, 7);
v_eAssignment_1312_ = lean_ctor_get(v_mctx_1296_, 8);
v_dAssignment_1313_ = lean_ctor_get(v_mctx_1296_, 9);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_mctx_1296_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1315_ = v_mctx_1296_;
v_isShared_1316_ = v_isSharedCheck_1327_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_dAssignment_1313_);
lean_inc(v_eAssignment_1312_);
lean_inc(v_lAssignment_1311_);
lean_inc(v_userNames_1310_);
lean_inc(v_decls_1309_);
lean_inc(v_lDecls_1308_);
lean_inc(v_mvarCounter_1307_);
lean_inc(v_lmvarCounter_1306_);
lean_inc(v_levelAssignDepth_1305_);
lean_inc(v_depth_1304_);
lean_dec(v_mctx_1296_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1327_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1___redArg(v_eAssignment_1312_, v_mvarId_1291_, v_val_1292_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 8, v___x_1317_);
v___x_1319_ = v___x_1315_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_depth_1304_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_levelAssignDepth_1305_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_lmvarCounter_1306_);
lean_ctor_set(v_reuseFailAlloc_1326_, 3, v_mvarCounter_1307_);
lean_ctor_set(v_reuseFailAlloc_1326_, 4, v_lDecls_1308_);
lean_ctor_set(v_reuseFailAlloc_1326_, 5, v_decls_1309_);
lean_ctor_set(v_reuseFailAlloc_1326_, 6, v_userNames_1310_);
lean_ctor_set(v_reuseFailAlloc_1326_, 7, v_lAssignment_1311_);
lean_ctor_set(v_reuseFailAlloc_1326_, 8, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1326_, 9, v_dAssignment_1313_);
v___x_1319_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1321_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1319_);
v___x_1321_ = v___x_1302_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_cache_1297_);
lean_ctor_set(v_reuseFailAlloc_1325_, 2, v_zetaDeltaFVarIds_1298_);
lean_ctor_set(v_reuseFailAlloc_1325_, 3, v_postponed_1299_);
lean_ctor_set(v_reuseFailAlloc_1325_, 4, v_diag_1300_);
v___x_1321_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = lean_st_ref_set(v___y_1293_, v___x_1321_);
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg___boxed(lean_object* v_mvarId_1329_, lean_object* v_val_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_mvarId_1329_, v_val_1330_, v___y_1331_);
lean_dec(v___y_1331_);
return v_res_1333_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__8));
v___x_1349_ = l_Lean_stringToMessageData(v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__12));
v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__14(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = lean_box(0);
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__3));
v___x_1359_ = l_Lean_mkConst(v___x_1358_, v___x_1357_);
return v___x_1359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__17(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__16));
v___x_1366_ = l_Lean_mkConst(v___x_1365_, v___x_1364_);
return v___x_1366_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__20(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = lean_box(0);
v___x_1372_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__19));
v___x_1373_ = l_Lean_mkConst(v___x_1372_, v___x_1371_);
return v___x_1373_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__22(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = lean_box(0);
v___x_1378_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__21));
v___x_1379_ = l_Lean_mkConst(v___x_1378_, v___x_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0(lean_object* v_goal_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
lean_inc(v_goal_1380_);
v___x_1393_ = l_Lean_MVarId_getType(v_goal_1380_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1395_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1395_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__0___redArg(v_a_1394_, v___y_1389_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1658_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1658_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1658_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__1));
v___x_1401_ = l_Lean_Expr_isAppOf(v_a_1396_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__3));
v___x_1403_ = l_Lean_Expr_isAppOf(v_a_1396_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1404_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__5));
v___x_1405_ = lean_unsigned_to_nat(3u);
v___x_1406_ = l_Lean_Expr_isAppOfArity(v_a_1396_, v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_dec(v_a_1396_);
v___x_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1407_, 0, v_goal_1380_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1407_);
v___x_1409_ = v___x_1398_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_del_object(v___x_1398_);
v___x_1411_ = l_Lean_Expr_appFn_x21(v_a_1396_);
v___x_1412_ = l_Lean_Expr_appArg_x21(v___x_1411_);
v___x_1413_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v___x_1412_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1415_ = l_Lean_Expr_appArg_x21(v_a_1396_);
lean_dec(v_a_1396_);
v___x_1416_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(v___x_1415_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = l_Lean_Expr_appFn_x21(v___x_1411_);
lean_dec_ref(v___x_1411_);
v___x_1419_ = l_Lean_Expr_appArg_x21(v___x_1418_);
lean_dec_ref(v___x_1418_);
lean_inc_ref(v___x_1419_);
v___x_1420_ = l_Lean_Meta_getLevel(v___x_1419_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1423_, 0, v_a_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = l_Lean_mkConst(v___x_1404_, v___x_1423_);
lean_inc(v_a_1417_);
lean_inc(v_a_1414_);
lean_inc_ref(v___x_1419_);
v___x_1425_ = l_Lean_mkApp3(v___x_1424_, v___x_1419_, v_a_1414_, v_a_1417_);
v___x_1426_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_1380_, v___x_1425_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic___lam__0___closed__0));
lean_inc(v_a_1414_);
v___x_1429_ = l_Lean_Meta_Sym_isDefEqS(v_a_1414_, v_a_1417_, v___x_1406_, v___x_1406_, v___x_1428_, v___x_1428_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1471_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1471_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1471_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_unbox(v_a_1430_);
lean_dec(v_a_1430_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
lean_dec_ref(v___x_1419_);
lean_dec(v_a_1414_);
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_a_1427_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1435_);
v___x_1437_ = v___x_1432_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
else
{
lean_object* v___x_1439_; 
lean_del_object(v___x_1432_);
lean_inc_ref(v___x_1419_);
v___x_1439_ = l_Lean_Meta_getLevel(v___x_1419_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__7));
v___x_1442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1442_, 0, v_a_1440_);
lean_ctor_set(v___x_1442_, 1, v___x_1422_);
v___x_1443_ = l_Lean_mkConst(v___x_1441_, v___x_1442_);
v___x_1444_ = l_Lean_mkAppB(v___x_1443_, v___x_1419_, v_a_1414_);
v___x_1445_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_a_1427_, v___x_1444_, v___y_1389_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1453_; 
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v___x_1445_, 0);
lean_dec(v_unused_1454_);
v___x_1447_ = v___x_1445_;
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v___x_1445_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_box(0);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1449_);
v___x_1451_ = v___x_1447_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
v_a_1455_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1445_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1445_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_a_1427_);
lean_dec_ref(v___x_1419_);
lean_dec(v_a_1414_);
v_a_1463_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1439_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1439_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
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
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_a_1427_);
lean_dec_ref(v___x_1419_);
lean_dec(v_a_1414_);
v_a_1472_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1429_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1429_);
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
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v___x_1419_);
lean_dec(v_a_1417_);
lean_dec(v_a_1414_);
v_a_1480_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1426_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1426_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v___x_1419_);
lean_dec(v_a_1417_);
lean_dec(v_a_1414_);
lean_dec(v_goal_1380_);
v_a_1488_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1420_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1420_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_a_1414_);
lean_dec_ref(v___x_1411_);
lean_dec(v_goal_1380_);
v_a_1496_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1416_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1416_);
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
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec_ref(v___x_1411_);
lean_dec(v_a_1396_);
lean_dec(v_goal_1380_);
v_a_1504_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1413_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1413_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
else
{
lean_object* v_backwardRules_1512_; lean_object* v_andIntro_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_del_object(v___x_1398_);
v_backwardRules_1512_ = lean_ctor_get(v___y_1381_, 0);
v_andIntro_1513_ = lean_ctor_get(v_backwardRules_1512_, 6);
v___x_1514_ = lean_box(0);
lean_inc_ref(v_andIntro_1513_);
v___x_1515_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_andIntro_1513_, v_goal_1380_, v___x_1514_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
if (lean_obj_tag(v_a_1516_) == 1)
{
lean_object* v_mvarIds_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1630_; 
v_mvarIds_1531_ = lean_ctor_get(v_a_1516_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_a_1516_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1533_ = v_a_1516_;
v_isShared_1534_ = v_isSharedCheck_1630_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_mvarIds_1531_);
lean_dec(v_a_1516_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1630_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
if (lean_obj_tag(v_mvarIds_1531_) == 1)
{
lean_object* v_tail_1535_; 
v_tail_1535_ = lean_ctor_get(v_mvarIds_1531_, 1);
lean_inc(v_tail_1535_);
if (lean_obj_tag(v_tail_1535_) == 1)
{
lean_object* v_tail_1536_; 
v_tail_1536_ = lean_ctor_get(v_tail_1535_, 1);
if (lean_obj_tag(v_tail_1536_) == 0)
{
lean_object* v_head_1537_; lean_object* v_head_1538_; lean_object* v___x_1539_; 
lean_dec(v_a_1396_);
v_head_1537_ = lean_ctor_get(v_mvarIds_1531_, 0);
lean_inc(v_head_1537_);
lean_dec_ref_known(v_mvarIds_1531_, 2);
v_head_1538_ = lean_ctor_get(v_tail_1535_, 0);
lean_inc(v_head_1538_);
lean_dec_ref_known(v_tail_1535_, 2);
v___x_1539_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(v_head_1537_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1629_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1629_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1629_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(v_head_1538_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v_g_1547_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
if (lean_obj_tag(v_a_1540_) == 0)
{
if (lean_obj_tag(v_a_1545_) == 0)
{
lean_del_object(v___x_1542_);
lean_del_object(v___x_1533_);
return v___x_1544_;
}
else
{
lean_object* v_val_1554_; 
lean_dec_ref_known(v___x_1544_, 1);
v_val_1554_ = lean_ctor_get(v_a_1545_, 0);
lean_inc(v_val_1554_);
lean_dec_ref_known(v_a_1545_, 1);
v_g_1547_ = v_val_1554_;
goto v___jp_1546_;
}
}
else
{
lean_dec_ref_known(v___x_1544_, 1);
if (lean_obj_tag(v_a_1545_) == 0)
{
lean_object* v_val_1555_; 
v_val_1555_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v_a_1540_, 1);
v_g_1547_ = v_val_1555_;
goto v___jp_1546_;
}
else
{
lean_object* v_val_1556_; lean_object* v_val_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1628_; 
lean_del_object(v___x_1542_);
lean_del_object(v___x_1533_);
v_val_1556_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v_a_1540_, 1);
v_val_1557_ = lean_ctor_get(v_a_1545_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_a_1545_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1559_ = v_a_1545_;
v_isShared_1560_ = v_isSharedCheck_1628_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_val_1557_);
lean_dec(v_a_1545_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1628_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; 
lean_inc(v_val_1556_);
v___x_1561_ = l_Lean_MVarId_getType(v_val_1556_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
lean_inc(v_val_1557_);
v___x_1563_ = l_Lean_MVarId_getType(v_val_1557_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc_n(v_a_1564_, 2);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1565_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__14, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__14_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__14);
lean_inc(v_a_1562_);
v___x_1566_ = l_Lean_mkAppB(v___x_1565_, v_a_1562_, v_a_1564_);
v___x_1567_ = lean_box(0);
v___x_1568_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_1566_, v___x_1567_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc_n(v_a_1569_, 2);
lean_dec_ref_known(v___x_1568_, 1);
v___x_1570_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__17, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__17_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__17);
lean_inc(v_a_1564_);
lean_inc(v_a_1562_);
v___x_1571_ = l_Lean_mkApp3(v___x_1570_, v_a_1562_, v_a_1564_, v_a_1569_);
v___x_1572_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_val_1556_, v___x_1571_, v___y_1389_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_dec_ref_known(v___x_1572_, 1);
v___x_1573_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__20, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__20_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__20);
lean_inc(v_a_1569_);
v___x_1574_ = l_Lean_mkApp3(v___x_1573_, v_a_1562_, v_a_1564_, v_a_1569_);
v___x_1575_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_val_1557_, v___x_1574_, v___y_1389_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1586_; 
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; 
v_unused_1587_ = lean_ctor_get(v___x_1575_, 0);
lean_dec(v_unused_1587_);
v___x_1577_ = v___x_1575_;
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
else
{
lean_dec(v___x_1575_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = l_Lean_Expr_mvarId_x21(v_a_1569_);
lean_dec(v_a_1569_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1579_);
v___x_1581_ = v___x_1559_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1581_);
v___x_1583_ = v___x_1577_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec(v_a_1569_);
lean_del_object(v___x_1559_);
v_a_1588_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1575_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1575_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_a_1569_);
lean_dec(v_a_1564_);
lean_dec(v_a_1562_);
lean_del_object(v___x_1559_);
lean_dec(v_val_1557_);
v_a_1596_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1572_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1572_);
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
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_a_1564_);
lean_dec(v_a_1562_);
lean_del_object(v___x_1559_);
lean_dec(v_val_1557_);
lean_dec(v_val_1556_);
v_a_1604_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1568_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1568_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_a_1562_);
lean_del_object(v___x_1559_);
lean_dec(v_val_1557_);
lean_dec(v_val_1556_);
v_a_1612_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1563_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1563_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_del_object(v___x_1559_);
lean_dec(v_val_1557_);
lean_dec(v_val_1556_);
v_a_1620_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1561_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1561_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
v___jp_1546_:
{
lean_object* v___x_1549_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v_g_1547_);
v___x_1549_ = v___x_1533_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_g_1547_);
v___x_1549_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1549_);
v___x_1551_ = v___x_1542_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_del_object(v___x_1542_);
lean_dec(v_a_1540_);
lean_del_object(v___x_1533_);
return v___x_1544_;
}
}
}
else
{
lean_dec(v_head_1538_);
lean_del_object(v___x_1533_);
return v___x_1539_;
}
}
else
{
lean_dec_ref_known(v_tail_1535_, 2);
lean_dec_ref_known(v_mvarIds_1531_, 2);
lean_del_object(v___x_1533_);
v___y_1518_ = v___y_1388_;
v___y_1519_ = v___y_1389_;
v___y_1520_ = v___y_1390_;
v___y_1521_ = v___y_1391_;
goto v___jp_1517_;
}
}
else
{
lean_dec(v_tail_1535_);
lean_dec_ref_known(v_mvarIds_1531_, 2);
lean_del_object(v___x_1533_);
v___y_1518_ = v___y_1388_;
v___y_1519_ = v___y_1389_;
v___y_1520_ = v___y_1390_;
v___y_1521_ = v___y_1391_;
goto v___jp_1517_;
}
}
else
{
lean_del_object(v___x_1533_);
lean_dec(v_mvarIds_1531_);
v___y_1518_ = v___y_1388_;
v___y_1519_ = v___y_1389_;
v___y_1520_ = v___y_1390_;
v___y_1521_ = v___y_1391_;
goto v___jp_1517_;
}
}
}
else
{
lean_dec(v_a_1516_);
v___y_1518_ = v___y_1388_;
v___y_1519_ = v___y_1389_;
v___y_1520_ = v___y_1390_;
v___y_1521_ = v___y_1391_;
goto v___jp_1517_;
}
v___jp_1517_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1522_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__9, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__9);
v___x_1523_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__11));
v___x_1524_ = l_Lean_MessageData_ofConstName(v___x_1523_, v___x_1401_);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1522_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__13, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__13);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = l_Lean_indentExpr(v_a_1396_);
v___x_1529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1529_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1530_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_a_1396_);
v_a_1631_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1515_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1515_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_del_object(v___x_1398_);
lean_dec(v_a_1396_);
v___x_1639_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__22, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__22_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___closed__22);
v___x_1640_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_goal_1380_, v___x_1639_, v___y_1389_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1648_; 
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; 
v_unused_1649_ = lean_ctor_get(v___x_1640_, 0);
lean_dec(v_unused_1649_);
v___x_1642_ = v___x_1640_;
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
else
{
lean_dec(v___x_1640_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1648_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_box(0);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1644_);
v___x_1646_ = v___x_1642_;
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
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_a_1650_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1640_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1640_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_goal_1380_);
v_a_1659_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1395_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1395_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_goal_1380_);
v_a_1667_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1393_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1393_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___boxed(lean_object* v_goal_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0(v_goal_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(lean_object* v_goal_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___f_1702_; lean_object* v___x_1703_; 
lean_inc(v_goal_1689_);
v___f_1702_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1702_, 0, v_goal_1689_);
v___x_1703_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic_spec__1___redArg(v_goal_1689_, v___f_1702_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts___boxed(lean_object* v_goal_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts(v_goal_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1(lean_object* v_mvarId_1718_, lean_object* v_val_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___redArg(v_mvarId_1718_, v_val_1719_, v___y_1728_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1___boxed(lean_object* v_mvarId_1733_, lean_object* v_val_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1(v_mvarId_1733_, v_val_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1(lean_object* v_00_u03b2_1748_, lean_object* v_x_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1___redArg(v_x_1749_, v_x_1750_, v_x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1753_, lean_object* v_x_1754_, size_t v_x_1755_, size_t v_x_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___redArg(v_x_1754_, v_x_1755_, v_x_1756_, v_x_1757_, v_x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
size_t v_x_60183__boxed_1766_; size_t v_x_60184__boxed_1767_; lean_object* v_res_1768_; 
v_x_60183__boxed_1766_ = lean_unbox_usize(v_x_1762_);
lean_dec(v_x_1762_);
v_x_60184__boxed_1767_ = lean_unbox_usize(v_x_1763_);
lean_dec(v_x_1763_);
v_res_1768_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2(v_00_u03b2_1760_, v_x_1761_, v_x_60183__boxed_1766_, v_x_60184__boxed_1767_, v_x_1764_, v_x_1765_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1769_, lean_object* v_n_1770_, lean_object* v_k_1771_, lean_object* v_v_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1770_, v_k_1771_, v_v_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1774_, size_t v_depth_1775_, lean_object* v_keys_1776_, lean_object* v_vals_1777_, lean_object* v_heq_1778_, lean_object* v_i_1779_, lean_object* v_entries_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1775_, v_keys_1776_, v_vals_1777_, v_i_1779_, v_entries_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1782_, lean_object* v_depth_1783_, lean_object* v_keys_1784_, lean_object* v_vals_1785_, lean_object* v_heq_1786_, lean_object* v_i_1787_, lean_object* v_entries_1788_){
_start:
{
size_t v_depth_boxed_1789_; lean_object* v_res_1790_; 
v_depth_boxed_1789_ = lean_unbox_usize(v_depth_1783_);
lean_dec(v_depth_1783_);
v_res_1790_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1782_, v_depth_boxed_1789_, v_keys_1784_, v_vals_1785_, v_heq_1786_, v_i_1787_, v_entries_1788_);
lean_dec_ref(v_vals_1785_);
lean_dec_ref(v_keys_1784_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_, lean_object* v_x_1794_, lean_object* v_x_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveTrivialConjuncts_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1792_, v_x_1793_, v_x_1794_, v_x_1795_);
return v___x_1796_;
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
