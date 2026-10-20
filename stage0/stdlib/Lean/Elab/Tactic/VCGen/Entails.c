// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.Entails
// Imports: public import Lean.Elab.Tactic.VCGen.Context public import Lean.Elab.Tactic.VCGen.RuleCache public import Lean.Elab.Tactic.VCGen.Util public import Lean.Meta.Sym.Util public import Lean.Meta.Tactic.Replace public import Std.WP import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS import Lean.Meta.Sym.AbstractS import Lean.Meta.Sym.MaxFVar import Lean.Meta.Sym.InstantiateS import Init.Sym.Lemmas
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_VCGen_latticeOps;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_getMaxFVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Failed to unfold the Triple target of "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1_value;
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "and_imp"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 187, 54, 56, 129, 238, 180, 43)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(14, 81, 9, 215, 230, 198, 87, 3)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "imp_subst"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(125, 24, 151, 61, 213, 29, 36, 180)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(180, 190, 140, 210, 253, 78, 130, 238)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 104, 229, 54, 179, 197, 12, 87)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(49, 235, 69, 93, 100, 93, 190, 221)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "subst: "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Failed to intro the lifted precondition of "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_introPre___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Failed to apply precondition intro rule to "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introPre___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introPre___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_introPre___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_introPre___closed__1;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_introPre___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_introPre___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_introPre___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(170, 44, 236, 58, 247, 164, 254, 114)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___boxed(lean_object**);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PreservesSup"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "upperAdjoint"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3_value_aux_2),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 52, 128, 160, 100, 147, 237, 166)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "himp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(173, 29, 48, 122, 5, 158, 45, 140)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__7 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "instCompleteLatticePi"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 67, 57, 247, 147, 127, 99, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "top_apply"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 219, 32, 190, 96, 78, 240, 61)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrFun"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(63, 110, 174, 29, 249, 91, 125, 152)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 33, 148, 124, 218, 91, 248, 169)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 37, .m_data = "Failed to strip the `⊤ ⊑` wrapper of "};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__0));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple(lean_object* v_goal_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___y_67_; lean_object* v___y_68_; lean_object* v___y_69_; lean_object* v___y_70_; lean_object* v___y_71_; lean_object* v___y_72_; lean_object* v___y_73_; lean_object* v___y_74_; lean_object* v___y_75_; lean_object* v___y_76_; lean_object* v___y_77_; lean_object* v_backwardRules_82_; lean_object* v_tripleIntro_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_backwardRules_82_ = lean_ctor_get(v_a_54_, 0);
v_tripleIntro_83_ = lean_ctor_get(v_backwardRules_82_, 0);
v___x_84_ = lean_box(0);
lean_inc(v_goal_53_);
lean_inc_ref(v_tripleIntro_83_);
v___x_85_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_tripleIntro_83_, v_goal_53_, v___x_84_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_96_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_96_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_96_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
if (lean_obj_tag(v_a_86_) == 1)
{
lean_object* v_mvarIds_90_; 
v_mvarIds_90_ = lean_ctor_get(v_a_86_, 0);
lean_inc(v_mvarIds_90_);
lean_dec_ref_known(v_a_86_, 1);
if (lean_obj_tag(v_mvarIds_90_) == 1)
{
lean_object* v_tail_91_; 
v_tail_91_ = lean_ctor_get(v_mvarIds_90_, 1);
if (lean_obj_tag(v_tail_91_) == 0)
{
lean_object* v_head_92_; lean_object* v___x_94_; 
lean_dec(v_goal_53_);
v_head_92_ = lean_ctor_get(v_mvarIds_90_, 0);
lean_inc(v_head_92_);
lean_dec_ref_known(v_mvarIds_90_, 2);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v_head_92_);
v___x_94_ = v___x_88_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_head_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
else
{
lean_dec_ref_known(v_mvarIds_90_, 2);
lean_del_object(v___x_88_);
v___y_67_ = v_a_54_;
v___y_68_ = v_a_55_;
v___y_69_ = v_a_56_;
v___y_70_ = v_a_57_;
v___y_71_ = v_a_58_;
v___y_72_ = v_a_59_;
v___y_73_ = v_a_60_;
v___y_74_ = v_a_61_;
v___y_75_ = v_a_62_;
v___y_76_ = v_a_63_;
v___y_77_ = v_a_64_;
goto v___jp_66_;
}
}
else
{
lean_dec(v_mvarIds_90_);
lean_del_object(v___x_88_);
v___y_67_ = v_a_54_;
v___y_68_ = v_a_55_;
v___y_69_ = v_a_56_;
v___y_70_ = v_a_57_;
v___y_71_ = v_a_58_;
v___y_72_ = v_a_59_;
v___y_73_ = v_a_60_;
v___y_74_ = v_a_61_;
v___y_75_ = v_a_62_;
v___y_76_ = v_a_63_;
v___y_77_ = v_a_64_;
goto v___jp_66_;
}
}
else
{
lean_del_object(v___x_88_);
lean_dec(v_a_86_);
v___y_67_ = v_a_54_;
v___y_68_ = v_a_55_;
v___y_69_ = v_a_56_;
v___y_70_ = v_a_57_;
v___y_71_ = v_a_58_;
v___y_72_ = v_a_59_;
v___y_73_ = v_a_60_;
v___y_74_ = v_a_61_;
v___y_75_ = v_a_62_;
v___y_76_ = v_a_63_;
v___y_77_ = v_a_64_;
goto v___jp_66_;
}
}
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
lean_dec(v_goal_53_);
v_a_97_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_85_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_85_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
v___jp_66_:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1, &l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_unfoldTriple___closed__1);
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v_goal_53_);
v___x_80_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_80_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_unfoldTriple___boxed(lean_object* v_goal_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Elab_Tactic_VCGen_unfoldTriple(v_goal_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0(lean_object* v_00_u03b1_119_, lean_object* v_msg_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v_msg_120_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___boxed(lean_object* v_00_u03b1_134_, lean_object* v_msg_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0(v_00_u03b1_134_, v_msg_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(lean_object* v_fvarId_149_, lean_object* v_as_150_, size_t v_i_151_, size_t v_stop_152_, lean_object* v_b_153_){
_start:
{
lean_object* v___y_155_; uint8_t v___x_159_; 
v___x_159_ = lean_usize_dec_eq(v_i_151_, v_stop_152_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_array_uget_borrowed(v_as_150_, v_i_151_);
if (lean_obj_tag(v___x_160_) == 0)
{
v___y_155_ = v_b_153_;
goto v___jp_154_;
}
else
{
lean_object* v_val_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_val_161_ = lean_ctor_get(v___x_160_, 0);
v___x_162_ = l_Lean_LocalDecl_type(v_val_161_);
v___x_163_ = l_Lean_Expr_containsFVar(v___x_162_, v_fvarId_149_);
lean_dec_ref(v___x_162_);
if (v___x_163_ == 0)
{
v___y_155_ = v_b_153_;
goto v___jp_154_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_inc(v_val_161_);
v___x_164_ = l_Lean_LocalDecl_toExpr(v_val_161_);
v___x_165_ = lean_array_push(v_b_153_, v___x_164_);
v___y_155_ = v___x_165_;
goto v___jp_154_;
}
}
}
else
{
return v_b_153_;
}
v___jp_154_:
{
size_t v___x_156_; size_t v___x_157_; 
v___x_156_ = ((size_t)1ULL);
v___x_157_ = lean_usize_add(v_i_151_, v___x_156_);
v_i_151_ = v___x_157_;
v_b_153_ = v___y_155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_fvarId_166_, lean_object* v_as_167_, lean_object* v_i_168_, lean_object* v_stop_169_, lean_object* v_b_170_){
_start:
{
size_t v_i_boxed_171_; size_t v_stop_boxed_172_; lean_object* v_res_173_; 
v_i_boxed_171_ = lean_unbox_usize(v_i_168_);
lean_dec(v_i_168_);
v_stop_boxed_172_ = lean_unbox_usize(v_stop_169_);
lean_dec(v_stop_169_);
v_res_173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v_fvarId_166_, v_as_167_, v_i_boxed_171_, v_stop_boxed_172_, v_b_170_);
lean_dec_ref(v_as_167_);
lean_dec(v_fvarId_166_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(lean_object* v_fvarId_174_, lean_object* v_x_175_, lean_object* v_x_176_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_object* v_cs_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_cs_177_ = lean_ctor_get(v_x_175_, 0);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_array_get_size(v_cs_177_);
v___x_180_ = lean_nat_dec_lt(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
return v_x_176_;
}
else
{
size_t v___x_181_; size_t v___x_182_; lean_object* v___x_183_; 
v___x_181_ = ((size_t)0ULL);
v___x_182_ = lean_usize_of_nat(v___x_179_);
v___x_183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(v_fvarId_174_, v_cs_177_, v___x_181_, v___x_182_, v_x_176_);
return v___x_183_;
}
}
else
{
lean_object* v_vs_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_vs_184_ = lean_ctor_get(v_x_175_, 0);
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = lean_array_get_size(v_vs_184_);
v___x_187_ = lean_nat_dec_lt(v___x_185_, v___x_186_);
if (v___x_187_ == 0)
{
return v_x_176_;
}
else
{
size_t v___x_188_; size_t v___x_189_; lean_object* v___x_190_; 
v___x_188_ = ((size_t)0ULL);
v___x_189_ = lean_usize_of_nat(v___x_186_);
v___x_190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v_fvarId_174_, v_vs_184_, v___x_188_, v___x_189_, v_x_176_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_fvarId_191_, lean_object* v_as_192_, size_t v_i_193_, size_t v_stop_194_, lean_object* v_b_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = lean_usize_dec_eq(v_i_193_, v_stop_194_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; size_t v___x_199_; size_t v___x_200_; 
v___x_197_ = lean_array_uget_borrowed(v_as_192_, v_i_193_);
v___x_198_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(v_fvarId_191_, v___x_197_, v_b_195_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_add(v_i_193_, v___x_199_);
v_i_193_ = v___x_200_;
v_b_195_ = v___x_198_;
goto _start;
}
else
{
return v_b_195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_fvarId_202_, lean_object* v_as_203_, lean_object* v_i_204_, lean_object* v_stop_205_, lean_object* v_b_206_){
_start:
{
size_t v_i_boxed_207_; size_t v_stop_boxed_208_; lean_object* v_res_209_; 
v_i_boxed_207_ = lean_unbox_usize(v_i_204_);
lean_dec(v_i_204_);
v_stop_boxed_208_ = lean_unbox_usize(v_stop_205_);
lean_dec(v_stop_205_);
v_res_209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(v_fvarId_202_, v_as_203_, v_i_boxed_207_, v_stop_boxed_208_, v_b_206_);
lean_dec_ref(v_as_203_);
lean_dec(v_fvarId_202_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v_fvarId_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(v_fvarId_210_, v_x_211_, v_x_212_);
lean_dec_ref(v_x_211_);
lean_dec(v_fvarId_210_);
return v_res_213_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(lean_object* v_fvarId_215_, lean_object* v_x_216_, size_t v_x_217_, size_t v_x_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v_cs_220_; lean_object* v___x_221_; size_t v___x_222_; lean_object* v_j_223_; lean_object* v___x_224_; size_t v___x_225_; size_t v___x_226_; size_t v___x_227_; size_t v___x_228_; size_t v___x_229_; size_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_cs_220_ = lean_ctor_get(v_x_216_, 0);
v___x_221_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0);
v___x_222_ = lean_usize_shift_right(v_x_217_, v_x_218_);
v_j_223_ = lean_usize_to_nat(v___x_222_);
v___x_224_ = lean_array_get_borrowed(v___x_221_, v_cs_220_, v_j_223_);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_shift_left(v___x_225_, v_x_218_);
v___x_227_ = lean_usize_sub(v___x_226_, v___x_225_);
v___x_228_ = lean_usize_land(v_x_217_, v___x_227_);
v___x_229_ = ((size_t)5ULL);
v___x_230_ = lean_usize_sub(v_x_218_, v___x_229_);
v___x_231_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(v_fvarId_215_, v___x_224_, v___x_228_, v___x_230_, v_x_219_);
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_add(v_j_223_, v___x_232_);
lean_dec(v_j_223_);
v___x_234_ = lean_array_get_size(v_cs_220_);
v___x_235_ = lean_nat_dec_lt(v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
lean_dec(v___x_233_);
return v___x_231_;
}
else
{
size_t v___x_236_; size_t v___x_237_; lean_object* v___x_238_; 
v___x_236_ = lean_usize_of_nat(v___x_233_);
lean_dec(v___x_233_);
v___x_237_ = lean_usize_of_nat(v___x_234_);
v___x_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(v_fvarId_215_, v_cs_220_, v___x_236_, v___x_237_, v___x_231_);
return v___x_238_;
}
}
else
{
lean_object* v_vs_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_vs_239_ = lean_ctor_get(v_x_216_, 0);
v___x_240_ = lean_usize_to_nat(v_x_217_);
v___x_241_ = lean_array_get_size(v_vs_239_);
v___x_242_ = lean_nat_dec_lt(v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_dec(v___x_240_);
return v_x_219_;
}
else
{
size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_usize_of_nat(v___x_240_);
lean_dec(v___x_240_);
v___x_244_ = lean_usize_of_nat(v___x_241_);
v___x_245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v_fvarId_215_, v_vs_239_, v___x_243_, v___x_244_, v_x_219_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_fvarId_246_, lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
size_t v_x_18126__boxed_251_; size_t v_x_18127__boxed_252_; lean_object* v_res_253_; 
v_x_18126__boxed_251_ = lean_unbox_usize(v_x_248_);
lean_dec(v_x_248_);
v_x_18127__boxed_252_ = lean_unbox_usize(v_x_249_);
lean_dec(v_x_249_);
v_res_253_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(v_fvarId_246_, v_x_247_, v_x_18126__boxed_251_, v_x_18127__boxed_252_, v_x_250_);
lean_dec_ref(v_x_247_);
lean_dec(v_fvarId_246_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0(lean_object* v_fvarId_254_, lean_object* v_t_255_, lean_object* v_init_256_, lean_object* v_start_257_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = lean_nat_dec_eq(v_start_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v_root_260_; lean_object* v_tail_261_; size_t v_shift_262_; lean_object* v_tailOff_263_; uint8_t v___x_264_; 
v_root_260_ = lean_ctor_get(v_t_255_, 0);
v_tail_261_ = lean_ctor_get(v_t_255_, 1);
v_shift_262_ = lean_ctor_get_usize(v_t_255_, 4);
v_tailOff_263_ = lean_ctor_get(v_t_255_, 3);
v___x_264_ = lean_nat_dec_le(v_tailOff_263_, v_start_257_);
if (v___x_264_ == 0)
{
size_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_265_ = lean_usize_of_nat(v_start_257_);
v___x_266_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(v_fvarId_254_, v_root_260_, v___x_265_, v_shift_262_, v_init_256_);
v___x_267_ = lean_array_get_size(v_tail_261_);
v___x_268_ = lean_nat_dec_lt(v___x_258_, v___x_267_);
if (v___x_268_ == 0)
{
return v___x_266_;
}
else
{
size_t v___x_269_; size_t v___x_270_; lean_object* v___x_271_; 
v___x_269_ = ((size_t)0ULL);
v___x_270_ = lean_usize_of_nat(v___x_267_);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v_fvarId_254_, v_tail_261_, v___x_269_, v___x_270_, v___x_266_);
return v___x_271_;
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_272_ = lean_nat_sub(v_start_257_, v_tailOff_263_);
v___x_273_ = lean_array_get_size(v_tail_261_);
v___x_274_ = lean_nat_dec_lt(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_dec(v___x_272_);
return v_init_256_;
}
else
{
size_t v___x_275_; size_t v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_usize_of_nat(v___x_272_);
lean_dec(v___x_272_);
v___x_276_ = lean_usize_of_nat(v___x_273_);
v___x_277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v_fvarId_254_, v_tail_261_, v___x_275_, v___x_276_, v_init_256_);
return v___x_277_;
}
}
}
else
{
lean_object* v_root_278_; lean_object* v_tail_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_root_278_ = lean_ctor_get(v_t_255_, 0);
v_tail_279_ = lean_ctor_get(v_t_255_, 1);
v___x_280_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(v_fvarId_254_, v_root_278_, v_init_256_);
v___x_281_ = lean_array_get_size(v_tail_279_);
v___x_282_ = lean_nat_dec_lt(v___x_258_, v___x_281_);
if (v___x_282_ == 0)
{
return v___x_280_;
}
else
{
size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
v___x_283_ = ((size_t)0ULL);
v___x_284_ = lean_usize_of_nat(v___x_281_);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v_fvarId_254_, v_tail_279_, v___x_283_, v___x_284_, v___x_280_);
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0___boxed(lean_object* v_fvarId_286_, lean_object* v_t_287_, lean_object* v_init_288_, lean_object* v_start_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0(v_fvarId_286_, v_t_287_, v_init_288_, v_start_289_);
lean_dec(v_start_289_);
lean_dec_ref(v_t_287_);
lean_dec(v_fvarId_286_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0(lean_object* v_fvarId_291_, lean_object* v_lctx_292_, lean_object* v_init_293_, lean_object* v_start_294_){
_start:
{
lean_object* v_decls_295_; lean_object* v___x_296_; 
v_decls_295_ = lean_ctor_get(v_lctx_292_, 1);
v___x_296_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0(v_fvarId_291_, v_decls_295_, v_init_293_, v_start_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0___boxed(lean_object* v_fvarId_297_, lean_object* v_lctx_298_, lean_object* v_init_299_, lean_object* v_start_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0(v_fvarId_297_, v_lctx_298_, v_init_299_, v_start_300_);
lean_dec(v_start_300_);
lean_dec_ref(v_lctx_298_);
lean_dec(v_fvarId_297_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(lean_object* v_eqn_307_, lean_object* v_G_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Meta_Sym_instantiateMVarsS(v_eqn_307_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_432_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_432_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_432_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_432_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = l_Lean_Expr_cleanupAnnotations(v_a_320_);
v___x_330_ = l_Lean_Expr_isApp(v___x_329_);
if (v___x_330_ == 0)
{
lean_dec_ref(v___x_329_);
lean_del_object(v___x_322_);
lean_dec_ref(v_G_308_);
goto v___jp_316_;
}
else
{
lean_object* v_arg_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_arg_331_ = lean_ctor_get(v___x_329_, 1);
lean_inc_ref(v_arg_331_);
v___x_332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_329_);
v___x_333_ = l_Lean_Expr_isApp(v___x_332_);
if (v___x_333_ == 0)
{
lean_dec_ref(v___x_332_);
lean_dec_ref(v_arg_331_);
lean_del_object(v___x_322_);
lean_dec_ref(v_G_308_);
goto v___jp_316_;
}
else
{
lean_object* v_arg_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v_arg_334_ = lean_ctor_get(v___x_332_, 1);
lean_inc_ref(v_arg_334_);
v___x_335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_332_);
v___x_336_ = l_Lean_Expr_isApp(v___x_335_);
if (v___x_336_ == 0)
{
lean_dec_ref(v___x_335_);
lean_dec_ref(v_arg_334_);
lean_dec_ref(v_arg_331_);
lean_del_object(v___x_322_);
lean_dec_ref(v_G_308_);
goto v___jp_316_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_335_);
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1));
v___x_339_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_338_);
lean_dec_ref(v___x_337_);
if (v___x_339_ == 0)
{
lean_dec_ref(v_arg_334_);
lean_dec_ref(v_arg_331_);
lean_del_object(v___x_322_);
lean_dec_ref(v_G_308_);
goto v___jp_316_;
}
else
{
if (lean_obj_tag(v_arg_334_) == 1)
{
lean_object* v_fvarId_340_; lean_object* v_lctx_341_; lean_object* v___x_342_; 
v_fvarId_340_ = lean_ctor_get(v_arg_334_, 0);
v_lctx_341_ = lean_ctor_get(v_a_311_, 2);
lean_inc(v_fvarId_340_);
lean_inc_ref(v_lctx_341_);
v___x_342_ = lean_local_ctx_find(v_lctx_341_, v_fvarId_340_);
if (lean_obj_tag(v___x_342_) == 1)
{
lean_object* v_val_343_; uint8_t v___x_344_; uint8_t v___x_345_; 
v_val_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = 0;
v___x_345_ = l_Lean_LocalDecl_isLet(v_val_343_, v___x_344_);
if (v___x_345_ == 0)
{
uint8_t v___x_346_; 
v___x_346_ = l_Lean_Expr_containsFVar(v_arg_331_, v_fvarId_340_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_del_object(v___x_322_);
lean_inc_ref(v_G_308_);
v___x_347_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_G_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_419_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_419_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_419_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_419_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
if (lean_obj_tag(v_a_348_) == 1)
{
lean_object* v_val_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_414_; 
lean_del_object(v___x_350_);
v_val_352_ = lean_ctor_get(v_a_348_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v_a_348_);
if (v_isSharedCheck_414_ == 0)
{
v___x_354_ = v_a_348_;
v_isShared_355_ = v_isSharedCheck_414_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_val_352_);
lean_dec(v_a_348_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_414_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_FVarId_getDecl___redArg(v_val_352_, v_a_311_, v_a_313_, v_a_314_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_405_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_405_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_405_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_405_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_361_ = l_Lean_LocalDecl_index(v_a_357_);
lean_dec(v_a_357_);
v___x_362_ = l_Lean_LocalDecl_index(v_val_343_);
lean_dec(v_val_343_);
v___x_363_ = lean_nat_dec_lt(v___x_361_, v___x_362_);
lean_dec(v___x_361_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
lean_del_object(v___x_359_);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__2));
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_nat_add(v___x_362_, v___x_366_);
lean_dec(v___x_362_);
v___x_368_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0(v_fvarId_340_, v_lctx_341_, v___x_365_, v___x_367_);
lean_dec(v___x_367_);
v___x_369_ = lean_mk_empty_array_with_capacity(v___x_366_);
lean_inc_ref_n(v_arg_334_, 2);
v___x_370_ = lean_array_push(v___x_369_, v_arg_334_);
v___x_371_ = l_Array_append___redArg(v___x_370_, v___x_368_);
lean_dec_ref(v___x_368_);
v___x_372_ = lean_array_push(v___x_371_, v_arg_334_);
v___x_373_ = l_Lean_Meta_Sym_abstractFVarsRange(v_G_308_, v___x_364_, v___x_372_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_392_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_392_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_392_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_392_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = l_Lean_Expr_looseBVarRange(v_a_374_);
v___x_379_ = lean_nat_dec_eq(v___x_378_, v___x_366_);
lean_dec(v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_382_; 
lean_dec(v_a_374_);
lean_del_object(v___x_354_);
lean_dec_ref_known(v_arg_334_, 1);
lean_dec_ref(v_arg_331_);
v___x_380_ = lean_box(0);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_380_);
v___x_382_ = v___x_376_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_arg_331_);
lean_ctor_set(v___x_384_, 1, v_a_374_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_arg_334_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_385_);
v___x_387_ = v___x_354_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_391_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_389_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_387_);
v___x_389_ = v___x_376_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_del_object(v___x_354_);
lean_dec_ref_known(v_arg_334_, 1);
lean_dec_ref(v_arg_331_);
v_a_393_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_373_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_373_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_403_; 
lean_dec(v___x_362_);
lean_del_object(v___x_354_);
lean_dec_ref_known(v_arg_334_, 1);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_G_308_);
v___x_401_ = lean_box(0);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_401_);
v___x_403_ = v___x_359_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_del_object(v___x_354_);
lean_dec(v_val_343_);
lean_dec_ref_known(v_arg_334_, 1);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_G_308_);
v_a_406_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_356_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_356_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_417_; 
lean_dec(v_a_348_);
lean_dec(v_val_343_);
lean_dec_ref_known(v_arg_334_, 1);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_G_308_);
v___x_415_ = lean_box(0);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_415_);
v___x_417_ = v___x_350_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v_val_343_);
lean_dec_ref_known(v_arg_334_, 1);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_G_308_);
v_a_420_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_347_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_347_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
else
{
lean_dec(v_val_343_);
lean_dec_ref_known(v_arg_334_, 1);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_G_308_);
goto v___jp_324_;
}
}
else
{
lean_dec(v_val_343_);
lean_dec_ref_known(v_arg_334_, 1);
lean_dec_ref(v_arg_331_);
lean_dec_ref(v_G_308_);
goto v___jp_324_;
}
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec(v___x_342_);
lean_dec_ref_known(v_arg_334_, 1);
lean_dec_ref(v_arg_331_);
lean_del_object(v___x_322_);
lean_dec_ref(v_G_308_);
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref(v_arg_334_);
lean_dec_ref(v_arg_331_);
lean_del_object(v___x_322_);
lean_dec_ref(v_G_308_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
}
}
}
v___jp_324_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_box(0);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_325_);
v___x_327_ = v___x_322_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
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
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec_ref(v_G_308_);
v_a_433_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_319_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_319_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
v___jp_316_:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_box(0);
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___boxed(lean_object* v_eqn_441_, lean_object* v_G_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_eqn_441_, v_G_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f(lean_object* v_eqn_451_, lean_object* v_G_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_eqn_451_, v_G_452_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___boxed(lean_object* v_eqn_466_, lean_object* v_G_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f(v_eqn_466_, v_G_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(lean_object* v_00_u03c6_484_, lean_object* v_G_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___x_524_; 
lean_inc_ref(v_00_u03c6_484_);
v___x_524_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03c6_484_, v_a_489_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = l_Lean_Expr_cleanupAnnotations(v_a_525_);
v___x_527_ = l_Lean_Expr_isApp(v___x_526_);
if (v___x_527_ == 0)
{
lean_dec_ref(v___x_526_);
v___y_494_ = v_a_486_;
v___y_495_ = v_a_487_;
v___y_496_ = v_a_488_;
v___y_497_ = v_a_489_;
v___y_498_ = v_a_490_;
v___y_499_ = v_a_491_;
goto v___jp_493_;
}
else
{
lean_object* v_arg_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_arg_528_ = lean_ctor_get(v___x_526_, 1);
lean_inc_ref(v_arg_528_);
v___x_529_ = l_Lean_Expr_appFnCleanup___redArg(v___x_526_);
v___x_530_ = l_Lean_Expr_isApp(v___x_529_);
if (v___x_530_ == 0)
{
lean_dec_ref(v___x_529_);
lean_dec_ref(v_arg_528_);
v___y_494_ = v_a_486_;
v___y_495_ = v_a_487_;
v___y_496_ = v_a_488_;
v___y_497_ = v_a_489_;
v___y_498_ = v_a_490_;
v___y_499_ = v_a_491_;
goto v___jp_493_;
}
else
{
lean_object* v_arg_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_arg_531_ = lean_ctor_get(v___x_529_, 1);
lean_inc_ref(v_arg_531_);
v___x_532_ = l_Lean_Expr_appFnCleanup___redArg(v___x_529_);
v___x_533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__1));
v___x_534_ = l_Lean_Expr_isConstOf(v___x_532_, v___x_533_);
lean_dec_ref(v___x_532_);
if (v___x_534_ == 0)
{
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_528_);
v___y_494_ = v_a_486_;
v___y_495_ = v_a_487_;
v___y_496_ = v_a_488_;
v___y_497_ = v_a_489_;
v___y_498_ = v_a_490_;
v___y_499_ = v_a_491_;
goto v___jp_493_;
}
else
{
lean_object* v___x_535_; 
lean_dec_ref(v_00_u03c6_484_);
lean_inc_ref(v_G_485_);
v___x_535_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_arg_531_, v_G_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; uint8_t v___x_537_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v___x_537_ = lean_unbox(v_a_536_);
if (v___x_537_ == 0)
{
lean_dec_ref_known(v___x_535_, 1);
v_00_u03c6_484_ = v_arg_528_;
goto _start;
}
else
{
lean_dec_ref(v_arg_528_);
lean_dec_ref(v_G_485_);
return v___x_535_;
}
}
else
{
lean_dec_ref(v_arg_528_);
lean_dec_ref(v_G_485_);
return v___x_535_;
}
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec_ref(v_G_485_);
lean_dec_ref(v_00_u03c6_484_);
v_a_539_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_524_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_524_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
v___jp_493_:
{
lean_object* v___x_500_; 
v___x_500_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_00_u03c6_484_, v_G_485_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_515_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_515_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_515_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_515_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
if (lean_obj_tag(v_a_501_) == 0)
{
uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_505_ = 0;
v___x_506_ = lean_box(v___x_505_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_506_);
v___x_508_ = v___x_503_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
else
{
uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
lean_dec_ref_known(v_a_501_, 1);
v___x_510_ = 1;
v___x_511_ = lean_box(v___x_510_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_511_);
v___x_513_ = v___x_503_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_a_516_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_500_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_500_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___boxed(lean_object* v_00_u03c6_547_, lean_object* v_G_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_00_u03c6_547_, v_G_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct(lean_object* v_00_u03c6_557_, lean_object* v_G_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_00_u03c6_557_, v_G_558_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___boxed(lean_object* v_00_u03c6_572_, lean_object* v_G_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct(v_00_u03c6_572_, v_G_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(lean_object* v_x_587_, uint8_t v_bi_588_, lean_object* v_t_589_, lean_object* v_b_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v___y_599_; lean_object* v___x_602_; uint8_t v_debug_603_; 
v___x_602_ = lean_st_ref_get(v___y_592_);
v_debug_603_ = lean_ctor_get_uint8(v___x_602_, sizeof(void*)*12);
lean_dec(v___x_602_);
if (v_debug_603_ == 0)
{
v___y_599_ = v___y_592_;
goto v___jp_598_;
}
else
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_589_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v___x_605_; 
lean_dec_ref_known(v___x_604_, 1);
v___x_605_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_dec_ref_known(v___x_605_, 1);
v___y_599_ = v___y_592_;
goto v___jp_598_;
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_b_590_);
lean_dec_ref(v_t_589_);
lean_dec(v_x_587_);
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v_b_590_);
lean_dec_ref(v_t_589_);
lean_dec(v_x_587_);
v_a_614_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_604_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_604_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
v___jp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = l_Lean_Expr_forallE___override(v_x_587_, v_t_589_, v_b_590_, v_bi_588_);
v___x_601_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_600_, v___y_599_);
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg___boxed(lean_object* v_x_622_, lean_object* v_bi_623_, lean_object* v_t_624_, lean_object* v_b_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
uint8_t v_bi_boxed_633_; lean_object* v_res_634_; 
v_bi_boxed_633_ = lean_unbox(v_bi_623_);
v_res_634_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_x_622_, v_bi_boxed_633_, v_t_624_, v_b_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0(lean_object* v_x_635_, uint8_t v_bi_636_, lean_object* v_t_637_, lean_object* v_b_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_x_635_, v_bi_636_, v_t_637_, v_b_638_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___boxed(lean_object* v_x_652_, lean_object* v_bi_653_, lean_object* v_t_654_, lean_object* v_b_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
uint8_t v_bi_boxed_668_; lean_object* v_res_669_; 
v_bi_boxed_668_ = lean_unbox(v_bi_653_);
v_res_669_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0(v_x_652_, v_bi_boxed_668_, v_t_654_, v_b_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(lean_object* v_declName_670_, lean_object* v_us_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = l_Lean_Expr_const___override(v_declName_670_, v_us_671_);
v___x_675_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_674_, v___y_672_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg___boxed(lean_object* v_declName_676_, lean_object* v_us_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v_declName_676_, v_us_677_, v___y_678_);
lean_dec(v___y_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1(lean_object* v_declName_681_, lean_object* v_us_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v_declName_681_, v_us_682_, v___y_689_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___boxed(lean_object* v_declName_696_, lean_object* v_us_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1(v_declName_696_, v_us_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_ks_715_; lean_object* v_vs_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_740_; 
v_ks_715_ = lean_ctor_get(v_x_711_, 0);
v_vs_716_ = lean_ctor_get(v_x_711_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_x_711_);
if (v_isSharedCheck_740_ == 0)
{
v___x_718_ = v_x_711_;
v_isShared_719_ = v_isSharedCheck_740_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_vs_716_);
lean_inc(v_ks_715_);
lean_dec(v_x_711_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_740_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = lean_array_get_size(v_ks_715_);
v___x_721_ = lean_nat_dec_lt(v_x_712_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec(v_x_712_);
v___x_722_ = lean_array_push(v_ks_715_, v_x_713_);
v___x_723_ = lean_array_push(v_vs_716_, v_x_714_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_723_);
lean_ctor_set(v___x_718_, 0, v___x_722_);
v___x_725_ = v___x_718_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_object* v_k_x27_727_; uint8_t v___x_728_; 
v_k_x27_727_ = lean_array_fget_borrowed(v_ks_715_, v_x_712_);
v___x_728_ = l_Lean_instBEqMVarId_beq(v_x_713_, v_k_x27_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_730_; 
if (v_isShared_719_ == 0)
{
v___x_730_ = v___x_718_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_ks_715_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_vs_716_);
v___x_730_ = v_reuseFailAlloc_734_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_nat_add(v_x_712_, v___x_731_);
lean_dec(v_x_712_);
v_x_711_ = v___x_730_;
v_x_712_ = v___x_732_;
goto _start;
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_735_ = lean_array_fset(v_ks_715_, v_x_712_, v_x_713_);
v___x_736_ = lean_array_fset(v_vs_716_, v_x_712_, v_x_714_);
lean_dec(v_x_712_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_736_);
lean_ctor_set(v___x_718_, 0, v___x_735_);
v___x_738_ = v___x_718_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* v_n_741_, lean_object* v_k_742_, lean_object* v_v_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_n_741_, v___x_744_, v_k_742_, v_v_743_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg(lean_object* v_x_747_, size_t v_x_748_, size_t v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
if (lean_obj_tag(v_x_747_) == 0)
{
lean_object* v_es_752_; size_t v___x_753_; size_t v___x_754_; lean_object* v_j_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_es_752_ = lean_ctor_get(v_x_747_, 0);
v___x_753_ = ((size_t)31ULL);
v___x_754_ = lean_usize_land(v_x_748_, v___x_753_);
v_j_755_ = lean_usize_to_nat(v___x_754_);
v___x_756_ = lean_array_get_size(v_es_752_);
v___x_757_ = lean_nat_dec_lt(v_j_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_dec(v_j_755_);
lean_dec(v_x_751_);
lean_dec(v_x_750_);
return v_x_747_;
}
else
{
lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_796_; 
lean_inc_ref(v_es_752_);
v_isSharedCheck_796_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_x_747_, 0);
lean_dec(v_unused_797_);
v___x_759_ = v_x_747_;
v_isShared_760_ = v_isSharedCheck_796_;
goto v_resetjp_758_;
}
else
{
lean_dec(v_x_747_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_796_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_v_761_; lean_object* v___x_762_; lean_object* v_xs_x27_763_; lean_object* v___y_765_; 
v_v_761_ = lean_array_fget(v_es_752_, v_j_755_);
v___x_762_ = lean_box(0);
v_xs_x27_763_ = lean_array_fset(v_es_752_, v_j_755_, v___x_762_);
switch(lean_obj_tag(v_v_761_))
{
case 0:
{
lean_object* v_key_770_; lean_object* v_val_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_781_; 
v_key_770_ = lean_ctor_get(v_v_761_, 0);
v_val_771_ = lean_ctor_get(v_v_761_, 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v_v_761_);
if (v_isSharedCheck_781_ == 0)
{
v___x_773_ = v_v_761_;
v_isShared_774_ = v_isSharedCheck_781_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_val_771_);
lean_inc(v_key_770_);
lean_dec(v_v_761_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_781_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
uint8_t v___x_775_; 
v___x_775_ = l_Lean_instBEqMVarId_beq(v_x_750_, v_key_770_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
lean_del_object(v___x_773_);
v___x_776_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_770_, v_val_771_, v_x_750_, v_x_751_);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
v___y_765_ = v___x_777_;
goto v___jp_764_;
}
else
{
lean_object* v___x_779_; 
lean_dec(v_val_771_);
lean_dec(v_key_770_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v_x_751_);
lean_ctor_set(v___x_773_, 0, v_x_750_);
v___x_779_ = v___x_773_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_x_750_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_x_751_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
v___y_765_ = v___x_779_;
goto v___jp_764_;
}
}
}
}
case 1:
{
lean_object* v_node_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_794_; 
v_node_782_ = lean_ctor_get(v_v_761_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_v_761_);
if (v_isSharedCheck_794_ == 0)
{
v___x_784_ = v_v_761_;
v_isShared_785_ = v_isSharedCheck_794_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_node_782_);
lean_dec(v_v_761_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_794_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
size_t v___x_786_; size_t v___x_787_; size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_786_ = ((size_t)5ULL);
v___x_787_ = lean_usize_shift_right(v_x_748_, v___x_786_);
v___x_788_ = ((size_t)1ULL);
v___x_789_ = lean_usize_add(v_x_749_, v___x_788_);
v___x_790_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg(v_node_782_, v___x_787_, v___x_789_, v_x_750_, v_x_751_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_790_);
v___x_792_ = v___x_784_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v___y_765_ = v___x_792_;
goto v___jp_764_;
}
}
}
default: 
{
lean_object* v___x_795_; 
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_x_750_);
lean_ctor_set(v___x_795_, 1, v_x_751_);
v___y_765_ = v___x_795_;
goto v___jp_764_;
}
}
v___jp_764_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_array_fset(v_xs_x27_763_, v_j_755_, v___y_765_);
lean_dec(v_j_755_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_766_);
v___x_768_ = v___x_759_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
else
{
lean_object* v_ks_798_; lean_object* v_vs_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_817_; 
v_ks_798_ = lean_ctor_get(v_x_747_, 0);
v_vs_799_ = lean_ctor_get(v_x_747_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_817_ == 0)
{
v___x_801_ = v_x_747_;
v_isShared_802_ = v_isSharedCheck_817_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_vs_799_);
lean_inc(v_ks_798_);
lean_dec(v_x_747_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_817_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_ks_798_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_vs_799_);
v___x_804_ = v_reuseFailAlloc_816_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v_newNode_805_; size_t v___x_806_; uint8_t v___x_807_; 
v_newNode_805_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7___redArg(v___x_804_, v_x_750_, v_x_751_);
v___x_806_ = ((size_t)7ULL);
v___x_807_ = lean_usize_dec_le(v___x_806_, v_x_749_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_808_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_805_);
v___x_809_ = lean_unsigned_to_nat(4u);
v___x_810_ = lean_nat_dec_lt(v___x_808_, v___x_809_);
lean_dec(v___x_808_);
if (v___x_810_ == 0)
{
lean_object* v_ks_811_; lean_object* v_vs_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_ks_811_ = lean_ctor_get(v_newNode_805_, 0);
lean_inc_ref(v_ks_811_);
v_vs_812_ = lean_ctor_get(v_newNode_805_, 1);
lean_inc_ref(v_vs_812_);
lean_dec_ref(v_newNode_805_);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg___closed__0);
v___x_815_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8___redArg(v_x_749_, v_ks_811_, v_vs_812_, v___x_813_, v___x_814_);
lean_dec_ref(v_vs_812_);
lean_dec_ref(v_ks_811_);
return v___x_815_;
}
else
{
return v_newNode_805_;
}
}
else
{
return v_newNode_805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8___redArg(size_t v_depth_818_, lean_object* v_keys_819_, lean_object* v_vals_820_, lean_object* v_i_821_, lean_object* v_entries_822_){
_start:
{
lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_823_ = lean_array_get_size(v_keys_819_);
v___x_824_ = lean_nat_dec_lt(v_i_821_, v___x_823_);
if (v___x_824_ == 0)
{
lean_dec(v_i_821_);
return v_entries_822_;
}
else
{
lean_object* v_k_825_; lean_object* v_v_826_; uint64_t v___x_827_; size_t v_h_828_; size_t v___x_829_; lean_object* v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v_h_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_k_825_ = lean_array_fget_borrowed(v_keys_819_, v_i_821_);
v_v_826_ = lean_array_fget_borrowed(v_vals_820_, v_i_821_);
v___x_827_ = l_Lean_instHashableMVarId_hash(v_k_825_);
v_h_828_ = lean_uint64_to_usize(v___x_827_);
v___x_829_ = ((size_t)5ULL);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_sub(v_depth_818_, v___x_831_);
v___x_833_ = lean_usize_mul(v___x_829_, v___x_832_);
v_h_834_ = lean_usize_shift_right(v_h_828_, v___x_833_);
v___x_835_ = lean_nat_add(v_i_821_, v___x_830_);
lean_dec(v_i_821_);
lean_inc(v_v_826_);
lean_inc(v_k_825_);
v___x_836_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg(v_entries_822_, v_h_834_, v_depth_818_, v_k_825_, v_v_826_);
v_i_821_ = v___x_835_;
v_entries_822_ = v___x_836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_depth_838_, lean_object* v_keys_839_, lean_object* v_vals_840_, lean_object* v_i_841_, lean_object* v_entries_842_){
_start:
{
size_t v_depth_boxed_843_; lean_object* v_res_844_; 
v_depth_boxed_843_ = lean_unbox_usize(v_depth_838_);
lean_dec(v_depth_838_);
v_res_844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_boxed_843_, v_keys_839_, v_vals_840_, v_i_841_, v_entries_842_);
lean_dec_ref(v_vals_840_);
lean_dec_ref(v_keys_839_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
size_t v_x_23695__boxed_850_; size_t v_x_23696__boxed_851_; lean_object* v_res_852_; 
v_x_23695__boxed_850_ = lean_unbox_usize(v_x_846_);
lean_dec(v_x_846_);
v_x_23696__boxed_851_ = lean_unbox_usize(v_x_847_);
lean_dec(v_x_847_);
v_res_852_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg(v_x_845_, v_x_23695__boxed_850_, v_x_23696__boxed_851_, v_x_848_, v_x_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4___redArg(lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
uint64_t v___x_856_; size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_856_ = l_Lean_instHashableMVarId_hash(v_x_854_);
v___x_857_ = lean_uint64_to_usize(v___x_856_);
v___x_858_ = ((size_t)1ULL);
v___x_859_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg(v_x_853_, v___x_857_, v___x_858_, v_x_854_, v_x_855_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3___redArg(lean_object* v_mvarId_860_, lean_object* v_val_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; lean_object* v_mctx_865_; lean_object* v_cache_866_; lean_object* v_zetaDeltaFVarIds_867_; lean_object* v_postponed_868_; lean_object* v_diag_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_899_; 
v___x_864_ = lean_st_ref_take(v___y_862_);
v_mctx_865_ = lean_ctor_get(v___x_864_, 0);
v_cache_866_ = lean_ctor_get(v___x_864_, 1);
v_zetaDeltaFVarIds_867_ = lean_ctor_get(v___x_864_, 2);
v_postponed_868_ = lean_ctor_get(v___x_864_, 3);
v_diag_869_ = lean_ctor_get(v___x_864_, 4);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_899_ == 0)
{
v___x_871_ = v___x_864_;
v_isShared_872_ = v_isSharedCheck_899_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_diag_869_);
lean_inc(v_postponed_868_);
lean_inc(v_zetaDeltaFVarIds_867_);
lean_inc(v_cache_866_);
lean_inc(v_mctx_865_);
lean_dec(v___x_864_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_899_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_depth_873_; lean_object* v_levelAssignDepth_874_; lean_object* v_lmvarCounter_875_; lean_object* v_mvarCounter_876_; lean_object* v_lDecls_877_; lean_object* v_decls_878_; lean_object* v_userNames_879_; lean_object* v_lAssignment_880_; lean_object* v_eAssignment_881_; lean_object* v_dAssignment_882_; lean_object* v_instanceTypedMVars_883_; lean_object* v_synthNormMemo_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_898_; 
v_depth_873_ = lean_ctor_get(v_mctx_865_, 0);
v_levelAssignDepth_874_ = lean_ctor_get(v_mctx_865_, 1);
v_lmvarCounter_875_ = lean_ctor_get(v_mctx_865_, 2);
v_mvarCounter_876_ = lean_ctor_get(v_mctx_865_, 3);
v_lDecls_877_ = lean_ctor_get(v_mctx_865_, 4);
v_decls_878_ = lean_ctor_get(v_mctx_865_, 5);
v_userNames_879_ = lean_ctor_get(v_mctx_865_, 6);
v_lAssignment_880_ = lean_ctor_get(v_mctx_865_, 7);
v_eAssignment_881_ = lean_ctor_get(v_mctx_865_, 8);
v_dAssignment_882_ = lean_ctor_get(v_mctx_865_, 9);
v_instanceTypedMVars_883_ = lean_ctor_get(v_mctx_865_, 10);
v_synthNormMemo_884_ = lean_ctor_get(v_mctx_865_, 11);
v_isSharedCheck_898_ = !lean_is_exclusive(v_mctx_865_);
if (v_isSharedCheck_898_ == 0)
{
v___x_886_ = v_mctx_865_;
v_isShared_887_ = v_isSharedCheck_898_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_synthNormMemo_884_);
lean_inc(v_instanceTypedMVars_883_);
lean_inc(v_dAssignment_882_);
lean_inc(v_eAssignment_881_);
lean_inc(v_lAssignment_880_);
lean_inc(v_userNames_879_);
lean_inc(v_decls_878_);
lean_inc(v_lDecls_877_);
lean_inc(v_mvarCounter_876_);
lean_inc(v_lmvarCounter_875_);
lean_inc(v_levelAssignDepth_874_);
lean_inc(v_depth_873_);
lean_dec(v_mctx_865_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_898_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_888_ = lean_box(0);
v___x_889_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4___redArg(v_eAssignment_881_, v_mvarId_860_, v_val_861_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 8, v___x_889_);
v___x_891_ = v___x_886_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_depth_873_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_levelAssignDepth_874_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_lmvarCounter_875_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_mvarCounter_876_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v_lDecls_877_);
lean_ctor_set(v_reuseFailAlloc_897_, 5, v_decls_878_);
lean_ctor_set(v_reuseFailAlloc_897_, 6, v_userNames_879_);
lean_ctor_set(v_reuseFailAlloc_897_, 7, v_lAssignment_880_);
lean_ctor_set(v_reuseFailAlloc_897_, 8, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_897_, 9, v_dAssignment_882_);
lean_ctor_set(v_reuseFailAlloc_897_, 10, v_instanceTypedMVars_883_);
lean_ctor_set(v_reuseFailAlloc_897_, 11, v_synthNormMemo_884_);
v___x_891_ = v_reuseFailAlloc_897_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_893_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_891_);
v___x_893_ = v___x_871_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_cache_866_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_zetaDeltaFVarIds_867_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v_postponed_868_);
lean_ctor_set(v_reuseFailAlloc_896_, 4, v_diag_869_);
v___x_893_ = v_reuseFailAlloc_896_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_st_ref_put(v___y_862_, v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_888_);
return v___x_895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3___redArg___boxed(lean_object* v_mvarId_900_, lean_object* v_val_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3___redArg(v_mvarId_900_, v_val_901_, v___y_902_);
lean_dec(v___y_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3___redArg(lean_object* v_f_905_, lean_object* v_a_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___y_915_; lean_object* v___x_918_; uint8_t v_debug_919_; 
v___x_918_ = lean_st_ref_get(v___y_908_);
v_debug_919_ = lean_ctor_get_uint8(v___x_918_, sizeof(void*)*12);
lean_dec(v___x_918_);
if (v_debug_919_ == 0)
{
v___y_915_ = v___y_908_;
goto v___jp_914_;
}
else
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_905_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v___x_921_; 
lean_dec_ref_known(v___x_920_, 1);
v___x_921_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_dec_ref_known(v___x_921_, 1);
v___y_915_ = v___y_908_;
goto v___jp_914_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec_ref(v_a_906_);
lean_dec_ref(v_f_905_);
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec_ref(v_a_906_);
lean_dec_ref(v_f_905_);
v_a_930_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_920_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_920_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
v___jp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = l_Lean_Expr_app___override(v_f_905_, v_a_906_);
v___x_917_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_916_, v___y_915_);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_f_938_, lean_object* v_a_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3___redArg(v_f_938_, v_a_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2(lean_object* v_args_948_, lean_object* v_endIdx_949_, lean_object* v_b_950_, lean_object* v_i_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
uint8_t v___x_964_; 
v___x_964_ = lean_nat_dec_le(v_endIdx_949_, v_i_951_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = l_Lean_instInhabitedExpr;
v___x_966_ = lean_array_get_borrowed(v___x_965_, v_args_948_, v_i_951_);
lean_inc(v___x_966_);
v___x_967_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3___redArg(v_b_950_, v___x_966_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = lean_unsigned_to_nat(1u);
v___x_970_ = lean_nat_add(v_i_951_, v___x_969_);
lean_dec(v_i_951_);
v_b_950_ = v_a_968_;
v_i_951_ = v___x_970_;
goto _start;
}
else
{
lean_dec(v_i_951_);
return v___x_967_;
}
}
else
{
lean_object* v___x_972_; 
lean_dec(v_i_951_);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v_b_950_);
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2___boxed(lean_object* v_args_973_, lean_object* v_endIdx_974_, lean_object* v_b_975_, lean_object* v_i_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2(v_args_973_, v_endIdx_974_, v_b_975_, v_i_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v_endIdx_974_);
lean_dec_ref(v_args_973_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2(lean_object* v_f_990_, lean_object* v_args_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_array_get_size(v_args_991_);
v___x_1006_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2(v_args_991_, v___x_1005_, v_f_990_, v___x_1004_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2___boxed(lean_object* v_f_1007_, lean_object* v_args_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2(v_f_1007_, v_args_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec_ref(v_args_1008_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f(lean_object* v_goal_1030_, lean_object* v_target_1031_, lean_object* v_nm_1032_, lean_object* v_00_u03c6_1033_, lean_object* v_G_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
lean_inc_ref(v_00_u03c6_1033_);
v___x_1050_ = l_Lean_Expr_cleanupAnnotations(v_00_u03c6_1033_);
v___x_1051_ = l_Lean_Expr_isApp(v___x_1050_);
if (v___x_1051_ == 0)
{
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_G_1034_);
lean_dec_ref(v_00_u03c6_1033_);
lean_dec(v_nm_1032_);
lean_dec_ref(v_target_1031_);
lean_dec(v_goal_1030_);
goto v___jp_1047_;
}
else
{
lean_object* v_arg_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_arg_1052_ = lean_ctor_get(v___x_1050_, 1);
lean_inc_ref(v_arg_1052_);
v___x_1053_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1050_);
v___x_1054_ = l_Lean_Expr_isApp(v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec_ref(v___x_1053_);
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v_G_1034_);
lean_dec_ref(v_00_u03c6_1033_);
lean_dec(v_nm_1032_);
lean_dec_ref(v_target_1031_);
lean_dec(v_goal_1030_);
goto v___jp_1047_;
}
else
{
lean_object* v_arg_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_arg_1055_ = lean_ctor_get(v___x_1053_, 1);
lean_inc_ref(v_arg_1055_);
v___x_1056_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1053_);
v___x_1057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__1));
v___x_1058_ = l_Lean_Expr_isConstOf(v___x_1056_, v___x_1057_);
lean_dec_ref(v___x_1056_);
if (v___x_1058_ == 0)
{
lean_dec_ref(v_arg_1055_);
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v_G_1034_);
lean_dec_ref(v_00_u03c6_1033_);
lean_dec(v_nm_1032_);
lean_dec_ref(v_target_1031_);
lean_dec(v_goal_1030_);
goto v___jp_1047_;
}
else
{
lean_object* v___x_1059_; 
lean_inc_ref(v_G_1034_);
v___x_1059_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_00_u03c6_1033_, v_G_1034_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1166_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1166_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1166_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_unbox(v_a_1060_);
lean_dec(v_a_1060_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_dec_ref(v_arg_1055_);
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v_G_1034_);
lean_dec(v_nm_1032_);
lean_dec_ref(v_target_1031_);
lean_dec(v_goal_1030_);
v___x_1065_ = lean_box(0);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v___x_1065_);
v___x_1067_ = v___x_1062_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
else
{
uint8_t v___x_1069_; lean_object* v___x_1070_; 
lean_del_object(v___x_1062_);
v___x_1069_ = 0;
lean_inc_ref(v_G_1034_);
lean_inc_ref(v_arg_1052_);
lean_inc(v_nm_1032_);
v___x_1070_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_nm_1032_, v___x_1069_, v_arg_1052_, v_G_1034_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
lean_inc_ref(v_arg_1055_);
v___x_1072_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_nm_1032_, v___x_1069_, v_arg_1055_, v_a_1071_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc_n(v_a_1073_, 2);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = lean_box(0);
v___x_1075_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1073_, v___x_1074_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__1));
v___x_1078_ = lean_box(0);
v___x_1079_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v___x_1077_, v___x_1078_, v_a_1041_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = lean_unsigned_to_nat(3u);
v___x_1082_ = lean_mk_empty_array_with_capacity(v___x_1081_);
v___x_1083_ = lean_array_push(v___x_1082_, v_arg_1055_);
v___x_1084_ = lean_array_push(v___x_1083_, v_arg_1052_);
v___x_1085_ = lean_array_push(v___x_1084_, v_G_1034_);
v___x_1086_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2(v_a_1080_, v___x_1085_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
lean_dec_ref(v___x_1085_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__4));
v___x_1089_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v___x_1088_, v___x_1078_, v_a_1041_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v___x_1091_ = lean_unsigned_to_nat(4u);
v___x_1092_ = lean_mk_empty_array_with_capacity(v___x_1091_);
v___x_1093_ = lean_array_push(v___x_1092_, v_target_1031_);
v___x_1094_ = lean_array_push(v___x_1093_, v_a_1073_);
v___x_1095_ = lean_array_push(v___x_1094_, v_a_1087_);
lean_inc(v_a_1076_);
v___x_1096_ = lean_array_push(v___x_1095_, v_a_1076_);
v___x_1097_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2(v_a_1090_, v___x_1096_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
lean_dec_ref(v___x_1096_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1108_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3___redArg(v_goal_1030_, v_a_1098_, v_a_1043_);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; 
v_unused_1109_ = lean_ctor_get(v___x_1099_, 0);
lean_dec(v_unused_1109_);
v___x_1101_ = v___x_1099_;
v_isShared_1102_ = v_isSharedCheck_1108_;
goto v_resetjp_1100_;
}
else
{
lean_dec(v___x_1099_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1108_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1103_ = l_Lean_Expr_mvarId_x21(v_a_1076_);
lean_dec(v_a_1076_);
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1104_);
v___x_1106_ = v___x_1101_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v_a_1076_);
lean_dec(v_goal_1030_);
v_a_1110_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1097_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1097_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_a_1087_);
lean_dec(v_a_1076_);
lean_dec(v_a_1073_);
lean_dec_ref(v_target_1031_);
lean_dec(v_goal_1030_);
v_a_1118_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1089_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1089_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_a_1076_);
lean_dec(v_a_1073_);
lean_dec_ref(v_target_1031_);
lean_dec(v_goal_1030_);
v_a_1126_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1086_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1086_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
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
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_a_1076_);
lean_dec(v_a_1073_);
lean_dec_ref(v_arg_1055_);
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v_G_1034_);
lean_dec_ref(v_target_1031_);
lean_dec(v_goal_1030_);
v_a_1134_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1079_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1079_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_a_1073_);
lean_dec_ref(v_arg_1055_);
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v_G_1034_);
lean_dec_ref(v_target_1031_);
lean_dec(v_goal_1030_);
v_a_1142_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1075_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1075_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
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
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_arg_1055_);
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v_G_1034_);
lean_dec_ref(v_target_1031_);
lean_dec(v_goal_1030_);
v_a_1150_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1072_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1072_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v_arg_1055_);
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v_G_1034_);
lean_dec(v_nm_1032_);
lean_dec_ref(v_target_1031_);
lean_dec(v_goal_1030_);
v_a_1158_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1070_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1070_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v_arg_1055_);
lean_dec_ref(v_arg_1052_);
lean_dec_ref(v_G_1034_);
lean_dec(v_nm_1032_);
lean_dec_ref(v_target_1031_);
lean_dec(v_goal_1030_);
v_a_1167_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1059_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1059_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
v___jp_1047_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_box(0);
v___x_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___boxed(lean_object** _args){
lean_object* v_goal_1175_ = _args[0];
lean_object* v_target_1176_ = _args[1];
lean_object* v_nm_1177_ = _args[2];
lean_object* v_00_u03c6_1178_ = _args[3];
lean_object* v_G_1179_ = _args[4];
lean_object* v_a_1180_ = _args[5];
lean_object* v_a_1181_ = _args[6];
lean_object* v_a_1182_ = _args[7];
lean_object* v_a_1183_ = _args[8];
lean_object* v_a_1184_ = _args[9];
lean_object* v_a_1185_ = _args[10];
lean_object* v_a_1186_ = _args[11];
lean_object* v_a_1187_ = _args[12];
lean_object* v_a_1188_ = _args[13];
lean_object* v_a_1189_ = _args[14];
lean_object* v_a_1190_ = _args[15];
lean_object* v_a_1191_ = _args[16];
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f(v_goal_1175_, v_target_1176_, v_nm_1177_, v_00_u03c6_1178_, v_G_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3(lean_object* v_mvarId_1193_, lean_object* v_val_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3___redArg(v_mvarId_1193_, v_val_1194_, v___y_1203_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3___boxed(lean_object* v_mvarId_1208_, lean_object* v_val_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3(v_mvarId_1208_, v_val_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3(lean_object* v_f_1223_, lean_object* v_a_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3___redArg(v_f_1223_, v_a_1224_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3___boxed(lean_object* v_f_1238_, lean_object* v_a_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2_spec__2_spec__3(v_f_1238_, v_a_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4(lean_object* v_00_u03b2_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4___redArg(v_x_1254_, v_x_1255_, v_x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1258_, lean_object* v_x_1259_, size_t v_x_1260_, size_t v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___redArg(v_x_1259_, v_x_1260_, v_x_1261_, v_x_1262_, v_x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
size_t v_x_24445__boxed_1271_; size_t v_x_24446__boxed_1272_; lean_object* v_res_1273_; 
v_x_24445__boxed_1271_ = lean_unbox_usize(v_x_1267_);
lean_dec(v_x_1267_);
v_x_24446__boxed_1272_ = lean_unbox_usize(v_x_1268_);
lean_dec(v_x_1268_);
v_res_1273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6(v_00_u03b2_1265_, v_x_1266_, v_x_24445__boxed_1271_, v_x_24446__boxed_1272_, v_x_1269_, v_x_1270_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7(lean_object* v_00_u03b2_1274_, lean_object* v_n_1275_, lean_object* v_k_1276_, lean_object* v_v_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7___redArg(v_n_1275_, v_k_1276_, v_v_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_1279_, size_t v_depth_1280_, lean_object* v_keys_1281_, lean_object* v_vals_1282_, lean_object* v_heq_1283_, lean_object* v_i_1284_, lean_object* v_entries_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8___redArg(v_depth_1280_, v_keys_1281_, v_vals_1282_, v_i_1284_, v_entries_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1287_, lean_object* v_depth_1288_, lean_object* v_keys_1289_, lean_object* v_vals_1290_, lean_object* v_heq_1291_, lean_object* v_i_1292_, lean_object* v_entries_1293_){
_start:
{
size_t v_depth_boxed_1294_; lean_object* v_res_1295_; 
v_depth_boxed_1294_ = lean_unbox_usize(v_depth_1288_);
lean_dec(v_depth_1288_);
v_res_1295_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__8(v_00_u03b2_1287_, v_depth_boxed_1294_, v_keys_1289_, v_vals_1290_, v_heq_1291_, v_i_1292_, v_entries_1293_);
lean_dec_ref(v_vals_1290_);
lean_dec_ref(v_keys_1289_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3_spec__4_spec__6_spec__7_spec__8___redArg(v_x_1297_, v_x_1298_, v_x_1299_, v_x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(lean_object* v_x_1302_, uint8_t v_bi_1303_, lean_object* v_t_1304_, lean_object* v_b_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___y_1314_; lean_object* v___x_1317_; uint8_t v_debug_1318_; 
v___x_1317_ = lean_st_ref_get(v___y_1307_);
v_debug_1318_ = lean_ctor_get_uint8(v___x_1317_, sizeof(void*)*12);
lean_dec(v___x_1317_);
if (v_debug_1318_ == 0)
{
v___y_1314_ = v___y_1307_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1304_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v___x_1320_; 
lean_dec_ref_known(v___x_1319_, 1);
v___x_1320_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_dec_ref_known(v___x_1320_, 1);
v___y_1314_ = v___y_1307_;
goto v___jp_1313_;
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_b_1305_);
lean_dec_ref(v_t_1304_);
lean_dec(v_x_1302_);
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_b_1305_);
lean_dec_ref(v_t_1304_);
lean_dec(v_x_1302_);
v_a_1329_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1319_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1319_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
v___jp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = l_Lean_Expr_lam___override(v_x_1302_, v_t_1304_, v_b_1305_, v_bi_1303_);
v___x_1316_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1315_, v___y_1314_);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg___boxed(lean_object* v_x_1337_, lean_object* v_bi_1338_, lean_object* v_t_1339_, lean_object* v_b_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v_bi_boxed_1348_; lean_object* v_res_1349_; 
v_bi_boxed_1348_ = lean_unbox(v_bi_1338_);
v_res_1349_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(v_x_1337_, v_bi_boxed_1348_, v_t_1339_, v_b_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0(lean_object* v_x_1350_, uint8_t v_bi_1351_, lean_object* v_t_1352_, lean_object* v_b_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(v_x_1350_, v_bi_1351_, v_t_1352_, v_b_1353_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___boxed(lean_object* v_x_1367_, lean_object* v_bi_1368_, lean_object* v_t_1369_, lean_object* v_b_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v_bi_boxed_1383_; lean_object* v_res_1384_; 
v_bi_boxed_1383_ = lean_unbox(v_bi_1368_);
v_res_1384_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0(v_x_1367_, v_bi_boxed_1383_, v_t_1369_, v_b_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
return v_res_1384_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1385_; double v___x_1386_; 
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = lean_float_of_nat(v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(lean_object* v_cls_1390_, lean_object* v_msg_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_ref_1397_; lean_object* v___x_1398_; lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1444_; 
v_ref_1397_ = lean_ctor_get(v___y_1394_, 2);
v___x_1398_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0(v_msg_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1444_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1444_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v_traceState_1404_; lean_object* v_env_1405_; lean_object* v_nextMacroScope_1406_; lean_object* v_ngen_1407_; lean_object* v_auxDeclNGen_1408_; lean_object* v_cache_1409_; lean_object* v_recordedDeps_1410_; lean_object* v_messages_1411_; lean_object* v_infoState_1412_; lean_object* v_snapshotTasks_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1443_; 
v___x_1403_ = lean_st_ref_take(v___y_1395_);
v_traceState_1404_ = lean_ctor_get(v___x_1403_, 4);
v_env_1405_ = lean_ctor_get(v___x_1403_, 0);
v_nextMacroScope_1406_ = lean_ctor_get(v___x_1403_, 1);
v_ngen_1407_ = lean_ctor_get(v___x_1403_, 2);
v_auxDeclNGen_1408_ = lean_ctor_get(v___x_1403_, 3);
v_cache_1409_ = lean_ctor_get(v___x_1403_, 5);
v_recordedDeps_1410_ = lean_ctor_get(v___x_1403_, 6);
v_messages_1411_ = lean_ctor_get(v___x_1403_, 7);
v_infoState_1412_ = lean_ctor_get(v___x_1403_, 8);
v_snapshotTasks_1413_ = lean_ctor_get(v___x_1403_, 9);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1415_ = v___x_1403_;
v_isShared_1416_ = v_isSharedCheck_1443_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_snapshotTasks_1413_);
lean_inc(v_infoState_1412_);
lean_inc(v_messages_1411_);
lean_inc(v_recordedDeps_1410_);
lean_inc(v_cache_1409_);
lean_inc(v_traceState_1404_);
lean_inc(v_auxDeclNGen_1408_);
lean_inc(v_ngen_1407_);
lean_inc(v_nextMacroScope_1406_);
lean_inc(v_env_1405_);
lean_dec(v___x_1403_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1443_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
uint64_t v_tid_1417_; lean_object* v_traces_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1442_; 
v_tid_1417_ = lean_ctor_get_uint64(v_traceState_1404_, sizeof(void*)*1);
v_traces_1418_ = lean_ctor_get(v_traceState_1404_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_traceState_1404_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1420_ = v_traceState_1404_;
v_isShared_1421_ = v_isSharedCheck_1442_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_traces_1418_);
lean_dec(v_traceState_1404_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1442_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; double v___x_1424_; uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0);
v___x_1425_ = 0;
v___x_1426_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__1));
v___x_1427_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1427_, 0, v_cls_1390_);
lean_ctor_set(v___x_1427_, 1, v___x_1423_);
lean_ctor_set(v___x_1427_, 2, v___x_1426_);
lean_ctor_set_float(v___x_1427_, sizeof(void*)*3, v___x_1424_);
lean_ctor_set_float(v___x_1427_, sizeof(void*)*3 + 8, v___x_1424_);
lean_ctor_set_uint8(v___x_1427_, sizeof(void*)*3 + 16, v___x_1425_);
v___x_1428_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__2));
v___x_1429_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v_a_1399_);
lean_ctor_set(v___x_1429_, 2, v___x_1428_);
lean_inc(v_ref_1397_);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v_ref_1397_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = l_Lean_PersistentArray_push___redArg(v_traces_1418_, v___x_1430_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1431_);
v___x_1433_ = v___x_1420_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1431_);
lean_ctor_set_uint64(v_reuseFailAlloc_1441_, sizeof(void*)*1, v_tid_1417_);
v___x_1433_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1435_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 4, v___x_1433_);
v___x_1435_ = v___x_1415_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_env_1405_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_nextMacroScope_1406_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_ngen_1407_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_auxDeclNGen_1408_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1440_, 5, v_cache_1409_);
lean_ctor_set(v_reuseFailAlloc_1440_, 6, v_recordedDeps_1410_);
lean_ctor_set(v_reuseFailAlloc_1440_, 7, v_messages_1411_);
lean_ctor_set(v_reuseFailAlloc_1440_, 8, v_infoState_1412_);
lean_ctor_set(v_reuseFailAlloc_1440_, 9, v_snapshotTasks_1413_);
v___x_1435_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_st_ref_put(v___y_1395_, v___x_1435_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1422_);
v___x_1438_ = v___x_1401_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1422_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___boxed(lean_object* v_cls_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(v_cls_1445_, v_msg_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1452_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8));
v___x_1473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__10));
v___x_1474_ = l_Lean_Name_append(v___x_1473_, v___x_1472_);
return v___x_1474_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__12));
v___x_1477_ = l_Lean_stringToMessageData(v___x_1476_);
return v___x_1477_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__14));
v___x_1480_ = l_Lean_stringToMessageData(v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f(lean_object* v_goal_1481_, lean_object* v_nm_1482_, lean_object* v_eqn_1483_, lean_object* v_G_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v___x_1497_; 
lean_inc_ref(v_eqn_1483_);
v___x_1497_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_eqn_1483_, v_G_1484_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1669_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1669_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1669_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
if (lean_obj_tag(v_a_1498_) == 1)
{
lean_object* v_val_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1664_; 
lean_del_object(v___x_1500_);
v_val_1502_ = lean_ctor_get(v_a_1498_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_a_1498_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1504_ = v_a_1498_;
v_isShared_1505_ = v_isSharedCheck_1664_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_val_1502_);
lean_dec(v_a_1498_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1664_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v_snd_1506_; lean_object* v_fst_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1663_; 
v_snd_1506_ = lean_ctor_get(v_val_1502_, 1);
v_fst_1507_ = lean_ctor_get(v_val_1502_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_val_1502_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1509_ = v_val_1502_;
v_isShared_1510_ = v_isSharedCheck_1663_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_snd_1506_);
lean_inc(v_fst_1507_);
lean_dec(v_val_1502_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1663_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1662_; 
v_fst_1511_ = lean_ctor_get(v_snd_1506_, 0);
v_snd_1512_ = lean_ctor_get(v_snd_1506_, 1);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_snd_1506_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1514_ = v_snd_1506_;
v_isShared_1515_ = v_isSharedCheck_1662_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_inc(v_fst_1511_);
lean_dec(v_snd_1506_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1662_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; 
lean_inc(v_fst_1507_);
v___x_1516_ = l_Lean_Meta_Sym_inferType(v_fst_1507_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc_n(v_a_1517_, 2);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_1517_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = l_Lean_Expr_fvarId_x21(v_fst_1507_);
v___x_1521_ = l_Lean_FVarId_getUserName___redArg(v___x_1520_, v_a_1492_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = 0;
lean_inc(v_snd_1512_);
lean_inc(v_a_1517_);
v___x_1524_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(v_a_1522_, v___x_1523_, v_a_1517_, v_snd_1512_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = lean_unsigned_to_nat(1u);
v___x_1527_ = lean_mk_empty_array_with_capacity(v___x_1526_);
lean_inc(v_fst_1511_);
v___x_1528_ = lean_array_push(v___x_1527_, v_fst_1511_);
v___x_1529_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_snd_1512_, v___x_1528_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_nm_1482_, v___x_1523_, v_eqn_1483_, v_a_1530_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1533_ = lean_box(0);
v___x_1534_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1532_, v___x_1533_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1605_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1605_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1605_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__3));
v___x_1548_ = lean_box(0);
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 1);
lean_ctor_set(v___x_1514_, 1, v___x_1548_);
lean_ctor_set(v___x_1514_, 0, v_a_1519_);
v___x_1550_ = v___x_1514_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1519_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1549_;
}
v___jp_1539_:
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = l_Lean_Expr_mvarId_x21(v_a_1535_);
lean_dec(v_a_1535_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1540_);
v___x_1542_ = v___x_1504_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1544_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1542_);
v___x_1544_ = v___x_1537_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v___x_1547_, v___x_1550_, v_a_1491_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = lean_unsigned_to_nat(5u);
v___x_1554_ = lean_mk_empty_array_with_capacity(v___x_1553_);
v___x_1555_ = lean_array_push(v___x_1554_, v_a_1517_);
lean_inc(v_fst_1507_);
v___x_1556_ = lean_array_push(v___x_1555_, v_fst_1507_);
lean_inc(v_fst_1511_);
v___x_1557_ = lean_array_push(v___x_1556_, v_fst_1511_);
v___x_1558_ = lean_array_push(v___x_1557_, v_a_1525_);
lean_inc(v_a_1535_);
v___x_1559_ = lean_array_push(v___x_1558_, v_a_1535_);
v___x_1560_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2(v_a_1552_, v___x_1559_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec_ref(v___x_1559_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; lean_object* v_toCold_1563_; lean_object* v_options_1564_; uint8_t v_hasTrace_1565_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__3___redArg(v_goal_1481_, v_a_1561_, v_a_1493_);
lean_dec_ref(v___x_1562_);
v_toCold_1563_ = lean_ctor_get(v_a_1494_, 0);
v_options_1564_ = lean_ctor_get(v_toCold_1563_, 2);
v_hasTrace_1565_ = lean_ctor_get_uint8(v_options_1564_, sizeof(void*)*1);
if (v_hasTrace_1565_ == 0)
{
lean_dec(v_fst_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_fst_1507_);
goto v___jp_1539_;
}
else
{
lean_object* v_inheritedTraceOptions_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v_inheritedTraceOptions_1566_ = lean_ctor_get(v_toCold_1563_, 11);
v___x_1567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8));
v___x_1568_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11);
v___x_1569_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1566_, v_options_1564_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_dec(v_fst_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_fst_1507_);
goto v___jp_1539_;
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1570_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13);
v___x_1571_ = l_Lean_MessageData_ofExpr(v_fst_1507_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set_tag(v___x_1509_, 7);
lean_ctor_set(v___x_1509_, 1, v___x_1571_);
lean_ctor_set(v___x_1509_, 0, v___x_1570_);
v___x_1573_ = v___x_1509_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1574_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = l_Lean_MessageData_ofExpr(v_fst_1511_);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(v___x_1567_, v___x_1577_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_dec_ref_known(v___x_1578_, 1);
goto v___jp_1539_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_del_object(v___x_1537_);
lean_dec(v_a_1535_);
lean_del_object(v___x_1504_);
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1578_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_del_object(v___x_1537_);
lean_dec(v_a_1535_);
lean_dec(v_fst_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_fst_1507_);
lean_del_object(v___x_1504_);
lean_dec(v_goal_1481_);
v_a_1588_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1560_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1560_);
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
lean_del_object(v___x_1537_);
lean_dec(v_a_1535_);
lean_dec(v_a_1525_);
lean_dec(v_a_1517_);
lean_dec(v_fst_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_fst_1507_);
lean_del_object(v___x_1504_);
lean_dec(v_goal_1481_);
v_a_1596_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1551_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1551_);
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
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_a_1525_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
lean_del_object(v___x_1514_);
lean_dec(v_fst_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_fst_1507_);
lean_del_object(v___x_1504_);
lean_dec(v_goal_1481_);
v_a_1606_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1534_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1534_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec(v_a_1525_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
lean_del_object(v___x_1514_);
lean_dec(v_fst_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_fst_1507_);
lean_del_object(v___x_1504_);
lean_dec(v_goal_1481_);
v_a_1614_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1531_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1531_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_a_1525_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
lean_del_object(v___x_1514_);
lean_dec(v_fst_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_fst_1507_);
lean_del_object(v___x_1504_);
lean_dec_ref(v_eqn_1483_);
lean_dec(v_nm_1482_);
lean_dec(v_goal_1481_);
v_a_1622_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1529_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1529_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
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
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_fst_1507_);
lean_del_object(v___x_1504_);
lean_dec_ref(v_eqn_1483_);
lean_dec(v_nm_1482_);
lean_dec(v_goal_1481_);
v_a_1630_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1524_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1524_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_fst_1507_);
lean_del_object(v___x_1504_);
lean_dec_ref(v_eqn_1483_);
lean_dec(v_nm_1482_);
lean_dec(v_goal_1481_);
v_a_1638_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1521_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1521_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v_a_1517_);
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_fst_1507_);
lean_del_object(v___x_1504_);
lean_dec_ref(v_eqn_1483_);
lean_dec(v_nm_1482_);
lean_dec(v_goal_1481_);
v_a_1646_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1518_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1518_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_del_object(v___x_1509_);
lean_dec(v_fst_1507_);
lean_del_object(v___x_1504_);
lean_dec_ref(v_eqn_1483_);
lean_dec(v_nm_1482_);
lean_dec(v_goal_1481_);
v_a_1654_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1516_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1516_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
lean_dec(v_a_1498_);
lean_dec_ref(v_eqn_1483_);
lean_dec(v_nm_1482_);
lean_dec(v_goal_1481_);
v___x_1665_ = lean_box(0);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1665_);
v___x_1667_ = v___x_1500_;
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
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v_eqn_1483_);
lean_dec(v_nm_1482_);
lean_dec(v_goal_1481_);
v_a_1670_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1497_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1497_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___boxed(lean_object* v_goal_1678_, lean_object* v_nm_1679_, lean_object* v_eqn_1680_, lean_object* v_G_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f(v_goal_1678_, v_nm_1679_, v_eqn_1680_, v_G_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1(lean_object* v_cls_1695_, lean_object* v_msg_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(v_cls_1695_, v_msg_1696_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___boxed(lean_object* v_cls_1710_, lean_object* v_msg_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1(v_cls_1710_, v_msg_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0(lean_object* v_x_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1730_);
lean_inc_ref(v___y_1729_);
lean_inc(v___y_1728_);
lean_inc(v___y_1727_);
lean_inc_ref(v___y_1726_);
v___x_1738_ = lean_apply_12(v_x_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, lean_box(0));
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0___boxed(lean_object* v_x_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0(v_x_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(lean_object* v_mvarId_1753_, lean_object* v_x_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___f_1767_; lean_object* v___x_1768_; 
lean_inc(v___y_1761_);
lean_inc_ref(v___y_1760_);
lean_inc(v___y_1759_);
lean_inc_ref(v___y_1758_);
lean_inc(v___y_1757_);
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1755_);
v___f_1767_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1767_, 0, v_x_1754_);
lean_closure_set(v___f_1767_, 1, v___y_1755_);
lean_closure_set(v___f_1767_, 2, v___y_1756_);
lean_closure_set(v___f_1767_, 3, v___y_1757_);
lean_closure_set(v___f_1767_, 4, v___y_1758_);
lean_closure_set(v___f_1767_, 5, v___y_1759_);
lean_closure_set(v___f_1767_, 6, v___y_1760_);
lean_closure_set(v___f_1767_, 7, v___y_1761_);
v___x_1768_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1753_, v___f_1767_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1768_) == 0)
{
return v___x_1768_;
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___boxed(lean_object* v_mvarId_1777_, lean_object* v_x_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_mvarId_1777_, v_x_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0(lean_object* v_00_u03b1_1792_, lean_object* v_mvarId_1793_, lean_object* v_x_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_mvarId_1793_, v_x_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___boxed(lean_object* v_00_u03b1_1808_, lean_object* v_mvarId_1809_, lean_object* v_x_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0(v_00_u03b1_1808_, v_mvarId_1809_, v_x_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(lean_object* v___x_1824_, lean_object* v___f_1825_, lean_object* v_____r_1826_, lean_object* v_goal_1827_, lean_object* v_pending_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; 
lean_inc(v___x_1824_);
v___x_1841_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_goal_1827_, v___x_1824_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc_n(v_a_1842_, 2);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_a_1842_, v___f_1825_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1868_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1868_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1868_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___y_1849_; lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_LocalContext_lastDecl(v_a_1844_);
lean_dec(v_a_1844_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_box(0);
v___y_1849_ = v___x_1858_;
goto v___jp_1848_;
}
else
{
lean_object* v_val_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1867_; 
v_val_1859_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1861_ = v___x_1857_;
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_val_1859_);
lean_dec(v___x_1857_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = l_Lean_LocalDecl_fvarId(v_val_1859_);
lean_dec(v_val_1859_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
v___y_1849_ = v___x_1865_;
goto v___jp_1848_;
}
}
}
v___jp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1850_ = lean_nat_sub(v_pending_1828_, v___x_1824_);
lean_dec(v___x_1824_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___y_1849_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v_a_1842_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1853_);
v___x_1855_ = v___x_1846_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
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
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1842_);
lean_dec(v___x_1824_);
v_a_1869_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1843_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1843_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v___f_1825_);
lean_dec(v___x_1824_);
v_a_1877_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1841_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1841_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1885_ = _args[0];
lean_object* v___f_1886_ = _args[1];
lean_object* v_____r_1887_ = _args[2];
lean_object* v_goal_1888_ = _args[3];
lean_object* v_pending_1889_ = _args[4];
lean_object* v___y_1890_ = _args[5];
lean_object* v___y_1891_ = _args[6];
lean_object* v___y_1892_ = _args[7];
lean_object* v___y_1893_ = _args[8];
lean_object* v___y_1894_ = _args[9];
lean_object* v___y_1895_ = _args[10];
lean_object* v___y_1896_ = _args[11];
lean_object* v___y_1897_ = _args[12];
lean_object* v___y_1898_ = _args[13];
lean_object* v___y_1899_ = _args[14];
lean_object* v___y_1900_ = _args[15];
lean_object* v___y_1901_ = _args[16];
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1885_, v___f_1886_, v_____r_1887_, v_goal_1888_, v_pending_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v_pending_1889_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0(lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_lctx_1915_; lean_object* v___x_1916_; 
v_lctx_1915_ = lean_ctor_get(v___y_1910_, 2);
lean_inc_ref(v_lctx_1915_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_lctx_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0___boxed(lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0(v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1929_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__1));
v___x_1933_ = l_Lean_stringToMessageData(v___x_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(lean_object* v_a_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___y_1948_; lean_object* v_snd_1968_; lean_object* v_fst_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2061_; 
v_snd_1968_ = lean_ctor_get(v_a_1934_, 1);
v_fst_1969_ = lean_ctor_get(v_a_1934_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_a_1934_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_1971_ = v_a_1934_;
v_isShared_1972_ = v_isSharedCheck_2061_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_snd_1968_);
lean_inc(v_fst_1969_);
lean_dec(v_a_1934_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2061_;
goto v_resetjp_1970_;
}
v___jp_1947_:
{
if (lean_obj_tag(v___y_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1959_; 
v_a_1949_ = lean_ctor_get(v___y_1948_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___y_1948_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1951_ = v___y_1948_;
v_isShared_1952_ = v_isSharedCheck_1959_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___y_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1959_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
if (lean_obj_tag(v_a_1949_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1955_; 
v_a_1953_ = lean_ctor_get(v_a_1949_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v_a_1949_, 1);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v_a_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
else
{
lean_object* v_a_1957_; 
lean_del_object(v___x_1951_);
v_a_1957_ = lean_ctor_get(v_a_1949_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v_a_1949_, 1);
v_a_1934_ = v_a_1957_;
goto _start;
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
v_a_1960_ = lean_ctor_get(v___y_1948_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___y_1948_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___y_1948_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___y_1948_);
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
v_resetjp_1970_:
{
lean_object* v_fst_1973_; lean_object* v_snd_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2060_; 
v_fst_1973_ = lean_ctor_get(v_snd_1968_, 0);
v_snd_1974_ = lean_ctor_get(v_snd_1968_, 1);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_snd_1968_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_1976_ = v_snd_1968_;
v_isShared_1977_ = v_isSharedCheck_2060_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_snd_1974_);
lean_inc(v_fst_1973_);
lean_dec(v_snd_1968_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2060_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = lean_unsigned_to_nat(0u);
v___x_1979_ = lean_nat_dec_lt(v___x_1978_, v_fst_1973_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1981_; 
if (v_isShared_1977_ == 0)
{
v___x_1981_ = v___x_1976_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_fst_1973_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_snd_1974_);
v___x_1981_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1983_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 1, v___x_1981_);
v___x_1983_ = v___x_1971_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_fst_1969_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1984_; 
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
return v___x_1984_;
}
}
}
else
{
lean_object* v___f_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___f_1987_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__0));
v___x_1988_ = lean_unsigned_to_nat(1u);
lean_inc(v_fst_1969_);
v___x_1989_ = l_Lean_MVarId_getType(v_fst_1969_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
if (lean_obj_tag(v_a_1990_) == 7)
{
lean_object* v_binderName_1991_; lean_object* v_binderType_1992_; lean_object* v_body_1993_; uint8_t v___x_1994_; 
v_binderName_1991_ = lean_ctor_get(v_a_1990_, 0);
lean_inc(v_binderName_1991_);
v_binderType_1992_ = lean_ctor_get(v_a_1990_, 1);
lean_inc_ref(v_binderType_1992_);
v_body_1993_ = lean_ctor_get(v_a_1990_, 2);
lean_inc_ref(v_body_1993_);
v___x_1994_ = l_Lean_Expr_hasLooseBVars(v_body_1993_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_inc_ref(v_body_1993_);
lean_inc_ref(v_binderType_1992_);
lean_inc(v_binderName_1991_);
lean_inc_n(v_fst_1969_, 2);
v___x_1995_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___boxed), 17, 5);
lean_closure_set(v___x_1995_, 0, v_fst_1969_);
lean_closure_set(v___x_1995_, 1, v_a_1990_);
lean_closure_set(v___x_1995_, 2, v_binderName_1991_);
lean_closure_set(v___x_1995_, 3, v_binderType_1992_);
lean_closure_set(v___x_1995_, 4, v_body_1993_);
v___x_1996_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_fst_1969_, v___x_1995_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
if (lean_obj_tag(v_a_1997_) == 1)
{
lean_object* v_val_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_dec_ref(v_body_1993_);
lean_dec_ref(v_binderType_1992_);
lean_dec(v_binderName_1991_);
lean_dec(v_fst_1969_);
v_val_1998_ = lean_ctor_get(v_a_1997_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v_a_1997_, 1);
v___x_1999_ = lean_nat_add(v_fst_1973_, v___x_1988_);
lean_dec(v_fst_1973_);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1999_);
v___x_2001_ = v___x_1976_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_snd_1974_);
v___x_2001_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2003_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 1, v___x_2001_);
lean_ctor_set(v___x_1971_, 0, v_val_1998_);
v___x_2003_ = v___x_1971_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_val_1998_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
v_a_1934_ = v___x_2003_;
goto _start;
}
}
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v_a_1997_);
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_del_object(v___x_1971_);
lean_inc_n(v_fst_1969_, 2);
v___x_2007_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___boxed), 16, 4);
lean_closure_set(v___x_2007_, 0, v_fst_1969_);
lean_closure_set(v___x_2007_, 1, v_binderName_1991_);
lean_closure_set(v___x_2007_, 2, v_binderType_1992_);
lean_closure_set(v___x_2007_, 3, v_body_1993_);
v___x_2008_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_fst_1969_, v___x_2007_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
if (lean_obj_tag(v_a_2009_) == 1)
{
lean_object* v_val_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
lean_dec(v_fst_1969_);
v_val_2010_ = lean_ctor_get(v_a_2009_, 0);
lean_inc(v_val_2010_);
lean_dec_ref_known(v_a_2009_, 1);
v___x_2011_ = lean_box(0);
v___x_2012_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1988_, v___f_1987_, v___x_2011_, v_val_2010_, v_fst_1973_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v_fst_1973_);
v___y_1948_ = v___x_2012_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec(v_a_2009_);
v___x_2013_ = lean_box(0);
v___x_2014_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1988_, v___f_1987_, v___x_2013_, v_fst_1969_, v_fst_1973_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v_fst_1973_);
v___y_1948_ = v___x_2014_;
goto v___jp_1947_;
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_fst_1973_);
lean_dec(v_fst_1969_);
v_a_2015_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2008_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2008_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v_body_1993_);
lean_dec_ref(v_binderType_1992_);
lean_dec(v_binderName_1991_);
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_dec(v_fst_1973_);
lean_del_object(v___x_1971_);
lean_dec(v_fst_1969_);
v_a_2023_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1996_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1996_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec_ref(v_body_1993_);
lean_dec_ref(v_binderType_1992_);
lean_dec_ref_known(v_a_1990_, 3);
lean_dec(v_binderName_1991_);
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_del_object(v___x_1971_);
v___x_2031_ = lean_box(0);
v___x_2032_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1988_, v___f_1987_, v___x_2031_, v_fst_1969_, v_fst_1973_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v_fst_1973_);
v___y_1948_ = v___x_2032_;
goto v___jp_1947_;
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec(v_a_1990_);
v___x_2033_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2);
lean_inc(v_fst_1969_);
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_fst_1969_);
v___x_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2033_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_2035_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v___x_2038_; 
lean_dec_ref_known(v___x_2036_, 1);
if (v_isShared_1977_ == 0)
{
v___x_2038_ = v___x_1976_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_fst_1973_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_snd_1974_);
v___x_2038_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 1, v___x_2038_);
v___x_2040_ = v___x_1971_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_fst_1969_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
v_a_1934_ = v___x_2040_;
goto _start;
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_dec(v_fst_1973_);
lean_del_object(v___x_1971_);
lean_dec(v_fst_1969_);
v_a_2044_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2036_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2036_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_del_object(v___x_1976_);
lean_dec(v_snd_1974_);
lean_dec(v_fst_1973_);
lean_del_object(v___x_1971_);
lean_dec(v_fst_1969_);
v_a_2052_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_1989_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_1989_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___boxed(lean_object* v_a_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(v_a_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2075_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introPre___closed__1(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introPre___closed__0));
v___x_2078_ = l_Lean_stringToMessageData(v___x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre(lean_object* v_rule_2082_, lean_object* v_goal_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_box(0);
lean_inc(v_goal_2083_);
v___x_2106_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_2082_, v_goal_2083_, v___x_2105_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
if (lean_obj_tag(v_a_2107_) == 1)
{
lean_object* v_mvarIds_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2166_; 
v_mvarIds_2108_ = lean_ctor_get(v_a_2107_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_a_2107_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2110_ = v_a_2107_;
v_isShared_2111_ = v_isSharedCheck_2166_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_mvarIds_2108_);
lean_dec(v_a_2107_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2166_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
if (lean_obj_tag(v_mvarIds_2108_) == 1)
{
lean_object* v_tail_2112_; 
v_tail_2112_ = lean_ctor_get(v_mvarIds_2108_, 1);
if (lean_obj_tag(v_tail_2112_) == 0)
{
lean_object* v_head_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_goal_2083_);
v_head_2113_ = lean_ctor_get(v_mvarIds_2108_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_mvarIds_2108_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; 
v_unused_2165_ = lean_ctor_get(v_mvarIds_2108_, 1);
lean_dec(v_unused_2165_);
v___x_2115_ = v_mvarIds_2108_;
v_isShared_2116_ = v_isSharedCheck_2164_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_head_2113_);
lean_dec(v_mvarIds_2108_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2164_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introPre___closed__2));
if (v_isShared_2116_ == 0)
{
lean_ctor_set_tag(v___x_2115_, 0);
lean_ctor_set(v___x_2115_, 1, v___x_2117_);
v___x_2119_ = v___x_2115_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_head_2113_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; 
v___x_2120_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(v___x_2119_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2154_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2154_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2154_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v_snd_2125_; lean_object* v_snd_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2152_; 
v_snd_2125_ = lean_ctor_get(v_a_2121_, 1);
lean_inc(v_snd_2125_);
v_snd_2126_ = lean_ctor_get(v_snd_2125_, 1);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_snd_2125_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v_snd_2125_, 0);
lean_dec(v_unused_2153_);
v___x_2128_ = v_snd_2125_;
v_isShared_2129_ = v_isSharedCheck_2152_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_snd_2126_);
lean_dec(v_snd_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2152_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
if (lean_obj_tag(v_snd_2126_) == 1)
{
lean_object* v_fst_2130_; lean_object* v_val_2131_; lean_object* v___x_2133_; 
lean_del_object(v___x_2110_);
v_fst_2130_ = lean_ctor_get(v_a_2121_, 0);
lean_inc(v_fst_2130_);
lean_dec(v_a_2121_);
v_val_2131_ = lean_ctor_get(v_snd_2126_, 0);
lean_inc(v_val_2131_);
lean_dec_ref_known(v_snd_2126_, 1);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_val_2131_);
lean_ctor_set(v___x_2128_, 0, v_fst_2130_);
v___x_2133_ = v___x_2128_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_fst_2130_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_val_2131_);
v___x_2133_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2135_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2133_);
v___x_2135_ = v___x_2123_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
else
{
lean_object* v_fst_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2150_; 
lean_del_object(v___x_2128_);
lean_dec(v_snd_2126_);
lean_del_object(v___x_2123_);
v_fst_2138_ = lean_ctor_get(v_a_2121_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_a_2121_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v_a_2121_, 1);
lean_dec(v_unused_2151_);
v___x_2140_ = v_a_2121_;
v_isShared_2141_ = v_isSharedCheck_2150_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_fst_2138_);
lean_dec(v_a_2121_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2150_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 0, v_fst_2138_);
v___x_2144_ = v___x_2110_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_fst_2138_);
v___x_2144_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2146_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set_tag(v___x_2140_, 7);
lean_ctor_set(v___x_2140_, 1, v___x_2144_);
lean_ctor_set(v___x_2140_, 0, v___x_2142_);
v___x_2146_ = v___x_2140_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_2146_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
return v___x_2147_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_del_object(v___x_2110_);
v_a_2155_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2120_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2120_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2108_, 2);
lean_del_object(v___x_2110_);
v___y_2097_ = v_a_2091_;
v___y_2098_ = v_a_2092_;
v___y_2099_ = v_a_2093_;
v___y_2100_ = v_a_2094_;
goto v___jp_2096_;
}
}
else
{
lean_del_object(v___x_2110_);
lean_dec(v_mvarIds_2108_);
v___y_2097_ = v_a_2091_;
v___y_2098_ = v_a_2092_;
v___y_2099_ = v_a_2093_;
v___y_2100_ = v_a_2094_;
goto v___jp_2096_;
}
}
}
else
{
lean_dec(v_a_2107_);
v___y_2097_ = v_a_2091_;
v___y_2098_ = v_a_2092_;
v___y_2099_ = v_a_2093_;
v___y_2100_ = v_a_2094_;
goto v___jp_2096_;
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_goal_2083_);
v_a_2167_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2106_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2106_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
v___jp_2096_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2101_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introPre___closed__1, &l_Lean_Elab_Tactic_VCGen_introPre___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_introPre___closed__1);
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v_goal_2083_);
v___x_2103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_2103_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
return v___x_2104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre___boxed(lean_object* v_rule_2175_, lean_object* v_goal_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Elab_Tactic_VCGen_introPre(v_rule_2175_, v_goal_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
lean_dec(v_a_2181_);
lean_dec_ref(v_a_2180_);
lean_dec(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1(lean_object* v_inst_2190_, lean_object* v_a_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(v_a_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___boxed(lean_object* v_inst_2205_, lean_object* v_a_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1(v_inst_2205_, v_a_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f(lean_object* v_goal_2225_, lean_object* v_target_2226_, lean_object* v_00_u03b1_2227_, lean_object* v_inst_2228_, lean_object* v_pre_2229_, lean_object* v_rhs_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2));
v___x_2244_ = l_Lean_Expr_isAppOf(v_rhs_2230_, v___x_2243_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec_ref(v_rhs_2230_);
lean_dec_ref(v_pre_2229_);
lean_dec_ref(v_inst_2228_);
lean_dec_ref(v_00_u03b1_2227_);
lean_dec(v_goal_2225_);
v___x_2245_ = lean_box(0);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_rhs_2230_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2298_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2298_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2298_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
if (lean_obj_tag(v_a_2248_) == 1)
{
lean_object* v_val_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2293_; 
lean_del_object(v___x_2250_);
v_val_2252_ = lean_ctor_get(v_a_2248_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_a_2248_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2254_ = v_a_2248_;
v_isShared_2255_ = v_isSharedCheck_2293_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_val_2252_);
lean_dec(v_a_2248_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2293_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2256_ = l_Lean_Expr_getAppFn(v_target_2226_);
v___x_2257_ = lean_unsigned_to_nat(4u);
v___x_2258_ = lean_mk_empty_array_with_capacity(v___x_2257_);
v___x_2259_ = lean_array_push(v___x_2258_, v_00_u03b1_2227_);
v___x_2260_ = lean_array_push(v___x_2259_, v_inst_2228_);
v___x_2261_ = lean_array_push(v___x_2260_, v_pre_2229_);
v___x_2262_ = lean_array_push(v___x_2261_, v_val_2252_);
v___x_2263_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__2(v___x_2256_, v___x_2262_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
lean_dec_ref(v___x_2262_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2265_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref_known(v___x_2263_, 1);
v___x_2265_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2225_, v_a_2264_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2276_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2276_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2276_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v_a_2266_);
v___x_2271_ = v___x_2254_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2273_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2271_);
v___x_2273_ = v___x_2268_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_del_object(v___x_2254_);
v_a_2277_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2265_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2265_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_del_object(v___x_2254_);
lean_dec(v_goal_2225_);
v_a_2285_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2263_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2263_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
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
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2296_; 
lean_dec(v_a_2248_);
lean_dec_ref(v_pre_2229_);
lean_dec_ref(v_inst_2228_);
lean_dec_ref(v_00_u03b1_2227_);
lean_dec(v_goal_2225_);
v___x_2294_ = lean_box(0);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2294_);
v___x_2296_ = v___x_2250_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec_ref(v_pre_2229_);
lean_dec_ref(v_inst_2228_);
lean_dec_ref(v_00_u03b1_2227_);
lean_dec(v_goal_2225_);
v_a_2299_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2247_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2247_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___boxed(lean_object** _args){
lean_object* v_goal_2307_ = _args[0];
lean_object* v_target_2308_ = _args[1];
lean_object* v_00_u03b1_2309_ = _args[2];
lean_object* v_inst_2310_ = _args[3];
lean_object* v_pre_2311_ = _args[4];
lean_object* v_rhs_2312_ = _args[5];
lean_object* v_a_2313_ = _args[6];
lean_object* v_a_2314_ = _args[7];
lean_object* v_a_2315_ = _args[8];
lean_object* v_a_2316_ = _args[9];
lean_object* v_a_2317_ = _args[10];
lean_object* v_a_2318_ = _args[11];
lean_object* v_a_2319_ = _args[12];
lean_object* v_a_2320_ = _args[13];
lean_object* v_a_2321_ = _args[14];
lean_object* v_a_2322_ = _args[15];
lean_object* v_a_2323_ = _args[16];
lean_object* v_a_2324_ = _args[17];
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f(v_goal_2307_, v_target_2308_, v_00_u03b1_2309_, v_inst_2310_, v_pre_2311_, v_rhs_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec_ref(v_target_2308_);
return v_res_2325_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2344_; lean_object* v_dummy_2345_; 
v___x_2344_ = lean_box(0);
v_dummy_2345_ = l_Lean_Expr_sort___override(v___x_2344_);
return v_dummy_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(lean_object* v_goal_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
if (lean_obj_tag(v_x_2347_) == 5)
{
lean_object* v_fn_2355_; lean_object* v_arg_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_fn_2355_ = lean_ctor_get(v_x_2347_, 0);
lean_inc_ref(v_fn_2355_);
v_arg_2356_ = lean_ctor_get(v_x_2347_, 1);
lean_inc_ref(v_arg_2356_);
lean_dec_ref_known(v_x_2347_, 2);
v___x_2357_ = lean_array_set(v_x_2348_, v_x_2349_, v_arg_2356_);
v___x_2358_ = lean_unsigned_to_nat(1u);
v___x_2359_ = lean_nat_sub(v_x_2349_, v___x_2358_);
lean_dec(v_x_2349_);
v_x_2347_ = v_fn_2355_;
v_x_2348_ = v___x_2357_;
v_x_2349_ = v___x_2359_;
goto _start;
}
else
{
lean_object* v___x_2361_; uint8_t v___x_2362_; 
lean_dec(v_x_2349_);
v___x_2361_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3));
v___x_2362_ = l_Lean_Expr_isConstOf(v_x_2347_, v___x_2361_);
lean_dec_ref(v_x_2347_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec_ref(v_x_2348_);
lean_dec(v_goal_2346_);
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2365_ = lean_unsigned_to_nat(2u);
v___x_2366_ = lean_array_get_size(v_x_2348_);
v___x_2367_ = lean_nat_dec_lt(v___x_2365_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
lean_dec_ref(v_x_2348_);
lean_dec(v_goal_2346_);
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2370_ = lean_array_fget_borrowed(v_x_2348_, v___x_2365_);
v___x_2371_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5));
v___x_2372_ = l_Lean_Expr_isAppOf(v___x_2370_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec_ref(v_x_2348_);
lean_dec(v_goal_2346_);
v___x_2373_ = lean_box(0);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
else
{
lean_object* v___x_2375_; uint8_t v___x_2376_; 
v___x_2375_ = lean_unsigned_to_nat(3u);
v___x_2376_ = lean_nat_dec_lt(v___x_2375_, v___x_2366_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec_ref(v_x_2348_);
lean_dec(v_goal_2346_);
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2379_ = lean_array_fget_borrowed(v_x_2348_, v___x_2375_);
v___x_2380_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__7));
v___x_2381_ = l_Lean_Expr_appArg_x21(v___x_2370_);
v___x_2382_ = lean_mk_empty_array_with_capacity(v___x_2365_);
v___x_2383_ = lean_array_push(v___x_2382_, v___x_2381_);
lean_inc(v___x_2379_);
v___x_2384_ = lean_array_push(v___x_2383_, v___x_2379_);
v___x_2385_ = l_Lean_Meta_mkAppM(v___x_2380_, v___x_2384_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2387_ = lean_unsigned_to_nat(4u);
v___x_2388_ = l_Array_extract___redArg(v_x_2348_, v___x_2387_, v___x_2366_);
lean_dec_ref(v_x_2348_);
v___x_2389_ = l_Lean_mkAppN(v_a_2386_, v___x_2388_);
lean_dec_ref(v___x_2388_);
lean_inc(v_goal_2346_);
v___x_2390_ = l_Lean_MVarId_getType(v_goal_2346_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; lean_object* v_dummy_2393_; lean_object* v_nargs_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = l_Lean_Expr_getAppFn(v_a_2391_);
v_dummy_2393_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8);
v_nargs_2394_ = l_Lean_Expr_getAppNumArgs(v_a_2391_);
lean_inc(v_nargs_2394_);
v___x_2395_ = lean_mk_array(v_nargs_2394_, v_dummy_2393_);
v___x_2396_ = lean_unsigned_to_nat(1u);
v___x_2397_ = lean_nat_sub(v_nargs_2394_, v___x_2396_);
lean_dec(v_nargs_2394_);
v___x_2398_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2391_, v___x_2395_, v___x_2397_);
lean_inc_ref(v___x_2389_);
v___x_2399_ = lean_array_set(v___x_2398_, v___x_2375_, v___x_2389_);
v___x_2400_ = l_Lean_mkAppN(v___x_2392_, v___x_2399_);
lean_dec_ref(v___x_2399_);
v___x_2401_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2346_, v___x_2400_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2411_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2411_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2411_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2406_, 0, v_a_2402_);
lean_ctor_set(v___x_2406_, 1, v___x_2389_);
v___x_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2407_);
v___x_2409_ = v___x_2404_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v___x_2389_);
v_a_2412_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2401_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2401_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec_ref(v___x_2389_);
lean_dec(v_goal_2346_);
v_a_2420_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2390_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2390_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec_ref(v_x_2348_);
lean_dec(v_goal_2346_);
v_a_2428_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2385_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2385_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___boxed(lean_object* v_goal_2436_, lean_object* v_x_2437_, lean_object* v_x_2438_, lean_object* v_x_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v_goal_2436_, v_x_2437_, v_x_2438_, v_x_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(lean_object* v_goal_2446_, lean_object* v_rhs_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_dummy_2460_; lean_object* v_nargs_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_dummy_2460_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8);
v_nargs_2461_ = l_Lean_Expr_getAppNumArgs(v_rhs_2447_);
lean_inc(v_nargs_2461_);
v___x_2462_ = lean_mk_array(v_nargs_2461_, v_dummy_2460_);
v___x_2463_ = lean_unsigned_to_nat(1u);
v___x_2464_ = lean_nat_sub(v_nargs_2461_, v___x_2463_);
lean_dec(v_nargs_2461_);
v___x_2465_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v_goal_2446_, v_rhs_2447_, v___x_2462_, v___x_2464_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f___boxed(lean_object* v_goal_2466_, lean_object* v_rhs_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(v_goal_2466_, v_rhs_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0(lean_object* v_goal_2481_, lean_object* v_x_2482_, lean_object* v_x_2483_, lean_object* v_x_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v_goal_2481_, v_x_2482_, v_x_2483_, v_x_2484_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___boxed(lean_object* v_goal_2498_, lean_object* v_x_2499_, lean_object* v_x_2500_, lean_object* v_x_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0(v_goal_2498_, v_x_2499_, v_x_2500_, v_x_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(lean_object* v_a_2515_, lean_object* v_x_2516_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 0)
{
lean_object* v___x_2517_; 
v___x_2517_ = lean_box(0);
return v___x_2517_;
}
else
{
lean_object* v_key_2518_; lean_object* v_value_2519_; lean_object* v_tail_2520_; uint8_t v___x_2521_; 
v_key_2518_ = lean_ctor_get(v_x_2516_, 0);
v_value_2519_ = lean_ctor_get(v_x_2516_, 1);
v_tail_2520_ = lean_ctor_get(v_x_2516_, 2);
v___x_2521_ = lean_name_eq(v_key_2518_, v_a_2515_);
if (v___x_2521_ == 0)
{
v_x_2516_ = v_tail_2520_;
goto _start;
}
else
{
lean_object* v___x_2523_; 
lean_inc(v_value_2519_);
v___x_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2523_, 0, v_value_2519_);
return v___x_2523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_2524_, lean_object* v_x_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_2524_, v_x_2525_);
lean_dec(v_x_2525_);
lean_dec(v_a_2524_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(lean_object* v_m_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v_buckets_2529_; lean_object* v___x_2530_; uint64_t v___y_2532_; 
v_buckets_2529_ = lean_ctor_get(v_m_2527_, 1);
v___x_2530_ = lean_array_get_size(v_buckets_2529_);
if (lean_obj_tag(v_a_2528_) == 0)
{
uint64_t v___x_2546_; 
v___x_2546_ = 1723ULL;
v___y_2532_ = v___x_2546_;
goto v___jp_2531_;
}
else
{
uint64_t v_hash_2547_; 
v_hash_2547_ = lean_ctor_get_uint64(v_a_2528_, sizeof(void*)*2);
v___y_2532_ = v_hash_2547_;
goto v___jp_2531_;
}
v___jp_2531_:
{
uint64_t v___x_2533_; uint64_t v___x_2534_; uint64_t v_fold_2535_; uint64_t v___x_2536_; uint64_t v___x_2537_; uint64_t v___x_2538_; size_t v___x_2539_; size_t v___x_2540_; size_t v___x_2541_; size_t v___x_2542_; size_t v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2533_ = 32ULL;
v___x_2534_ = lean_uint64_shift_right(v___y_2532_, v___x_2533_);
v_fold_2535_ = lean_uint64_xor(v___y_2532_, v___x_2534_);
v___x_2536_ = 16ULL;
v___x_2537_ = lean_uint64_shift_right(v_fold_2535_, v___x_2536_);
v___x_2538_ = lean_uint64_xor(v_fold_2535_, v___x_2537_);
v___x_2539_ = lean_uint64_to_usize(v___x_2538_);
v___x_2540_ = lean_usize_of_nat(v___x_2530_);
v___x_2541_ = ((size_t)1ULL);
v___x_2542_ = lean_usize_sub(v___x_2540_, v___x_2541_);
v___x_2543_ = lean_usize_land(v___x_2539_, v___x_2542_);
v___x_2544_ = lean_array_uget_borrowed(v_buckets_2529_, v___x_2543_);
v___x_2545_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_2528_, v___x_2544_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg___boxed(lean_object* v_m_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v_m_2548_, v_a_2549_);
lean_dec(v_a_2549_);
lean_dec_ref(v_m_2548_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(lean_object* v_goal_2551_, lean_object* v_rhs_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v___x_2565_; 
lean_inc_ref(v_rhs_2552_);
lean_inc(v_goal_2551_);
v___x_2565_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(v_goal_2551_, v_rhs_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2636_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2636_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2636_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_fst_2571_; lean_object* v_snd_2572_; 
if (lean_obj_tag(v_a_2566_) == 0)
{
v_fst_2571_ = v_goal_2551_;
v_snd_2572_ = v_rhs_2552_;
goto v___jp_2570_;
}
else
{
lean_object* v_val_2633_; lean_object* v_fst_2634_; lean_object* v_snd_2635_; 
lean_dec_ref(v_rhs_2552_);
lean_dec(v_goal_2551_);
v_val_2633_ = lean_ctor_get(v_a_2566_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v_a_2566_, 1);
v_fst_2634_ = lean_ctor_get(v_val_2633_, 0);
lean_inc(v_fst_2634_);
v_snd_2635_ = lean_ctor_get(v_val_2633_, 1);
lean_inc(v_snd_2635_);
lean_dec(v_val_2633_);
v_fst_2571_ = v_fst_2634_;
v_snd_2572_ = v_snd_2635_;
goto v___jp_2570_;
}
v___jp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = l_Lean_Expr_getAppFn(v_snd_2572_);
v___x_2574_ = l_Lean_Expr_constName_x3f(v___x_2573_);
lean_dec_ref(v___x_2573_);
if (lean_obj_tag(v___x_2574_) == 1)
{
lean_object* v_val_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_val_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_val_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2576_ = l_Lean_Elab_Tactic_VCGen_latticeOps;
v___x_2577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v___x_2576_, v_val_2575_);
lean_dec(v_val_2575_);
if (lean_obj_tag(v___x_2577_) == 1)
{
lean_object* v_val_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2624_; 
v_val_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2624_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_val_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2624_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v_applies_x3f_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_applies_x3f_2582_ = lean_ctor_get(v_val_2578_, 4);
lean_inc_ref(v_applies_x3f_2582_);
lean_inc_ref(v_snd_2572_);
v___x_2583_ = lean_apply_1(v_applies_x3f_2582_, v_snd_2572_);
v___x_2584_ = lean_unbox(v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_del_object(v___x_2580_);
lean_dec(v_val_2578_);
lean_dec_ref(v_snd_2572_);
lean_dec(v_fst_2571_);
v___x_2585_ = lean_box(0);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2585_);
v___x_2587_ = v___x_2568_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
else
{
lean_object* v___x_2589_; 
lean_del_object(v___x_2568_);
v___x_2589_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_snd_2572_, v_val_2578_, v_a_2554_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = lean_box(0);
v___x_2592_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_2590_, v_fst_2571_, v___x_2591_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2607_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2607_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2607_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
if (lean_obj_tag(v_a_2593_) == 0)
{
lean_object* v___x_2598_; 
lean_del_object(v___x_2580_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2591_);
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2591_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
else
{
lean_object* v_mvarIds_2600_; lean_object* v___x_2602_; 
v_mvarIds_2600_ = lean_ctor_get(v_a_2593_, 0);
lean_inc(v_mvarIds_2600_);
lean_dec_ref_known(v_a_2593_, 1);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v_mvarIds_2600_);
v___x_2602_ = v___x_2580_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_mvarIds_2600_);
v___x_2602_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2604_; 
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2602_);
v___x_2604_ = v___x_2595_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_del_object(v___x_2580_);
v_a_2608_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2592_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2592_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_del_object(v___x_2580_);
lean_dec(v_fst_2571_);
v_a_2616_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2589_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2589_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
lean_dec(v___x_2577_);
lean_dec_ref(v_snd_2572_);
lean_dec(v_fst_2571_);
v___x_2625_ = lean_box(0);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2625_);
v___x_2627_ = v___x_2568_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2631_; 
lean_dec(v___x_2574_);
lean_dec_ref(v_snd_2572_);
lean_dec(v_fst_2571_);
v___x_2629_ = lean_box(0);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2629_);
v___x_2631_ = v___x_2568_;
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
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref(v_rhs_2552_);
lean_dec(v_goal_2551_);
v_a_2637_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2565_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2565_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f___boxed(lean_object* v_goal_2645_, lean_object* v_rhs_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(v_goal_2645_, v_rhs_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec_ref(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0(lean_object* v_00_u03b2_2660_, lean_object* v_m_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v_m_2661_, v_a_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___boxed(lean_object* v_00_u03b2_2664_, lean_object* v_m_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0(v_00_u03b2_2664_, v_m_2665_, v_a_2666_);
lean_dec(v_a_2666_);
lean_dec_ref(v_m_2665_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2668_, lean_object* v_a_2669_, lean_object* v_x_2670_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_2669_, v_x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2672_, lean_object* v_a_2673_, lean_object* v_x_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0(v_00_u03b2_2672_, v_a_2673_, v_x_2674_);
lean_dec(v_x_2674_);
lean_dec(v_a_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(lean_object* v_goal_2676_, lean_object* v_rhs_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
uint8_t v___x_2690_; 
v___x_2690_ = l_Lean_Expr_isForall(v_rhs_2677_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec(v_goal_2676_);
v___x_2691_ = lean_box(0);
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
return v___x_2692_;
}
else
{
lean_object* v_backwardRules_2693_; lean_object* v_forallIntro_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_backwardRules_2693_ = lean_ctor_get(v_a_2678_, 0);
v_forallIntro_2694_ = lean_ctor_get(v_backwardRules_2693_, 11);
v___x_2695_ = lean_box(0);
lean_inc_ref(v_forallIntro_2694_);
v___x_2696_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_forallIntro_2694_, v_goal_2676_, v___x_2695_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2715_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2715_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2715_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
if (lean_obj_tag(v_a_2697_) == 0)
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2695_);
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2695_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
else
{
lean_object* v_mvarIds_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2714_; 
v_mvarIds_2704_ = lean_ctor_get(v_a_2697_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_a_2697_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2706_ = v_a_2697_;
v_isShared_2707_ = v_isSharedCheck_2714_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_mvarIds_2704_);
lean_dec(v_a_2697_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2714_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_mvarIds_2704_);
v___x_2709_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2711_; 
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2709_);
v___x_2711_ = v___x_2699_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
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
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
v_a_2716_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2696_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2696_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f___boxed(lean_object* v_goal_2724_, lean_object* v_rhs_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(v_goal_2724_, v_rhs_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
lean_dec(v_a_2728_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
lean_dec_ref(v_rhs_2725_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(lean_object* v_as_2761_, size_t v_sz_2762_, size_t v_i_2763_, lean_object* v_b_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
uint8_t v___x_2772_; 
v___x_2772_ = lean_usize_dec_lt(v_i_2763_, v_sz_2762_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2773_, 0, v_b_2764_);
return v___x_2773_;
}
else
{
lean_object* v_snd_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_3018_; 
v_snd_2774_ = lean_ctor_get(v_b_2764_, 1);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_b_2764_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; 
v_unused_3019_ = lean_ctor_get(v_b_2764_, 0);
lean_dec(v_unused_3019_);
v___x_2776_ = v_b_2764_;
v_isShared_2777_ = v_isSharedCheck_3018_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_snd_2774_);
lean_dec(v_b_2764_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_3018_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v_snd_2778_; lean_object* v_snd_2779_; lean_object* v_snd_2780_; lean_object* v_fst_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_3016_; 
v_snd_2778_ = lean_ctor_get(v_snd_2774_, 1);
lean_inc(v_snd_2778_);
v_snd_2779_ = lean_ctor_get(v_snd_2778_, 1);
lean_inc(v_snd_2779_);
v_snd_2780_ = lean_ctor_get(v_snd_2779_, 1);
lean_inc(v_snd_2780_);
v_fst_2781_ = lean_ctor_get(v_snd_2774_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v_snd_2774_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v_snd_2774_, 1);
lean_dec(v_unused_3017_);
v___x_2783_ = v_snd_2774_;
v_isShared_2784_ = v_isSharedCheck_3016_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_fst_2781_);
lean_dec(v_snd_2774_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_3016_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v_fst_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_3014_; 
v_fst_2785_ = lean_ctor_get(v_snd_2778_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_snd_2778_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; 
v_unused_3015_ = lean_ctor_get(v_snd_2778_, 1);
lean_dec(v_unused_3015_);
v___x_2787_ = v_snd_2778_;
v_isShared_2788_ = v_isSharedCheck_3014_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_fst_2785_);
lean_dec(v_snd_2778_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_3014_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v_fst_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_3012_; 
v_fst_2789_ = lean_ctor_get(v_snd_2779_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_snd_2779_);
if (v_isSharedCheck_3012_ == 0)
{
lean_object* v_unused_3013_; 
v_unused_3013_ = lean_ctor_get(v_snd_2779_, 1);
lean_dec(v_unused_3013_);
v___x_2791_ = v_snd_2779_;
v_isShared_2792_ = v_isSharedCheck_3012_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_fst_2789_);
lean_dec(v_snd_2779_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_3012_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v_fst_2793_; lean_object* v_snd_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_3011_; 
v_fst_2793_ = lean_ctor_get(v_snd_2780_, 0);
v_snd_2794_ = lean_ctor_get(v_snd_2780_, 1);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_snd_2780_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_2796_ = v_snd_2780_;
v_isShared_2797_ = v_isSharedCheck_3011_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_snd_2794_);
lean_inc(v_fst_2793_);
lean_dec(v_snd_2780_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_3011_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v_a_2800_; lean_object* v___x_2801_; 
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_box(0);
v_a_2800_ = lean_array_uget_borrowed(v_as_2761_, v_i_2763_);
lean_inc(v_fst_2793_);
v___x_2801_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_fst_2793_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_3002_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_3002_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_3002_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
if (lean_obj_tag(v_a_2802_) == 7)
{
lean_object* v_binderType_2806_; lean_object* v_body_2807_; uint8_t v___x_2808_; 
v_binderType_2806_ = lean_ctor_get(v_a_2802_, 1);
lean_inc_ref(v_binderType_2806_);
v_body_2807_ = lean_ctor_get(v_a_2802_, 2);
lean_inc_ref(v_body_2807_);
lean_dec_ref_known(v_a_2802_, 3);
v___x_2808_ = l_Lean_Expr_hasLooseBVars(v_body_2807_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___x_2809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1));
v___x_2810_ = l_Lean_Expr_isAppOf(v_snd_2794_, v___x_2809_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2813_; 
lean_dec_ref(v_body_2807_);
lean_dec_ref(v_binderType_2806_);
v___x_2811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2797_ == 0)
{
v___x_2813_ = v___x_2796_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_fst_2793_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_snd_2794_);
v___x_2813_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2815_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 1, v___x_2813_);
v___x_2815_ = v___x_2791_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_fst_2789_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2817_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 1, v___x_2815_);
v___x_2817_ = v___x_2787_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_fst_2785_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2819_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v___x_2817_);
v___x_2819_ = v___x_2783_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_fst_2781_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v___x_2817_);
v___x_2819_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2821_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v___x_2819_);
lean_ctor_set(v___x_2776_, 0, v___x_2811_);
v___x_2821_ = v___x_2776_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2821_);
v___x_2823_ = v___x_2804_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
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
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_Expr_appArg_x21(v_snd_2794_);
if (lean_obj_tag(v___x_2830_) == 6)
{
lean_object* v_body_2831_; lean_object* v___x_2832_; 
lean_del_object(v___x_2804_);
v_body_2831_ = lean_ctor_get(v___x_2830_, 2);
lean_inc_ref(v_body_2831_);
lean_dec_ref_known(v___x_2830_, 3);
lean_inc_ref(v_binderType_2806_);
v___x_2832_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2806_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2834_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2832_, 1);
lean_inc_ref(v_body_2807_);
v___x_2834_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2807_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
lean_inc(v_a_2833_);
v___x_2836_ = l_Lean_Meta_decLevel(v_a_2833_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2838_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
lean_inc(v_a_2835_);
v___x_2838_ = l_Lean_Meta_decLevel(v_a_2835_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4));
v___x_2841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2841_, 0, v_a_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2798_);
v___x_2842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2842_, 0, v_a_2837_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = l_Lean_mkConst(v___x_2840_, v___x_2842_);
lean_inc(v_a_2800_);
lean_inc_ref(v_body_2831_);
lean_inc_ref(v_body_2807_);
lean_inc_ref(v_binderType_2806_);
v___x_2844_ = l_Lean_mkApp4(v___x_2843_, v_binderType_2806_, v_body_2807_, v_body_2831_, v_a_2800_);
lean_inc_ref(v___x_2844_);
v___x_2845_ = l_Lean_Meta_Sym_inferType(v___x_2844_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2904_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2904_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2904_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2850_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1));
v___x_2851_ = lean_unsigned_to_nat(3u);
v___x_2852_ = l_Lean_Expr_isAppOfArity(v_a_2846_, v___x_2850_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; lean_object* v___x_2855_; 
lean_dec(v_a_2846_);
lean_dec_ref(v___x_2844_);
lean_dec(v_a_2835_);
lean_dec(v_a_2833_);
lean_dec_ref(v_body_2831_);
lean_dec_ref(v_body_2807_);
lean_dec_ref(v_binderType_2806_);
v___x_2853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2797_ == 0)
{
v___x_2855_ = v___x_2796_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_fst_2793_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_snd_2794_);
v___x_2855_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2857_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 1, v___x_2855_);
v___x_2857_ = v___x_2791_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_fst_2789_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2859_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 1, v___x_2857_);
v___x_2859_ = v___x_2787_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_fst_2785_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2861_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v___x_2859_);
v___x_2861_ = v___x_2783_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_fst_2781_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2863_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v___x_2861_);
lean_ctor_set(v___x_2776_, 0, v___x_2853_);
v___x_2863_ = v___x_2776_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2865_; 
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2863_);
v___x_2865_ = v___x_2848_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
lean_del_object(v___x_2848_);
lean_dec(v_snd_2794_);
lean_dec(v_fst_2793_);
v___x_2872_ = l_Lean_Expr_appArg_x21(v_a_2846_);
lean_dec(v_a_2846_);
v___x_2873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6));
v___x_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2874_, 0, v_a_2835_);
lean_ctor_set(v___x_2874_, 1, v___x_2798_);
lean_inc_ref(v___x_2874_);
v___x_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2875_, 0, v_a_2833_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = l_Lean_mkConst(v___x_2873_, v___x_2875_);
v___x_2877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8));
v___x_2878_ = 0;
lean_inc_ref_n(v_body_2807_, 2);
lean_inc_ref(v_binderType_2806_);
v___x_2879_ = l_Lean_Expr_lam___override(v___x_2877_, v_binderType_2806_, v_body_2807_, v___x_2878_);
lean_inc_n(v_a_2800_, 3);
lean_inc(v_fst_2789_);
lean_inc(v_fst_2785_);
v___x_2880_ = l_Lean_mkApp6(v___x_2876_, v_binderType_2806_, v___x_2879_, v_fst_2785_, v_fst_2789_, v_fst_2781_, v_a_2800_);
v___x_2881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10));
v___x_2882_ = l_Lean_mkConst(v___x_2881_, v___x_2874_);
v___x_2883_ = l_Lean_Expr_app___override(v_fst_2785_, v_a_2800_);
v___x_2884_ = l_Lean_Expr_app___override(v_fst_2789_, v_a_2800_);
lean_inc_ref(v___x_2872_);
lean_inc_ref(v___x_2883_);
v___x_2885_ = l_Lean_mkApp6(v___x_2882_, v_body_2807_, v___x_2883_, v___x_2884_, v___x_2872_, v___x_2880_, v___x_2844_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v_body_2831_);
lean_ctor_set(v___x_2796_, 0, v_body_2807_);
v___x_2887_ = v___x_2796_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_body_2807_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_body_2831_);
v___x_2887_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2889_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 1, v___x_2887_);
lean_ctor_set(v___x_2791_, 0, v___x_2872_);
v___x_2889_ = v___x_2791_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2891_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 1, v___x_2889_);
lean_ctor_set(v___x_2787_, 0, v___x_2883_);
v___x_2891_ = v___x_2787_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2893_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v___x_2891_);
lean_ctor_set(v___x_2783_, 0, v___x_2885_);
v___x_2893_ = v___x_2783_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v___x_2891_);
v___x_2893_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2895_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v___x_2893_);
lean_ctor_set(v___x_2776_, 0, v___x_2799_);
v___x_2895_ = v___x_2776_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
size_t v___x_2896_; size_t v___x_2897_; 
v___x_2896_ = ((size_t)1ULL);
v___x_2897_ = lean_usize_add(v_i_2763_, v___x_2896_);
v_i_2763_ = v___x_2897_;
v_b_2764_ = v___x_2895_;
goto _start;
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
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec_ref(v___x_2844_);
lean_dec(v_a_2835_);
lean_dec(v_a_2833_);
lean_dec_ref(v_body_2831_);
lean_dec_ref(v_body_2807_);
lean_dec_ref(v_binderType_2806_);
lean_del_object(v___x_2796_);
lean_dec(v_snd_2794_);
lean_dec(v_fst_2793_);
lean_del_object(v___x_2791_);
lean_dec(v_fst_2789_);
lean_del_object(v___x_2787_);
lean_dec(v_fst_2785_);
lean_del_object(v___x_2783_);
lean_dec(v_fst_2781_);
lean_del_object(v___x_2776_);
v_a_2905_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2845_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2845_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_a_2837_);
lean_dec(v_a_2835_);
lean_dec(v_a_2833_);
lean_dec_ref(v_body_2831_);
lean_dec_ref(v_body_2807_);
lean_dec_ref(v_binderType_2806_);
lean_del_object(v___x_2796_);
lean_dec(v_snd_2794_);
lean_dec(v_fst_2793_);
lean_del_object(v___x_2791_);
lean_dec(v_fst_2789_);
lean_del_object(v___x_2787_);
lean_dec(v_fst_2785_);
lean_del_object(v___x_2783_);
lean_dec(v_fst_2781_);
lean_del_object(v___x_2776_);
v_a_2913_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2838_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2838_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v_a_2835_);
lean_dec(v_a_2833_);
lean_dec_ref(v_body_2831_);
lean_dec_ref(v_body_2807_);
lean_dec_ref(v_binderType_2806_);
lean_del_object(v___x_2796_);
lean_dec(v_snd_2794_);
lean_dec(v_fst_2793_);
lean_del_object(v___x_2791_);
lean_dec(v_fst_2789_);
lean_del_object(v___x_2787_);
lean_dec(v_fst_2785_);
lean_del_object(v___x_2783_);
lean_dec(v_fst_2781_);
lean_del_object(v___x_2776_);
v_a_2921_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2836_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2836_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v_a_2833_);
lean_dec_ref(v_body_2831_);
lean_dec_ref(v_body_2807_);
lean_dec_ref(v_binderType_2806_);
lean_del_object(v___x_2796_);
lean_dec(v_snd_2794_);
lean_dec(v_fst_2793_);
lean_del_object(v___x_2791_);
lean_dec(v_fst_2789_);
lean_del_object(v___x_2787_);
lean_dec(v_fst_2785_);
lean_del_object(v___x_2783_);
lean_dec(v_fst_2781_);
lean_del_object(v___x_2776_);
v_a_2929_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2834_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2834_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref(v_body_2831_);
lean_dec_ref(v_body_2807_);
lean_dec_ref(v_binderType_2806_);
lean_del_object(v___x_2796_);
lean_dec(v_snd_2794_);
lean_dec(v_fst_2793_);
lean_del_object(v___x_2791_);
lean_dec(v_fst_2789_);
lean_del_object(v___x_2787_);
lean_dec(v_fst_2785_);
lean_del_object(v___x_2783_);
lean_dec(v_fst_2781_);
lean_del_object(v___x_2776_);
v_a_2937_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2832_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2832_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
lean_dec_ref(v___x_2830_);
lean_dec_ref(v_body_2807_);
lean_dec_ref(v_binderType_2806_);
v___x_2945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2797_ == 0)
{
v___x_2947_ = v___x_2796_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_fst_2793_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_snd_2794_);
v___x_2947_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2949_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 1, v___x_2947_);
v___x_2949_ = v___x_2791_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_fst_2789_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2951_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 1, v___x_2949_);
v___x_2951_ = v___x_2787_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_fst_2785_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2953_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v___x_2951_);
v___x_2953_ = v___x_2783_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_fst_2781_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2955_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v___x_2953_);
lean_ctor_set(v___x_2776_, 0, v___x_2945_);
v___x_2955_ = v___x_2776_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2957_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2955_);
v___x_2957_ = v___x_2804_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
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
lean_object* v___x_2964_; lean_object* v___x_2966_; 
lean_dec_ref(v_body_2807_);
lean_dec_ref(v_binderType_2806_);
v___x_2964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2797_ == 0)
{
v___x_2966_ = v___x_2796_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_fst_2793_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_snd_2794_);
v___x_2966_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2968_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 1, v___x_2966_);
v___x_2968_ = v___x_2791_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_fst_2789_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2970_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 1, v___x_2968_);
v___x_2970_ = v___x_2787_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_fst_2785_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2972_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v___x_2970_);
v___x_2972_ = v___x_2783_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_fst_2781_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2974_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v___x_2972_);
lean_ctor_set(v___x_2776_, 0, v___x_2964_);
v___x_2974_ = v___x_2776_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2976_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2974_);
v___x_2976_ = v___x_2804_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
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
lean_object* v___x_2983_; lean_object* v___x_2985_; 
lean_dec(v_a_2802_);
v___x_2983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2797_ == 0)
{
v___x_2985_ = v___x_2796_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_fst_2793_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_snd_2794_);
v___x_2985_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2987_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 1, v___x_2985_);
v___x_2987_ = v___x_2791_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_fst_2789_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2989_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 1, v___x_2987_);
v___x_2989_ = v___x_2787_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_fst_2785_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2991_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v___x_2989_);
v___x_2991_ = v___x_2783_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_fst_2781_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2993_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v___x_2991_);
lean_ctor_set(v___x_2776_, 0, v___x_2983_);
v___x_2993_ = v___x_2776_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2995_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2993_);
v___x_2995_ = v___x_2804_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2993_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
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
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_del_object(v___x_2796_);
lean_dec(v_snd_2794_);
lean_dec(v_fst_2793_);
lean_del_object(v___x_2791_);
lean_dec(v_fst_2789_);
lean_del_object(v___x_2787_);
lean_dec(v_fst_2785_);
lean_del_object(v___x_2783_);
lean_dec(v_fst_2781_);
lean_del_object(v___x_2776_);
v_a_3003_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2801_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2801_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___boxed(lean_object* v_as_3020_, lean_object* v_sz_3021_, lean_object* v_i_3022_, lean_object* v_b_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
size_t v_sz_boxed_3031_; size_t v_i_boxed_3032_; lean_object* v_res_3033_; 
v_sz_boxed_3031_ = lean_unbox_usize(v_sz_3021_);
lean_dec(v_sz_3021_);
v_i_boxed_3032_ = lean_unbox_usize(v_i_3022_);
lean_dec(v_i_3022_);
v_res_3033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(v_as_3020_, v_sz_boxed_3031_, v_i_boxed_3032_, v_b_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec_ref(v_as_3020_);
return v_res_3033_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_unsigned_to_nat(0u);
v___x_3047_ = l_Lean_Expr_bvar___override(v___x_3046_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9(void){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = lean_box(0);
v___x_3052_ = l_Lean_Level_succ___override(v___x_3051_);
return v___x_3052_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = lean_box(0);
v___x_3054_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9);
v___x_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___x_3053_);
return v___x_3055_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_box(0);
v___x_3057_ = l_Lean_mkSort(v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(lean_object* v_goal_3058_, lean_object* v_target_3059_, lean_object* v_pre_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v___x_3071_; uint8_t v___x_3072_; 
v___x_3071_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1));
v___x_3072_ = l_Lean_Expr_isAppOf(v_pre_3060_, v___x_3071_);
if (v___x_3072_ == 0)
{
lean_dec_ref(v_pre_3060_);
lean_dec_ref(v_target_3059_);
lean_dec(v_goal_3058_);
goto v___jp_3068_;
}
else
{
lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_3073_ = lean_unsigned_to_nat(2u);
v___x_3074_ = l_Lean_Expr_getAppNumArgs(v_pre_3060_);
v___x_3075_ = lean_nat_dec_lt(v___x_3073_, v___x_3074_);
if (v___x_3075_ == 0)
{
lean_dec(v___x_3074_);
lean_dec_ref(v_pre_3060_);
lean_dec_ref(v_target_3059_);
lean_dec(v_goal_3058_);
goto v___jp_3068_;
}
else
{
lean_object* v_dummy_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v_args_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
v_dummy_3076_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8);
lean_inc(v___x_3074_);
v___x_3077_ = lean_mk_array(v___x_3074_, v_dummy_3076_);
v___x_3078_ = lean_unsigned_to_nat(1u);
v___x_3079_ = lean_nat_sub(v___x_3074_, v___x_3078_);
lean_dec(v___x_3074_);
lean_inc_ref(v_pre_3060_);
v_args_3080_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_pre_3060_, v___x_3077_, v___x_3079_);
v___x_3081_ = lean_unsigned_to_nat(0u);
v___x_3082_ = lean_array_get_size(v_args_3080_);
v___x_3083_ = lean_nat_dec_lt(v___x_3081_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
lean_dec_ref(v_args_3080_);
lean_dec_ref(v_pre_3060_);
lean_dec_ref(v_target_3059_);
lean_dec(v_goal_3058_);
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
else
{
uint8_t v___x_3086_; 
v___x_3086_ = lean_nat_dec_lt(v___x_3078_, v___x_3082_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
lean_dec_ref(v_args_3080_);
lean_dec_ref(v_pre_3060_);
lean_dec_ref(v_target_3059_);
lean_dec(v_goal_3058_);
v___x_3087_ = lean_box(0);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
return v___x_3088_;
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v_curTop_3092_; lean_object* v___x_3093_; 
v___x_3089_ = lean_array_fget(v_args_3080_, v___x_3081_);
v___x_3090_ = lean_array_fget(v_args_3080_, v___x_3078_);
v___x_3091_ = l_Lean_Expr_getAppFn(v_pre_3060_);
lean_inc(v___x_3090_);
lean_inc_n(v___x_3089_, 2);
v_curTop_3092_ = l_Lean_mkAppB(v___x_3091_, v___x_3089_, v___x_3090_);
v___x_3093_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_3089_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; size_t v_sz_3107_; size_t v___x_3108_; lean_object* v___x_3109_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
v___x_3095_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3));
v___x_3096_ = lean_box(0);
v___x_3097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3097_, 0, v_a_3094_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = l_Lean_mkConst(v___x_3095_, v___x_3097_);
lean_inc_ref_n(v_curTop_3092_, 2);
lean_inc(v___x_3089_);
v___x_3099_ = l_Lean_mkAppB(v___x_3098_, v___x_3089_, v_curTop_3092_);
v___x_3100_ = l_Array_extract___redArg(v_args_3080_, v___x_3073_, v___x_3082_);
lean_dec_ref(v_args_3080_);
v___x_3101_ = lean_box(0);
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3089_);
lean_ctor_set(v___x_3102_, 1, v___x_3090_);
v___x_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3103_, 0, v_curTop_3092_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3104_, 0, v_curTop_3092_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3099_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3101_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v_sz_3107_ = lean_array_size(v___x_3100_);
v___x_3108_ = ((size_t)0ULL);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(v___x_3100_, v_sz_3107_, v___x_3108_, v___x_3106_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
lean_dec_ref(v___x_3100_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3193_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3193_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3193_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v_fst_3114_; 
v_fst_3114_ = lean_ctor_get(v_a_3110_, 0);
if (lean_obj_tag(v_fst_3114_) == 0)
{
lean_object* v_snd_3115_; lean_object* v_nargs_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v_snd_3115_ = lean_ctor_get(v_a_3110_, 1);
lean_inc(v_snd_3115_);
lean_dec(v_a_3110_);
v_nargs_3116_ = l_Lean_Expr_getAppNumArgs(v_target_3059_);
lean_inc(v_nargs_3116_);
v___x_3117_ = lean_mk_array(v_nargs_3116_, v_dummy_3076_);
v___x_3118_ = lean_nat_sub(v_nargs_3116_, v___x_3078_);
lean_dec(v_nargs_3116_);
lean_inc_ref(v_target_3059_);
v___x_3119_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_target_3059_, v___x_3117_, v___x_3118_);
v___x_3120_ = lean_array_get_size(v___x_3119_);
v___x_3121_ = lean_nat_dec_lt(v___x_3081_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3123_; 
lean_dec_ref(v___x_3119_);
lean_dec(v_snd_3115_);
lean_dec_ref(v_pre_3060_);
lean_dec_ref(v_target_3059_);
lean_dec(v_goal_3058_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3101_);
v___x_3123_ = v___x_3112_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3101_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
else
{
uint8_t v___x_3125_; 
v___x_3125_ = lean_nat_dec_lt(v___x_3078_, v___x_3120_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3127_; 
lean_dec_ref(v___x_3119_);
lean_dec(v_snd_3115_);
lean_dec_ref(v_pre_3060_);
lean_dec_ref(v_target_3059_);
lean_dec(v_goal_3058_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3101_);
v___x_3127_ = v___x_3112_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3101_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
else
{
lean_object* v___x_3129_; uint8_t v___x_3130_; 
v___x_3129_ = lean_unsigned_to_nat(3u);
v___x_3130_ = lean_nat_dec_lt(v___x_3129_, v___x_3120_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3132_; 
lean_dec_ref(v___x_3119_);
lean_dec(v_snd_3115_);
lean_dec_ref(v_pre_3060_);
lean_dec_ref(v_target_3059_);
lean_dec(v_goal_3058_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3101_);
v___x_3132_ = v___x_3112_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3101_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
else
{
lean_object* v_snd_3134_; lean_object* v_snd_3135_; lean_object* v_fst_3136_; lean_object* v_fst_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3187_; 
lean_del_object(v___x_3112_);
v_snd_3134_ = lean_ctor_get(v_snd_3115_, 1);
v_snd_3135_ = lean_ctor_get(v_snd_3134_, 1);
lean_inc(v_snd_3135_);
v_fst_3136_ = lean_ctor_get(v_snd_3115_, 0);
lean_inc(v_fst_3136_);
lean_dec(v_snd_3115_);
v_fst_3137_ = lean_ctor_get(v_snd_3135_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v_snd_3135_);
if (v_isSharedCheck_3187_ == 0)
{
lean_object* v_unused_3188_; 
v_unused_3188_ = lean_ctor_get(v_snd_3135_, 1);
lean_dec(v_unused_3188_);
v___x_3139_ = v_snd_3135_;
v_isShared_3140_ = v_isSharedCheck_3187_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_fst_3137_);
lean_dec(v_snd_3135_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3187_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3141_ = lean_array_fget(v___x_3119_, v___x_3081_);
v___x_3142_ = lean_array_fget(v___x_3119_, v___x_3078_);
v___x_3143_ = lean_array_fget(v___x_3119_, v___x_3129_);
lean_dec_ref(v___x_3119_);
lean_inc(v___x_3141_);
v___x_3144_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_3141_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3146_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__5));
v___x_3147_ = l_Lean_Expr_getAppFn(v_target_3059_);
lean_dec_ref(v_target_3059_);
v___x_3148_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6);
lean_inc(v___x_3143_);
lean_inc(v___x_3142_);
lean_inc_n(v___x_3141_, 2);
lean_inc_ref(v___x_3147_);
v___x_3149_ = l_Lean_mkApp4(v___x_3147_, v___x_3141_, v___x_3142_, v___x_3148_, v___x_3143_);
v___x_3150_ = 0;
v___x_3151_ = l_Lean_Expr_lam___override(v___x_3146_, v___x_3141_, v___x_3149_, v___x_3150_);
v___x_3152_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8));
v___x_3153_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10);
if (v_isShared_3140_ == 0)
{
lean_ctor_set_tag(v___x_3139_, 1);
lean_ctor_set(v___x_3139_, 1, v___x_3153_);
lean_ctor_set(v___x_3139_, 0, v_a_3145_);
v___x_3155_ = v___x_3139_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3145_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3156_ = l_Lean_mkConst(v___x_3152_, v___x_3155_);
v___x_3157_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11);
lean_inc(v_fst_3137_);
lean_inc(v___x_3141_);
v___x_3158_ = l_Lean_mkApp6(v___x_3156_, v___x_3141_, v___x_3157_, v_pre_3060_, v_fst_3137_, v___x_3151_, v_fst_3136_);
v___x_3159_ = l_Lean_mkApp4(v___x_3147_, v___x_3141_, v___x_3142_, v_fst_3137_, v___x_3143_);
v___x_3160_ = l_Lean_MVarId_replaceTargetEq(v_goal_3058_, v___x_3159_, v___x_3158_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3169_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3169_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3169_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3165_, 0, v_a_3161_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3167_ = v___x_3163_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
v_a_3170_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3160_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3160_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v___x_3143_);
lean_dec(v___x_3142_);
lean_dec(v___x_3141_);
lean_del_object(v___x_3139_);
lean_dec(v_fst_3137_);
lean_dec(v_fst_3136_);
lean_dec_ref(v_pre_3060_);
lean_dec_ref(v_target_3059_);
lean_dec(v_goal_3058_);
v_a_3179_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3144_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3144_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
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
lean_object* v_val_3189_; lean_object* v___x_3191_; 
lean_inc_ref(v_fst_3114_);
lean_dec(v_a_3110_);
lean_dec_ref(v_pre_3060_);
lean_dec_ref(v_target_3059_);
lean_dec(v_goal_3058_);
v_val_3189_ = lean_ctor_get(v_fst_3114_, 0);
lean_inc(v_val_3189_);
lean_dec_ref_known(v_fst_3114_, 1);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v_val_3189_);
v___x_3191_ = v___x_3112_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_val_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref(v_pre_3060_);
lean_dec_ref(v_target_3059_);
lean_dec(v_goal_3058_);
v_a_3194_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3109_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3109_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v_curTop_3092_);
lean_dec(v___x_3090_);
lean_dec(v___x_3089_);
lean_dec_ref(v_args_3080_);
lean_dec_ref(v_pre_3060_);
lean_dec_ref(v_target_3059_);
lean_dec(v_goal_3058_);
v_a_3202_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3093_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3093_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
}
}
v___jp_3068_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_box(0);
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
return v___x_3070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___boxed(lean_object* v_goal_3210_, lean_object* v_target_3211_, lean_object* v_pre_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(v_goal_3210_, v_target_3211_, v_pre_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
return v_res_3220_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__0));
v___x_3223_ = l_Lean_stringToMessageData(v___x_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(lean_object* v_goal_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___x_3249_; 
lean_inc(v_goal_3231_);
v___x_3249_ = l_Lean_MVarId_getType(v_goal_3231_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3313_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3313_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3313_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___x_3254_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4));
v___x_3255_ = lean_unsigned_to_nat(4u);
v___x_3256_ = l_Lean_Expr_isAppOfArity(v_a_3250_, v___x_3254_, v___x_3255_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3258_; 
lean_dec(v_a_3250_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v_goal_3231_);
v___x_3258_ = v___x_3252_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_goal_3231_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
else
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3260_ = l_Lean_Expr_appFn_x21(v_a_3250_);
lean_dec(v_a_3250_);
v___x_3261_ = l_Lean_Expr_appFn_x21(v___x_3260_);
v___x_3262_ = l_Lean_Expr_appFn_x21(v___x_3261_);
lean_dec_ref(v___x_3261_);
v___x_3263_ = l_Lean_Expr_appArg_x21(v___x_3262_);
lean_dec_ref(v___x_3262_);
if (lean_obj_tag(v___x_3263_) == 3)
{
lean_object* v_u_3264_; 
v_u_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_u_3264_);
lean_dec_ref_known(v___x_3263_, 1);
if (lean_obj_tag(v_u_3264_) == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_del_object(v___x_3252_);
v___x_3265_ = l_Lean_Expr_appArg_x21(v___x_3260_);
lean_dec_ref(v___x_3260_);
v___x_3266_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v___x_3265_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3298_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3298_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3298_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; uint8_t v___x_3272_; 
v___x_3271_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1));
v___x_3272_ = l_Lean_Expr_isAppOf(v_a_3267_, v___x_3271_);
lean_dec(v_a_3267_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3274_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v_goal_3231_);
v___x_3274_ = v___x_3269_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_goal_3231_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
else
{
lean_object* v_backwardRules_3276_; lean_object* v_elimPre_3277_; lean_object* v___x_3278_; 
lean_del_object(v___x_3269_);
v_backwardRules_3276_ = lean_ctor_get(v_a_3232_, 0);
v_elimPre_3277_ = lean_ctor_get(v_backwardRules_3276_, 7);
lean_inc_ref(v_elimPre_3277_);
lean_inc(v_goal_3231_);
v___x_3278_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_3231_, v_elimPre_3277_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3289_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3281_ = v___x_3278_;
v_isShared_3282_ = v_isSharedCheck_3289_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3278_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3289_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
if (lean_obj_tag(v_a_3279_) == 1)
{
lean_object* v_mvarIds_3283_; 
v_mvarIds_3283_ = lean_ctor_get(v_a_3279_, 0);
lean_inc(v_mvarIds_3283_);
lean_dec_ref_known(v_a_3279_, 1);
if (lean_obj_tag(v_mvarIds_3283_) == 1)
{
lean_object* v_tail_3284_; 
v_tail_3284_ = lean_ctor_get(v_mvarIds_3283_, 1);
if (lean_obj_tag(v_tail_3284_) == 0)
{
lean_object* v_head_3285_; lean_object* v___x_3287_; 
lean_dec(v_goal_3231_);
v_head_3285_ = lean_ctor_get(v_mvarIds_3283_, 0);
lean_inc(v_head_3285_);
lean_dec_ref_known(v_mvarIds_3283_, 2);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 0, v_head_3285_);
v___x_3287_ = v___x_3281_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_head_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
else
{
lean_dec_ref_known(v_mvarIds_3283_, 2);
lean_del_object(v___x_3281_);
v___y_3241_ = v_a_3235_;
v___y_3242_ = v_a_3236_;
v___y_3243_ = v_a_3237_;
v___y_3244_ = v_a_3238_;
goto v___jp_3240_;
}
}
else
{
lean_dec(v_mvarIds_3283_);
lean_del_object(v___x_3281_);
v___y_3241_ = v_a_3235_;
v___y_3242_ = v_a_3236_;
v___y_3243_ = v_a_3237_;
v___y_3244_ = v_a_3238_;
goto v___jp_3240_;
}
}
else
{
lean_del_object(v___x_3281_);
lean_dec(v_a_3279_);
v___y_3241_ = v_a_3235_;
v___y_3242_ = v_a_3236_;
v___y_3243_ = v_a_3237_;
v___y_3244_ = v_a_3238_;
goto v___jp_3240_;
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec(v_goal_3231_);
v_a_3290_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3278_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3278_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec(v_goal_3231_);
v_a_3299_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3266_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3266_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
else
{
lean_object* v___x_3308_; 
lean_dec(v_u_3264_);
lean_dec_ref(v___x_3260_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v_goal_3231_);
v___x_3308_ = v___x_3252_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_goal_3231_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
else
{
lean_object* v___x_3311_; 
lean_dec_ref(v___x_3263_);
lean_dec_ref(v___x_3260_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v_goal_3231_);
v___x_3311_ = v___x_3252_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_goal_3231_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec(v_goal_3231_);
v_a_3314_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3249_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3249_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
v___jp_3240_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3245_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1, &l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1);
v___x_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_goal_3231_);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_3247_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
return v___x_3248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___boxed(lean_object* v_goal_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_goal_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec_ref(v_a_3326_);
lean_dec(v_a_3325_);
lean_dec_ref(v_a_3324_);
lean_dec_ref(v_a_3323_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre(lean_object* v_goal_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_goal_3332_, v_a_3333_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___boxed(lean_object* v_goal_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lean_Elab_Tactic_VCGen_elimTopPre(v_goal_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec(v_a_3355_);
lean_dec_ref(v_a_3354_);
lean_dec(v_a_3353_);
lean_dec_ref(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3350_);
lean_dec(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
return v_res_3359_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_RuleCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Std_WP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Init_Sym_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_MaxFVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Sym_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_RuleCache(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Std_WP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_MaxFVar(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Init_Sym_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_Entails(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_MaxFVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_Entails(builtin);
}
#ifdef __cplusplus
}
#endif
