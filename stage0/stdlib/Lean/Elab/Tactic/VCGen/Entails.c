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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_introsHygienicN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_lastDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1_value;
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(14, 81, 9, 215, 230, 198, 87, 3)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "and_imp"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(97, 187, 54, 56, 129, 238, 180, 43)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(170, 44, 236, 58, 247, 164, 254, 114)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(lean_object* v___x_149_, lean_object* v___x_150_, lean_object* v_fvarId_151_, lean_object* v_as_152_, size_t v_i_153_, size_t v_stop_154_, lean_object* v_b_155_){
_start:
{
lean_object* v___y_157_; uint8_t v___x_161_; 
v___x_161_ = lean_usize_dec_eq(v_i_153_, v_stop_154_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
v___x_162_ = lean_array_uget_borrowed(v_as_152_, v_i_153_);
if (lean_obj_tag(v___x_162_) == 0)
{
v___y_157_ = v_b_155_;
goto v___jp_156_;
}
else
{
lean_object* v_val_163_; lean_object* v_fst_164_; lean_object* v_snd_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_191_; 
v_val_163_ = lean_ctor_get(v___x_162_, 0);
v_fst_164_ = lean_ctor_get(v_b_155_, 0);
v_snd_165_ = lean_ctor_get(v_b_155_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_b_155_);
if (v_isSharedCheck_191_ == 0)
{
v___x_167_ = v_b_155_;
v_isShared_168_ = v_isSharedCheck_191_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_snd_165_);
lean_inc(v_fst_164_);
lean_dec(v_b_155_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_191_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
uint8_t v___x_169_; lean_object* v___y_171_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_169_ = lean_nat_dec_lt(v___x_149_, v___x_150_);
v___x_187_ = l_Lean_LocalDecl_type(v_val_163_);
v___x_188_ = l_Lean_Expr_containsFVar(v___x_187_, v_fvarId_151_);
lean_dec_ref(v___x_187_);
if (v___x_188_ == 0)
{
v___y_171_ = v_fst_164_;
goto v___jp_170_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_inc(v_val_163_);
v___x_189_ = l_Lean_LocalDecl_toExpr(v_val_163_);
v___x_190_ = lean_array_push(v_fst_164_, v___x_189_);
v___y_171_ = v___x_190_;
goto v___jp_170_;
}
v___jp_170_:
{
uint8_t v___x_172_; 
v___x_172_ = lean_unbox(v_snd_165_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
lean_dec(v_snd_165_);
v___x_173_ = l_Lean_LocalDecl_value_x3f(v_val_163_, v___x_161_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_box(v___x_169_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_174_);
lean_ctor_set(v___x_167_, 0, v___y_171_);
v___x_176_ = v___x_167_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___y_171_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
v___y_157_ = v___x_176_;
goto v___jp_156_;
}
}
else
{
lean_object* v_val_178_; uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v_val_178_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_val_178_);
lean_dec_ref_known(v___x_173_, 1);
v___x_179_ = l_Lean_Expr_containsFVar(v_val_178_, v_fvarId_151_);
lean_dec(v_val_178_);
v___x_180_ = lean_box(v___x_179_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_180_);
lean_ctor_set(v___x_167_, 0, v___y_171_);
v___x_182_ = v___x_167_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___y_171_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
v___y_157_ = v___x_182_;
goto v___jp_156_;
}
}
}
else
{
lean_object* v___x_185_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___y_171_);
v___x_185_ = v___x_167_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___y_171_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_snd_165_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
v___y_157_ = v___x_185_;
goto v___jp_156_;
}
}
}
}
}
}
else
{
return v_b_155_;
}
v___jp_156_:
{
size_t v___x_158_; size_t v___x_159_; 
v___x_158_ = ((size_t)1ULL);
v___x_159_ = lean_usize_add(v_i_153_, v___x_158_);
v_i_153_ = v___x_159_;
v_b_155_ = v___y_157_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v___x_192_, lean_object* v___x_193_, lean_object* v_fvarId_194_, lean_object* v_as_195_, lean_object* v_i_196_, lean_object* v_stop_197_, lean_object* v_b_198_){
_start:
{
size_t v_i_boxed_199_; size_t v_stop_boxed_200_; lean_object* v_res_201_; 
v_i_boxed_199_ = lean_unbox_usize(v_i_196_);
lean_dec(v_i_196_);
v_stop_boxed_200_ = lean_unbox_usize(v_stop_197_);
lean_dec(v_stop_197_);
v_res_201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_192_, v___x_193_, v_fvarId_194_, v_as_195_, v_i_boxed_199_, v_stop_boxed_200_, v_b_198_);
lean_dec_ref(v_as_195_);
lean_dec(v_fvarId_194_);
lean_dec(v___x_193_);
lean_dec(v___x_192_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(lean_object* v___x_202_, lean_object* v___x_203_, lean_object* v_fvarId_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_object* v_cs_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_cs_207_ = lean_ctor_get(v_x_205_, 0);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_array_get_size(v_cs_207_);
v___x_210_ = lean_nat_dec_lt(v___x_208_, v___x_209_);
if (v___x_210_ == 0)
{
return v_x_206_;
}
else
{
size_t v___x_211_; size_t v___x_212_; lean_object* v___x_213_; 
v___x_211_ = ((size_t)0ULL);
v___x_212_ = lean_usize_of_nat(v___x_209_);
v___x_213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(v___x_202_, v___x_203_, v_fvarId_204_, v_cs_207_, v___x_211_, v___x_212_, v_x_206_);
return v___x_213_;
}
}
else
{
lean_object* v_vs_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_vs_214_ = lean_ctor_get(v_x_205_, 0);
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = lean_array_get_size(v_vs_214_);
v___x_217_ = lean_nat_dec_lt(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
return v_x_206_;
}
else
{
size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; 
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_216_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_202_, v___x_203_, v_fvarId_204_, v_vs_214_, v___x_218_, v___x_219_, v_x_206_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v___x_221_, lean_object* v___x_222_, lean_object* v_fvarId_223_, lean_object* v_as_224_, size_t v_i_225_, size_t v_stop_226_, lean_object* v_b_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_eq(v_i_225_, v_stop_226_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; size_t v___x_231_; size_t v___x_232_; 
v___x_229_ = lean_array_uget_borrowed(v_as_224_, v_i_225_);
v___x_230_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(v___x_221_, v___x_222_, v_fvarId_223_, v___x_229_, v_b_227_);
v___x_231_ = ((size_t)1ULL);
v___x_232_ = lean_usize_add(v_i_225_, v___x_231_);
v_i_225_ = v___x_232_;
v_b_227_ = v___x_230_;
goto _start;
}
else
{
return v_b_227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v___x_234_, lean_object* v___x_235_, lean_object* v_fvarId_236_, lean_object* v_as_237_, lean_object* v_i_238_, lean_object* v_stop_239_, lean_object* v_b_240_){
_start:
{
size_t v_i_boxed_241_; size_t v_stop_boxed_242_; lean_object* v_res_243_; 
v_i_boxed_241_ = lean_unbox_usize(v_i_238_);
lean_dec(v_i_238_);
v_stop_boxed_242_ = lean_unbox_usize(v_stop_239_);
lean_dec(v_stop_239_);
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(v___x_234_, v___x_235_, v_fvarId_236_, v_as_237_, v_i_boxed_241_, v_stop_boxed_242_, v_b_240_);
lean_dec_ref(v_as_237_);
lean_dec(v_fvarId_236_);
lean_dec(v___x_235_);
lean_dec(v___x_234_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v___x_244_, lean_object* v___x_245_, lean_object* v_fvarId_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(v___x_244_, v___x_245_, v_fvarId_246_, v_x_247_, v_x_248_);
lean_dec_ref(v_x_247_);
lean_dec(v_fvarId_246_);
lean_dec(v___x_245_);
lean_dec(v___x_244_);
return v_res_249_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(lean_object* v___x_251_, lean_object* v___x_252_, lean_object* v_fvarId_253_, lean_object* v_x_254_, size_t v_x_255_, size_t v_x_256_, lean_object* v_x_257_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v_cs_258_; lean_object* v___x_259_; size_t v___x_260_; lean_object* v_j_261_; lean_object* v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_cs_258_ = lean_ctor_get(v_x_254_, 0);
v___x_259_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0);
v___x_260_ = lean_usize_shift_right(v_x_255_, v_x_256_);
v_j_261_ = lean_usize_to_nat(v___x_260_);
v___x_262_ = lean_array_get_borrowed(v___x_259_, v_cs_258_, v_j_261_);
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_shift_left(v___x_263_, v_x_256_);
v___x_265_ = lean_usize_sub(v___x_264_, v___x_263_);
v___x_266_ = lean_usize_land(v_x_255_, v___x_265_);
v___x_267_ = ((size_t)5ULL);
v___x_268_ = lean_usize_sub(v_x_256_, v___x_267_);
v___x_269_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(v___x_251_, v___x_252_, v_fvarId_253_, v___x_262_, v___x_266_, v___x_268_, v_x_257_);
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_j_261_, v___x_270_);
lean_dec(v_j_261_);
v___x_272_ = lean_array_get_size(v_cs_258_);
v___x_273_ = lean_nat_dec_lt(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec(v___x_271_);
return v___x_269_;
}
else
{
size_t v___x_274_; size_t v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_usize_of_nat(v___x_271_);
lean_dec(v___x_271_);
v___x_275_ = lean_usize_of_nat(v___x_272_);
v___x_276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(v___x_251_, v___x_252_, v_fvarId_253_, v_cs_258_, v___x_274_, v___x_275_, v___x_269_);
return v___x_276_;
}
}
else
{
lean_object* v_vs_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_vs_277_ = lean_ctor_get(v_x_254_, 0);
v___x_278_ = lean_usize_to_nat(v_x_255_);
v___x_279_ = lean_array_get_size(v_vs_277_);
v___x_280_ = lean_nat_dec_lt(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_dec(v___x_278_);
return v_x_257_;
}
else
{
size_t v___x_281_; size_t v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_usize_of_nat(v___x_278_);
lean_dec(v___x_278_);
v___x_282_ = lean_usize_of_nat(v___x_279_);
v___x_283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_251_, v___x_252_, v_fvarId_253_, v_vs_277_, v___x_281_, v___x_282_, v_x_257_);
return v___x_283_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_284_, lean_object* v___x_285_, lean_object* v_fvarId_286_, lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
size_t v_x_22083__boxed_291_; size_t v_x_22084__boxed_292_; lean_object* v_res_293_; 
v_x_22083__boxed_291_ = lean_unbox_usize(v_x_288_);
lean_dec(v_x_288_);
v_x_22084__boxed_292_ = lean_unbox_usize(v_x_289_);
lean_dec(v_x_289_);
v_res_293_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(v___x_284_, v___x_285_, v_fvarId_286_, v_x_287_, v_x_22083__boxed_291_, v_x_22084__boxed_292_, v_x_290_);
lean_dec_ref(v_x_287_);
lean_dec(v_fvarId_286_);
lean_dec(v___x_285_);
lean_dec(v___x_284_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0(lean_object* v___x_294_, lean_object* v___x_295_, lean_object* v_fvarId_296_, lean_object* v_t_297_, lean_object* v_init_298_, lean_object* v_start_299_){
_start:
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_nat_dec_eq(v_start_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v_root_302_; lean_object* v_tail_303_; size_t v_shift_304_; lean_object* v_tailOff_305_; uint8_t v___x_306_; 
v_root_302_ = lean_ctor_get(v_t_297_, 0);
v_tail_303_ = lean_ctor_get(v_t_297_, 1);
v_shift_304_ = lean_ctor_get_usize(v_t_297_, 4);
v_tailOff_305_ = lean_ctor_get(v_t_297_, 3);
v___x_306_ = lean_nat_dec_le(v_tailOff_305_, v_start_299_);
if (v___x_306_ == 0)
{
size_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_307_ = lean_usize_of_nat(v_start_299_);
v___x_308_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(v___x_294_, v___x_295_, v_fvarId_296_, v_root_302_, v___x_307_, v_shift_304_, v_init_298_);
v___x_309_ = lean_array_get_size(v_tail_303_);
v___x_310_ = lean_nat_dec_lt(v___x_300_, v___x_309_);
if (v___x_310_ == 0)
{
return v___x_308_;
}
else
{
size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; 
v___x_311_ = ((size_t)0ULL);
v___x_312_ = lean_usize_of_nat(v___x_309_);
v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_294_, v___x_295_, v_fvarId_296_, v_tail_303_, v___x_311_, v___x_312_, v___x_308_);
return v___x_313_;
}
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_nat_sub(v_start_299_, v_tailOff_305_);
v___x_315_ = lean_array_get_size(v_tail_303_);
v___x_316_ = lean_nat_dec_lt(v___x_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_dec(v___x_314_);
return v_init_298_;
}
else
{
size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_usize_of_nat(v___x_314_);
lean_dec(v___x_314_);
v___x_318_ = lean_usize_of_nat(v___x_315_);
v___x_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_294_, v___x_295_, v_fvarId_296_, v_tail_303_, v___x_317_, v___x_318_, v_init_298_);
return v___x_319_;
}
}
}
else
{
lean_object* v_root_320_; lean_object* v_tail_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_root_320_ = lean_ctor_get(v_t_297_, 0);
v_tail_321_ = lean_ctor_get(v_t_297_, 1);
v___x_322_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(v___x_294_, v___x_295_, v_fvarId_296_, v_root_320_, v_init_298_);
v___x_323_ = lean_array_get_size(v_tail_321_);
v___x_324_ = lean_nat_dec_lt(v___x_300_, v___x_323_);
if (v___x_324_ == 0)
{
return v___x_322_;
}
else
{
size_t v___x_325_; size_t v___x_326_; lean_object* v___x_327_; 
v___x_325_ = ((size_t)0ULL);
v___x_326_ = lean_usize_of_nat(v___x_323_);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_294_, v___x_295_, v_fvarId_296_, v_tail_321_, v___x_325_, v___x_326_, v___x_322_);
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0___boxed(lean_object* v___x_328_, lean_object* v___x_329_, lean_object* v_fvarId_330_, lean_object* v_t_331_, lean_object* v_init_332_, lean_object* v_start_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0(v___x_328_, v___x_329_, v_fvarId_330_, v_t_331_, v_init_332_, v_start_333_);
lean_dec(v_start_333_);
lean_dec_ref(v_t_331_);
lean_dec(v_fvarId_330_);
lean_dec(v___x_329_);
lean_dec(v___x_328_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0(lean_object* v___x_335_, lean_object* v___x_336_, lean_object* v_fvarId_337_, lean_object* v_lctx_338_, lean_object* v_init_339_, lean_object* v_start_340_){
_start:
{
lean_object* v_decls_341_; lean_object* v___x_342_; 
v_decls_341_ = lean_ctor_get(v_lctx_338_, 1);
v___x_342_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0(v___x_335_, v___x_336_, v_fvarId_337_, v_decls_341_, v_init_339_, v_start_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0___boxed(lean_object* v___x_343_, lean_object* v___x_344_, lean_object* v_fvarId_345_, lean_object* v_lctx_346_, lean_object* v_init_347_, lean_object* v_start_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0(v___x_343_, v___x_344_, v_fvarId_345_, v_lctx_346_, v_init_347_, v_start_348_);
lean_dec(v_start_348_);
lean_dec_ref(v_lctx_346_);
lean_dec(v_fvarId_345_);
lean_dec(v___x_344_);
lean_dec(v___x_343_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(lean_object* v_eqn_359_, lean_object* v_G_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Meta_Sym_instantiateMVarsS(v_eqn_359_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_499_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_499_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_499_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_499_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = l_Lean_Expr_cleanupAnnotations(v_a_372_);
lean_dec(v_a_372_);
v___x_382_ = l_Lean_Expr_isApp(v___x_381_);
if (v___x_382_ == 0)
{
lean_dec_ref(v___x_381_);
lean_del_object(v___x_374_);
lean_dec_ref(v_G_360_);
goto v___jp_368_;
}
else
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_381_);
v___x_384_ = l_Lean_Expr_isApp(v___x_383_);
if (v___x_384_ == 0)
{
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_381_);
lean_del_object(v___x_374_);
lean_dec_ref(v_G_360_);
goto v___jp_368_;
}
else
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = l_Lean_Expr_appFnCleanup___redArg(v___x_383_);
v___x_386_ = l_Lean_Expr_isApp(v___x_385_);
if (v___x_386_ == 0)
{
lean_dec_ref(v___x_385_);
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_381_);
lean_del_object(v___x_374_);
lean_dec_ref(v_G_360_);
goto v___jp_368_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_387_ = l_Lean_Expr_appFnCleanup___redArg(v___x_385_);
lean_dec_ref(v___x_385_);
v___x_388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1));
v___x_389_ = l_Lean_Expr_isConstOf(v___x_387_, v___x_388_);
lean_dec_ref(v___x_387_);
if (v___x_389_ == 0)
{
lean_dec_ref(v___x_383_);
lean_dec_ref(v___x_381_);
lean_del_object(v___x_374_);
lean_dec_ref(v_G_360_);
goto v___jp_368_;
}
else
{
lean_object* v_arg_390_; 
v_arg_390_ = lean_ctor_get(v___x_383_, 1);
lean_inc_ref(v_arg_390_);
lean_dec_ref(v___x_383_);
if (lean_obj_tag(v_arg_390_) == 1)
{
lean_object* v_fvarId_391_; lean_object* v_lctx_392_; lean_object* v___x_393_; 
v_fvarId_391_ = lean_ctor_get(v_arg_390_, 0);
v_lctx_392_ = lean_ctor_get(v_a_363_, 2);
lean_inc(v_fvarId_391_);
lean_inc_ref(v_lctx_392_);
v___x_393_ = lean_local_ctx_find(v_lctx_392_, v_fvarId_391_);
if (lean_obj_tag(v___x_393_) == 1)
{
lean_object* v_val_394_; uint8_t v___x_395_; uint8_t v___x_396_; 
v_val_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v___x_393_, 1);
v___x_395_ = 0;
v___x_396_ = l_Lean_LocalDecl_isLet(v_val_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v_arg_397_; uint8_t v___x_398_; 
v_arg_397_ = lean_ctor_get(v___x_381_, 1);
lean_inc_ref(v_arg_397_);
lean_dec_ref(v___x_381_);
v___x_398_ = l_Lean_Expr_containsFVar(v_arg_397_, v_fvarId_391_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_del_object(v___x_374_);
lean_inc_ref(v_G_360_);
v___x_399_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_G_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_486_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_486_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_486_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_486_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
if (lean_obj_tag(v_a_400_) == 1)
{
lean_object* v_val_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_481_; 
lean_del_object(v___x_402_);
v_val_404_ = lean_ctor_get(v_a_400_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_a_400_);
if (v_isSharedCheck_481_ == 0)
{
v___x_406_ = v_a_400_;
v_isShared_407_ = v_isSharedCheck_481_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_val_404_);
lean_dec(v_a_400_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_481_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_FVarId_getDecl___redArg(v_val_404_, v_a_363_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_472_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_472_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_472_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_472_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_413_ = l_Lean_LocalDecl_index(v_a_409_);
lean_dec(v_a_409_);
v___x_414_ = l_Lean_LocalDecl_index(v_val_394_);
lean_dec(v_val_394_);
v___x_415_ = lean_nat_dec_lt(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_fst_421_; lean_object* v_snd_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_467_; 
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__3));
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_add(v___x_414_, v___x_418_);
v___x_420_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0(v___x_413_, v___x_414_, v_fvarId_391_, v_lctx_392_, v___x_417_, v___x_419_);
lean_dec(v___x_419_);
lean_dec(v___x_414_);
lean_dec(v___x_413_);
v_fst_421_ = lean_ctor_get(v___x_420_, 0);
v_snd_422_ = lean_ctor_get(v___x_420_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_467_ == 0)
{
v___x_424_ = v___x_420_;
v_isShared_425_ = v_isSharedCheck_467_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_snd_422_);
lean_inc(v_fst_421_);
lean_dec(v___x_420_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_467_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_426_ = lean_mk_empty_array_with_capacity(v___x_418_);
lean_inc_ref_n(v_arg_390_, 2);
v___x_427_ = lean_array_push(v___x_426_, v_arg_390_);
v___x_428_ = l_Array_append___redArg(v___x_427_, v_fst_421_);
v___x_429_ = lean_array_push(v___x_428_, v_arg_390_);
v___x_430_ = l_Lean_Meta_Sym_abstractFVarsRange(v_G_360_, v___x_416_, v___x_429_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_458_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_458_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_458_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_458_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
uint8_t v___y_436_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = l_Lean_Expr_looseBVarRange(v_a_431_);
v___x_450_ = lean_nat_dec_eq(v___x_449_, v___x_418_);
lean_dec(v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_453_; 
lean_del_object(v___x_433_);
lean_dec(v_a_431_);
lean_del_object(v___x_424_);
lean_dec(v_snd_422_);
lean_dec(v_fst_421_);
lean_del_object(v___x_406_);
lean_dec_ref(v_arg_397_);
lean_dec_ref_known(v_arg_390_, 1);
v___x_451_ = lean_box(0);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_451_);
v___x_453_ = v___x_411_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
else
{
lean_object* v___x_455_; uint8_t v___x_456_; 
lean_del_object(v___x_411_);
v___x_455_ = lean_array_get_size(v_fst_421_);
lean_dec(v_fst_421_);
v___x_456_ = lean_nat_dec_eq(v___x_455_, v___x_416_);
if (v___x_456_ == 0)
{
lean_dec(v_snd_422_);
v___y_436_ = v___x_395_;
goto v___jp_435_;
}
else
{
uint8_t v___x_457_; 
v___x_457_ = lean_unbox(v_snd_422_);
lean_dec(v_snd_422_);
if (v___x_457_ == 0)
{
v___y_436_ = v___x_450_;
goto v___jp_435_;
}
else
{
v___y_436_ = v___x_415_;
goto v___jp_435_;
}
}
}
v___jp_435_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_box(v___y_436_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v___x_437_);
lean_ctor_set(v___x_424_, 0, v_a_431_);
v___x_439_ = v___x_424_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_431_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_448_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v_arg_397_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_arg_390_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_441_);
v___x_443_ = v___x_406_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_447_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_443_);
v___x_445_ = v___x_433_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
lean_del_object(v___x_424_);
lean_dec(v_snd_422_);
lean_dec(v_fst_421_);
lean_del_object(v___x_411_);
lean_del_object(v___x_406_);
lean_dec_ref(v_arg_397_);
lean_dec_ref_known(v_arg_390_, 1);
v_a_459_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_430_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_430_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_470_; 
lean_dec(v___x_414_);
lean_dec(v___x_413_);
lean_del_object(v___x_406_);
lean_dec_ref(v_arg_397_);
lean_dec_ref_known(v_arg_390_, 1);
lean_dec_ref(v_G_360_);
v___x_468_ = lean_box(0);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_468_);
v___x_470_ = v___x_411_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_del_object(v___x_406_);
lean_dec_ref(v_arg_397_);
lean_dec(v_val_394_);
lean_dec_ref_known(v_arg_390_, 1);
lean_dec_ref(v_G_360_);
v_a_473_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_408_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_408_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_object* v___x_482_; lean_object* v___x_484_; 
lean_dec(v_a_400_);
lean_dec_ref(v_arg_397_);
lean_dec(v_val_394_);
lean_dec_ref_known(v_arg_390_, 1);
lean_dec_ref(v_G_360_);
v___x_482_ = lean_box(0);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_482_);
v___x_484_ = v___x_402_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec_ref(v_arg_397_);
lean_dec(v_val_394_);
lean_dec_ref_known(v_arg_390_, 1);
lean_dec_ref(v_G_360_);
v_a_487_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_399_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_399_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
else
{
lean_dec_ref(v_arg_397_);
lean_dec(v_val_394_);
lean_dec_ref_known(v_arg_390_, 1);
lean_dec_ref(v_G_360_);
goto v___jp_376_;
}
}
else
{
lean_dec(v_val_394_);
lean_dec_ref_known(v_arg_390_, 1);
lean_dec_ref(v___x_381_);
lean_dec_ref(v_G_360_);
goto v___jp_376_;
}
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v___x_393_);
lean_dec_ref_known(v_arg_390_, 1);
lean_dec_ref(v___x_381_);
lean_del_object(v___x_374_);
lean_dec_ref(v_G_360_);
v___x_495_ = lean_box(0);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec_ref(v_arg_390_);
lean_dec_ref(v___x_381_);
lean_del_object(v___x_374_);
lean_dec_ref(v_G_360_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
}
}
}
v___jp_376_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_box(0);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_377_);
v___x_379_ = v___x_374_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec_ref(v_G_360_);
v_a_500_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_371_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_371_);
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
v___jp_368_:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___boxed(lean_object* v_eqn_508_, lean_object* v_G_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_eqn_508_, v_G_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f(lean_object* v_eqn_518_, lean_object* v_G_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_eqn_518_, v_G_519_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___boxed(lean_object* v_eqn_533_, lean_object* v_G_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f(v_eqn_533_, v_G_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(lean_object* v_00_u03c6_551_, lean_object* v_G_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___x_591_; 
lean_inc_ref(v_00_u03c6_551_);
v___x_591_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03c6_551_, v_a_556_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = l_Lean_Expr_cleanupAnnotations(v_a_592_);
lean_dec(v_a_592_);
v___x_594_ = l_Lean_Expr_isApp(v___x_593_);
if (v___x_594_ == 0)
{
lean_dec_ref(v___x_593_);
v___y_561_ = v_a_553_;
v___y_562_ = v_a_554_;
v___y_563_ = v_a_555_;
v___y_564_ = v_a_556_;
v___y_565_ = v_a_557_;
v___y_566_ = v_a_558_;
goto v___jp_560_;
}
else
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = l_Lean_Expr_appFnCleanup___redArg(v___x_593_);
v___x_596_ = l_Lean_Expr_isApp(v___x_595_);
if (v___x_596_ == 0)
{
lean_dec_ref(v___x_595_);
lean_dec_ref(v___x_593_);
v___y_561_ = v_a_553_;
v___y_562_ = v_a_554_;
v___y_563_ = v_a_555_;
v___y_564_ = v_a_556_;
v___y_565_ = v_a_557_;
v___y_566_ = v_a_558_;
goto v___jp_560_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_597_ = l_Lean_Expr_appFnCleanup___redArg(v___x_595_);
v___x_598_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__1));
v___x_599_ = l_Lean_Expr_isConstOf(v___x_597_, v___x_598_);
lean_dec_ref(v___x_597_);
if (v___x_599_ == 0)
{
lean_dec_ref(v___x_595_);
lean_dec_ref(v___x_593_);
v___y_561_ = v_a_553_;
v___y_562_ = v_a_554_;
v___y_563_ = v_a_555_;
v___y_564_ = v_a_556_;
v___y_565_ = v_a_557_;
v___y_566_ = v_a_558_;
goto v___jp_560_;
}
else
{
lean_object* v_arg_600_; lean_object* v_arg_601_; lean_object* v___x_602_; 
lean_dec_ref(v_00_u03c6_551_);
v_arg_600_ = lean_ctor_get(v___x_593_, 1);
lean_inc_ref(v_arg_600_);
lean_dec_ref(v___x_593_);
v_arg_601_ = lean_ctor_get(v___x_595_, 1);
lean_inc_ref(v_arg_601_);
lean_dec_ref(v___x_595_);
lean_inc_ref(v_G_552_);
v___x_602_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_arg_601_, v_G_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; uint8_t v___x_604_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v___x_604_ = lean_unbox(v_a_603_);
if (v___x_604_ == 0)
{
lean_dec_ref_known(v___x_602_, 1);
v_00_u03c6_551_ = v_arg_600_;
goto _start;
}
else
{
lean_dec_ref(v_arg_600_);
lean_dec_ref(v_G_552_);
return v___x_602_;
}
}
else
{
lean_dec_ref(v_arg_600_);
lean_dec_ref(v_G_552_);
return v___x_602_;
}
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_G_552_);
lean_dec_ref(v_00_u03c6_551_);
v_a_606_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_591_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_591_);
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
v___jp_560_:
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_00_u03c6_551_, v_G_552_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_582_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_582_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_582_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_582_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
if (lean_obj_tag(v_a_568_) == 0)
{
uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_572_ = 0;
v___x_573_ = lean_box(v___x_572_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_573_);
v___x_575_ = v___x_570_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
uint8_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
lean_dec_ref_known(v_a_568_, 1);
v___x_577_ = 1;
v___x_578_ = lean_box(v___x_577_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_578_);
v___x_580_ = v___x_570_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_a_583_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_567_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_567_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___boxed(lean_object* v_00_u03c6_614_, lean_object* v_G_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_00_u03c6_614_, v_G_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct(lean_object* v_00_u03c6_624_, lean_object* v_G_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_00_u03c6_624_, v_G_625_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___boxed(lean_object* v_00_u03c6_639_, lean_object* v_G_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct(v_00_u03c6_639_, v_G_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(lean_object* v_x_654_, uint8_t v_bi_655_, lean_object* v_t_656_, lean_object* v_b_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___y_666_; lean_object* v___x_669_; uint8_t v_debug_670_; 
v___x_669_ = lean_st_ref_get(v___y_659_);
v_debug_670_ = lean_ctor_get_uint8(v___x_669_, sizeof(void*)*12);
lean_dec(v___x_669_);
if (v_debug_670_ == 0)
{
v___y_666_ = v___y_659_;
goto v___jp_665_;
}
else
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_656_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v___x_672_; 
lean_dec_ref_known(v___x_671_, 1);
v___x_672_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_dec_ref_known(v___x_672_, 1);
v___y_666_ = v___y_659_;
goto v___jp_665_;
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_b_657_);
lean_dec_ref(v_t_656_);
lean_dec(v_x_654_);
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
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
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_b_657_);
lean_dec_ref(v_t_656_);
lean_dec(v_x_654_);
v_a_681_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_671_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_671_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
v___jp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = l_Lean_Expr_forallE___override(v_x_654_, v_t_656_, v_b_657_, v_bi_655_);
v___x_668_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_667_, v___y_666_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg___boxed(lean_object* v_x_689_, lean_object* v_bi_690_, lean_object* v_t_691_, lean_object* v_b_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
uint8_t v_bi_boxed_700_; lean_object* v_res_701_; 
v_bi_boxed_700_ = lean_unbox(v_bi_690_);
v_res_701_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_x_689_, v_bi_boxed_700_, v_t_691_, v_b_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0(lean_object* v_x_702_, uint8_t v_bi_703_, lean_object* v_t_704_, lean_object* v_b_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_x_702_, v_bi_703_, v_t_704_, v_b_705_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___boxed(lean_object* v_x_719_, lean_object* v_bi_720_, lean_object* v_t_721_, lean_object* v_b_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
uint8_t v_bi_boxed_735_; lean_object* v_res_736_; 
v_bi_boxed_735_ = lean_unbox(v_bi_720_);
v_res_736_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0(v_x_719_, v_bi_boxed_735_, v_t_721_, v_b_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v_ks_741_; lean_object* v_vs_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_766_; 
v_ks_741_ = lean_ctor_get(v_x_737_, 0);
v_vs_742_ = lean_ctor_get(v_x_737_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_766_ == 0)
{
v___x_744_ = v_x_737_;
v_isShared_745_ = v_isSharedCheck_766_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_vs_742_);
lean_inc(v_ks_741_);
lean_dec(v_x_737_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_766_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_array_get_size(v_ks_741_);
v___x_747_ = lean_nat_dec_lt(v_x_738_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
lean_dec(v_x_738_);
v___x_748_ = lean_array_push(v_ks_741_, v_x_739_);
v___x_749_ = lean_array_push(v_vs_742_, v_x_740_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___x_749_);
lean_ctor_set(v___x_744_, 0, v___x_748_);
v___x_751_ = v___x_744_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v___x_749_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
else
{
lean_object* v_k_x27_753_; uint8_t v___x_754_; 
v_k_x27_753_ = lean_array_fget_borrowed(v_ks_741_, v_x_738_);
v___x_754_ = l_Lean_instBEqMVarId_beq(v_x_739_, v_k_x27_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_756_; 
if (v_isShared_745_ == 0)
{
v___x_756_ = v___x_744_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_ks_741_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_vs_742_);
v___x_756_ = v_reuseFailAlloc_760_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(1u);
v___x_758_ = lean_nat_add(v_x_738_, v___x_757_);
lean_dec(v_x_738_);
v_x_737_ = v___x_756_;
v_x_738_ = v___x_758_;
goto _start;
}
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_761_ = lean_array_fset(v_ks_741_, v_x_738_, v_x_739_);
v___x_762_ = lean_array_fset(v_vs_742_, v_x_738_, v_x_740_);
lean_dec(v_x_738_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v___x_762_);
lean_ctor_set(v___x_744_, 0, v___x_761_);
v___x_764_ = v___x_744_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_767_, lean_object* v_k_768_, lean_object* v_v_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_767_, v___x_770_, v_k_768_, v_v_769_);
return v___x_771_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_x_773_, size_t v_x_774_, size_t v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
if (lean_obj_tag(v_x_773_) == 0)
{
lean_object* v_es_778_; size_t v___x_779_; size_t v___x_780_; lean_object* v_j_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_es_778_ = lean_ctor_get(v_x_773_, 0);
v___x_779_ = ((size_t)31ULL);
v___x_780_ = lean_usize_land(v_x_774_, v___x_779_);
v_j_781_ = lean_usize_to_nat(v___x_780_);
v___x_782_ = lean_array_get_size(v_es_778_);
v___x_783_ = lean_nat_dec_lt(v_j_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_dec(v_j_781_);
lean_dec(v_x_777_);
lean_dec(v_x_776_);
return v_x_773_;
}
else
{
lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_822_; 
lean_inc_ref(v_es_778_);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_773_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_x_773_, 0);
lean_dec(v_unused_823_);
v___x_785_ = v_x_773_;
v_isShared_786_ = v_isSharedCheck_822_;
goto v_resetjp_784_;
}
else
{
lean_dec(v_x_773_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_822_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_v_787_; lean_object* v___x_788_; lean_object* v_xs_x27_789_; lean_object* v___y_791_; 
v_v_787_ = lean_array_fget(v_es_778_, v_j_781_);
v___x_788_ = lean_box(0);
v_xs_x27_789_ = lean_array_fset(v_es_778_, v_j_781_, v___x_788_);
switch(lean_obj_tag(v_v_787_))
{
case 0:
{
lean_object* v_key_796_; lean_object* v_val_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_807_; 
v_key_796_ = lean_ctor_get(v_v_787_, 0);
v_val_797_ = lean_ctor_get(v_v_787_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_v_787_);
if (v_isSharedCheck_807_ == 0)
{
v___x_799_ = v_v_787_;
v_isShared_800_ = v_isSharedCheck_807_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_val_797_);
lean_inc(v_key_796_);
lean_dec(v_v_787_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_807_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
uint8_t v___x_801_; 
v___x_801_ = l_Lean_instBEqMVarId_beq(v_x_776_, v_key_796_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_del_object(v___x_799_);
v___x_802_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_796_, v_val_797_, v_x_776_, v_x_777_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
v___y_791_ = v___x_803_;
goto v___jp_790_;
}
else
{
lean_object* v___x_805_; 
lean_dec(v_val_797_);
lean_dec(v_key_796_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v_x_777_);
lean_ctor_set(v___x_799_, 0, v_x_776_);
v___x_805_ = v___x_799_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_x_776_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_x_777_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
v___y_791_ = v___x_805_;
goto v___jp_790_;
}
}
}
}
case 1:
{
lean_object* v_node_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_820_; 
v_node_808_ = lean_ctor_get(v_v_787_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v_v_787_);
if (v_isSharedCheck_820_ == 0)
{
v___x_810_ = v_v_787_;
v_isShared_811_ = v_isSharedCheck_820_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_node_808_);
lean_dec(v_v_787_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_820_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_812_ = ((size_t)5ULL);
v___x_813_ = lean_usize_shift_right(v_x_774_, v___x_812_);
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_add(v_x_775_, v___x_814_);
v___x_816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(v_node_808_, v___x_813_, v___x_815_, v_x_776_, v_x_777_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_816_);
v___x_818_ = v___x_810_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
v___y_791_ = v___x_818_;
goto v___jp_790_;
}
}
}
default: 
{
lean_object* v___x_821_; 
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_x_776_);
lean_ctor_set(v___x_821_, 1, v_x_777_);
v___y_791_ = v___x_821_;
goto v___jp_790_;
}
}
v___jp_790_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_array_fset(v_xs_x27_789_, v_j_781_, v___y_791_);
lean_dec(v_j_781_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_792_);
v___x_794_ = v___x_785_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
else
{
lean_object* v_ks_824_; lean_object* v_vs_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_843_; 
v_ks_824_ = lean_ctor_get(v_x_773_, 0);
v_vs_825_ = lean_ctor_get(v_x_773_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_x_773_);
if (v_isSharedCheck_843_ == 0)
{
v___x_827_ = v_x_773_;
v_isShared_828_ = v_isSharedCheck_843_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_vs_825_);
lean_inc(v_ks_824_);
lean_dec(v_x_773_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_843_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_ks_824_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_vs_825_);
v___x_830_ = v_reuseFailAlloc_842_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v_newNode_831_; size_t v___x_832_; uint8_t v___x_833_; 
v_newNode_831_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v___x_830_, v_x_776_, v_x_777_);
v___x_832_ = ((size_t)7ULL);
v___x_833_ = lean_usize_dec_le(v___x_832_, v_x_775_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_834_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_831_);
v___x_835_ = lean_unsigned_to_nat(4u);
v___x_836_ = lean_nat_dec_lt(v___x_834_, v___x_835_);
lean_dec(v___x_834_);
if (v___x_836_ == 0)
{
lean_object* v_ks_837_; lean_object* v_vs_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_ks_837_ = lean_ctor_get(v_newNode_831_, 0);
lean_inc_ref(v_ks_837_);
v_vs_838_ = lean_ctor_get(v_newNode_831_, 1);
lean_inc_ref(v_vs_838_);
lean_dec_ref(v_newNode_831_);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_841_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg(v_x_775_, v_ks_837_, v_vs_838_, v___x_839_, v___x_840_);
lean_dec_ref(v_vs_838_);
lean_dec_ref(v_ks_837_);
return v___x_841_;
}
else
{
return v_newNode_831_;
}
}
else
{
return v_newNode_831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_844_, lean_object* v_keys_845_, lean_object* v_vals_846_, lean_object* v_i_847_, lean_object* v_entries_848_){
_start:
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = lean_array_get_size(v_keys_845_);
v___x_850_ = lean_nat_dec_lt(v_i_847_, v___x_849_);
if (v___x_850_ == 0)
{
lean_dec(v_i_847_);
return v_entries_848_;
}
else
{
lean_object* v_k_851_; lean_object* v_v_852_; uint64_t v___x_853_; size_t v_h_854_; size_t v___x_855_; lean_object* v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v___x_859_; size_t v_h_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_k_851_ = lean_array_fget_borrowed(v_keys_845_, v_i_847_);
v_v_852_ = lean_array_fget_borrowed(v_vals_846_, v_i_847_);
v___x_853_ = l_Lean_instHashableMVarId_hash(v_k_851_);
v_h_854_ = lean_uint64_to_usize(v___x_853_);
v___x_855_ = ((size_t)5ULL);
v___x_856_ = lean_unsigned_to_nat(1u);
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_sub(v_depth_844_, v___x_857_);
v___x_859_ = lean_usize_mul(v___x_855_, v___x_858_);
v_h_860_ = lean_usize_shift_right(v_h_854_, v___x_859_);
v___x_861_ = lean_nat_add(v_i_847_, v___x_856_);
lean_dec(v_i_847_);
lean_inc(v_v_852_);
lean_inc(v_k_851_);
v___x_862_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(v_entries_848_, v_h_860_, v_depth_844_, v_k_851_, v_v_852_);
v_i_847_ = v___x_861_;
v_entries_848_ = v___x_862_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_864_, lean_object* v_keys_865_, lean_object* v_vals_866_, lean_object* v_i_867_, lean_object* v_entries_868_){
_start:
{
size_t v_depth_boxed_869_; lean_object* v_res_870_; 
v_depth_boxed_869_ = lean_unbox_usize(v_depth_864_);
lean_dec(v_depth_864_);
v_res_870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_869_, v_keys_865_, v_vals_866_, v_i_867_, v_entries_868_);
lean_dec_ref(v_vals_866_);
lean_dec_ref(v_keys_865_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
size_t v_x_11293__boxed_876_; size_t v_x_11294__boxed_877_; lean_object* v_res_878_; 
v_x_11293__boxed_876_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_x_11294__boxed_877_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_res_878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(v_x_871_, v_x_11293__boxed_876_, v_x_11294__boxed_877_, v_x_874_, v_x_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1___redArg(lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
uint64_t v___x_882_; size_t v___x_883_; size_t v___x_884_; lean_object* v___x_885_; 
v___x_882_ = l_Lean_instHashableMVarId_hash(v_x_880_);
v___x_883_ = lean_uint64_to_usize(v___x_882_);
v___x_884_ = ((size_t)1ULL);
v___x_885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(v_x_879_, v___x_883_, v___x_884_, v_x_880_, v_x_881_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(lean_object* v_mvarId_886_, lean_object* v_val_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; lean_object* v_mctx_891_; lean_object* v_cache_892_; lean_object* v_zetaDeltaFVarIds_893_; lean_object* v_postponed_894_; lean_object* v_diag_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_925_; 
v___x_890_ = lean_st_ref_take(v___y_888_);
v_mctx_891_ = lean_ctor_get(v___x_890_, 0);
v_cache_892_ = lean_ctor_get(v___x_890_, 1);
v_zetaDeltaFVarIds_893_ = lean_ctor_get(v___x_890_, 2);
v_postponed_894_ = lean_ctor_get(v___x_890_, 3);
v_diag_895_ = lean_ctor_get(v___x_890_, 4);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_925_ == 0)
{
v___x_897_ = v___x_890_;
v_isShared_898_ = v_isSharedCheck_925_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_diag_895_);
lean_inc(v_postponed_894_);
lean_inc(v_zetaDeltaFVarIds_893_);
lean_inc(v_cache_892_);
lean_inc(v_mctx_891_);
lean_dec(v___x_890_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_925_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_depth_899_; lean_object* v_levelAssignDepth_900_; lean_object* v_lmvarCounter_901_; lean_object* v_mvarCounter_902_; lean_object* v_lDecls_903_; lean_object* v_decls_904_; lean_object* v_userNames_905_; lean_object* v_lAssignment_906_; lean_object* v_eAssignment_907_; lean_object* v_dAssignment_908_; lean_object* v_instanceTypedMVars_909_; lean_object* v_synthNormMemo_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_924_; 
v_depth_899_ = lean_ctor_get(v_mctx_891_, 0);
v_levelAssignDepth_900_ = lean_ctor_get(v_mctx_891_, 1);
v_lmvarCounter_901_ = lean_ctor_get(v_mctx_891_, 2);
v_mvarCounter_902_ = lean_ctor_get(v_mctx_891_, 3);
v_lDecls_903_ = lean_ctor_get(v_mctx_891_, 4);
v_decls_904_ = lean_ctor_get(v_mctx_891_, 5);
v_userNames_905_ = lean_ctor_get(v_mctx_891_, 6);
v_lAssignment_906_ = lean_ctor_get(v_mctx_891_, 7);
v_eAssignment_907_ = lean_ctor_get(v_mctx_891_, 8);
v_dAssignment_908_ = lean_ctor_get(v_mctx_891_, 9);
v_instanceTypedMVars_909_ = lean_ctor_get(v_mctx_891_, 10);
v_synthNormMemo_910_ = lean_ctor_get(v_mctx_891_, 11);
v_isSharedCheck_924_ = !lean_is_exclusive(v_mctx_891_);
if (v_isSharedCheck_924_ == 0)
{
v___x_912_ = v_mctx_891_;
v_isShared_913_ = v_isSharedCheck_924_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_synthNormMemo_910_);
lean_inc(v_instanceTypedMVars_909_);
lean_inc(v_dAssignment_908_);
lean_inc(v_eAssignment_907_);
lean_inc(v_lAssignment_906_);
lean_inc(v_userNames_905_);
lean_inc(v_decls_904_);
lean_inc(v_lDecls_903_);
lean_inc(v_mvarCounter_902_);
lean_inc(v_lmvarCounter_901_);
lean_inc(v_levelAssignDepth_900_);
lean_inc(v_depth_899_);
lean_dec(v_mctx_891_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_924_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_914_ = lean_box(0);
v___x_915_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1___redArg(v_eAssignment_907_, v_mvarId_886_, v_val_887_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 8, v___x_915_);
v___x_917_ = v___x_912_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_depth_899_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_levelAssignDepth_900_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_lmvarCounter_901_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v_mvarCounter_902_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v_lDecls_903_);
lean_ctor_set(v_reuseFailAlloc_923_, 5, v_decls_904_);
lean_ctor_set(v_reuseFailAlloc_923_, 6, v_userNames_905_);
lean_ctor_set(v_reuseFailAlloc_923_, 7, v_lAssignment_906_);
lean_ctor_set(v_reuseFailAlloc_923_, 8, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_923_, 9, v_dAssignment_908_);
lean_ctor_set(v_reuseFailAlloc_923_, 10, v_instanceTypedMVars_909_);
lean_ctor_set(v_reuseFailAlloc_923_, 11, v_synthNormMemo_910_);
v___x_917_ = v_reuseFailAlloc_923_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_917_);
v___x_919_ = v___x_897_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_cache_892_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_zetaDeltaFVarIds_893_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_postponed_894_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_diag_895_);
v___x_919_ = v_reuseFailAlloc_922_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_st_ref_put(v___y_888_, v___x_919_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_914_);
return v___x_921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_926_, lean_object* v_val_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v_mvarId_926_, v_val_927_, v___y_928_);
lean_dec(v___y_928_);
return v_res_930_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = lean_box(0);
v___x_937_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__2));
v___x_938_ = l_Lean_mkConst(v___x_937_, v___x_936_);
return v___x_938_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__6(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = lean_box(0);
v___x_943_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__5));
v___x_944_ = l_Lean_mkConst(v___x_943_, v___x_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f(lean_object* v_goal_945_, lean_object* v_target_946_, lean_object* v_nm_947_, lean_object* v_00_u03c6_948_, lean_object* v_G_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = l_Lean_Expr_cleanupAnnotations(v_00_u03c6_948_);
v___x_966_ = l_Lean_Expr_isApp(v___x_965_);
if (v___x_966_ == 0)
{
lean_dec_ref(v___x_965_);
lean_dec_ref(v_G_949_);
lean_dec_ref(v_00_u03c6_948_);
lean_dec(v_nm_947_);
lean_dec_ref(v_target_946_);
lean_dec(v_goal_945_);
goto v___jp_962_;
}
else
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_965_);
v___x_968_ = l_Lean_Expr_isApp(v___x_967_);
if (v___x_968_ == 0)
{
lean_dec_ref(v___x_967_);
lean_dec_ref(v___x_965_);
lean_dec_ref(v_G_949_);
lean_dec_ref(v_00_u03c6_948_);
lean_dec(v_nm_947_);
lean_dec_ref(v_target_946_);
lean_dec(v_goal_945_);
goto v___jp_962_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_969_ = l_Lean_Expr_appFnCleanup___redArg(v___x_967_);
v___x_970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__1));
v___x_971_ = l_Lean_Expr_isConstOf(v___x_969_, v___x_970_);
lean_dec_ref(v___x_969_);
if (v___x_971_ == 0)
{
lean_dec_ref(v___x_967_);
lean_dec_ref(v___x_965_);
lean_dec_ref(v_G_949_);
lean_dec_ref(v_00_u03c6_948_);
lean_dec(v_nm_947_);
lean_dec_ref(v_target_946_);
lean_dec(v_goal_945_);
goto v___jp_962_;
}
else
{
lean_object* v_arg_972_; lean_object* v_arg_973_; lean_object* v___x_974_; 
v_arg_972_ = lean_ctor_get(v___x_965_, 1);
lean_inc_ref(v_arg_972_);
lean_dec_ref(v___x_965_);
v_arg_973_ = lean_ctor_get(v___x_967_, 1);
lean_inc_ref(v_arg_973_);
lean_dec_ref(v___x_967_);
lean_inc_ref(v_G_949_);
v___x_974_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_00_u03c6_948_, v_G_949_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1031_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_1031_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1031_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
uint8_t v___x_979_; 
v___x_979_ = lean_unbox(v_a_975_);
lean_dec(v_a_975_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_982_; 
lean_dec_ref(v_arg_973_);
lean_dec_ref(v_arg_972_);
lean_dec_ref(v_G_949_);
lean_dec(v_nm_947_);
lean_dec_ref(v_target_946_);
lean_dec(v_goal_945_);
v___x_980_ = lean_box(0);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_980_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
uint8_t v___x_984_; lean_object* v___x_985_; 
lean_del_object(v___x_977_);
v___x_984_ = 0;
lean_inc_ref(v_G_949_);
lean_inc_ref(v_arg_972_);
lean_inc(v_nm_947_);
v___x_985_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_nm_947_, v___x_984_, v_arg_972_, v_G_949_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
lean_inc_ref(v_arg_973_);
v___x_987_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_nm_947_, v___x_984_, v_arg_973_, v_a_986_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc_n(v_a_988_, 2);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = lean_box(0);
v___x_990_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_988_, v___x_989_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1005_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc_n(v_a_991_, 2);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3);
v___x_993_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__6, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__6_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__6);
v___x_994_ = l_Lean_mkApp3(v___x_993_, v_arg_973_, v_arg_972_, v_G_949_);
v___x_995_ = l_Lean_mkApp4(v___x_992_, v_target_946_, v_a_988_, v___x_994_, v_a_991_);
v___x_996_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v_goal_945_, v___x_995_, v_a_958_);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; 
v_unused_1006_ = lean_ctor_get(v___x_996_, 0);
lean_dec(v_unused_1006_);
v___x_998_ = v___x_996_;
v_isShared_999_ = v_isSharedCheck_1005_;
goto v_resetjp_997_;
}
else
{
lean_dec(v___x_996_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1005_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1000_ = l_Lean_Expr_mvarId_x21(v_a_991_);
lean_dec(v_a_991_);
v___x_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1001_);
v___x_1003_ = v___x_998_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_a_988_);
lean_dec_ref(v_arg_973_);
lean_dec_ref(v_arg_972_);
lean_dec_ref(v_G_949_);
lean_dec_ref(v_target_946_);
lean_dec(v_goal_945_);
v_a_1007_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_990_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_990_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v_arg_973_);
lean_dec_ref(v_arg_972_);
lean_dec_ref(v_G_949_);
lean_dec_ref(v_target_946_);
lean_dec(v_goal_945_);
v_a_1015_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_987_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_987_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_arg_973_);
lean_dec_ref(v_arg_972_);
lean_dec_ref(v_G_949_);
lean_dec(v_nm_947_);
lean_dec_ref(v_target_946_);
lean_dec(v_goal_945_);
v_a_1023_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_985_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_985_);
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
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v_arg_973_);
lean_dec_ref(v_arg_972_);
lean_dec_ref(v_G_949_);
lean_dec(v_nm_947_);
lean_dec_ref(v_target_946_);
lean_dec(v_goal_945_);
v_a_1032_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_974_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_974_);
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
}
v___jp_962_:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_box(0);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___boxed(lean_object** _args){
lean_object* v_goal_1040_ = _args[0];
lean_object* v_target_1041_ = _args[1];
lean_object* v_nm_1042_ = _args[2];
lean_object* v_00_u03c6_1043_ = _args[3];
lean_object* v_G_1044_ = _args[4];
lean_object* v_a_1045_ = _args[5];
lean_object* v_a_1046_ = _args[6];
lean_object* v_a_1047_ = _args[7];
lean_object* v_a_1048_ = _args[8];
lean_object* v_a_1049_ = _args[9];
lean_object* v_a_1050_ = _args[10];
lean_object* v_a_1051_ = _args[11];
lean_object* v_a_1052_ = _args[12];
lean_object* v_a_1053_ = _args[13];
lean_object* v_a_1054_ = _args[14];
lean_object* v_a_1055_ = _args[15];
lean_object* v_a_1056_ = _args[16];
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f(v_goal_1040_, v_target_1041_, v_nm_1042_, v_00_u03c6_1043_, v_G_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1(lean_object* v_mvarId_1058_, lean_object* v_val_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v_mvarId_1058_, v_val_1059_, v___y_1068_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___boxed(lean_object* v_mvarId_1073_, lean_object* v_val_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1(v_mvarId_1073_, v_val_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1___redArg(v_x_1089_, v_x_1090_, v_x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1093_, lean_object* v_x_1094_, size_t v_x_1095_, size_t v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(v_x_1094_, v_x_1095_, v_x_1096_, v_x_1097_, v_x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
size_t v_x_11756__boxed_1106_; size_t v_x_11757__boxed_1107_; lean_object* v_res_1108_; 
v_x_11756__boxed_1106_ = lean_unbox_usize(v_x_1102_);
lean_dec(v_x_1102_);
v_x_11757__boxed_1107_ = lean_unbox_usize(v_x_1103_);
lean_dec(v_x_1103_);
v_res_1108_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2(v_00_u03b2_1100_, v_x_1101_, v_x_11756__boxed_1106_, v_x_11757__boxed_1107_, v_x_1104_, v_x_1105_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1109_, lean_object* v_n_1110_, lean_object* v_k_1111_, lean_object* v_v_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1110_, v_k_1111_, v_v_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1114_, size_t v_depth_1115_, lean_object* v_keys_1116_, lean_object* v_vals_1117_, lean_object* v_heq_1118_, lean_object* v_i_1119_, lean_object* v_entries_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1115_, v_keys_1116_, v_vals_1117_, v_i_1119_, v_entries_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1122_, lean_object* v_depth_1123_, lean_object* v_keys_1124_, lean_object* v_vals_1125_, lean_object* v_heq_1126_, lean_object* v_i_1127_, lean_object* v_entries_1128_){
_start:
{
size_t v_depth_boxed_1129_; lean_object* v_res_1130_; 
v_depth_boxed_1129_ = lean_unbox_usize(v_depth_1123_);
lean_dec(v_depth_1123_);
v_res_1130_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1122_, v_depth_boxed_1129_, v_keys_1124_, v_vals_1125_, v_heq_1126_, v_i_1127_, v_entries_1128_);
lean_dec_ref(v_vals_1125_);
lean_dec_ref(v_keys_1124_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1132_, v_x_1133_, v_x_1134_, v_x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(lean_object* v_x_1137_, uint8_t v_bi_1138_, lean_object* v_t_1139_, lean_object* v_b_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___y_1149_; lean_object* v___x_1152_; uint8_t v_debug_1153_; 
v___x_1152_ = lean_st_ref_get(v___y_1142_);
v_debug_1153_ = lean_ctor_get_uint8(v___x_1152_, sizeof(void*)*12);
lean_dec(v___x_1152_);
if (v_debug_1153_ == 0)
{
v___y_1149_ = v___y_1142_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1139_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v___x_1155_; 
lean_dec_ref_known(v___x_1154_, 1);
v___x_1155_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_dec_ref_known(v___x_1155_, 1);
v___y_1149_ = v___y_1142_;
goto v___jp_1148_;
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec_ref(v_b_1140_);
lean_dec_ref(v_t_1139_);
lean_dec(v_x_1137_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v_b_1140_);
lean_dec_ref(v_t_1139_);
lean_dec(v_x_1137_);
v_a_1164_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1154_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1154_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
v___jp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = l_Lean_Expr_lam___override(v_x_1137_, v_t_1139_, v_b_1140_, v_bi_1138_);
v___x_1151_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1150_, v___y_1149_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg___boxed(lean_object* v_x_1172_, lean_object* v_bi_1173_, lean_object* v_t_1174_, lean_object* v_b_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_bi_boxed_1183_; lean_object* v_res_1184_; 
v_bi_boxed_1183_ = lean_unbox(v_bi_1173_);
v_res_1184_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(v_x_1172_, v_bi_boxed_1183_, v_t_1174_, v_b_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0(lean_object* v_x_1185_, uint8_t v_bi_1186_, lean_object* v_t_1187_, lean_object* v_b_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(v_x_1185_, v_bi_1186_, v_t_1187_, v_b_1188_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___boxed(lean_object* v_x_1202_, lean_object* v_bi_1203_, lean_object* v_t_1204_, lean_object* v_b_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v_bi_boxed_1218_; lean_object* v_res_1219_; 
v_bi_boxed_1218_ = lean_unbox(v_bi_1203_);
v_res_1219_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0(v_x_1202_, v_bi_boxed_1218_, v_t_1204_, v_b_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1219_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1220_; double v___x_1221_; 
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_float_of_nat(v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(lean_object* v_cls_1225_, lean_object* v_msg_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_ref_1232_; lean_object* v___x_1233_; lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1279_; 
v_ref_1232_ = lean_ctor_get(v___y_1229_, 2);
v___x_1233_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0(v_msg_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1279_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1279_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v_traceState_1239_; lean_object* v_env_1240_; lean_object* v_nextMacroScope_1241_; lean_object* v_ngen_1242_; lean_object* v_auxDeclNGen_1243_; lean_object* v_cache_1244_; lean_object* v_recordedDeps_1245_; lean_object* v_messages_1246_; lean_object* v_infoState_1247_; lean_object* v_snapshotTasks_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1278_; 
v___x_1238_ = lean_st_ref_take(v___y_1230_);
v_traceState_1239_ = lean_ctor_get(v___x_1238_, 4);
v_env_1240_ = lean_ctor_get(v___x_1238_, 0);
v_nextMacroScope_1241_ = lean_ctor_get(v___x_1238_, 1);
v_ngen_1242_ = lean_ctor_get(v___x_1238_, 2);
v_auxDeclNGen_1243_ = lean_ctor_get(v___x_1238_, 3);
v_cache_1244_ = lean_ctor_get(v___x_1238_, 5);
v_recordedDeps_1245_ = lean_ctor_get(v___x_1238_, 6);
v_messages_1246_ = lean_ctor_get(v___x_1238_, 7);
v_infoState_1247_ = lean_ctor_get(v___x_1238_, 8);
v_snapshotTasks_1248_ = lean_ctor_get(v___x_1238_, 9);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1250_ = v___x_1238_;
v_isShared_1251_ = v_isSharedCheck_1278_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snapshotTasks_1248_);
lean_inc(v_infoState_1247_);
lean_inc(v_messages_1246_);
lean_inc(v_recordedDeps_1245_);
lean_inc(v_cache_1244_);
lean_inc(v_traceState_1239_);
lean_inc(v_auxDeclNGen_1243_);
lean_inc(v_ngen_1242_);
lean_inc(v_nextMacroScope_1241_);
lean_inc(v_env_1240_);
lean_dec(v___x_1238_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1278_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
uint64_t v_tid_1252_; lean_object* v_traces_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1277_; 
v_tid_1252_ = lean_ctor_get_uint64(v_traceState_1239_, sizeof(void*)*1);
v_traces_1253_ = lean_ctor_get(v_traceState_1239_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_traceState_1239_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1255_ = v_traceState_1239_;
v_isShared_1256_ = v_isSharedCheck_1277_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_traces_1253_);
lean_dec(v_traceState_1239_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1277_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; double v___x_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_box(0);
v___x_1259_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0);
v___x_1260_ = 0;
v___x_1261_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__1));
v___x_1262_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1262_, 0, v_cls_1225_);
lean_ctor_set(v___x_1262_, 1, v___x_1258_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
lean_ctor_set_float(v___x_1262_, sizeof(void*)*3, v___x_1259_);
lean_ctor_set_float(v___x_1262_, sizeof(void*)*3 + 8, v___x_1259_);
lean_ctor_set_uint8(v___x_1262_, sizeof(void*)*3 + 16, v___x_1260_);
v___x_1263_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__2));
v___x_1264_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v_a_1234_);
lean_ctor_set(v___x_1264_, 2, v___x_1263_);
lean_inc(v_ref_1232_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v_ref_1232_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = l_Lean_PersistentArray_push___redArg(v_traces_1253_, v___x_1265_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1266_);
v___x_1268_ = v___x_1255_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1266_);
lean_ctor_set_uint64(v_reuseFailAlloc_1276_, sizeof(void*)*1, v_tid_1252_);
v___x_1268_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1270_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 4, v___x_1268_);
v___x_1270_ = v___x_1250_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_env_1240_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_nextMacroScope_1241_);
lean_ctor_set(v_reuseFailAlloc_1275_, 2, v_ngen_1242_);
lean_ctor_set(v_reuseFailAlloc_1275_, 3, v_auxDeclNGen_1243_);
lean_ctor_set(v_reuseFailAlloc_1275_, 4, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1275_, 5, v_cache_1244_);
lean_ctor_set(v_reuseFailAlloc_1275_, 6, v_recordedDeps_1245_);
lean_ctor_set(v_reuseFailAlloc_1275_, 7, v_messages_1246_);
lean_ctor_set(v_reuseFailAlloc_1275_, 8, v_infoState_1247_);
lean_ctor_set(v_reuseFailAlloc_1275_, 9, v_snapshotTasks_1248_);
v___x_1270_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_st_ref_put(v___y_1230_, v___x_1270_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1257_);
v___x_1273_ = v___x_1236_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1257_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___boxed(lean_object* v_cls_1280_, lean_object* v_msg_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(v_cls_1280_, v_msg_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1287_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8));
v___x_1308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__10));
v___x_1309_ = l_Lean_Name_append(v___x_1308_, v___x_1307_);
return v___x_1309_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__12));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__14));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f(lean_object* v_goal_1316_, lean_object* v_nm_1317_, lean_object* v_eqn_1318_, lean_object* v_G_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v___y_1333_; uint8_t v___y_1334_; lean_object* v___x_1339_; 
lean_inc_ref(v_eqn_1318_);
v___x_1339_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_eqn_1318_, v_G_1319_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1533_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1533_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1533_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
if (lean_obj_tag(v_a_1340_) == 1)
{
lean_object* v_val_1344_; lean_object* v_snd_1345_; lean_object* v_snd_1346_; lean_object* v_fst_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1527_; 
lean_del_object(v___x_1342_);
v_val_1344_ = lean_ctor_get(v_a_1340_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v_a_1340_, 1);
v_snd_1345_ = lean_ctor_get(v_val_1344_, 1);
lean_inc(v_snd_1345_);
v_snd_1346_ = lean_ctor_get(v_snd_1345_, 1);
lean_inc(v_snd_1346_);
v_fst_1347_ = lean_ctor_get(v_val_1344_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_val_1344_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v_val_1344_, 1);
lean_dec(v_unused_1528_);
v___x_1349_ = v_val_1344_;
v_isShared_1350_ = v_isSharedCheck_1527_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_fst_1347_);
lean_dec(v_val_1344_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1527_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_fst_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1525_; 
v_fst_1351_ = lean_ctor_get(v_snd_1345_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_snd_1345_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v_snd_1345_, 1);
lean_dec(v_unused_1526_);
v___x_1353_ = v_snd_1345_;
v_isShared_1354_ = v_isSharedCheck_1525_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_fst_1351_);
lean_dec(v_snd_1345_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1525_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v_fst_1355_; lean_object* v_snd_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1524_; 
v_fst_1355_ = lean_ctor_get(v_snd_1346_, 0);
v_snd_1356_ = lean_ctor_get(v_snd_1346_, 1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_snd_1346_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1358_ = v_snd_1346_;
v_isShared_1359_ = v_isSharedCheck_1524_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_snd_1356_);
lean_inc(v_fst_1355_);
lean_dec(v_snd_1346_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1524_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___y_1361_; lean_object* v___x_1366_; 
lean_inc(v_fst_1347_);
v___x_1366_ = l_Lean_Meta_Sym_inferType(v_fst_1347_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1368_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc_n(v_a_1367_, 2);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1368_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_1367_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___x_1370_ = l_Lean_Expr_fvarId_x21(v_fst_1347_);
v___x_1371_ = l_Lean_FVarId_getUserName___redArg(v___x_1370_, v_a_1327_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1373_ = 0;
lean_inc(v_fst_1355_);
lean_inc(v_a_1367_);
v___x_1374_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(v_a_1372_, v___x_1373_, v_a_1367_, v_fst_1355_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v_fst_1377_; lean_object* v_snd_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = lean_mk_empty_array_with_capacity(v___x_1425_);
lean_inc(v_fst_1351_);
v___x_1427_ = lean_array_push(v___x_1426_, v_fst_1351_);
v___x_1428_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_fst_1355_, v___x_1427_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1428_) == 0)
{
uint8_t v___x_1429_; 
v___x_1429_ = lean_unbox(v_snd_1356_);
if (v___x_1429_ == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1431_; 
v_a_1430_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1431_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_nm_1317_, v___x_1373_, v_eqn_1318_, v_a_1430_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = lean_box(0);
v___x_1434_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1432_, v___x_1433_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc_n(v_a_1435_, 2);
lean_dec_ref_known(v___x_1434_, 1);
v_fst_1377_ = v_a_1435_;
v_snd_1378_ = v_a_1435_;
v___y_1379_ = v_a_1320_;
v___y_1380_ = v_a_1321_;
v___y_1381_ = v_a_1322_;
v___y_1382_ = v_a_1323_;
v___y_1383_ = v_a_1324_;
v___y_1384_ = v_a_1325_;
v___y_1385_ = v_a_1326_;
v___y_1386_ = v_a_1327_;
v___y_1387_ = v_a_1328_;
v___y_1388_ = v_a_1329_;
v___y_1389_ = v_a_1330_;
goto v___jp_1376_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v_a_1375_);
lean_dec(v_a_1369_);
lean_dec(v_a_1367_);
lean_del_object(v___x_1358_);
lean_dec(v_snd_1356_);
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
lean_dec(v_goal_1316_);
v_a_1436_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1434_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1434_);
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
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_a_1375_);
lean_dec(v_a_1369_);
lean_dec(v_a_1367_);
lean_del_object(v___x_1358_);
lean_dec(v_snd_1356_);
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
lean_dec(v_goal_1316_);
v_a_1444_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1431_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1431_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
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
lean_object* v_a_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_a_1452_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1453_ = lean_box(0);
v___x_1454_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1452_, v___x_1453_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v___x_1456_ = l_Lean_Meta_Sym_shareCommon(v_a_1455_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_n(v_a_1457_, 2);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(v_nm_1317_, v___x_1373_, v_eqn_1318_, v_a_1457_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
v_fst_1377_ = v_a_1457_;
v_snd_1378_ = v_a_1459_;
v___y_1379_ = v_a_1320_;
v___y_1380_ = v_a_1321_;
v___y_1381_ = v_a_1322_;
v___y_1382_ = v_a_1323_;
v___y_1383_ = v_a_1324_;
v___y_1384_ = v_a_1325_;
v___y_1385_ = v_a_1326_;
v___y_1386_ = v_a_1327_;
v___y_1387_ = v_a_1328_;
v___y_1388_ = v_a_1329_;
v___y_1389_ = v_a_1330_;
goto v___jp_1376_;
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_a_1457_);
lean_dec(v_a_1375_);
lean_dec(v_a_1369_);
lean_dec(v_a_1367_);
lean_del_object(v___x_1358_);
lean_dec(v_snd_1356_);
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
lean_dec(v_goal_1316_);
v_a_1460_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1458_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1458_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_a_1375_);
lean_dec(v_a_1369_);
lean_dec(v_a_1367_);
lean_del_object(v___x_1358_);
lean_dec(v_snd_1356_);
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
lean_dec_ref(v_eqn_1318_);
lean_dec(v_nm_1317_);
lean_dec(v_goal_1316_);
v_a_1468_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1456_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1456_);
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
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec(v_a_1375_);
lean_dec(v_a_1369_);
lean_dec(v_a_1367_);
lean_del_object(v___x_1358_);
lean_dec(v_snd_1356_);
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
lean_dec_ref(v_eqn_1318_);
lean_dec(v_nm_1317_);
lean_dec(v_goal_1316_);
v_a_1476_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1454_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1454_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_a_1375_);
lean_dec(v_a_1369_);
lean_dec(v_a_1367_);
lean_del_object(v___x_1358_);
lean_dec(v_snd_1356_);
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
lean_dec_ref(v_eqn_1318_);
lean_dec(v_nm_1317_);
lean_dec(v_goal_1316_);
v_a_1484_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1428_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1428_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
v___jp_1376_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__3));
v___x_1391_ = lean_box(0);
if (v_isShared_1359_ == 0)
{
lean_ctor_set_tag(v___x_1358_, 1);
lean_ctor_set(v___x_1358_, 1, v___x_1391_);
lean_ctor_set(v___x_1358_, 0, v_a_1369_);
v___x_1393_ = v___x_1358_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1369_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_toCold_1397_; lean_object* v_options_1398_; uint8_t v_hasTrace_1399_; 
v___x_1394_ = l_Lean_mkConst(v___x_1390_, v___x_1393_);
lean_inc(v_fst_1351_);
lean_inc(v_fst_1347_);
v___x_1395_ = l_Lean_mkApp5(v___x_1394_, v_a_1367_, v_fst_1347_, v_fst_1351_, v_a_1375_, v_snd_1378_);
v___x_1396_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v_goal_1316_, v___x_1395_, v___y_1387_);
lean_dec_ref(v___x_1396_);
v_toCold_1397_ = lean_ctor_get(v___y_1388_, 0);
v_options_1398_ = lean_ctor_get(v_toCold_1397_, 2);
v_hasTrace_1399_ = lean_ctor_get_uint8(v_options_1398_, sizeof(void*)*1);
if (v_hasTrace_1399_ == 0)
{
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
v___y_1361_ = v_fst_1377_;
goto v___jp_1360_;
}
else
{
lean_object* v_inheritedTraceOptions_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_inheritedTraceOptions_1400_ = lean_ctor_get(v_toCold_1397_, 11);
v___x_1401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8));
v___x_1402_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11);
v___x_1403_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1400_, v_options_1398_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
v___y_1361_ = v_fst_1377_;
goto v___jp_1360_;
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1404_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13);
v___x_1405_ = l_Lean_MessageData_ofExpr(v_fst_1347_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 7);
lean_ctor_set(v___x_1353_, 1, v___x_1405_);
lean_ctor_set(v___x_1353_, 0, v___x_1404_);
v___x_1407_ = v___x_1353_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15);
if (v_isShared_1350_ == 0)
{
lean_ctor_set_tag(v___x_1349_, 7);
lean_ctor_set(v___x_1349_, 1, v___x_1408_);
lean_ctor_set(v___x_1349_, 0, v___x_1407_);
v___x_1410_ = v___x_1349_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = l_Lean_MessageData_ofExpr(v_fst_1351_);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(v___x_1401_, v___x_1412_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_dec_ref_known(v___x_1413_, 1);
v___y_1361_ = v_fst_1377_;
goto v___jp_1360_;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v_fst_1377_);
lean_dec(v_snd_1356_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
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
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_a_1369_);
lean_dec(v_a_1367_);
lean_del_object(v___x_1358_);
lean_dec(v_snd_1356_);
lean_dec(v_fst_1355_);
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
lean_dec_ref(v_eqn_1318_);
lean_dec(v_nm_1317_);
lean_dec(v_goal_1316_);
v_a_1492_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1374_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1374_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_a_1369_);
lean_dec(v_a_1367_);
lean_del_object(v___x_1358_);
lean_dec(v_snd_1356_);
lean_dec(v_fst_1355_);
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
lean_dec_ref(v_eqn_1318_);
lean_dec(v_nm_1317_);
lean_dec(v_goal_1316_);
v_a_1500_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1371_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1371_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_a_1367_);
lean_del_object(v___x_1358_);
lean_dec(v_snd_1356_);
lean_dec(v_fst_1355_);
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
lean_dec_ref(v_eqn_1318_);
lean_dec(v_nm_1317_);
lean_dec(v_goal_1316_);
v_a_1508_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1368_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1368_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_del_object(v___x_1358_);
lean_dec(v_snd_1356_);
lean_dec(v_fst_1355_);
lean_del_object(v___x_1353_);
lean_dec(v_fst_1351_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1347_);
lean_dec_ref(v_eqn_1318_);
lean_dec(v_nm_1317_);
lean_dec(v_goal_1316_);
v_a_1516_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1366_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1366_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
v___jp_1360_:
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = l_Lean_Expr_mvarId_x21(v___y_1361_);
lean_dec_ref(v___y_1361_);
v___x_1363_ = lean_unbox(v_snd_1356_);
lean_dec(v_snd_1356_);
if (v___x_1363_ == 0)
{
uint8_t v___x_1364_; 
v___x_1364_ = 1;
v___y_1333_ = v___x_1362_;
v___y_1334_ = v___x_1364_;
goto v___jp_1332_;
}
else
{
uint8_t v___x_1365_; 
v___x_1365_ = 0;
v___y_1333_ = v___x_1362_;
v___y_1334_ = v___x_1365_;
goto v___jp_1332_;
}
}
}
}
}
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1531_; 
lean_dec(v_a_1340_);
lean_dec_ref(v_eqn_1318_);
lean_dec(v_nm_1317_);
lean_dec(v_goal_1316_);
v___x_1529_ = lean_box(0);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1529_);
v___x_1531_ = v___x_1342_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref(v_eqn_1318_);
lean_dec(v_nm_1317_);
lean_dec(v_goal_1316_);
v_a_1534_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1339_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1339_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
v___jp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1335_ = lean_box(v___y_1334_);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___y_1333_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___boxed(lean_object* v_goal_1542_, lean_object* v_nm_1543_, lean_object* v_eqn_1544_, lean_object* v_G_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f(v_goal_1542_, v_nm_1543_, v_eqn_1544_, v_G_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
lean_dec(v_a_1548_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1(lean_object* v_cls_1559_, lean_object* v_msg_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(v_cls_1559_, v_msg_1560_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___boxed(lean_object* v_cls_1574_, lean_object* v_msg_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1(v_cls_1574_, v_msg_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0(lean_object* v_x_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; 
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1595_);
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
lean_inc(v___y_1592_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
v___x_1602_ = lean_apply_12(v_x_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, lean_box(0));
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0___boxed(lean_object* v_x_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0(v_x_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(lean_object* v_mvarId_1617_, lean_object* v_x_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___f_1631_; lean_object* v___x_1632_; 
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
lean_inc(v___y_1621_);
lean_inc(v___y_1620_);
lean_inc_ref(v___y_1619_);
v___f_1631_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1631_, 0, v_x_1618_);
lean_closure_set(v___f_1631_, 1, v___y_1619_);
lean_closure_set(v___f_1631_, 2, v___y_1620_);
lean_closure_set(v___f_1631_, 3, v___y_1621_);
lean_closure_set(v___f_1631_, 4, v___y_1622_);
lean_closure_set(v___f_1631_, 5, v___y_1623_);
lean_closure_set(v___f_1631_, 6, v___y_1624_);
lean_closure_set(v___f_1631_, 7, v___y_1625_);
v___x_1632_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1617_, v___f_1631_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1632_) == 0)
{
return v___x_1632_;
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___boxed(lean_object* v_mvarId_1641_, lean_object* v_x_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_mvarId_1641_, v_x_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0(lean_object* v_00_u03b1_1656_, lean_object* v_mvarId_1657_, lean_object* v_x_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_mvarId_1657_, v_x_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___boxed(lean_object* v_00_u03b1_1672_, lean_object* v_mvarId_1673_, lean_object* v_x_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0(v_00_u03b1_1672_, v_mvarId_1673_, v_x_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(lean_object* v___x_1688_, lean_object* v___f_1689_, lean_object* v_____r_1690_, lean_object* v_goal_1691_, lean_object* v_pending_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; 
lean_inc(v___x_1688_);
v___x_1705_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_goal_1691_, v___x_1688_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc_n(v_a_1706_, 2);
lean_dec_ref_known(v___x_1705_, 1);
v___x_1707_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_a_1706_, v___f_1689_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1732_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1732_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1732_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___y_1713_; lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_LocalContext_lastDecl(v_a_1708_);
lean_dec(v_a_1708_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_box(0);
v___y_1713_ = v___x_1722_;
goto v___jp_1712_;
}
else
{
lean_object* v_val_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1731_; 
v_val_1723_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1725_ = v___x_1721_;
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_val_1723_);
lean_dec(v___x_1721_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = l_Lean_LocalDecl_fvarId(v_val_1723_);
lean_dec(v_val_1723_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
v___y_1713_ = v___x_1729_;
goto v___jp_1712_;
}
}
}
v___jp_1712_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1714_ = lean_nat_sub(v_pending_1692_, v___x_1688_);
lean_dec(v___x_1688_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v___y_1713_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v_a_1706_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1717_);
v___x_1719_ = v___x_1710_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_a_1706_);
lean_dec(v___x_1688_);
v_a_1733_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1707_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1707_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec_ref(v___f_1689_);
lean_dec(v___x_1688_);
v_a_1741_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1705_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1705_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1749_ = _args[0];
lean_object* v___f_1750_ = _args[1];
lean_object* v_____r_1751_ = _args[2];
lean_object* v_goal_1752_ = _args[3];
lean_object* v_pending_1753_ = _args[4];
lean_object* v___y_1754_ = _args[5];
lean_object* v___y_1755_ = _args[6];
lean_object* v___y_1756_ = _args[7];
lean_object* v___y_1757_ = _args[8];
lean_object* v___y_1758_ = _args[9];
lean_object* v___y_1759_ = _args[10];
lean_object* v___y_1760_ = _args[11];
lean_object* v___y_1761_ = _args[12];
lean_object* v___y_1762_ = _args[13];
lean_object* v___y_1763_ = _args[14];
lean_object* v___y_1764_ = _args[15];
lean_object* v___y_1765_ = _args[16];
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1749_, v___f_1750_, v_____r_1751_, v_goal_1752_, v_pending_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v_pending_1753_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0(lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_lctx_1779_; lean_object* v___x_1780_; 
v_lctx_1779_ = lean_ctor_get(v___y_1774_, 2);
lean_inc_ref(v_lctx_1779_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_lctx_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0___boxed(lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0(v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
return v_res_1793_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__1));
v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(lean_object* v_a_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___y_1812_; lean_object* v_snd_1832_; lean_object* v_fst_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1942_; 
v_snd_1832_ = lean_ctor_get(v_a_1798_, 1);
v_fst_1833_ = lean_ctor_get(v_a_1798_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_a_1798_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1835_ = v_a_1798_;
v_isShared_1836_ = v_isSharedCheck_1942_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_snd_1832_);
lean_inc(v_fst_1833_);
lean_dec(v_a_1798_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1942_;
goto v_resetjp_1834_;
}
v___jp_1811_:
{
if (lean_obj_tag(v___y_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1823_; 
v_a_1813_ = lean_ctor_get(v___y_1812_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___y_1812_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1815_ = v___y_1812_;
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___y_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
if (lean_obj_tag(v_a_1813_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; 
v_a_1817_ = lean_ctor_get(v_a_1813_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v_a_1813_, 1);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v_a_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
else
{
lean_object* v_a_1821_; 
lean_del_object(v___x_1815_);
v_a_1821_ = lean_ctor_get(v_a_1813_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v_a_1813_, 1);
v_a_1798_ = v_a_1821_;
goto _start;
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___y_1812_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___y_1812_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___y_1812_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___y_1812_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
v_resetjp_1834_:
{
lean_object* v_fst_1837_; lean_object* v_snd_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1941_; 
v_fst_1837_ = lean_ctor_get(v_snd_1832_, 0);
v_snd_1838_ = lean_ctor_get(v_snd_1832_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_snd_1832_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1840_ = v_snd_1832_;
v_isShared_1841_ = v_isSharedCheck_1941_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_snd_1838_);
lean_inc(v_fst_1837_);
lean_dec(v_snd_1832_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1941_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_nat_dec_lt(v___x_1842_, v_fst_1837_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1845_; 
if (v_isShared_1841_ == 0)
{
v___x_1845_ = v___x_1840_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_fst_1837_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_snd_1838_);
v___x_1845_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 1, v___x_1845_);
v___x_1847_ = v___x_1835_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_fst_1833_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
}
else
{
lean_object* v___f_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___f_1851_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__0));
v___x_1852_ = lean_unsigned_to_nat(1u);
lean_inc(v_fst_1833_);
v___x_1853_ = l_Lean_MVarId_getType(v_fst_1833_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
if (lean_obj_tag(v_a_1854_) == 7)
{
lean_object* v_binderName_1855_; lean_object* v_binderType_1856_; lean_object* v_body_1857_; uint8_t v___x_1858_; 
v_binderName_1855_ = lean_ctor_get(v_a_1854_, 0);
lean_inc(v_binderName_1855_);
v_binderType_1856_ = lean_ctor_get(v_a_1854_, 1);
lean_inc_ref(v_binderType_1856_);
v_body_1857_ = lean_ctor_get(v_a_1854_, 2);
lean_inc_ref(v_body_1857_);
v___x_1858_ = l_Lean_Expr_hasLooseBVars(v_body_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_inc_ref(v_body_1857_);
lean_inc_ref(v_binderType_1856_);
lean_inc(v_binderName_1855_);
lean_inc_n(v_fst_1833_, 2);
v___x_1859_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___boxed), 17, 5);
lean_closure_set(v___x_1859_, 0, v_fst_1833_);
lean_closure_set(v___x_1859_, 1, v_a_1854_);
lean_closure_set(v___x_1859_, 2, v_binderName_1855_);
lean_closure_set(v___x_1859_, 3, v_binderType_1856_);
lean_closure_set(v___x_1859_, 4, v_body_1857_);
v___x_1860_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_fst_1833_, v___x_1859_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
if (lean_obj_tag(v_a_1861_) == 1)
{
lean_object* v_val_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
lean_dec_ref(v_body_1857_);
lean_dec_ref(v_binderType_1856_);
lean_dec(v_binderName_1855_);
lean_dec(v_fst_1833_);
v_val_1862_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_val_1862_);
lean_dec_ref_known(v_a_1861_, 1);
v___x_1863_ = lean_nat_add(v_fst_1837_, v___x_1852_);
lean_dec(v_fst_1837_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1863_);
v___x_1865_ = v___x_1840_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_snd_1838_);
v___x_1865_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1867_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 1, v___x_1865_);
lean_ctor_set(v___x_1835_, 0, v_val_1862_);
v___x_1867_ = v___x_1835_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_val_1862_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
v_a_1798_ = v___x_1867_;
goto _start;
}
}
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec(v_a_1861_);
lean_del_object(v___x_1835_);
lean_inc_n(v_fst_1833_, 2);
v___x_1871_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___boxed), 16, 4);
lean_closure_set(v___x_1871_, 0, v_fst_1833_);
lean_closure_set(v___x_1871_, 1, v_binderName_1855_);
lean_closure_set(v___x_1871_, 2, v_binderType_1856_);
lean_closure_set(v___x_1871_, 3, v_body_1857_);
v___x_1872_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_fst_1833_, v___x_1871_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
if (lean_obj_tag(v_a_1873_) == 1)
{
lean_object* v_val_1874_; lean_object* v_snd_1875_; uint8_t v___x_1876_; 
lean_dec(v_fst_1833_);
v_val_1874_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_val_1874_);
lean_dec_ref_known(v_a_1873_, 1);
v_snd_1875_ = lean_ctor_get(v_val_1874_, 1);
v___x_1876_ = lean_unbox(v_snd_1875_);
if (v___x_1876_ == 0)
{
lean_object* v_fst_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1889_; 
v_fst_1877_ = lean_ctor_get(v_val_1874_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_val_1874_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v_val_1874_, 1);
lean_dec(v_unused_1890_);
v___x_1879_ = v_val_1874_;
v_isShared_1880_ = v_isSharedCheck_1889_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_fst_1877_);
lean_dec(v_val_1874_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1889_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1881_ = lean_nat_sub(v_fst_1837_, v___x_1852_);
lean_dec(v_fst_1837_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v_snd_1838_);
lean_ctor_set(v___x_1879_, 0, v___x_1881_);
v___x_1883_ = v___x_1879_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_snd_1838_);
v___x_1883_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 1, v___x_1883_);
lean_ctor_set(v___x_1840_, 0, v_fst_1877_);
v___x_1885_ = v___x_1840_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_fst_1877_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
v_a_1798_ = v___x_1885_;
goto _start;
}
}
}
}
else
{
lean_object* v_fst_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_del_object(v___x_1840_);
lean_dec(v_snd_1838_);
v_fst_1891_ = lean_ctor_get(v_val_1874_, 0);
lean_inc(v_fst_1891_);
lean_dec(v_val_1874_);
v___x_1892_ = lean_box(0);
v___x_1893_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1852_, v___f_1851_, v___x_1892_, v_fst_1891_, v_fst_1837_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v_fst_1837_);
v___y_1812_ = v___x_1893_;
goto v___jp_1811_;
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec(v_a_1873_);
lean_del_object(v___x_1840_);
lean_dec(v_snd_1838_);
v___x_1894_ = lean_box(0);
v___x_1895_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1852_, v___f_1851_, v___x_1894_, v_fst_1833_, v_fst_1837_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v_fst_1837_);
v___y_1812_ = v___x_1895_;
goto v___jp_1811_;
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_del_object(v___x_1840_);
lean_dec(v_snd_1838_);
lean_dec(v_fst_1837_);
lean_dec(v_fst_1833_);
v_a_1896_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1872_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1872_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec_ref(v_body_1857_);
lean_dec_ref(v_binderType_1856_);
lean_dec(v_binderName_1855_);
lean_del_object(v___x_1840_);
lean_dec(v_snd_1838_);
lean_dec(v_fst_1837_);
lean_del_object(v___x_1835_);
lean_dec(v_fst_1833_);
v_a_1904_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1860_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1860_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_dec_ref(v_body_1857_);
lean_dec_ref(v_binderType_1856_);
lean_dec(v_binderName_1855_);
lean_dec_ref_known(v_a_1854_, 3);
lean_del_object(v___x_1840_);
lean_dec(v_snd_1838_);
lean_del_object(v___x_1835_);
v___x_1912_ = lean_box(0);
v___x_1913_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1852_, v___f_1851_, v___x_1912_, v_fst_1833_, v_fst_1837_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v_fst_1837_);
v___y_1812_ = v___x_1913_;
goto v___jp_1811_;
}
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec(v_a_1854_);
v___x_1914_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2);
lean_inc(v_fst_1833_);
v___x_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_fst_1833_);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_1916_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v___x_1919_; 
lean_dec_ref_known(v___x_1917_, 1);
if (v_isShared_1841_ == 0)
{
v___x_1919_ = v___x_1840_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_fst_1837_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_snd_1838_);
v___x_1919_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1921_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 1, v___x_1919_);
v___x_1921_ = v___x_1835_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_fst_1833_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
v_a_1798_ = v___x_1921_;
goto _start;
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_del_object(v___x_1840_);
lean_dec(v_snd_1838_);
lean_dec(v_fst_1837_);
lean_del_object(v___x_1835_);
lean_dec(v_fst_1833_);
v_a_1925_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1917_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1917_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_del_object(v___x_1840_);
lean_dec(v_snd_1838_);
lean_dec(v_fst_1837_);
lean_del_object(v___x_1835_);
lean_dec(v_fst_1833_);
v_a_1933_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1853_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1853_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___boxed(lean_object* v_a_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(v_a_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1956_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introPre___closed__1(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introPre___closed__0));
v___x_1959_ = l_Lean_stringToMessageData(v___x_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre(lean_object* v_rule_1963_, lean_object* v_goal_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_box(0);
lean_inc(v_goal_1964_);
v___x_1987_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_1963_, v_goal_1964_, v___x_1986_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
if (lean_obj_tag(v_a_1988_) == 1)
{
lean_object* v_mvarIds_1989_; 
v_mvarIds_1989_ = lean_ctor_get(v_a_1988_, 0);
lean_inc(v_mvarIds_1989_);
lean_dec_ref_known(v_a_1988_, 1);
if (lean_obj_tag(v_mvarIds_1989_) == 1)
{
lean_object* v_tail_1990_; 
v_tail_1990_ = lean_ctor_get(v_mvarIds_1989_, 1);
if (lean_obj_tag(v_tail_1990_) == 0)
{
lean_object* v_head_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_goal_1964_);
v_head_1991_ = lean_ctor_get(v_mvarIds_1989_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_mvarIds_1989_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v_mvarIds_1989_, 1);
lean_dec(v_unused_2028_);
v___x_1993_ = v_mvarIds_1989_;
v_isShared_1994_ = v_isSharedCheck_2027_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_head_1991_);
lean_dec(v_mvarIds_1989_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2027_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1995_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introPre___closed__2));
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 0);
lean_ctor_set(v___x_1993_, 1, v___x_1995_);
v___x_1997_ = v___x_1993_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_head_1991_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_2026_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; 
v___x_1998_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(v___x_1997_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2017_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2017_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2017_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_snd_2003_; lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2015_; 
v_snd_2003_ = lean_ctor_get(v_a_1999_, 1);
lean_inc(v_snd_2003_);
v_fst_2004_ = lean_ctor_get(v_a_1999_, 0);
lean_inc(v_fst_2004_);
lean_dec(v_a_1999_);
v_snd_2005_ = lean_ctor_get(v_snd_2003_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_snd_2003_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v_snd_2003_, 0);
lean_dec(v_unused_2016_);
v___x_2007_ = v_snd_2003_;
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_snd_2005_);
lean_dec(v_snd_2003_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v_fst_2004_);
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_fst_2004_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_snd_2005_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2010_);
v___x_2012_ = v___x_2001_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
v_a_2018_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_1998_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_1998_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1989_, 2);
v___y_1978_ = v_a_1972_;
v___y_1979_ = v_a_1973_;
v___y_1980_ = v_a_1974_;
v___y_1981_ = v_a_1975_;
goto v___jp_1977_;
}
}
else
{
lean_dec(v_mvarIds_1989_);
v___y_1978_ = v_a_1972_;
v___y_1979_ = v_a_1973_;
v___y_1980_ = v_a_1974_;
v___y_1981_ = v_a_1975_;
goto v___jp_1977_;
}
}
else
{
lean_dec(v_a_1988_);
v___y_1978_ = v_a_1972_;
v___y_1979_ = v_a_1973_;
v___y_1980_ = v_a_1974_;
v___y_1981_ = v_a_1975_;
goto v___jp_1977_;
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_goal_1964_);
v_a_2029_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1987_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1987_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
v___jp_1977_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1982_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introPre___closed__1, &l_Lean_Elab_Tactic_VCGen_introPre___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_introPre___closed__1);
v___x_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_goal_1964_);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_1984_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre___boxed(lean_object* v_rule_2037_, lean_object* v_goal_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Elab_Tactic_VCGen_introPre(v_rule_2037_, v_goal_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
lean_dec(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1(lean_object* v_inst_2052_, lean_object* v_a_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(v_a_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___boxed(lean_object* v_inst_2067_, lean_object* v_a_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1(v_inst_2067_, v_a_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2082_, lean_object* v_a_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___y_2092_; lean_object* v___x_2095_; uint8_t v_debug_2096_; 
v___x_2095_ = lean_st_ref_get(v___y_2085_);
v_debug_2096_ = lean_ctor_get_uint8(v___x_2095_, sizeof(void*)*12);
lean_dec(v___x_2095_);
if (v_debug_2096_ == 0)
{
v___y_2092_ = v___y_2085_;
goto v___jp_2091_;
}
else
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2082_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v___x_2098_; 
lean_dec_ref_known(v___x_2097_, 1);
v___x_2098_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_dec_ref_known(v___x_2098_, 1);
v___y_2092_ = v___y_2085_;
goto v___jp_2091_;
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref(v_a_2083_);
lean_dec_ref(v_f_2082_);
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v_a_2083_);
lean_dec_ref(v_f_2082_);
v_a_2107_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2097_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2097_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
v___jp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = l_Lean_Expr_app___override(v_f_2082_, v_a_2083_);
v___x_2094_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2093_, v___y_2092_);
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2115_, lean_object* v_a_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1___redArg(v_f_2115_, v_a_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0(lean_object* v_args_2125_, lean_object* v_endIdx_2126_, lean_object* v_b_2127_, lean_object* v_i_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_nat_dec_le(v_endIdx_2126_, v_i_2128_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = l_Lean_instInhabitedExpr;
v___x_2143_ = lean_array_get_borrowed(v___x_2142_, v_args_2125_, v_i_2128_);
lean_inc(v___x_2143_);
v___x_2144_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1___redArg(v_b_2127_, v___x_2143_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = lean_nat_add(v_i_2128_, v___x_2146_);
lean_dec(v_i_2128_);
v_b_2127_ = v_a_2145_;
v_i_2128_ = v___x_2147_;
goto _start;
}
else
{
lean_dec(v_i_2128_);
return v___x_2144_;
}
}
else
{
lean_object* v___x_2149_; 
lean_dec(v_i_2128_);
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v_b_2127_);
return v___x_2149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0___boxed(lean_object* v_args_2150_, lean_object* v_endIdx_2151_, lean_object* v_b_2152_, lean_object* v_i_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0(v_args_2150_, v_endIdx_2151_, v_b_2152_, v_i_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v_endIdx_2151_);
lean_dec_ref(v_args_2150_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0(lean_object* v_f_2167_, lean_object* v_args_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = lean_array_get_size(v_args_2168_);
v___x_2183_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0(v_args_2168_, v___x_2182_, v_f_2167_, v___x_2181_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0___boxed(lean_object* v_f_2184_, lean_object* v_args_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0(v_f_2184_, v_args_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec_ref(v_args_2185_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f(lean_object* v_goal_2204_, lean_object* v_target_2205_, lean_object* v_00_u03b1_2206_, lean_object* v_inst_2207_, lean_object* v_pre_2208_, lean_object* v_rhs_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2222_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___closed__2));
v___x_2223_ = l_Lean_Expr_isAppOf(v_rhs_2209_, v___x_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec_ref(v_rhs_2209_);
lean_dec_ref(v_pre_2208_);
lean_dec_ref(v_inst_2207_);
lean_dec_ref(v_00_u03b1_2206_);
lean_dec(v_goal_2204_);
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
return v___x_2225_;
}
else
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_Elab_Tactic_VCGen_reduceHead_x3f(v_rhs_2209_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2277_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2277_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2277_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
if (lean_obj_tag(v_a_2227_) == 1)
{
lean_object* v_val_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2272_; 
lean_del_object(v___x_2229_);
v_val_2231_ = lean_ctor_get(v_a_2227_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_a_2227_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2233_ = v_a_2227_;
v_isShared_2234_ = v_isSharedCheck_2272_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_val_2231_);
lean_dec(v_a_2227_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2272_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2235_ = l_Lean_Expr_getAppFn(v_target_2205_);
v___x_2236_ = lean_unsigned_to_nat(4u);
v___x_2237_ = lean_mk_empty_array_with_capacity(v___x_2236_);
v___x_2238_ = lean_array_push(v___x_2237_, v_00_u03b1_2206_);
v___x_2239_ = lean_array_push(v___x_2238_, v_inst_2207_);
v___x_2240_ = lean_array_push(v___x_2239_, v_pre_2208_);
v___x_2241_ = lean_array_push(v___x_2240_, v_val_2231_);
v___x_2242_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0(v___x_2235_, v___x_2241_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec_ref(v___x_2241_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2244_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v___x_2242_, 1);
v___x_2244_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2204_, v_a_2243_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2255_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2255_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2255_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v_a_2245_);
v___x_2250_ = v___x_2233_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2252_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2250_);
v___x_2252_ = v___x_2247_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_del_object(v___x_2233_);
v_a_2256_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2244_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2244_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_del_object(v___x_2233_);
lean_dec(v_goal_2204_);
v_a_2264_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2242_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2242_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2275_; 
lean_dec(v_a_2227_);
lean_dec_ref(v_pre_2208_);
lean_dec_ref(v_inst_2207_);
lean_dec_ref(v_00_u03b1_2206_);
lean_dec(v_goal_2204_);
v___x_2273_ = lean_box(0);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2273_);
v___x_2275_ = v___x_2229_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v_pre_2208_);
lean_dec_ref(v_inst_2207_);
lean_dec_ref(v_00_u03b1_2206_);
lean_dec(v_goal_2204_);
v_a_2278_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2226_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2226_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f___boxed(lean_object** _args){
lean_object* v_goal_2286_ = _args[0];
lean_object* v_target_2287_ = _args[1];
lean_object* v_00_u03b1_2288_ = _args[2];
lean_object* v_inst_2289_ = _args[3];
lean_object* v_pre_2290_ = _args[4];
lean_object* v_rhs_2291_ = _args[5];
lean_object* v_a_2292_ = _args[6];
lean_object* v_a_2293_ = _args[7];
lean_object* v_a_2294_ = _args[8];
lean_object* v_a_2295_ = _args[9];
lean_object* v_a_2296_ = _args[10];
lean_object* v_a_2297_ = _args[11];
lean_object* v_a_2298_ = _args[12];
lean_object* v_a_2299_ = _args[13];
lean_object* v_a_2300_ = _args[14];
lean_object* v_a_2301_ = _args[15];
lean_object* v_a_2302_ = _args[16];
lean_object* v_a_2303_ = _args[17];
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f(v_goal_2286_, v_target_2287_, v_00_u03b1_2288_, v_inst_2289_, v_pre_2290_, v_rhs_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec_ref(v_target_2287_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1(lean_object* v_f_2305_, lean_object* v_a_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1___redArg(v_f_2305_, v_a_2306_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2320_, lean_object* v_a_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00Lean_Elab_Tactic_VCGen_headReduceFstRhs_x3f_spec__0_spec__0_spec__1(v_f_2320_, v_a_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2334_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_2353_; lean_object* v_dummy_2354_; 
v___x_2353_ = lean_box(0);
v_dummy_2354_ = l_Lean_Expr_sort___override(v___x_2353_);
return v_dummy_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(lean_object* v_goal_2355_, lean_object* v_x_2356_, lean_object* v_x_2357_, lean_object* v_x_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
if (lean_obj_tag(v_x_2356_) == 5)
{
lean_object* v_fn_2364_; lean_object* v_arg_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_fn_2364_ = lean_ctor_get(v_x_2356_, 0);
lean_inc_ref(v_fn_2364_);
v_arg_2365_ = lean_ctor_get(v_x_2356_, 1);
lean_inc_ref(v_arg_2365_);
lean_dec_ref_known(v_x_2356_, 2);
v___x_2366_ = lean_array_set(v_x_2357_, v_x_2358_, v_arg_2365_);
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = lean_nat_sub(v_x_2358_, v___x_2367_);
lean_dec(v_x_2358_);
v_x_2356_ = v_fn_2364_;
v_x_2357_ = v___x_2366_;
v_x_2358_ = v___x_2368_;
goto _start;
}
else
{
lean_object* v___x_2370_; uint8_t v___x_2371_; 
lean_dec(v_x_2358_);
v___x_2370_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__3));
v___x_2371_ = l_Lean_Expr_isConstOf(v_x_2356_, v___x_2370_);
lean_dec_ref(v_x_2356_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
lean_dec_ref(v_x_2357_);
lean_dec(v_goal_2355_);
v___x_2372_ = lean_box(0);
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
return v___x_2373_;
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; 
v___x_2374_ = lean_unsigned_to_nat(2u);
v___x_2375_ = lean_array_get_size(v_x_2357_);
v___x_2376_ = lean_nat_dec_lt(v___x_2374_, v___x_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec_ref(v_x_2357_);
lean_dec(v_goal_2355_);
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2379_ = lean_array_fget_borrowed(v_x_2357_, v___x_2374_);
v___x_2380_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__5));
v___x_2381_ = l_Lean_Expr_isAppOf(v___x_2379_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec_ref(v_x_2357_);
lean_dec(v_goal_2355_);
v___x_2382_ = lean_box(0);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
else
{
lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = lean_unsigned_to_nat(3u);
v___x_2385_ = lean_nat_dec_lt(v___x_2384_, v___x_2375_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
lean_dec_ref(v_x_2357_);
lean_dec(v_goal_2355_);
v___x_2386_ = lean_box(0);
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2388_ = lean_array_fget_borrowed(v_x_2357_, v___x_2384_);
v___x_2389_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__7));
v___x_2390_ = l_Lean_Expr_appArg_x21(v___x_2379_);
v___x_2391_ = lean_mk_empty_array_with_capacity(v___x_2374_);
v___x_2392_ = lean_array_push(v___x_2391_, v___x_2390_);
lean_inc(v___x_2388_);
v___x_2393_ = lean_array_push(v___x_2392_, v___x_2388_);
v___x_2394_ = l_Lean_Meta_mkAppM(v___x_2389_, v___x_2393_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v___x_2396_ = lean_unsigned_to_nat(4u);
v___x_2397_ = l_Array_extract___redArg(v_x_2357_, v___x_2396_, v___x_2375_);
lean_dec_ref(v_x_2357_);
v___x_2398_ = l_Lean_mkAppN(v_a_2395_, v___x_2397_);
lean_dec_ref(v___x_2397_);
lean_inc(v_goal_2355_);
v___x_2399_ = l_Lean_MVarId_getType(v_goal_2355_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2401_; lean_object* v_dummy_2402_; lean_object* v_nargs_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v___x_2401_ = l_Lean_Expr_getAppFn(v_a_2400_);
v_dummy_2402_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8);
v_nargs_2403_ = l_Lean_Expr_getAppNumArgs(v_a_2400_);
lean_inc(v_nargs_2403_);
v___x_2404_ = lean_mk_array(v_nargs_2403_, v_dummy_2402_);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_nat_sub(v_nargs_2403_, v___x_2405_);
lean_dec(v_nargs_2403_);
v___x_2407_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2400_, v___x_2404_, v___x_2406_);
lean_inc_ref(v___x_2398_);
v___x_2408_ = lean_array_set(v___x_2407_, v___x_2384_, v___x_2398_);
v___x_2409_ = l_Lean_mkAppN(v___x_2401_, v___x_2408_);
lean_dec_ref(v___x_2408_);
v___x_2410_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2355_, v___x_2409_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2420_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2420_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2420_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v_a_2411_);
lean_ctor_set(v___x_2415_, 1, v___x_2398_);
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2416_);
v___x_2418_ = v___x_2413_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec_ref(v___x_2398_);
v_a_2421_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2410_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2410_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
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
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec_ref(v___x_2398_);
lean_dec(v_goal_2355_);
v_a_2429_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2399_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2399_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec_ref(v_x_2357_);
lean_dec(v_goal_2355_);
v_a_2437_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2394_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2394_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___boxed(lean_object* v_goal_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_, lean_object* v_x_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v_goal_2445_, v_x_2446_, v_x_2447_, v_x_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(lean_object* v_goal_2455_, lean_object* v_rhs_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_dummy_2469_; lean_object* v_nargs_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_dummy_2469_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8);
v_nargs_2470_ = l_Lean_Expr_getAppNumArgs(v_rhs_2456_);
lean_inc(v_nargs_2470_);
v___x_2471_ = lean_mk_array(v_nargs_2470_, v_dummy_2469_);
v___x_2472_ = lean_unsigned_to_nat(1u);
v___x_2473_ = lean_nat_sub(v_nargs_2470_, v___x_2472_);
lean_dec(v_nargs_2470_);
v___x_2474_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v_goal_2455_, v_rhs_2456_, v___x_2471_, v___x_2473_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f___boxed(lean_object* v_goal_2475_, lean_object* v_rhs_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(v_goal_2475_, v_rhs_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0(lean_object* v_goal_2490_, lean_object* v_x_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v_goal_2490_, v_x_2491_, v_x_2492_, v_x_2493_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___boxed(lean_object* v_goal_2507_, lean_object* v_x_2508_, lean_object* v_x_2509_, lean_object* v_x_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0(v_goal_2507_, v_x_2508_, v_x_2509_, v_x_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(lean_object* v_a_2524_, lean_object* v_x_2525_){
_start:
{
if (lean_obj_tag(v_x_2525_) == 0)
{
lean_object* v___x_2526_; 
v___x_2526_ = lean_box(0);
return v___x_2526_;
}
else
{
lean_object* v_key_2527_; lean_object* v_value_2528_; lean_object* v_tail_2529_; uint8_t v___x_2530_; 
v_key_2527_ = lean_ctor_get(v_x_2525_, 0);
v_value_2528_ = lean_ctor_get(v_x_2525_, 1);
v_tail_2529_ = lean_ctor_get(v_x_2525_, 2);
v___x_2530_ = lean_name_eq(v_key_2527_, v_a_2524_);
if (v___x_2530_ == 0)
{
v_x_2525_ = v_tail_2529_;
goto _start;
}
else
{
lean_object* v___x_2532_; 
lean_inc(v_value_2528_);
v___x_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_value_2528_);
return v___x_2532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_2533_, lean_object* v_x_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_2533_, v_x_2534_);
lean_dec(v_x_2534_);
lean_dec(v_a_2533_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(lean_object* v_m_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_buckets_2538_; lean_object* v___x_2539_; uint64_t v___y_2541_; 
v_buckets_2538_ = lean_ctor_get(v_m_2536_, 1);
v___x_2539_ = lean_array_get_size(v_buckets_2538_);
if (lean_obj_tag(v_a_2537_) == 0)
{
uint64_t v___x_2555_; 
v___x_2555_ = 1723ULL;
v___y_2541_ = v___x_2555_;
goto v___jp_2540_;
}
else
{
uint64_t v_hash_2556_; 
v_hash_2556_ = lean_ctor_get_uint64(v_a_2537_, sizeof(void*)*2);
v___y_2541_ = v_hash_2556_;
goto v___jp_2540_;
}
v___jp_2540_:
{
uint64_t v___x_2542_; uint64_t v___x_2543_; uint64_t v_fold_2544_; uint64_t v___x_2545_; uint64_t v___x_2546_; uint64_t v___x_2547_; size_t v___x_2548_; size_t v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; size_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2542_ = 32ULL;
v___x_2543_ = lean_uint64_shift_right(v___y_2541_, v___x_2542_);
v_fold_2544_ = lean_uint64_xor(v___y_2541_, v___x_2543_);
v___x_2545_ = 16ULL;
v___x_2546_ = lean_uint64_shift_right(v_fold_2544_, v___x_2545_);
v___x_2547_ = lean_uint64_xor(v_fold_2544_, v___x_2546_);
v___x_2548_ = lean_uint64_to_usize(v___x_2547_);
v___x_2549_ = lean_usize_of_nat(v___x_2539_);
v___x_2550_ = ((size_t)1ULL);
v___x_2551_ = lean_usize_sub(v___x_2549_, v___x_2550_);
v___x_2552_ = lean_usize_land(v___x_2548_, v___x_2551_);
v___x_2553_ = lean_array_uget_borrowed(v_buckets_2538_, v___x_2552_);
v___x_2554_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_2537_, v___x_2553_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg___boxed(lean_object* v_m_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v_m_2557_, v_a_2558_);
lean_dec(v_a_2558_);
lean_dec_ref(v_m_2557_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(lean_object* v_goal_2560_, lean_object* v_rhs_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v___x_2574_; 
lean_inc_ref(v_rhs_2561_);
lean_inc(v_goal_2560_);
v___x_2574_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(v_goal_2560_, v_rhs_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2645_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2645_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2645_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v_fst_2580_; lean_object* v_snd_2581_; 
if (lean_obj_tag(v_a_2575_) == 0)
{
v_fst_2580_ = v_goal_2560_;
v_snd_2581_ = v_rhs_2561_;
goto v___jp_2579_;
}
else
{
lean_object* v_val_2642_; lean_object* v_fst_2643_; lean_object* v_snd_2644_; 
lean_dec_ref(v_rhs_2561_);
lean_dec(v_goal_2560_);
v_val_2642_ = lean_ctor_get(v_a_2575_, 0);
lean_inc(v_val_2642_);
lean_dec_ref_known(v_a_2575_, 1);
v_fst_2643_ = lean_ctor_get(v_val_2642_, 0);
lean_inc(v_fst_2643_);
v_snd_2644_ = lean_ctor_get(v_val_2642_, 1);
lean_inc(v_snd_2644_);
lean_dec(v_val_2642_);
v_fst_2580_ = v_fst_2643_;
v_snd_2581_ = v_snd_2644_;
goto v___jp_2579_;
}
v___jp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = l_Lean_Expr_getAppFn(v_snd_2581_);
v___x_2583_ = l_Lean_Expr_constName_x3f(v___x_2582_);
lean_dec_ref(v___x_2582_);
if (lean_obj_tag(v___x_2583_) == 1)
{
lean_object* v_val_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_val_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_val_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v___x_2585_ = l_Lean_Elab_Tactic_VCGen_latticeOps;
v___x_2586_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v___x_2585_, v_val_2584_);
lean_dec(v_val_2584_);
if (lean_obj_tag(v___x_2586_) == 1)
{
lean_object* v_val_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2633_; 
v_val_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2633_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_val_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2633_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_applies_x3f_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v_applies_x3f_2591_ = lean_ctor_get(v_val_2587_, 4);
lean_inc_ref(v_applies_x3f_2591_);
lean_inc_ref(v_snd_2581_);
v___x_2592_ = lean_apply_1(v_applies_x3f_2591_, v_snd_2581_);
v___x_2593_ = lean_unbox(v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
lean_del_object(v___x_2589_);
lean_dec(v_val_2587_);
lean_dec_ref(v_snd_2581_);
lean_dec(v_fst_2580_);
v___x_2594_ = lean_box(0);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2594_);
v___x_2596_ = v___x_2577_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
else
{
lean_object* v___x_2598_; 
lean_del_object(v___x_2577_);
v___x_2598_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_snd_2581_, v_val_2587_, v_a_2563_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v___x_2600_ = lean_box(0);
v___x_2601_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_2599_, v_fst_2580_, v___x_2600_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2616_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2616_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2616_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
if (lean_obj_tag(v_a_2602_) == 0)
{
lean_object* v___x_2607_; 
lean_del_object(v___x_2589_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2600_);
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2600_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
else
{
lean_object* v_mvarIds_2609_; lean_object* v___x_2611_; 
v_mvarIds_2609_ = lean_ctor_get(v_a_2602_, 0);
lean_inc(v_mvarIds_2609_);
lean_dec_ref_known(v_a_2602_, 1);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v_mvarIds_2609_);
v___x_2611_ = v___x_2589_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_mvarIds_2609_);
v___x_2611_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2613_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2611_);
v___x_2613_ = v___x_2604_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2611_);
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
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_del_object(v___x_2589_);
v_a_2617_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2601_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2601_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_del_object(v___x_2589_);
lean_dec(v_fst_2580_);
v_a_2625_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2598_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2598_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
lean_dec(v___x_2586_);
lean_dec_ref(v_snd_2581_);
lean_dec(v_fst_2580_);
v___x_2634_ = lean_box(0);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2634_);
v___x_2636_ = v___x_2577_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
lean_dec(v___x_2583_);
lean_dec_ref(v_snd_2581_);
lean_dec(v_fst_2580_);
v___x_2638_ = lean_box(0);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2638_);
v___x_2640_ = v___x_2577_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec_ref(v_rhs_2561_);
lean_dec(v_goal_2560_);
v_a_2646_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2574_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2574_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f___boxed(lean_object* v_goal_2654_, lean_object* v_rhs_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(v_goal_2654_, v_rhs_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0(lean_object* v_00_u03b2_2669_, lean_object* v_m_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v_m_2670_, v_a_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___boxed(lean_object* v_00_u03b2_2673_, lean_object* v_m_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0(v_00_u03b2_2673_, v_m_2674_, v_a_2675_);
lean_dec(v_a_2675_);
lean_dec_ref(v_m_2674_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2677_, lean_object* v_a_2678_, lean_object* v_x_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_2678_, v_x_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2681_, lean_object* v_a_2682_, lean_object* v_x_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0(v_00_u03b2_2681_, v_a_2682_, v_x_2683_);
lean_dec(v_x_2683_);
lean_dec(v_a_2682_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(lean_object* v_goal_2685_, lean_object* v_rhs_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = l_Lean_Expr_isForall(v_rhs_2686_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_dec(v_goal_2685_);
v___x_2700_ = lean_box(0);
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
else
{
lean_object* v_backwardRules_2702_; lean_object* v_forallIntro_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_backwardRules_2702_ = lean_ctor_get(v_a_2687_, 0);
v_forallIntro_2703_ = lean_ctor_get(v_backwardRules_2702_, 11);
v___x_2704_ = lean_box(0);
lean_inc_ref(v_forallIntro_2703_);
v___x_2705_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_forallIntro_2703_, v_goal_2685_, v___x_2704_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2724_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2708_ = v___x_2705_;
v_isShared_2709_ = v_isSharedCheck_2724_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2724_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
if (lean_obj_tag(v_a_2706_) == 0)
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v___x_2704_);
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2704_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
else
{
lean_object* v_mvarIds_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2723_; 
v_mvarIds_2713_ = lean_ctor_get(v_a_2706_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_a_2706_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2715_ = v_a_2706_;
v_isShared_2716_ = v_isSharedCheck_2723_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_mvarIds_2713_);
lean_dec(v_a_2706_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2723_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_mvarIds_2713_);
v___x_2718_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2720_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v___x_2718_);
v___x_2720_ = v___x_2708_;
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
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
v_a_2725_ = lean_ctor_get(v___x_2705_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2705_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2705_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f___boxed(lean_object* v_goal_2733_, lean_object* v_rhs_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(v_goal_2733_, v_rhs_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_a_2739_);
lean_dec_ref(v_a_2738_);
lean_dec(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec_ref(v_rhs_2734_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(lean_object* v_as_2770_, size_t v_sz_2771_, size_t v_i_2772_, lean_object* v_b_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_usize_dec_lt(v_i_2772_, v_sz_2771_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2782_, 0, v_b_2773_);
return v___x_2782_;
}
else
{
lean_object* v_snd_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_3027_; 
v_snd_2783_ = lean_ctor_get(v_b_2773_, 1);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_b_2773_);
if (v_isSharedCheck_3027_ == 0)
{
lean_object* v_unused_3028_; 
v_unused_3028_ = lean_ctor_get(v_b_2773_, 0);
lean_dec(v_unused_3028_);
v___x_2785_ = v_b_2773_;
v_isShared_2786_ = v_isSharedCheck_3027_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_snd_2783_);
lean_dec(v_b_2773_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_3027_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v_snd_2787_; lean_object* v_snd_2788_; lean_object* v_snd_2789_; lean_object* v_fst_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_3025_; 
v_snd_2787_ = lean_ctor_get(v_snd_2783_, 1);
lean_inc(v_snd_2787_);
v_snd_2788_ = lean_ctor_get(v_snd_2787_, 1);
lean_inc(v_snd_2788_);
v_snd_2789_ = lean_ctor_get(v_snd_2788_, 1);
lean_inc(v_snd_2789_);
v_fst_2790_ = lean_ctor_get(v_snd_2783_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_snd_2783_);
if (v_isSharedCheck_3025_ == 0)
{
lean_object* v_unused_3026_; 
v_unused_3026_ = lean_ctor_get(v_snd_2783_, 1);
lean_dec(v_unused_3026_);
v___x_2792_ = v_snd_2783_;
v_isShared_2793_ = v_isSharedCheck_3025_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_fst_2790_);
lean_dec(v_snd_2783_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_3025_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v_fst_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_3023_; 
v_fst_2794_ = lean_ctor_get(v_snd_2787_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_snd_2787_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; 
v_unused_3024_ = lean_ctor_get(v_snd_2787_, 1);
lean_dec(v_unused_3024_);
v___x_2796_ = v_snd_2787_;
v_isShared_2797_ = v_isSharedCheck_3023_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_fst_2794_);
lean_dec(v_snd_2787_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_3023_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v_fst_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_3021_; 
v_fst_2798_ = lean_ctor_get(v_snd_2788_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_snd_2788_);
if (v_isSharedCheck_3021_ == 0)
{
lean_object* v_unused_3022_; 
v_unused_3022_ = lean_ctor_get(v_snd_2788_, 1);
lean_dec(v_unused_3022_);
v___x_2800_ = v_snd_2788_;
v_isShared_2801_ = v_isSharedCheck_3021_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_fst_2798_);
lean_dec(v_snd_2788_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_3021_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v_fst_2802_; lean_object* v_snd_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_3020_; 
v_fst_2802_ = lean_ctor_get(v_snd_2789_, 0);
v_snd_2803_ = lean_ctor_get(v_snd_2789_, 1);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_snd_2789_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_2805_ = v_snd_2789_;
v_isShared_2806_ = v_isSharedCheck_3020_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_snd_2803_);
lean_inc(v_fst_2802_);
lean_dec(v_snd_2789_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_3020_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v_a_2809_; lean_object* v___x_2810_; 
v___x_2807_ = lean_box(0);
v___x_2808_ = lean_box(0);
v_a_2809_ = lean_array_uget_borrowed(v_as_2770_, v_i_2772_);
lean_inc(v_fst_2802_);
v___x_2810_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_fst_2802_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_3011_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_3011_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_3011_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
if (lean_obj_tag(v_a_2811_) == 7)
{
lean_object* v_binderType_2815_; lean_object* v_body_2816_; uint8_t v___x_2817_; 
v_binderType_2815_ = lean_ctor_get(v_a_2811_, 1);
lean_inc_ref(v_binderType_2815_);
v_body_2816_ = lean_ctor_get(v_a_2811_, 2);
lean_inc_ref(v_body_2816_);
lean_dec_ref_known(v_a_2811_, 3);
v___x_2817_ = l_Lean_Expr_hasLooseBVars(v_body_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1));
v___x_2819_ = l_Lean_Expr_isAppOf(v_snd_2803_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; lean_object* v___x_2822_; 
lean_dec_ref(v_body_2816_);
lean_dec_ref(v_binderType_2815_);
v___x_2820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2806_ == 0)
{
v___x_2822_ = v___x_2805_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_fst_2802_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_snd_2803_);
v___x_2822_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2824_; 
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 1, v___x_2822_);
v___x_2824_ = v___x_2800_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_fst_2798_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2826_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v___x_2824_);
v___x_2826_ = v___x_2796_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_fst_2794_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2828_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2826_);
v___x_2828_ = v___x_2792_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_fst_2790_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 1, v___x_2828_);
lean_ctor_set(v___x_2785_, 0, v___x_2820_);
v___x_2830_ = v___x_2785_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2832_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2830_);
v___x_2832_ = v___x_2813_;
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
}
}
}
else
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_Expr_appArg_x21(v_snd_2803_);
if (lean_obj_tag(v___x_2839_) == 6)
{
lean_object* v_body_2840_; lean_object* v___x_2841_; 
lean_del_object(v___x_2813_);
v_body_2840_ = lean_ctor_get(v___x_2839_, 2);
lean_inc_ref(v_body_2840_);
lean_dec_ref_known(v___x_2839_, 3);
lean_inc_ref(v_binderType_2815_);
v___x_2841_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2815_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2843_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
lean_inc_ref(v_body_2816_);
v___x_2843_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2816_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2845_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
lean_inc(v_a_2842_);
v___x_2845_ = l_Lean_Meta_decLevel(v_a_2842_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2847_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2845_, 1);
lean_inc(v_a_2844_);
v___x_2847_ = l_Lean_Meta_decLevel(v_a_2844_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
v___x_2849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4));
v___x_2850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2850_, 0, v_a_2848_);
lean_ctor_set(v___x_2850_, 1, v___x_2807_);
v___x_2851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2851_, 0, v_a_2846_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = l_Lean_mkConst(v___x_2849_, v___x_2851_);
lean_inc(v_a_2809_);
lean_inc_ref(v_body_2840_);
lean_inc_ref(v_body_2816_);
lean_inc_ref(v_binderType_2815_);
v___x_2853_ = l_Lean_mkApp4(v___x_2852_, v_binderType_2815_, v_body_2816_, v_body_2840_, v_a_2809_);
lean_inc_ref(v___x_2853_);
v___x_2854_ = l_Lean_Meta_Sym_inferType(v___x_2853_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2913_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2913_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2913_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2859_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1));
v___x_2860_ = lean_unsigned_to_nat(3u);
v___x_2861_ = l_Lean_Expr_isAppOfArity(v_a_2855_, v___x_2859_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
lean_dec(v_a_2855_);
lean_dec_ref(v___x_2853_);
lean_dec(v_a_2844_);
lean_dec(v_a_2842_);
lean_dec_ref(v_body_2840_);
lean_dec_ref(v_body_2816_);
lean_dec_ref(v_binderType_2815_);
v___x_2862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2806_ == 0)
{
v___x_2864_ = v___x_2805_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_fst_2802_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_snd_2803_);
v___x_2864_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2866_; 
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 1, v___x_2864_);
v___x_2866_ = v___x_2800_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_fst_2798_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2868_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v___x_2866_);
v___x_2868_ = v___x_2796_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_fst_2794_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2870_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2868_);
v___x_2870_ = v___x_2792_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_fst_2790_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2872_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 1, v___x_2870_);
lean_ctor_set(v___x_2785_, 0, v___x_2862_);
v___x_2872_ = v___x_2785_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2874_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2872_);
v___x_2874_ = v___x_2857_;
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
}
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
lean_del_object(v___x_2857_);
lean_dec(v_snd_2803_);
lean_dec(v_fst_2802_);
v___x_2881_ = l_Lean_Expr_appArg_x21(v_a_2855_);
lean_dec(v_a_2855_);
v___x_2882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6));
v___x_2883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_a_2844_);
lean_ctor_set(v___x_2883_, 1, v___x_2807_);
lean_inc_ref(v___x_2883_);
v___x_2884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2884_, 0, v_a_2842_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = l_Lean_mkConst(v___x_2882_, v___x_2884_);
v___x_2886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8));
v___x_2887_ = 0;
lean_inc_ref_n(v_body_2816_, 2);
lean_inc_ref(v_binderType_2815_);
v___x_2888_ = l_Lean_Expr_lam___override(v___x_2886_, v_binderType_2815_, v_body_2816_, v___x_2887_);
lean_inc_n(v_a_2809_, 3);
lean_inc(v_fst_2798_);
lean_inc(v_fst_2794_);
v___x_2889_ = l_Lean_mkApp6(v___x_2885_, v_binderType_2815_, v___x_2888_, v_fst_2794_, v_fst_2798_, v_fst_2790_, v_a_2809_);
v___x_2890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10));
v___x_2891_ = l_Lean_mkConst(v___x_2890_, v___x_2883_);
v___x_2892_ = l_Lean_Expr_app___override(v_fst_2794_, v_a_2809_);
v___x_2893_ = l_Lean_Expr_app___override(v_fst_2798_, v_a_2809_);
lean_inc_ref(v___x_2881_);
lean_inc_ref(v___x_2892_);
v___x_2894_ = l_Lean_mkApp6(v___x_2891_, v_body_2816_, v___x_2892_, v___x_2893_, v___x_2881_, v___x_2889_, v___x_2853_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 1, v_body_2840_);
lean_ctor_set(v___x_2805_, 0, v_body_2816_);
v___x_2896_ = v___x_2805_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_body_2816_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_body_2840_);
v___x_2896_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2898_; 
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 1, v___x_2896_);
lean_ctor_set(v___x_2800_, 0, v___x_2881_);
v___x_2898_ = v___x_2800_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2900_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v___x_2898_);
lean_ctor_set(v___x_2796_, 0, v___x_2892_);
v___x_2900_ = v___x_2796_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2892_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2902_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2900_);
lean_ctor_set(v___x_2792_, 0, v___x_2894_);
v___x_2902_ = v___x_2792_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2904_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 1, v___x_2902_);
lean_ctor_set(v___x_2785_, 0, v___x_2808_);
v___x_2904_ = v___x_2785_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2808_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
size_t v___x_2905_; size_t v___x_2906_; 
v___x_2905_ = ((size_t)1ULL);
v___x_2906_ = lean_usize_add(v_i_2772_, v___x_2905_);
v_i_2772_ = v___x_2906_;
v_b_2773_ = v___x_2904_;
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
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v___x_2853_);
lean_dec(v_a_2844_);
lean_dec(v_a_2842_);
lean_dec_ref(v_body_2840_);
lean_dec_ref(v_body_2816_);
lean_dec_ref(v_binderType_2815_);
lean_del_object(v___x_2805_);
lean_dec(v_snd_2803_);
lean_dec(v_fst_2802_);
lean_del_object(v___x_2800_);
lean_dec(v_fst_2798_);
lean_del_object(v___x_2796_);
lean_dec(v_fst_2794_);
lean_del_object(v___x_2792_);
lean_dec(v_fst_2790_);
lean_del_object(v___x_2785_);
v_a_2914_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2854_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2854_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
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
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_a_2846_);
lean_dec(v_a_2844_);
lean_dec(v_a_2842_);
lean_dec_ref(v_body_2840_);
lean_dec_ref(v_body_2816_);
lean_dec_ref(v_binderType_2815_);
lean_del_object(v___x_2805_);
lean_dec(v_snd_2803_);
lean_dec(v_fst_2802_);
lean_del_object(v___x_2800_);
lean_dec(v_fst_2798_);
lean_del_object(v___x_2796_);
lean_dec(v_fst_2794_);
lean_del_object(v___x_2792_);
lean_dec(v_fst_2790_);
lean_del_object(v___x_2785_);
v_a_2922_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2847_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2847_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_a_2844_);
lean_dec(v_a_2842_);
lean_dec_ref(v_body_2840_);
lean_dec_ref(v_body_2816_);
lean_dec_ref(v_binderType_2815_);
lean_del_object(v___x_2805_);
lean_dec(v_snd_2803_);
lean_dec(v_fst_2802_);
lean_del_object(v___x_2800_);
lean_dec(v_fst_2798_);
lean_del_object(v___x_2796_);
lean_dec(v_fst_2794_);
lean_del_object(v___x_2792_);
lean_dec(v_fst_2790_);
lean_del_object(v___x_2785_);
v_a_2930_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2845_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2845_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v_a_2842_);
lean_dec_ref(v_body_2840_);
lean_dec_ref(v_body_2816_);
lean_dec_ref(v_binderType_2815_);
lean_del_object(v___x_2805_);
lean_dec(v_snd_2803_);
lean_dec(v_fst_2802_);
lean_del_object(v___x_2800_);
lean_dec(v_fst_2798_);
lean_del_object(v___x_2796_);
lean_dec(v_fst_2794_);
lean_del_object(v___x_2792_);
lean_dec(v_fst_2790_);
lean_del_object(v___x_2785_);
v_a_2938_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2843_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2843_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec_ref(v_body_2840_);
lean_dec_ref(v_body_2816_);
lean_dec_ref(v_binderType_2815_);
lean_del_object(v___x_2805_);
lean_dec(v_snd_2803_);
lean_dec(v_fst_2802_);
lean_del_object(v___x_2800_);
lean_dec(v_fst_2798_);
lean_del_object(v___x_2796_);
lean_dec(v_fst_2794_);
lean_del_object(v___x_2792_);
lean_dec(v_fst_2790_);
lean_del_object(v___x_2785_);
v_a_2946_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2841_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2841_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
else
{
lean_object* v___x_2954_; lean_object* v___x_2956_; 
lean_dec_ref(v___x_2839_);
lean_dec_ref(v_body_2816_);
lean_dec_ref(v_binderType_2815_);
v___x_2954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2806_ == 0)
{
v___x_2956_ = v___x_2805_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_fst_2802_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_snd_2803_);
v___x_2956_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2958_; 
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 1, v___x_2956_);
v___x_2958_ = v___x_2800_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_fst_2798_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2960_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v___x_2958_);
v___x_2960_ = v___x_2796_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_fst_2794_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2962_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2960_);
v___x_2962_ = v___x_2792_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_fst_2790_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2964_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 1, v___x_2962_);
lean_ctor_set(v___x_2785_, 0, v___x_2954_);
v___x_2964_ = v___x_2785_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2966_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2964_);
v___x_2966_ = v___x_2813_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
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
lean_object* v___x_2973_; lean_object* v___x_2975_; 
lean_dec_ref(v_body_2816_);
lean_dec_ref(v_binderType_2815_);
v___x_2973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2806_ == 0)
{
v___x_2975_ = v___x_2805_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_fst_2802_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_snd_2803_);
v___x_2975_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2977_; 
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 1, v___x_2975_);
v___x_2977_ = v___x_2800_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_fst_2798_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2979_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v___x_2977_);
v___x_2979_ = v___x_2796_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_fst_2794_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2981_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2979_);
v___x_2981_ = v___x_2792_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_fst_2790_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2983_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 1, v___x_2981_);
lean_ctor_set(v___x_2785_, 0, v___x_2973_);
v___x_2983_ = v___x_2785_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2973_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2985_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2983_);
v___x_2985_ = v___x_2813_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2983_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
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
lean_object* v___x_2992_; lean_object* v___x_2994_; 
lean_dec(v_a_2811_);
v___x_2992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2806_ == 0)
{
v___x_2994_ = v___x_2805_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_fst_2802_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_snd_2803_);
v___x_2994_ = v_reuseFailAlloc_3010_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2996_; 
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 1, v___x_2994_);
v___x_2996_ = v___x_2800_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_fst_2798_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v___x_2994_);
v___x_2996_ = v_reuseFailAlloc_3009_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2998_; 
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 1, v___x_2996_);
v___x_2998_ = v___x_2796_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_fst_2794_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_3008_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_3000_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2998_);
v___x_3000_ = v___x_2792_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_fst_2790_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3007_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3002_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 1, v___x_3000_);
lean_ctor_set(v___x_2785_, 0, v___x_2992_);
v___x_3002_ = v___x_2785_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
lean_object* v___x_3004_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_3002_);
v___x_3004_ = v___x_2813_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
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
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_del_object(v___x_2805_);
lean_dec(v_snd_2803_);
lean_dec(v_fst_2802_);
lean_del_object(v___x_2800_);
lean_dec(v_fst_2798_);
lean_del_object(v___x_2796_);
lean_dec(v_fst_2794_);
lean_del_object(v___x_2792_);
lean_dec(v_fst_2790_);
lean_del_object(v___x_2785_);
v_a_3012_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_2810_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_2810_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___boxed(lean_object* v_as_3029_, lean_object* v_sz_3030_, lean_object* v_i_3031_, lean_object* v_b_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
size_t v_sz_boxed_3040_; size_t v_i_boxed_3041_; lean_object* v_res_3042_; 
v_sz_boxed_3040_ = lean_unbox_usize(v_sz_3030_);
lean_dec(v_sz_3030_);
v_i_boxed_3041_ = lean_unbox_usize(v_i_3031_);
lean_dec(v_i_3031_);
v_res_3042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(v_as_3029_, v_sz_boxed_3040_, v_i_boxed_3041_, v_b_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec_ref(v_as_3029_);
return v_res_3042_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_unsigned_to_nat(0u);
v___x_3056_ = l_Lean_Expr_bvar___override(v___x_3055_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = lean_box(0);
v___x_3061_ = l_Lean_Level_succ___override(v___x_3060_);
return v___x_3061_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = lean_box(0);
v___x_3063_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9);
v___x_3064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
lean_ctor_set(v___x_3064_, 1, v___x_3062_);
return v___x_3064_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = lean_box(0);
v___x_3066_ = l_Lean_mkSort(v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(lean_object* v_goal_3067_, lean_object* v_target_3068_, lean_object* v_pre_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1));
v___x_3081_ = l_Lean_Expr_isAppOf(v_pre_3069_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_dec_ref(v_pre_3069_);
lean_dec_ref(v_target_3068_);
lean_dec(v_goal_3067_);
goto v___jp_3077_;
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3082_ = lean_unsigned_to_nat(2u);
v___x_3083_ = l_Lean_Expr_getAppNumArgs(v_pre_3069_);
v___x_3084_ = lean_nat_dec_lt(v___x_3082_, v___x_3083_);
if (v___x_3084_ == 0)
{
lean_dec(v___x_3083_);
lean_dec_ref(v_pre_3069_);
lean_dec_ref(v_target_3068_);
lean_dec(v_goal_3067_);
goto v___jp_3077_;
}
else
{
lean_object* v_dummy_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v_args_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v_dummy_3085_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___closed__8);
lean_inc(v___x_3083_);
v___x_3086_ = lean_mk_array(v___x_3083_, v_dummy_3085_);
v___x_3087_ = lean_unsigned_to_nat(1u);
v___x_3088_ = lean_nat_sub(v___x_3083_, v___x_3087_);
lean_dec(v___x_3083_);
lean_inc_ref(v_pre_3069_);
v_args_3089_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_pre_3069_, v___x_3086_, v___x_3088_);
v___x_3090_ = lean_unsigned_to_nat(0u);
v___x_3091_ = lean_array_get_size(v_args_3089_);
v___x_3092_ = lean_nat_dec_lt(v___x_3090_, v___x_3091_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_dec_ref(v_args_3089_);
lean_dec_ref(v_pre_3069_);
lean_dec_ref(v_target_3068_);
lean_dec(v_goal_3067_);
v___x_3093_ = lean_box(0);
v___x_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
return v___x_3094_;
}
else
{
uint8_t v___x_3095_; 
v___x_3095_ = lean_nat_dec_lt(v___x_3087_, v___x_3091_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
lean_dec_ref(v_args_3089_);
lean_dec_ref(v_pre_3069_);
lean_dec_ref(v_target_3068_);
lean_dec(v_goal_3067_);
v___x_3096_ = lean_box(0);
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
return v___x_3097_;
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v_curTop_3101_; lean_object* v___x_3102_; 
v___x_3098_ = lean_array_fget(v_args_3089_, v___x_3090_);
v___x_3099_ = lean_array_fget(v_args_3089_, v___x_3087_);
v___x_3100_ = l_Lean_Expr_getAppFn(v_pre_3069_);
lean_inc(v___x_3099_);
lean_inc_n(v___x_3098_, 2);
v_curTop_3101_ = l_Lean_mkAppB(v___x_3100_, v___x_3098_, v___x_3099_);
v___x_3102_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_3098_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; size_t v_sz_3116_; size_t v___x_3117_; lean_object* v___x_3118_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
v___x_3104_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3));
v___x_3105_ = lean_box(0);
v___x_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3106_, 0, v_a_3103_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = l_Lean_mkConst(v___x_3104_, v___x_3106_);
lean_inc_ref_n(v_curTop_3101_, 2);
lean_inc(v___x_3098_);
v___x_3108_ = l_Lean_mkAppB(v___x_3107_, v___x_3098_, v_curTop_3101_);
v___x_3109_ = l_Array_extract___redArg(v_args_3089_, v___x_3082_, v___x_3091_);
lean_dec_ref(v_args_3089_);
v___x_3110_ = lean_box(0);
v___x_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3098_);
lean_ctor_set(v___x_3111_, 1, v___x_3099_);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v_curTop_3101_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v_curTop_3101_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3108_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
v___x_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3110_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v_sz_3116_ = lean_array_size(v___x_3109_);
v___x_3117_ = ((size_t)0ULL);
v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(v___x_3109_, v_sz_3116_, v___x_3117_, v___x_3115_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
lean_dec_ref(v___x_3109_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3202_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3202_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3202_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v_fst_3123_; 
v_fst_3123_ = lean_ctor_get(v_a_3119_, 0);
if (lean_obj_tag(v_fst_3123_) == 0)
{
lean_object* v_snd_3124_; lean_object* v_nargs_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v_snd_3124_ = lean_ctor_get(v_a_3119_, 1);
lean_inc(v_snd_3124_);
lean_dec(v_a_3119_);
v_nargs_3125_ = l_Lean_Expr_getAppNumArgs(v_target_3068_);
lean_inc(v_nargs_3125_);
v___x_3126_ = lean_mk_array(v_nargs_3125_, v_dummy_3085_);
v___x_3127_ = lean_nat_sub(v_nargs_3125_, v___x_3087_);
lean_dec(v_nargs_3125_);
lean_inc_ref(v_target_3068_);
v___x_3128_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_target_3068_, v___x_3126_, v___x_3127_);
v___x_3129_ = lean_array_get_size(v___x_3128_);
v___x_3130_ = lean_nat_dec_lt(v___x_3090_, v___x_3129_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3132_; 
lean_dec_ref(v___x_3128_);
lean_dec(v_snd_3124_);
lean_dec_ref(v_pre_3069_);
lean_dec_ref(v_target_3068_);
lean_dec(v_goal_3067_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3110_);
v___x_3132_ = v___x_3121_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3110_);
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
uint8_t v___x_3134_; 
v___x_3134_ = lean_nat_dec_lt(v___x_3087_, v___x_3129_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3136_; 
lean_dec_ref(v___x_3128_);
lean_dec(v_snd_3124_);
lean_dec_ref(v_pre_3069_);
lean_dec_ref(v_target_3068_);
lean_dec(v_goal_3067_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3110_);
v___x_3136_ = v___x_3121_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3110_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
else
{
lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3138_ = lean_unsigned_to_nat(3u);
v___x_3139_ = lean_nat_dec_lt(v___x_3138_, v___x_3129_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3141_; 
lean_dec_ref(v___x_3128_);
lean_dec(v_snd_3124_);
lean_dec_ref(v_pre_3069_);
lean_dec_ref(v_target_3068_);
lean_dec(v_goal_3067_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3110_);
v___x_3141_ = v___x_3121_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3110_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
else
{
lean_object* v_snd_3143_; lean_object* v_snd_3144_; lean_object* v_fst_3145_; lean_object* v_fst_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3196_; 
lean_del_object(v___x_3121_);
v_snd_3143_ = lean_ctor_get(v_snd_3124_, 1);
v_snd_3144_ = lean_ctor_get(v_snd_3143_, 1);
lean_inc(v_snd_3144_);
v_fst_3145_ = lean_ctor_get(v_snd_3124_, 0);
lean_inc(v_fst_3145_);
lean_dec(v_snd_3124_);
v_fst_3146_ = lean_ctor_get(v_snd_3144_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_snd_3144_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; 
v_unused_3197_ = lean_ctor_get(v_snd_3144_, 1);
lean_dec(v_unused_3197_);
v___x_3148_ = v_snd_3144_;
v_isShared_3149_ = v_isSharedCheck_3196_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_fst_3146_);
lean_dec(v_snd_3144_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3196_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3150_ = lean_array_fget(v___x_3128_, v___x_3090_);
v___x_3151_ = lean_array_fget(v___x_3128_, v___x_3087_);
v___x_3152_ = lean_array_fget(v___x_3128_, v___x_3138_);
lean_dec_ref(v___x_3128_);
lean_inc(v___x_3150_);
v___x_3153_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_3150_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v___x_3155_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__5));
v___x_3156_ = l_Lean_Expr_getAppFn(v_target_3068_);
lean_dec_ref(v_target_3068_);
v___x_3157_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6);
lean_inc(v___x_3152_);
lean_inc(v___x_3151_);
lean_inc_n(v___x_3150_, 2);
lean_inc_ref(v___x_3156_);
v___x_3158_ = l_Lean_mkApp4(v___x_3156_, v___x_3150_, v___x_3151_, v___x_3157_, v___x_3152_);
v___x_3159_ = 0;
v___x_3160_ = l_Lean_Expr_lam___override(v___x_3155_, v___x_3150_, v___x_3158_, v___x_3159_);
v___x_3161_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8));
v___x_3162_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10);
if (v_isShared_3149_ == 0)
{
lean_ctor_set_tag(v___x_3148_, 1);
lean_ctor_set(v___x_3148_, 1, v___x_3162_);
lean_ctor_set(v___x_3148_, 0, v_a_3154_);
v___x_3164_ = v___x_3148_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3154_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3165_ = l_Lean_mkConst(v___x_3161_, v___x_3164_);
v___x_3166_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11);
lean_inc(v_fst_3146_);
lean_inc(v___x_3150_);
v___x_3167_ = l_Lean_mkApp6(v___x_3165_, v___x_3150_, v___x_3166_, v_pre_3069_, v_fst_3146_, v___x_3160_, v_fst_3145_);
v___x_3168_ = l_Lean_mkApp4(v___x_3156_, v___x_3150_, v___x_3151_, v_fst_3146_, v___x_3152_);
v___x_3169_ = l_Lean_MVarId_replaceTargetEq(v_goal_3067_, v___x_3168_, v___x_3167_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3178_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3178_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3174_, 0, v_a_3170_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3174_);
v___x_3176_ = v___x_3172_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
v_a_3179_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3169_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3169_);
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
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec(v___x_3152_);
lean_dec(v___x_3151_);
lean_dec(v___x_3150_);
lean_del_object(v___x_3148_);
lean_dec(v_fst_3146_);
lean_dec(v_fst_3145_);
lean_dec_ref(v_pre_3069_);
lean_dec_ref(v_target_3068_);
lean_dec(v_goal_3067_);
v_a_3188_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3153_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3153_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
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
lean_object* v_val_3198_; lean_object* v___x_3200_; 
lean_inc_ref(v_fst_3123_);
lean_dec(v_a_3119_);
lean_dec_ref(v_pre_3069_);
lean_dec_ref(v_target_3068_);
lean_dec(v_goal_3067_);
v_val_3198_ = lean_ctor_get(v_fst_3123_, 0);
lean_inc(v_val_3198_);
lean_dec_ref_known(v_fst_3123_, 1);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v_val_3198_);
v___x_3200_ = v___x_3121_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_val_3198_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec_ref(v_pre_3069_);
lean_dec_ref(v_target_3068_);
lean_dec(v_goal_3067_);
v_a_3203_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3118_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3118_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec_ref(v_curTop_3101_);
lean_dec(v___x_3099_);
lean_dec(v___x_3098_);
lean_dec_ref(v_args_3089_);
lean_dec_ref(v_pre_3069_);
lean_dec_ref(v_target_3068_);
lean_dec(v_goal_3067_);
v_a_3211_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3102_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3102_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
}
}
v___jp_3077_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = lean_box(0);
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___boxed(lean_object* v_goal_3219_, lean_object* v_target_3220_, lean_object* v_pre_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(v_goal_3219_, v_target_3220_, v_pre_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
return v_res_3229_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1(void){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__0));
v___x_3232_ = l_Lean_stringToMessageData(v___x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(lean_object* v_goal_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_){
_start:
{
lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___x_3258_; 
lean_inc(v_goal_3240_);
v___x_3258_ = l_Lean_MVarId_getType(v_goal_3240_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3322_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3322_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3322_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v___x_3263_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4));
v___x_3264_ = lean_unsigned_to_nat(4u);
v___x_3265_ = l_Lean_Expr_isAppOfArity(v_a_3259_, v___x_3263_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3267_; 
lean_dec(v_a_3259_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v_goal_3240_);
v___x_3267_ = v___x_3261_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_goal_3240_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
else
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3269_ = l_Lean_Expr_appFn_x21(v_a_3259_);
lean_dec(v_a_3259_);
v___x_3270_ = l_Lean_Expr_appFn_x21(v___x_3269_);
v___x_3271_ = l_Lean_Expr_appFn_x21(v___x_3270_);
lean_dec_ref(v___x_3270_);
v___x_3272_ = l_Lean_Expr_appArg_x21(v___x_3271_);
lean_dec_ref(v___x_3271_);
if (lean_obj_tag(v___x_3272_) == 3)
{
lean_object* v_u_3273_; 
v_u_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_u_3273_);
lean_dec_ref_known(v___x_3272_, 1);
if (lean_obj_tag(v_u_3273_) == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_del_object(v___x_3261_);
v___x_3274_ = l_Lean_Expr_appArg_x21(v___x_3269_);
lean_dec_ref(v___x_3269_);
v___x_3275_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v___x_3274_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3307_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3307_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3307_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; uint8_t v___x_3281_; 
v___x_3280_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1));
v___x_3281_ = l_Lean_Expr_isAppOf(v_a_3276_, v___x_3280_);
lean_dec(v_a_3276_);
if (v___x_3281_ == 0)
{
lean_object* v___x_3283_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v_goal_3240_);
v___x_3283_ = v___x_3278_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_goal_3240_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
else
{
lean_object* v_backwardRules_3285_; lean_object* v_elimPre_3286_; lean_object* v___x_3287_; 
lean_del_object(v___x_3278_);
v_backwardRules_3285_ = lean_ctor_get(v_a_3241_, 0);
v_elimPre_3286_ = lean_ctor_get(v_backwardRules_3285_, 7);
lean_inc_ref(v_elimPre_3286_);
lean_inc(v_goal_3240_);
v___x_3287_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_3240_, v_elimPre_3286_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3298_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3298_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3298_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
if (lean_obj_tag(v_a_3288_) == 1)
{
lean_object* v_mvarIds_3292_; 
v_mvarIds_3292_ = lean_ctor_get(v_a_3288_, 0);
lean_inc(v_mvarIds_3292_);
lean_dec_ref_known(v_a_3288_, 1);
if (lean_obj_tag(v_mvarIds_3292_) == 1)
{
lean_object* v_tail_3293_; 
v_tail_3293_ = lean_ctor_get(v_mvarIds_3292_, 1);
if (lean_obj_tag(v_tail_3293_) == 0)
{
lean_object* v_head_3294_; lean_object* v___x_3296_; 
lean_dec(v_goal_3240_);
v_head_3294_ = lean_ctor_get(v_mvarIds_3292_, 0);
lean_inc(v_head_3294_);
lean_dec_ref_known(v_mvarIds_3292_, 2);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v_head_3294_);
v___x_3296_ = v___x_3290_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_head_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
else
{
lean_dec_ref_known(v_mvarIds_3292_, 2);
lean_del_object(v___x_3290_);
v___y_3250_ = v_a_3244_;
v___y_3251_ = v_a_3245_;
v___y_3252_ = v_a_3246_;
v___y_3253_ = v_a_3247_;
goto v___jp_3249_;
}
}
else
{
lean_dec(v_mvarIds_3292_);
lean_del_object(v___x_3290_);
v___y_3250_ = v_a_3244_;
v___y_3251_ = v_a_3245_;
v___y_3252_ = v_a_3246_;
v___y_3253_ = v_a_3247_;
goto v___jp_3249_;
}
}
else
{
lean_del_object(v___x_3290_);
lean_dec(v_a_3288_);
v___y_3250_ = v_a_3244_;
v___y_3251_ = v_a_3245_;
v___y_3252_ = v_a_3246_;
v___y_3253_ = v_a_3247_;
goto v___jp_3249_;
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec(v_goal_3240_);
v_a_3299_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3287_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3287_);
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
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec(v_goal_3240_);
v_a_3308_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3275_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3275_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
else
{
lean_object* v___x_3317_; 
lean_dec(v_u_3273_);
lean_dec_ref(v___x_3269_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v_goal_3240_);
v___x_3317_ = v___x_3261_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_goal_3240_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
else
{
lean_object* v___x_3320_; 
lean_dec_ref(v___x_3272_);
lean_dec_ref(v___x_3269_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v_goal_3240_);
v___x_3320_ = v___x_3261_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_goal_3240_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec(v_goal_3240_);
v_a_3323_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3258_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3258_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
v___jp_3249_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3254_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1, &l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1);
v___x_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3255_, 0, v_goal_3240_);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_3256_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
return v___x_3257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___boxed(lean_object* v_goal_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_goal_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3333_);
lean_dec_ref(v_a_3332_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre(lean_object* v_goal_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_goal_3341_, v_a_3342_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___boxed(lean_object* v_goal_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_Elab_Tactic_VCGen_elimTopPre(v_goal_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
return v_res_3368_;
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
