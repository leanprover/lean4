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
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkFVar(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_fvarEq_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___boxed(lean_object*);
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
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PreservesSup"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "upperAdjoint"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__2_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__3_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__3_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__3_value_aux_2),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 52, 128, 160, 100, 147, 237, 166)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__3_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__5_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__5_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__5_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "himp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__6 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__6_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__7_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__7_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(173, 29, 48, 122, 5, 158, 45, 140)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__7 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__7_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 67, 57, 247, 147, 127, 99, 32)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "top_apply"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 33, 148, 124, 218, 91, 248, 169)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
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
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_fvarEq_x3f(lean_object* v_00_u03c6_152_){
_start:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = l_Lean_Expr_cleanupAnnotations(v_00_u03c6_152_);
v___x_154_ = l_Lean_Expr_isApp(v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
lean_dec_ref(v___x_153_);
v___x_155_ = lean_box(0);
return v___x_155_;
}
else
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = l_Lean_Expr_appFnCleanup___redArg(v___x_153_);
v___x_157_ = l_Lean_Expr_isApp(v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
lean_dec_ref(v___x_156_);
lean_dec_ref(v___x_153_);
v___x_158_ = lean_box(0);
return v___x_158_;
}
else
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = l_Lean_Expr_appFnCleanup___redArg(v___x_156_);
v___x_160_ = l_Lean_Expr_isApp(v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
lean_dec_ref(v___x_159_);
lean_dec_ref(v___x_156_);
lean_dec_ref(v___x_153_);
v___x_161_ = lean_box(0);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_162_ = l_Lean_Expr_appFnCleanup___redArg(v___x_159_);
lean_dec_ref(v___x_159_);
v___x_163_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___closed__1));
v___x_164_ = l_Lean_Expr_isConstOf(v___x_162_, v___x_163_);
lean_dec_ref(v___x_162_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
lean_dec_ref(v___x_156_);
lean_dec_ref(v___x_153_);
v___x_165_ = lean_box(0);
return v___x_165_;
}
else
{
lean_object* v_arg_166_; 
v_arg_166_ = lean_ctor_get(v___x_156_, 1);
lean_inc_ref(v_arg_166_);
lean_dec_ref(v___x_156_);
if (lean_obj_tag(v_arg_166_) == 1)
{
lean_object* v_fvarId_167_; lean_object* v_arg_168_; uint8_t v___x_169_; 
v_fvarId_167_ = lean_ctor_get(v_arg_166_, 0);
lean_inc(v_fvarId_167_);
lean_dec_ref_known(v_arg_166_, 1);
v_arg_168_ = lean_ctor_get(v___x_153_, 1);
lean_inc_ref(v_arg_168_);
lean_dec_ref(v___x_153_);
v___x_169_ = l_Lean_Expr_containsFVar(v_arg_168_, v_fvarId_167_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v_fvarId_167_);
lean_ctor_set(v___x_170_, 1, v_arg_168_);
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; 
lean_dec_ref(v_arg_168_);
lean_dec(v_fvarId_167_);
v___x_172_ = lean_box(0);
return v___x_172_;
}
}
else
{
lean_object* v___x_173_; 
lean_dec_ref(v_arg_166_);
lean_dec_ref(v___x_153_);
v___x_173_ = lean_box(0);
return v___x_173_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___boxed(lean_object* v_00_u03c6_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Elab_Tactic_VCGen_fvarEq_x3f(v_00_u03c6_174_);
lean_dec_ref(v_00_u03c6_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(lean_object* v___x_176_, lean_object* v___x_177_, lean_object* v_fst_178_, lean_object* v_as_179_, size_t v_i_180_, size_t v_stop_181_, lean_object* v_b_182_){
_start:
{
lean_object* v___y_184_; uint8_t v___x_188_; 
v___x_188_ = lean_usize_dec_eq(v_i_180_, v_stop_181_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_array_uget_borrowed(v_as_179_, v_i_180_);
if (lean_obj_tag(v___x_189_) == 0)
{
v___y_184_ = v_b_182_;
goto v___jp_183_;
}
else
{
lean_object* v_val_190_; lean_object* v_fst_191_; lean_object* v_snd_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_220_; 
v_val_190_ = lean_ctor_get(v___x_189_, 0);
v_fst_191_ = lean_ctor_get(v_b_182_, 0);
v_snd_192_ = lean_ctor_get(v_b_182_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_b_182_);
if (v_isSharedCheck_220_ == 0)
{
v___x_194_ = v_b_182_;
v_isShared_195_ = v_isSharedCheck_220_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_snd_192_);
lean_inc(v_fst_191_);
lean_dec(v_b_182_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_220_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
uint8_t v___x_196_; uint8_t v___x_197_; lean_object* v___y_199_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_196_ = lean_nat_dec_lt(v___x_176_, v___x_177_);
v___x_197_ = 1;
v___x_216_ = l_Lean_LocalDecl_type(v_val_190_);
v___x_217_ = l_Lean_Expr_containsFVar(v___x_216_, v_fst_178_);
lean_dec_ref(v___x_216_);
if (v___x_217_ == 0)
{
v___y_199_ = v_fst_191_;
goto v___jp_198_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_inc(v_val_190_);
v___x_218_ = l_Lean_LocalDecl_toExpr(v_val_190_);
v___x_219_ = lean_array_push(v_fst_191_, v___x_218_);
v___y_199_ = v___x_219_;
goto v___jp_198_;
}
v___jp_198_:
{
uint8_t v___x_200_; 
v___x_200_ = lean_unbox(v_snd_192_);
lean_dec(v_snd_192_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_LocalDecl_value_x3f(v_val_190_, v___x_188_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_box(v___x_196_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 1, v___x_202_);
lean_ctor_set(v___x_194_, 0, v___y_199_);
v___x_204_ = v___x_194_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___y_199_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
v___y_184_ = v___x_204_;
goto v___jp_183_;
}
}
else
{
lean_object* v_val_206_; uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v_val_206_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_val_206_);
lean_dec_ref_known(v___x_201_, 1);
v___x_207_ = l_Lean_Expr_containsFVar(v_val_206_, v_fst_178_);
lean_dec(v_val_206_);
v___x_208_ = lean_box(v___x_207_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 1, v___x_208_);
lean_ctor_set(v___x_194_, 0, v___y_199_);
v___x_210_ = v___x_194_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___y_199_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
v___y_184_ = v___x_210_;
goto v___jp_183_;
}
}
}
else
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = lean_box(v___x_197_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 1, v___x_212_);
lean_ctor_set(v___x_194_, 0, v___y_199_);
v___x_214_ = v___x_194_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___y_199_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
v___y_184_ = v___x_214_;
goto v___jp_183_;
}
}
}
}
}
}
else
{
return v_b_182_;
}
v___jp_183_:
{
size_t v___x_185_; size_t v___x_186_; 
v___x_185_ = ((size_t)1ULL);
v___x_186_ = lean_usize_add(v_i_180_, v___x_185_);
v_i_180_ = v___x_186_;
v_b_182_ = v___y_184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v___x_221_, lean_object* v___x_222_, lean_object* v_fst_223_, lean_object* v_as_224_, lean_object* v_i_225_, lean_object* v_stop_226_, lean_object* v_b_227_){
_start:
{
size_t v_i_boxed_228_; size_t v_stop_boxed_229_; lean_object* v_res_230_; 
v_i_boxed_228_ = lean_unbox_usize(v_i_225_);
lean_dec(v_i_225_);
v_stop_boxed_229_ = lean_unbox_usize(v_stop_226_);
lean_dec(v_stop_226_);
v_res_230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_221_, v___x_222_, v_fst_223_, v_as_224_, v_i_boxed_228_, v_stop_boxed_229_, v_b_227_);
lean_dec_ref(v_as_224_);
lean_dec(v_fst_223_);
lean_dec(v___x_222_);
lean_dec(v___x_221_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(lean_object* v___x_231_, lean_object* v___x_232_, lean_object* v_fst_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
lean_object* v_cs_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_cs_236_ = lean_ctor_get(v_x_234_, 0);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_array_get_size(v_cs_236_);
v___x_239_ = lean_nat_dec_lt(v___x_237_, v___x_238_);
if (v___x_239_ == 0)
{
return v_x_235_;
}
else
{
size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; 
v___x_240_ = ((size_t)0ULL);
v___x_241_ = lean_usize_of_nat(v___x_238_);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(v___x_231_, v___x_232_, v_fst_233_, v_cs_236_, v___x_240_, v___x_241_, v_x_235_);
return v___x_242_;
}
}
else
{
lean_object* v_vs_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_vs_243_ = lean_ctor_get(v_x_234_, 0);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_array_get_size(v_vs_243_);
v___x_246_ = lean_nat_dec_lt(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
return v_x_235_;
}
else
{
size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; 
v___x_247_ = ((size_t)0ULL);
v___x_248_ = lean_usize_of_nat(v___x_245_);
v___x_249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_231_, v___x_232_, v_fst_233_, v_vs_243_, v___x_247_, v___x_248_, v_x_235_);
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v___x_250_, lean_object* v___x_251_, lean_object* v_fst_252_, lean_object* v_as_253_, size_t v_i_254_, size_t v_stop_255_, lean_object* v_b_256_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = lean_usize_dec_eq(v_i_254_, v_stop_255_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; size_t v___x_260_; size_t v___x_261_; 
v___x_258_ = lean_array_uget_borrowed(v_as_253_, v_i_254_);
v___x_259_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(v___x_250_, v___x_251_, v_fst_252_, v___x_258_, v_b_256_);
v___x_260_ = ((size_t)1ULL);
v___x_261_ = lean_usize_add(v_i_254_, v___x_260_);
v_i_254_ = v___x_261_;
v_b_256_ = v___x_259_;
goto _start;
}
else
{
return v_b_256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v___x_263_, lean_object* v___x_264_, lean_object* v_fst_265_, lean_object* v_as_266_, lean_object* v_i_267_, lean_object* v_stop_268_, lean_object* v_b_269_){
_start:
{
size_t v_i_boxed_270_; size_t v_stop_boxed_271_; lean_object* v_res_272_; 
v_i_boxed_270_ = lean_unbox_usize(v_i_267_);
lean_dec(v_i_267_);
v_stop_boxed_271_ = lean_unbox_usize(v_stop_268_);
lean_dec(v_stop_268_);
v_res_272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(v___x_263_, v___x_264_, v_fst_265_, v_as_266_, v_i_boxed_270_, v_stop_boxed_271_, v_b_269_);
lean_dec_ref(v_as_266_);
lean_dec(v_fst_265_);
lean_dec(v___x_264_);
lean_dec(v___x_263_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3___boxed(lean_object* v___x_273_, lean_object* v___x_274_, lean_object* v_fst_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(v___x_273_, v___x_274_, v_fst_275_, v_x_276_, v_x_277_);
lean_dec_ref(v_x_276_);
lean_dec(v_fst_275_);
lean_dec(v___x_274_);
lean_dec(v___x_273_);
return v_res_278_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(lean_object* v___x_280_, lean_object* v___x_281_, lean_object* v_fst_282_, lean_object* v_x_283_, size_t v_x_284_, size_t v_x_285_, lean_object* v_x_286_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v_cs_287_; lean_object* v___x_288_; size_t v___x_289_; lean_object* v_j_290_; lean_object* v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_cs_287_ = lean_ctor_get(v_x_283_, 0);
v___x_288_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___closed__0);
v___x_289_ = lean_usize_shift_right(v_x_284_, v_x_285_);
v_j_290_ = lean_usize_to_nat(v___x_289_);
v___x_291_ = lean_array_get_borrowed(v___x_288_, v_cs_287_, v_j_290_);
v___x_292_ = ((size_t)1ULL);
v___x_293_ = lean_usize_shift_left(v___x_292_, v_x_285_);
v___x_294_ = lean_usize_sub(v___x_293_, v___x_292_);
v___x_295_ = lean_usize_land(v_x_284_, v___x_294_);
v___x_296_ = ((size_t)5ULL);
v___x_297_ = lean_usize_sub(v_x_285_, v___x_296_);
v___x_298_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(v___x_280_, v___x_281_, v_fst_282_, v___x_291_, v___x_295_, v___x_297_, v_x_286_);
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_add(v_j_290_, v___x_299_);
lean_dec(v_j_290_);
v___x_301_ = lean_array_get_size(v_cs_287_);
v___x_302_ = lean_nat_dec_lt(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_dec(v___x_300_);
return v___x_298_;
}
else
{
size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_usize_of_nat(v___x_300_);
lean_dec(v___x_300_);
v___x_304_ = lean_usize_of_nat(v___x_301_);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1_spec__2(v___x_280_, v___x_281_, v_fst_282_, v_cs_287_, v___x_303_, v___x_304_, v___x_298_);
return v___x_305_;
}
}
else
{
lean_object* v_vs_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_vs_306_ = lean_ctor_get(v_x_283_, 0);
v___x_307_ = lean_usize_to_nat(v_x_284_);
v___x_308_ = lean_array_get_size(v_vs_306_);
v___x_309_ = lean_nat_dec_lt(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_dec(v___x_307_);
return v_x_286_;
}
else
{
size_t v___x_310_; size_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_usize_of_nat(v___x_307_);
lean_dec(v___x_307_);
v___x_311_ = lean_usize_of_nat(v___x_308_);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_280_, v___x_281_, v_fst_282_, v_vs_306_, v___x_310_, v___x_311_, v_x_286_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_313_, lean_object* v___x_314_, lean_object* v_fst_315_, lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
size_t v_x_19327__boxed_320_; size_t v_x_19328__boxed_321_; lean_object* v_res_322_; 
v_x_19327__boxed_320_ = lean_unbox_usize(v_x_317_);
lean_dec(v_x_317_);
v_x_19328__boxed_321_ = lean_unbox_usize(v_x_318_);
lean_dec(v_x_318_);
v_res_322_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(v___x_313_, v___x_314_, v_fst_315_, v_x_316_, v_x_19327__boxed_320_, v_x_19328__boxed_321_, v_x_319_);
lean_dec_ref(v_x_316_);
lean_dec(v_fst_315_);
lean_dec(v___x_314_);
lean_dec(v___x_313_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0(lean_object* v___x_323_, lean_object* v___x_324_, lean_object* v_fst_325_, lean_object* v_t_326_, lean_object* v_init_327_, lean_object* v_start_328_){
_start:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_nat_dec_eq(v_start_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v_root_331_; lean_object* v_tail_332_; size_t v_shift_333_; lean_object* v_tailOff_334_; uint8_t v___x_335_; 
v_root_331_ = lean_ctor_get(v_t_326_, 0);
v_tail_332_ = lean_ctor_get(v_t_326_, 1);
v_shift_333_ = lean_ctor_get_usize(v_t_326_, 4);
v_tailOff_334_ = lean_ctor_get(v_t_326_, 3);
v___x_335_ = lean_nat_dec_le(v_tailOff_334_, v_start_328_);
if (v___x_335_ == 0)
{
size_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_336_ = lean_usize_of_nat(v_start_328_);
v___x_337_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__1(v___x_323_, v___x_324_, v_fst_325_, v_root_331_, v___x_336_, v_shift_333_, v_init_327_);
v___x_338_ = lean_array_get_size(v_tail_332_);
v___x_339_ = lean_nat_dec_lt(v___x_329_, v___x_338_);
if (v___x_339_ == 0)
{
return v___x_337_;
}
else
{
size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((size_t)0ULL);
v___x_341_ = lean_usize_of_nat(v___x_338_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_323_, v___x_324_, v_fst_325_, v_tail_332_, v___x_340_, v___x_341_, v___x_337_);
return v___x_342_;
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_343_ = lean_nat_sub(v_start_328_, v_tailOff_334_);
v___x_344_ = lean_array_get_size(v_tail_332_);
v___x_345_ = lean_nat_dec_lt(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
lean_dec(v___x_343_);
return v_init_327_;
}
else
{
size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_usize_of_nat(v___x_343_);
lean_dec(v___x_343_);
v___x_347_ = lean_usize_of_nat(v___x_344_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_323_, v___x_324_, v_fst_325_, v_tail_332_, v___x_346_, v___x_347_, v_init_327_);
return v___x_348_;
}
}
}
else
{
lean_object* v_root_349_; lean_object* v_tail_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v_root_349_ = lean_ctor_get(v_t_326_, 0);
v_tail_350_ = lean_ctor_get(v_t_326_, 1);
v___x_351_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__3(v___x_323_, v___x_324_, v_fst_325_, v_root_349_, v_init_327_);
v___x_352_ = lean_array_get_size(v_tail_350_);
v___x_353_ = lean_nat_dec_lt(v___x_329_, v___x_352_);
if (v___x_353_ == 0)
{
return v___x_351_;
}
else
{
size_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; 
v___x_354_ = ((size_t)0ULL);
v___x_355_ = lean_usize_of_nat(v___x_352_);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0_spec__2(v___x_323_, v___x_324_, v_fst_325_, v_tail_350_, v___x_354_, v___x_355_, v___x_351_);
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0___boxed(lean_object* v___x_357_, lean_object* v___x_358_, lean_object* v_fst_359_, lean_object* v_t_360_, lean_object* v_init_361_, lean_object* v_start_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0(v___x_357_, v___x_358_, v_fst_359_, v_t_360_, v_init_361_, v_start_362_);
lean_dec(v_start_362_);
lean_dec_ref(v_t_360_);
lean_dec(v_fst_359_);
lean_dec(v___x_358_);
lean_dec(v___x_357_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0(lean_object* v___x_364_, lean_object* v___x_365_, lean_object* v_fst_366_, lean_object* v_lctx_367_, lean_object* v_init_368_, lean_object* v_start_369_){
_start:
{
lean_object* v_decls_370_; lean_object* v___x_371_; 
v_decls_370_ = lean_ctor_get(v_lctx_367_, 1);
v___x_371_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0_spec__0(v___x_364_, v___x_365_, v_fst_366_, v_decls_370_, v_init_368_, v_start_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0___boxed(lean_object* v___x_372_, lean_object* v___x_373_, lean_object* v_fst_374_, lean_object* v_lctx_375_, lean_object* v_init_376_, lean_object* v_start_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0(v___x_372_, v___x_373_, v_fst_374_, v_lctx_375_, v_init_376_, v_start_377_);
lean_dec(v_start_377_);
lean_dec_ref(v_lctx_375_);
lean_dec(v_fst_374_);
lean_dec(v___x_373_);
lean_dec(v___x_372_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(lean_object* v_eqn_385_, lean_object* v_G_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Sym_instantiateMVarsS(v_eqn_385_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_523_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_523_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_523_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_523_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Elab_Tactic_VCGen_fvarEq_x3f(v_a_395_);
lean_dec(v_a_395_);
if (lean_obj_tag(v___x_399_) == 1)
{
lean_object* v_val_400_; lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_518_; 
v_val_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v___x_399_, 1);
v_fst_401_ = lean_ctor_get(v_val_400_, 0);
v_snd_402_ = lean_ctor_get(v_val_400_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_val_400_);
if (v_isSharedCheck_518_ == 0)
{
v___x_404_ = v_val_400_;
v_isShared_405_ = v_isSharedCheck_518_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_402_);
lean_inc(v_fst_401_);
lean_dec(v_val_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_518_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_lctx_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_lctx_406_ = lean_ctor_get(v_a_389_, 2);
lean_inc_n(v_fst_401_, 2);
v___x_407_ = l_Lean_mkFVar(v_fst_401_);
lean_inc_ref(v_lctx_406_);
v___x_408_ = lean_local_ctx_find(v_lctx_406_, v_fst_401_);
if (lean_obj_tag(v___x_408_) == 1)
{
lean_object* v_val_409_; uint8_t v___x_410_; uint8_t v___x_411_; 
v_val_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_val_409_);
lean_dec_ref_known(v___x_408_, 1);
v___x_410_ = 0;
v___x_411_ = l_Lean_LocalDecl_isLet(v_val_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_del_object(v___x_397_);
lean_inc_ref(v_G_386_);
v___x_412_ = l_Lean_Meta_Sym_getMaxFVar_x3f(v_G_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_501_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_501_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_501_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_501_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
if (lean_obj_tag(v_a_413_) == 1)
{
lean_object* v_val_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_496_; 
lean_del_object(v___x_415_);
v_val_417_ = lean_ctor_get(v_a_413_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_413_);
if (v_isSharedCheck_496_ == 0)
{
v___x_419_ = v_a_413_;
v_isShared_420_ = v_isSharedCheck_496_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_val_417_);
lean_dec(v_a_413_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_496_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_FVarId_getDecl___redArg(v_val_417_, v_a_389_, v_a_391_, v_a_392_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_487_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_487_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_487_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_487_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_426_ = l_Lean_LocalDecl_index(v_a_422_);
lean_dec(v_a_422_);
v___x_427_ = l_Lean_LocalDecl_index(v_val_409_);
lean_dec(v_val_409_);
v___x_428_ = lean_nat_dec_lt(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v_fst_434_; lean_object* v_snd_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_482_; 
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___closed__1));
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = lean_nat_add(v___x_427_, v___x_431_);
v___x_433_ = l_Lean_LocalContext_foldlM___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f_spec__0(v___x_426_, v___x_427_, v_fst_401_, v_lctx_406_, v___x_430_, v___x_432_);
lean_dec(v___x_432_);
lean_dec(v_fst_401_);
lean_dec(v___x_427_);
lean_dec(v___x_426_);
v_fst_434_ = lean_ctor_get(v___x_433_, 0);
v_snd_435_ = lean_ctor_get(v___x_433_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_482_ == 0)
{
v___x_437_ = v___x_433_;
v_isShared_438_ = v_isSharedCheck_482_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_snd_435_);
lean_inc(v_fst_434_);
lean_dec(v___x_433_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_482_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_439_ = lean_mk_empty_array_with_capacity(v___x_431_);
lean_inc_ref_n(v___x_407_, 2);
v___x_440_ = lean_array_push(v___x_439_, v___x_407_);
v___x_441_ = l_Array_append___redArg(v___x_440_, v_fst_434_);
v___x_442_ = lean_array_push(v___x_441_, v___x_407_);
v___x_443_ = l_Lean_Meta_Sym_abstractFVarsRange(v_G_386_, v___x_429_, v___x_442_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_473_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_473_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_473_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_473_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint8_t v___y_449_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = l_Lean_Expr_looseBVarRange(v_a_444_);
v___x_465_ = lean_nat_dec_eq(v___x_464_, v___x_431_);
lean_dec(v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_468_; 
lean_del_object(v___x_446_);
lean_dec(v_a_444_);
lean_del_object(v___x_437_);
lean_dec(v_snd_435_);
lean_dec(v_fst_434_);
lean_del_object(v___x_419_);
lean_dec_ref(v___x_407_);
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
v___x_466_ = lean_box(0);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_466_);
v___x_468_ = v___x_424_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
else
{
lean_object* v___x_470_; uint8_t v___x_471_; 
lean_del_object(v___x_424_);
v___x_470_ = lean_array_get_size(v_fst_434_);
lean_dec(v_fst_434_);
v___x_471_ = lean_nat_dec_eq(v___x_470_, v___x_429_);
if (v___x_471_ == 0)
{
lean_dec(v_snd_435_);
v___y_449_ = v___x_410_;
goto v___jp_448_;
}
else
{
uint8_t v___x_472_; 
v___x_472_ = lean_unbox(v_snd_435_);
lean_dec(v_snd_435_);
if (v___x_472_ == 0)
{
v___y_449_ = v___x_465_;
goto v___jp_448_;
}
else
{
v___y_449_ = v___x_428_;
goto v___jp_448_;
}
}
}
v___jp_448_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = lean_box(v___y_449_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v___x_450_);
lean_ctor_set(v___x_437_, 0, v_a_444_);
v___x_452_ = v___x_437_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_444_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_463_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_452_);
lean_ctor_set(v___x_404_, 0, v_snd_402_);
v___x_454_ = v___x_404_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_snd_402_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_462_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_407_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_455_);
v___x_457_ = v___x_419_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_457_);
v___x_459_ = v___x_446_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_del_object(v___x_437_);
lean_dec(v_snd_435_);
lean_dec(v_fst_434_);
lean_del_object(v___x_424_);
lean_del_object(v___x_419_);
lean_dec_ref(v___x_407_);
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
v_a_474_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_443_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_443_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
else
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec(v___x_427_);
lean_dec(v___x_426_);
lean_del_object(v___x_419_);
lean_dec_ref(v___x_407_);
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
lean_dec(v_fst_401_);
lean_dec_ref(v_G_386_);
v___x_483_ = lean_box(0);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_483_);
v___x_485_ = v___x_424_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_del_object(v___x_419_);
lean_dec(v_val_409_);
lean_dec_ref(v___x_407_);
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
lean_dec(v_fst_401_);
lean_dec_ref(v_G_386_);
v_a_488_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_421_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_421_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec(v_a_413_);
lean_dec(v_val_409_);
lean_dec_ref(v___x_407_);
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
lean_dec(v_fst_401_);
lean_dec_ref(v_G_386_);
v___x_497_ = lean_box(0);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_497_);
v___x_499_ = v___x_415_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec(v_val_409_);
lean_dec_ref(v___x_407_);
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
lean_dec(v_fst_401_);
lean_dec_ref(v_G_386_);
v_a_502_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_412_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_412_);
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
else
{
lean_object* v___x_510_; lean_object* v___x_512_; 
lean_dec(v_val_409_);
lean_dec_ref(v___x_407_);
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
lean_dec(v_fst_401_);
lean_dec_ref(v_G_386_);
v___x_510_ = lean_box(0);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_510_);
v___x_512_ = v___x_397_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_516_; 
lean_dec(v___x_408_);
lean_dec_ref(v___x_407_);
lean_del_object(v___x_404_);
lean_dec(v_snd_402_);
lean_dec(v_fst_401_);
lean_dec_ref(v_G_386_);
v___x_514_ = lean_box(0);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_514_);
v___x_516_ = v___x_397_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_521_; 
lean_dec(v___x_399_);
lean_dec_ref(v_G_386_);
v___x_519_ = lean_box(0);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_519_);
v___x_521_ = v___x_397_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
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
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec_ref(v_G_386_);
v_a_524_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_394_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_394_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg___boxed(lean_object* v_eqn_532_, lean_object* v_G_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_eqn_532_, v_G_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f(lean_object* v_eqn_542_, lean_object* v_G_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_eqn_542_, v_G_543_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___boxed(lean_object* v_eqn_557_, lean_object* v_G_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f(v_eqn_557_, v_G_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(lean_object* v_00_u03c6_575_, lean_object* v_G_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___x_615_; 
lean_inc_ref(v_00_u03c6_575_);
v___x_615_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03c6_575_, v_a_580_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = l_Lean_Expr_cleanupAnnotations(v_a_616_);
lean_dec(v_a_616_);
v___x_618_ = l_Lean_Expr_isApp(v___x_617_);
if (v___x_618_ == 0)
{
lean_dec_ref(v___x_617_);
v___y_585_ = v_a_577_;
v___y_586_ = v_a_578_;
v___y_587_ = v_a_579_;
v___y_588_ = v_a_580_;
v___y_589_ = v_a_581_;
v___y_590_ = v_a_582_;
goto v___jp_584_;
}
else
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = l_Lean_Expr_appFnCleanup___redArg(v___x_617_);
v___x_620_ = l_Lean_Expr_isApp(v___x_619_);
if (v___x_620_ == 0)
{
lean_dec_ref(v___x_619_);
lean_dec_ref(v___x_617_);
v___y_585_ = v_a_577_;
v___y_586_ = v_a_578_;
v___y_587_ = v_a_579_;
v___y_588_ = v_a_580_;
v___y_589_ = v_a_581_;
v___y_590_ = v_a_582_;
goto v___jp_584_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = l_Lean_Expr_appFnCleanup___redArg(v___x_619_);
v___x_622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__1));
v___x_623_ = l_Lean_Expr_isConstOf(v___x_621_, v___x_622_);
lean_dec_ref(v___x_621_);
if (v___x_623_ == 0)
{
lean_dec_ref(v___x_619_);
lean_dec_ref(v___x_617_);
v___y_585_ = v_a_577_;
v___y_586_ = v_a_578_;
v___y_587_ = v_a_579_;
v___y_588_ = v_a_580_;
v___y_589_ = v_a_581_;
v___y_590_ = v_a_582_;
goto v___jp_584_;
}
else
{
lean_object* v_arg_624_; lean_object* v_arg_625_; lean_object* v___x_626_; 
lean_dec_ref(v_00_u03c6_575_);
v_arg_624_ = lean_ctor_get(v___x_617_, 1);
lean_inc_ref(v_arg_624_);
lean_dec_ref(v___x_617_);
v_arg_625_ = lean_ctor_get(v___x_619_, 1);
lean_inc_ref(v_arg_625_);
lean_dec_ref(v___x_619_);
lean_inc_ref(v_G_576_);
v___x_626_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_arg_625_, v_G_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; uint8_t v___x_628_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v___x_628_ = lean_unbox(v_a_627_);
if (v___x_628_ == 0)
{
lean_dec_ref_known(v___x_626_, 1);
v_00_u03c6_575_ = v_arg_624_;
goto _start;
}
else
{
lean_dec_ref(v_arg_624_);
lean_dec_ref(v_G_576_);
return v___x_626_;
}
}
else
{
lean_dec_ref(v_arg_624_);
lean_dec_ref(v_G_576_);
return v___x_626_;
}
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v_G_576_);
lean_dec_ref(v_00_u03c6_575_);
v_a_630_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_615_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_615_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
v___jp_584_:
{
lean_object* v___x_591_; 
v___x_591_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_00_u03c6_575_, v_G_576_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_606_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_606_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
if (lean_obj_tag(v_a_592_) == 0)
{
uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_596_ = 0;
v___x_597_ = lean_box(v___x_596_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_597_);
v___x_599_ = v___x_594_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
lean_dec_ref_known(v_a_592_, 1);
v___x_601_ = 1;
v___x_602_ = lean_box(v___x_601_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_602_);
v___x_604_ = v___x_594_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_a_607_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_591_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_591_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___boxed(lean_object* v_00_u03c6_638_, lean_object* v_G_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_00_u03c6_638_, v_G_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct(lean_object* v_00_u03c6_648_, lean_object* v_G_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_00_u03c6_648_, v_G_649_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___boxed(lean_object* v_00_u03c6_663_, lean_object* v_G_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct(v_00_u03c6_663_, v_G_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(lean_object* v_x_678_, uint8_t v_bi_679_, lean_object* v_t_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___y_690_; lean_object* v___x_693_; uint8_t v_debug_694_; 
v___x_693_ = lean_st_ref_get(v___y_683_);
v_debug_694_ = lean_ctor_get_uint8(v___x_693_, sizeof(void*)*13);
lean_dec(v___x_693_);
if (v_debug_694_ == 0)
{
v___y_690_ = v___y_683_;
goto v___jp_689_;
}
else
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_680_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_696_; 
lean_dec_ref_known(v___x_695_, 1);
v___x_696_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_dec_ref_known(v___x_696_, 1);
v___y_690_ = v___y_683_;
goto v___jp_689_;
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref(v_b_681_);
lean_dec_ref(v_t_680_);
lean_dec(v_x_678_);
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref(v_b_681_);
lean_dec_ref(v_t_680_);
lean_dec(v_x_678_);
v_a_705_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_695_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_695_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = l_Lean_Expr_forallE___override(v_x_678_, v_t_680_, v_b_681_, v_bi_679_);
v___x_692_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_691_, v___y_690_);
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg___boxed(lean_object* v_x_713_, lean_object* v_bi_714_, lean_object* v_t_715_, lean_object* v_b_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
uint8_t v_bi_boxed_724_; lean_object* v_res_725_; 
v_bi_boxed_724_ = lean_unbox(v_bi_714_);
v_res_725_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_x_713_, v_bi_boxed_724_, v_t_715_, v_b_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0(lean_object* v_x_726_, uint8_t v_bi_727_, lean_object* v_t_728_, lean_object* v_b_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_x_726_, v_bi_727_, v_t_728_, v_b_729_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___boxed(lean_object* v_x_743_, lean_object* v_bi_744_, lean_object* v_t_745_, lean_object* v_b_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
uint8_t v_bi_boxed_759_; lean_object* v_res_760_; 
v_bi_boxed_759_ = lean_unbox(v_bi_744_);
v_res_760_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0(v_x_743_, v_bi_boxed_759_, v_t_745_, v_b_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
lean_object* v_ks_765_; lean_object* v_vs_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_790_; 
v_ks_765_ = lean_ctor_get(v_x_761_, 0);
v_vs_766_ = lean_ctor_get(v_x_761_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_790_ == 0)
{
v___x_768_ = v_x_761_;
v_isShared_769_ = v_isSharedCheck_790_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_vs_766_);
lean_inc(v_ks_765_);
lean_dec(v_x_761_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_790_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = lean_array_get_size(v_ks_765_);
v___x_771_ = lean_nat_dec_lt(v_x_762_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec(v_x_762_);
v___x_772_ = lean_array_push(v_ks_765_, v_x_763_);
v___x_773_ = lean_array_push(v_vs_766_, v_x_764_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_773_);
lean_ctor_set(v___x_768_, 0, v___x_772_);
v___x_775_ = v___x_768_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
lean_object* v_k_x27_777_; uint8_t v___x_778_; 
v_k_x27_777_ = lean_array_fget_borrowed(v_ks_765_, v_x_762_);
v___x_778_ = l_Lean_instBEqMVarId_beq(v_x_763_, v_k_x27_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_780_; 
if (v_isShared_769_ == 0)
{
v___x_780_ = v___x_768_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_ks_765_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_vs_766_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_x_762_, v___x_781_);
lean_dec(v_x_762_);
v_x_761_ = v___x_780_;
v_x_762_ = v___x_782_;
goto _start;
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = lean_array_fset(v_ks_765_, v_x_762_, v_x_763_);
v___x_786_ = lean_array_fset(v_vs_766_, v_x_762_, v_x_764_);
lean_dec(v_x_762_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_786_);
lean_ctor_set(v___x_768_, 0, v___x_785_);
v___x_788_ = v___x_768_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_786_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_n_791_, lean_object* v_k_792_, lean_object* v_v_793_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_791_, v___x_794_, v_k_792_, v_v_793_);
return v___x_795_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_x_797_, size_t v_x_798_, size_t v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
lean_object* v_es_802_; size_t v___x_803_; size_t v___x_804_; lean_object* v_j_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_es_802_ = lean_ctor_get(v_x_797_, 0);
v___x_803_ = ((size_t)31ULL);
v___x_804_ = lean_usize_land(v_x_798_, v___x_803_);
v_j_805_ = lean_usize_to_nat(v___x_804_);
v___x_806_ = lean_array_get_size(v_es_802_);
v___x_807_ = lean_nat_dec_lt(v_j_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_dec(v_j_805_);
lean_dec(v_x_801_);
lean_dec(v_x_800_);
return v_x_797_;
}
else
{
lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_846_; 
lean_inc_ref(v_es_802_);
v_isSharedCheck_846_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v_x_797_, 0);
lean_dec(v_unused_847_);
v___x_809_ = v_x_797_;
v_isShared_810_ = v_isSharedCheck_846_;
goto v_resetjp_808_;
}
else
{
lean_dec(v_x_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_846_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_v_811_; lean_object* v___x_812_; lean_object* v_xs_x27_813_; lean_object* v___y_815_; 
v_v_811_ = lean_array_fget(v_es_802_, v_j_805_);
v___x_812_ = lean_box(0);
v_xs_x27_813_ = lean_array_fset(v_es_802_, v_j_805_, v___x_812_);
switch(lean_obj_tag(v_v_811_))
{
case 0:
{
lean_object* v_key_820_; lean_object* v_val_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_831_; 
v_key_820_ = lean_ctor_get(v_v_811_, 0);
v_val_821_ = lean_ctor_get(v_v_811_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_v_811_);
if (v_isSharedCheck_831_ == 0)
{
v___x_823_ = v_v_811_;
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_val_821_);
lean_inc(v_key_820_);
lean_dec(v_v_811_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
uint8_t v___x_825_; 
v___x_825_ = l_Lean_instBEqMVarId_beq(v_x_800_, v_key_820_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
lean_del_object(v___x_823_);
v___x_826_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_820_, v_val_821_, v_x_800_, v_x_801_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___y_815_ = v___x_827_;
goto v___jp_814_;
}
else
{
lean_object* v___x_829_; 
lean_dec(v_val_821_);
lean_dec(v_key_820_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_x_801_);
lean_ctor_set(v___x_823_, 0, v_x_800_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_x_800_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_x_801_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
v___y_815_ = v___x_829_;
goto v___jp_814_;
}
}
}
}
case 1:
{
lean_object* v_node_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_844_; 
v_node_832_ = lean_ctor_get(v_v_811_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_v_811_);
if (v_isSharedCheck_844_ == 0)
{
v___x_834_ = v_v_811_;
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_node_832_);
lean_dec(v_v_811_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_836_ = ((size_t)5ULL);
v___x_837_ = lean_usize_shift_right(v_x_798_, v___x_836_);
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_add(v_x_799_, v___x_838_);
v___x_840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(v_node_832_, v___x_837_, v___x_839_, v_x_800_, v_x_801_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_840_);
v___x_842_ = v___x_834_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
v___y_815_ = v___x_842_;
goto v___jp_814_;
}
}
}
default: 
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_x_800_);
lean_ctor_set(v___x_845_, 1, v_x_801_);
v___y_815_ = v___x_845_;
goto v___jp_814_;
}
}
v___jp_814_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_array_fset(v_xs_x27_813_, v_j_805_, v___y_815_);
lean_dec(v_j_805_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_816_);
v___x_818_ = v___x_809_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
else
{
lean_object* v_ks_848_; lean_object* v_vs_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_867_; 
v_ks_848_ = lean_ctor_get(v_x_797_, 0);
v_vs_849_ = lean_ctor_get(v_x_797_, 1);
v_isSharedCheck_867_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_867_ == 0)
{
v___x_851_ = v_x_797_;
v_isShared_852_ = v_isSharedCheck_867_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_vs_849_);
lean_inc(v_ks_848_);
lean_dec(v_x_797_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_867_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_ks_848_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_vs_849_);
v___x_854_ = v_reuseFailAlloc_866_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v_newNode_855_; size_t v___x_856_; uint8_t v___x_857_; 
v_newNode_855_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v___x_854_, v_x_800_, v_x_801_);
v___x_856_ = ((size_t)7ULL);
v___x_857_ = lean_usize_dec_le(v___x_856_, v_x_799_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_858_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_855_);
v___x_859_ = lean_unsigned_to_nat(4u);
v___x_860_ = lean_nat_dec_lt(v___x_858_, v___x_859_);
lean_dec(v___x_858_);
if (v___x_860_ == 0)
{
lean_object* v_ks_861_; lean_object* v_vs_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_ks_861_ = lean_ctor_get(v_newNode_855_, 0);
lean_inc_ref(v_ks_861_);
v_vs_862_ = lean_ctor_get(v_newNode_855_, 1);
lean_inc_ref(v_vs_862_);
lean_dec_ref(v_newNode_855_);
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_865_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg(v_x_799_, v_ks_861_, v_vs_862_, v___x_863_, v___x_864_);
lean_dec_ref(v_vs_862_);
lean_dec_ref(v_ks_861_);
return v___x_865_;
}
else
{
return v_newNode_855_;
}
}
else
{
return v_newNode_855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg(size_t v_depth_868_, lean_object* v_keys_869_, lean_object* v_vals_870_, lean_object* v_i_871_, lean_object* v_entries_872_){
_start:
{
lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_873_ = lean_array_get_size(v_keys_869_);
v___x_874_ = lean_nat_dec_lt(v_i_871_, v___x_873_);
if (v___x_874_ == 0)
{
lean_dec(v_i_871_);
return v_entries_872_;
}
else
{
lean_object* v_k_875_; lean_object* v_v_876_; uint64_t v___x_877_; size_t v_h_878_; size_t v___x_879_; lean_object* v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; size_t v_h_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_k_875_ = lean_array_fget_borrowed(v_keys_869_, v_i_871_);
v_v_876_ = lean_array_fget_borrowed(v_vals_870_, v_i_871_);
v___x_877_ = l_Lean_instHashableMVarId_hash(v_k_875_);
v_h_878_ = lean_uint64_to_usize(v___x_877_);
v___x_879_ = ((size_t)5ULL);
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_881_ = ((size_t)1ULL);
v___x_882_ = lean_usize_sub(v_depth_868_, v___x_881_);
v___x_883_ = lean_usize_mul(v___x_879_, v___x_882_);
v_h_884_ = lean_usize_shift_right(v_h_878_, v___x_883_);
v___x_885_ = lean_nat_add(v_i_871_, v___x_880_);
lean_dec(v_i_871_);
lean_inc(v_v_876_);
lean_inc(v_k_875_);
v___x_886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(v_entries_872_, v_h_884_, v_depth_868_, v_k_875_, v_v_876_);
v_i_871_ = v___x_885_;
v_entries_872_ = v___x_886_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_depth_888_, lean_object* v_keys_889_, lean_object* v_vals_890_, lean_object* v_i_891_, lean_object* v_entries_892_){
_start:
{
size_t v_depth_boxed_893_; lean_object* v_res_894_; 
v_depth_boxed_893_ = lean_unbox_usize(v_depth_888_);
lean_dec(v_depth_888_);
v_res_894_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_893_, v_keys_889_, v_vals_890_, v_i_891_, v_entries_892_);
lean_dec_ref(v_vals_890_);
lean_dec_ref(v_keys_889_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
size_t v_x_11286__boxed_900_; size_t v_x_11287__boxed_901_; lean_object* v_res_902_; 
v_x_11286__boxed_900_ = lean_unbox_usize(v_x_896_);
lean_dec(v_x_896_);
v_x_11287__boxed_901_ = lean_unbox_usize(v_x_897_);
lean_dec(v_x_897_);
v_res_902_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(v_x_895_, v_x_11286__boxed_900_, v_x_11287__boxed_901_, v_x_898_, v_x_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1___redArg(lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
uint64_t v___x_906_; size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; 
v___x_906_ = l_Lean_instHashableMVarId_hash(v_x_904_);
v___x_907_ = lean_uint64_to_usize(v___x_906_);
v___x_908_ = ((size_t)1ULL);
v___x_909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(v_x_903_, v___x_907_, v___x_908_, v_x_904_, v_x_905_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(lean_object* v_mvarId_910_, lean_object* v_val_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v_mctx_915_; lean_object* v_cache_916_; lean_object* v_zetaDeltaFVarIds_917_; lean_object* v_postponed_918_; lean_object* v_diag_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_948_; 
v___x_914_ = lean_st_ref_take(v___y_912_);
v_mctx_915_ = lean_ctor_get(v___x_914_, 0);
v_cache_916_ = lean_ctor_get(v___x_914_, 1);
v_zetaDeltaFVarIds_917_ = lean_ctor_get(v___x_914_, 2);
v_postponed_918_ = lean_ctor_get(v___x_914_, 3);
v_diag_919_ = lean_ctor_get(v___x_914_, 4);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_948_ == 0)
{
v___x_921_ = v___x_914_;
v_isShared_922_ = v_isSharedCheck_948_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_diag_919_);
lean_inc(v_postponed_918_);
lean_inc(v_zetaDeltaFVarIds_917_);
lean_inc(v_cache_916_);
lean_inc(v_mctx_915_);
lean_dec(v___x_914_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_948_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_depth_923_; lean_object* v_levelAssignDepth_924_; lean_object* v_lmvarCounter_925_; lean_object* v_mvarCounter_926_; lean_object* v_lDecls_927_; lean_object* v_decls_928_; lean_object* v_userNames_929_; lean_object* v_lAssignment_930_; lean_object* v_eAssignment_931_; lean_object* v_dAssignment_932_; lean_object* v_instanceTypedMVars_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_947_; 
v_depth_923_ = lean_ctor_get(v_mctx_915_, 0);
v_levelAssignDepth_924_ = lean_ctor_get(v_mctx_915_, 1);
v_lmvarCounter_925_ = lean_ctor_get(v_mctx_915_, 2);
v_mvarCounter_926_ = lean_ctor_get(v_mctx_915_, 3);
v_lDecls_927_ = lean_ctor_get(v_mctx_915_, 4);
v_decls_928_ = lean_ctor_get(v_mctx_915_, 5);
v_userNames_929_ = lean_ctor_get(v_mctx_915_, 6);
v_lAssignment_930_ = lean_ctor_get(v_mctx_915_, 7);
v_eAssignment_931_ = lean_ctor_get(v_mctx_915_, 8);
v_dAssignment_932_ = lean_ctor_get(v_mctx_915_, 9);
v_instanceTypedMVars_933_ = lean_ctor_get(v_mctx_915_, 10);
v_isSharedCheck_947_ = !lean_is_exclusive(v_mctx_915_);
if (v_isSharedCheck_947_ == 0)
{
v___x_935_ = v_mctx_915_;
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_instanceTypedMVars_933_);
lean_inc(v_dAssignment_932_);
lean_inc(v_eAssignment_931_);
lean_inc(v_lAssignment_930_);
lean_inc(v_userNames_929_);
lean_inc(v_decls_928_);
lean_inc(v_lDecls_927_);
lean_inc(v_mvarCounter_926_);
lean_inc(v_lmvarCounter_925_);
lean_inc(v_levelAssignDepth_924_);
lean_inc(v_depth_923_);
lean_dec(v_mctx_915_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_937_ = lean_box(0);
v___x_938_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1___redArg(v_eAssignment_931_, v_mvarId_910_, v_val_911_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 8, v___x_938_);
v___x_940_ = v___x_935_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_depth_923_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_levelAssignDepth_924_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_lmvarCounter_925_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_mvarCounter_926_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_lDecls_927_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v_decls_928_);
lean_ctor_set(v_reuseFailAlloc_946_, 6, v_userNames_929_);
lean_ctor_set(v_reuseFailAlloc_946_, 7, v_lAssignment_930_);
lean_ctor_set(v_reuseFailAlloc_946_, 8, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_946_, 9, v_dAssignment_932_);
lean_ctor_set(v_reuseFailAlloc_946_, 10, v_instanceTypedMVars_933_);
v___x_940_ = v_reuseFailAlloc_946_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_940_);
v___x_942_ = v___x_921_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_cache_916_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_zetaDeltaFVarIds_917_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_postponed_918_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_diag_919_);
v___x_942_ = v_reuseFailAlloc_945_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_st_ref_put(v___y_912_, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_937_);
return v___x_944_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg___boxed(lean_object* v_mvarId_949_, lean_object* v_val_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v_mvarId_949_, v_val_950_, v___y_951_);
lean_dec(v___y_951_);
return v_res_953_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_box(0);
v___x_960_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__2));
v___x_961_ = l_Lean_mkConst(v___x_960_, v___x_959_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__6(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_box(0);
v___x_966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__5));
v___x_967_ = l_Lean_mkConst(v___x_966_, v___x_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f(lean_object* v_goal_968_, lean_object* v_target_969_, lean_object* v_nm_970_, lean_object* v_00_u03c6_971_, lean_object* v_G_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = l_Lean_Expr_cleanupAnnotations(v_00_u03c6_971_);
v___x_989_ = l_Lean_Expr_isApp(v___x_988_);
if (v___x_989_ == 0)
{
lean_dec_ref(v___x_988_);
lean_dec_ref(v_G_972_);
lean_dec_ref(v_00_u03c6_971_);
lean_dec(v_nm_970_);
lean_dec_ref(v_target_969_);
lean_dec(v_goal_968_);
goto v___jp_985_;
}
else
{
lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = l_Lean_Expr_appFnCleanup___redArg(v___x_988_);
v___x_991_ = l_Lean_Expr_isApp(v___x_990_);
if (v___x_991_ == 0)
{
lean_dec_ref(v___x_990_);
lean_dec_ref(v___x_988_);
lean_dec_ref(v_G_972_);
lean_dec_ref(v_00_u03c6_971_);
lean_dec(v_nm_970_);
lean_dec_ref(v_target_969_);
lean_dec(v_goal_968_);
goto v___jp_985_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_992_ = l_Lean_Expr_appFnCleanup___redArg(v___x_990_);
v___x_993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg___closed__1));
v___x_994_ = l_Lean_Expr_isConstOf(v___x_992_, v___x_993_);
lean_dec_ref(v___x_992_);
if (v___x_994_ == 0)
{
lean_dec_ref(v___x_990_);
lean_dec_ref(v___x_988_);
lean_dec_ref(v_G_972_);
lean_dec_ref(v_00_u03c6_971_);
lean_dec(v_nm_970_);
lean_dec_ref(v_target_969_);
lean_dec(v_goal_968_);
goto v___jp_985_;
}
else
{
lean_object* v_arg_995_; lean_object* v_arg_996_; lean_object* v___x_997_; 
v_arg_995_ = lean_ctor_get(v___x_988_, 1);
lean_inc_ref(v_arg_995_);
lean_dec_ref(v___x_988_);
v_arg_996_ = lean_ctor_get(v___x_990_, 1);
lean_inc_ref(v_arg_996_);
lean_dec_ref(v___x_990_);
lean_inc_ref(v_G_972_);
v___x_997_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_hasSubstConjunct___redArg(v_00_u03c6_971_, v_G_972_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1054_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1054_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1054_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_unbox(v_a_998_);
lean_dec(v_a_998_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_G_972_);
lean_dec(v_nm_970_);
lean_dec_ref(v_target_969_);
lean_dec(v_goal_968_);
v___x_1003_ = lean_box(0);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1003_);
v___x_1005_ = v___x_1000_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
uint8_t v___x_1007_; lean_object* v___x_1008_; 
lean_del_object(v___x_1000_);
v___x_1007_ = 0;
lean_inc_ref(v_G_972_);
lean_inc_ref(v_arg_995_);
lean_inc(v_nm_970_);
v___x_1008_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_nm_970_, v___x_1007_, v_arg_995_, v_G_972_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
lean_inc_ref(v_arg_996_);
v___x_1010_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_nm_970_, v___x_1007_, v_arg_996_, v_a_1009_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc_n(v_a_1011_, 2);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = lean_box(0);
v___x_1013_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1011_, v___x_1012_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1028_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_n(v_a_1014_, 2);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__3);
v___x_1016_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__6, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__6_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___closed__6);
v___x_1017_ = l_Lean_mkApp3(v___x_1016_, v_arg_996_, v_arg_995_, v_G_972_);
v___x_1018_ = l_Lean_mkApp4(v___x_1015_, v_target_969_, v_a_1011_, v___x_1017_, v_a_1014_);
v___x_1019_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v_goal_968_, v___x_1018_, v_a_981_);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v___x_1019_, 0);
lean_dec(v_unused_1029_);
v___x_1021_ = v___x_1019_;
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
else
{
lean_dec(v___x_1019_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1023_ = l_Lean_Expr_mvarId_x21(v_a_1014_);
lean_dec(v_a_1014_);
v___x_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1024_);
v___x_1026_ = v___x_1021_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v_a_1011_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_G_972_);
lean_dec_ref(v_target_969_);
lean_dec(v_goal_968_);
v_a_1030_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1013_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1013_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_G_972_);
lean_dec_ref(v_target_969_);
lean_dec(v_goal_968_);
v_a_1038_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1010_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1010_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_G_972_);
lean_dec(v_nm_970_);
lean_dec_ref(v_target_969_);
lean_dec(v_goal_968_);
v_a_1046_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1008_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1008_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_G_972_);
lean_dec(v_nm_970_);
lean_dec_ref(v_target_969_);
lean_dec(v_goal_968_);
v_a_1055_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_997_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_997_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
}
v___jp_985_:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_box(0);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___boxed(lean_object** _args){
lean_object* v_goal_1063_ = _args[0];
lean_object* v_target_1064_ = _args[1];
lean_object* v_nm_1065_ = _args[2];
lean_object* v_00_u03c6_1066_ = _args[3];
lean_object* v_G_1067_ = _args[4];
lean_object* v_a_1068_ = _args[5];
lean_object* v_a_1069_ = _args[6];
lean_object* v_a_1070_ = _args[7];
lean_object* v_a_1071_ = _args[8];
lean_object* v_a_1072_ = _args[9];
lean_object* v_a_1073_ = _args[10];
lean_object* v_a_1074_ = _args[11];
lean_object* v_a_1075_ = _args[12];
lean_object* v_a_1076_ = _args[13];
lean_object* v_a_1077_ = _args[14];
lean_object* v_a_1078_ = _args[15];
lean_object* v_a_1079_ = _args[16];
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f(v_goal_1063_, v_target_1064_, v_nm_1065_, v_00_u03c6_1066_, v_G_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1(lean_object* v_mvarId_1081_, lean_object* v_val_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v_mvarId_1081_, v_val_1082_, v___y_1091_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___boxed(lean_object* v_mvarId_1096_, lean_object* v_val_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1(v_mvarId_1096_, v_val_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1(lean_object* v_00_u03b2_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1___redArg(v_x_1112_, v_x_1113_, v_x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1116_, lean_object* v_x_1117_, size_t v_x_1118_, size_t v_x_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___redArg(v_x_1117_, v_x_1118_, v_x_1119_, v_x_1120_, v_x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
size_t v_x_11749__boxed_1129_; size_t v_x_11750__boxed_1130_; lean_object* v_res_1131_; 
v_x_11749__boxed_1129_ = lean_unbox_usize(v_x_1125_);
lean_dec(v_x_1125_);
v_x_11750__boxed_1130_ = lean_unbox_usize(v_x_1126_);
lean_dec(v_x_1126_);
v_res_1131_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2(v_00_u03b2_1123_, v_x_1124_, v_x_11749__boxed_1129_, v_x_11750__boxed_1130_, v_x_1127_, v_x_1128_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1132_, lean_object* v_n_1133_, lean_object* v_k_1134_, lean_object* v_v_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3___redArg(v_n_1133_, v_k_1134_, v_v_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1137_, size_t v_depth_1138_, lean_object* v_keys_1139_, lean_object* v_vals_1140_, lean_object* v_heq_1141_, lean_object* v_i_1142_, lean_object* v_entries_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___redArg(v_depth_1138_, v_keys_1139_, v_vals_1140_, v_i_1142_, v_entries_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1145_, lean_object* v_depth_1146_, lean_object* v_keys_1147_, lean_object* v_vals_1148_, lean_object* v_heq_1149_, lean_object* v_i_1150_, lean_object* v_entries_1151_){
_start:
{
size_t v_depth_boxed_1152_; lean_object* v_res_1153_; 
v_depth_boxed_1152_ = lean_unbox_usize(v_depth_1146_);
lean_dec(v_depth_1146_);
v_res_1153_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__4(v_00_u03b2_1145_, v_depth_boxed_1152_, v_keys_1147_, v_vals_1148_, v_heq_1149_, v_i_1150_, v_entries_1151_);
lean_dec_ref(v_vals_1148_);
lean_dec_ref(v_keys_1147_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_, lean_object* v_x_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_1155_, v_x_1156_, v_x_1157_, v_x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(lean_object* v_x_1160_, uint8_t v_bi_1161_, lean_object* v_t_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___y_1172_; lean_object* v___x_1175_; uint8_t v_debug_1176_; 
v___x_1175_ = lean_st_ref_get(v___y_1165_);
v_debug_1176_ = lean_ctor_get_uint8(v___x_1175_, sizeof(void*)*13);
lean_dec(v___x_1175_);
if (v_debug_1176_ == 0)
{
v___y_1172_ = v___y_1165_;
goto v___jp_1171_;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1162_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v___x_1178_; 
lean_dec_ref_known(v___x_1177_, 1);
v___x_1178_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_dec_ref_known(v___x_1178_, 1);
v___y_1172_ = v___y_1165_;
goto v___jp_1171_;
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v_b_1163_);
lean_dec_ref(v_t_1162_);
lean_dec(v_x_1160_);
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
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
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_b_1163_);
lean_dec_ref(v_t_1162_);
lean_dec(v_x_1160_);
v_a_1187_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1177_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1177_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
v___jp_1171_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = l_Lean_Expr_lam___override(v_x_1160_, v_t_1162_, v_b_1163_, v_bi_1161_);
v___x_1174_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1173_, v___y_1172_);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg___boxed(lean_object* v_x_1195_, lean_object* v_bi_1196_, lean_object* v_t_1197_, lean_object* v_b_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
uint8_t v_bi_boxed_1206_; lean_object* v_res_1207_; 
v_bi_boxed_1206_ = lean_unbox(v_bi_1196_);
v_res_1207_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(v_x_1195_, v_bi_boxed_1206_, v_t_1197_, v_b_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0(lean_object* v_x_1208_, uint8_t v_bi_1209_, lean_object* v_t_1210_, lean_object* v_b_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(v_x_1208_, v_bi_1209_, v_t_1210_, v_b_1211_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___boxed(lean_object* v_x_1225_, lean_object* v_bi_1226_, lean_object* v_t_1227_, lean_object* v_b_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
uint8_t v_bi_boxed_1241_; lean_object* v_res_1242_; 
v_bi_boxed_1241_ = lean_unbox(v_bi_1226_);
v_res_1242_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0(v_x_1225_, v_bi_boxed_1241_, v_t_1227_, v_b_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1242_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1243_; double v___x_1244_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_float_of_nat(v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(lean_object* v_cls_1248_, lean_object* v_msg_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_ref_1255_; lean_object* v___x_1256_; lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1302_; 
v_ref_1255_ = lean_ctor_get(v___y_1252_, 2);
v___x_1256_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0_spec__0(v_msg_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1302_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1302_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v_traceState_1262_; lean_object* v_env_1263_; lean_object* v_nextMacroScope_1264_; lean_object* v_ngen_1265_; lean_object* v_auxDeclNGen_1266_; lean_object* v_cache_1267_; lean_object* v_recordedDeps_1268_; lean_object* v_messages_1269_; lean_object* v_infoState_1270_; lean_object* v_snapshotTasks_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1301_; 
v___x_1261_ = lean_st_ref_take(v___y_1253_);
v_traceState_1262_ = lean_ctor_get(v___x_1261_, 4);
v_env_1263_ = lean_ctor_get(v___x_1261_, 0);
v_nextMacroScope_1264_ = lean_ctor_get(v___x_1261_, 1);
v_ngen_1265_ = lean_ctor_get(v___x_1261_, 2);
v_auxDeclNGen_1266_ = lean_ctor_get(v___x_1261_, 3);
v_cache_1267_ = lean_ctor_get(v___x_1261_, 5);
v_recordedDeps_1268_ = lean_ctor_get(v___x_1261_, 6);
v_messages_1269_ = lean_ctor_get(v___x_1261_, 7);
v_infoState_1270_ = lean_ctor_get(v___x_1261_, 8);
v_snapshotTasks_1271_ = lean_ctor_get(v___x_1261_, 9);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1273_ = v___x_1261_;
v_isShared_1274_ = v_isSharedCheck_1301_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_snapshotTasks_1271_);
lean_inc(v_infoState_1270_);
lean_inc(v_messages_1269_);
lean_inc(v_recordedDeps_1268_);
lean_inc(v_cache_1267_);
lean_inc(v_traceState_1262_);
lean_inc(v_auxDeclNGen_1266_);
lean_inc(v_ngen_1265_);
lean_inc(v_nextMacroScope_1264_);
lean_inc(v_env_1263_);
lean_dec(v___x_1261_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1301_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
uint64_t v_tid_1275_; lean_object* v_traces_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1300_; 
v_tid_1275_ = lean_ctor_get_uint64(v_traceState_1262_, sizeof(void*)*1);
v_traces_1276_ = lean_ctor_get(v_traceState_1262_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_traceState_1262_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1278_ = v_traceState_1262_;
v_isShared_1279_ = v_isSharedCheck_1300_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_traces_1276_);
lean_dec(v_traceState_1262_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1300_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; double v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__0);
v___x_1283_ = 0;
v___x_1284_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__1));
v___x_1285_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1285_, 0, v_cls_1248_);
lean_ctor_set(v___x_1285_, 1, v___x_1281_);
lean_ctor_set(v___x_1285_, 2, v___x_1284_);
lean_ctor_set_float(v___x_1285_, sizeof(void*)*3, v___x_1282_);
lean_ctor_set_float(v___x_1285_, sizeof(void*)*3 + 8, v___x_1282_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*3 + 16, v___x_1283_);
v___x_1286_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___closed__2));
v___x_1287_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v_a_1257_);
lean_ctor_set(v___x_1287_, 2, v___x_1286_);
lean_inc(v_ref_1255_);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v_ref_1255_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = l_Lean_PersistentArray_push___redArg(v_traces_1276_, v___x_1288_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1289_);
v___x_1291_ = v___x_1278_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1289_);
lean_ctor_set_uint64(v_reuseFailAlloc_1299_, sizeof(void*)*1, v_tid_1275_);
v___x_1291_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1293_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 4, v___x_1291_);
v___x_1293_ = v___x_1273_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_env_1263_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_nextMacroScope_1264_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v_ngen_1265_);
lean_ctor_set(v_reuseFailAlloc_1298_, 3, v_auxDeclNGen_1266_);
lean_ctor_set(v_reuseFailAlloc_1298_, 4, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1298_, 5, v_cache_1267_);
lean_ctor_set(v_reuseFailAlloc_1298_, 6, v_recordedDeps_1268_);
lean_ctor_set(v_reuseFailAlloc_1298_, 7, v_messages_1269_);
lean_ctor_set(v_reuseFailAlloc_1298_, 8, v_infoState_1270_);
lean_ctor_set(v_reuseFailAlloc_1298_, 9, v_snapshotTasks_1271_);
v___x_1293_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = lean_st_ref_put(v___y_1253_, v___x_1293_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1280_);
v___x_1296_ = v___x_1259_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1280_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg___boxed(lean_object* v_cls_1303_, lean_object* v_msg_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(v_cls_1303_, v_msg_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1310_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8));
v___x_1331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__10));
v___x_1332_ = l_Lean_Name_append(v___x_1331_, v___x_1330_);
return v___x_1332_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__12));
v___x_1335_ = l_Lean_stringToMessageData(v___x_1334_);
return v___x_1335_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__14));
v___x_1338_ = l_Lean_stringToMessageData(v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f(lean_object* v_goal_1339_, lean_object* v_nm_1340_, lean_object* v_eqn_1341_, lean_object* v_G_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___y_1356_; uint8_t v___y_1357_; lean_object* v___x_1362_; 
lean_inc_ref(v_eqn_1341_);
v___x_1362_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_eqSubstCandidate_x3f___redArg(v_eqn_1341_, v_G_1342_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1556_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1556_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1556_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
if (lean_obj_tag(v_a_1363_) == 1)
{
lean_object* v_val_1367_; lean_object* v_snd_1368_; lean_object* v_snd_1369_; lean_object* v_fst_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1550_; 
lean_del_object(v___x_1365_);
v_val_1367_ = lean_ctor_get(v_a_1363_, 0);
lean_inc(v_val_1367_);
lean_dec_ref_known(v_a_1363_, 1);
v_snd_1368_ = lean_ctor_get(v_val_1367_, 1);
lean_inc(v_snd_1368_);
v_snd_1369_ = lean_ctor_get(v_snd_1368_, 1);
lean_inc(v_snd_1369_);
v_fst_1370_ = lean_ctor_get(v_val_1367_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_val_1367_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_val_1367_, 1);
lean_dec(v_unused_1551_);
v___x_1372_ = v_val_1367_;
v_isShared_1373_ = v_isSharedCheck_1550_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_fst_1370_);
lean_dec(v_val_1367_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1550_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v_fst_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1548_; 
v_fst_1374_ = lean_ctor_get(v_snd_1368_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_snd_1368_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v_snd_1368_, 1);
lean_dec(v_unused_1549_);
v___x_1376_ = v_snd_1368_;
v_isShared_1377_ = v_isSharedCheck_1548_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_fst_1374_);
lean_dec(v_snd_1368_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1548_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v_fst_1378_; lean_object* v_snd_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1547_; 
v_fst_1378_ = lean_ctor_get(v_snd_1369_, 0);
v_snd_1379_ = lean_ctor_get(v_snd_1369_, 1);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_snd_1369_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1381_ = v_snd_1369_;
v_isShared_1382_ = v_isSharedCheck_1547_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_snd_1379_);
lean_inc(v_fst_1378_);
lean_dec(v_snd_1369_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1547_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___y_1384_; lean_object* v___x_1389_; 
lean_inc(v_fst_1370_);
v___x_1389_ = l_Lean_Meta_Sym_inferType(v_fst_1370_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc_n(v_a_1390_, 2);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_1390_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = l_Lean_Expr_fvarId_x21(v_fst_1370_);
v___x_1394_ = l_Lean_FVarId_getUserName___redArg(v___x_1393_, v_a_1350_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___x_1396_ = 0;
lean_inc(v_fst_1378_);
lean_inc(v_a_1390_);
v___x_1397_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(v_a_1395_, v___x_1396_, v_a_1390_, v_fst_1378_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v_fst_1400_; lean_object* v_snd_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_mk_empty_array_with_capacity(v___x_1448_);
lean_inc(v_fst_1374_);
v___x_1450_ = lean_array_push(v___x_1449_, v_fst_1374_);
v___x_1451_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_fst_1378_, v___x_1450_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1451_) == 0)
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_unbox(v_snd_1379_);
if (v___x_1452_ == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1454_; 
v_a_1453_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1454_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__0___redArg(v_nm_1340_, v___x_1396_, v_eqn_1341_, v_a_1453_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v___x_1456_ = lean_box(0);
v___x_1457_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1455_, v___x_1456_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc_n(v_a_1458_, 2);
lean_dec_ref_known(v___x_1457_, 1);
v_fst_1400_ = v_a_1458_;
v_snd_1401_ = v_a_1458_;
v___y_1402_ = v_a_1343_;
v___y_1403_ = v_a_1344_;
v___y_1404_ = v_a_1345_;
v___y_1405_ = v_a_1346_;
v___y_1406_ = v_a_1347_;
v___y_1407_ = v_a_1348_;
v___y_1408_ = v_a_1349_;
v___y_1409_ = v_a_1350_;
v___y_1410_ = v_a_1351_;
v___y_1411_ = v_a_1352_;
v___y_1412_ = v_a_1353_;
goto v___jp_1399_;
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec(v_a_1398_);
lean_dec(v_a_1392_);
lean_dec(v_a_1390_);
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
lean_dec(v_goal_1339_);
v_a_1459_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1457_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1457_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_a_1398_);
lean_dec(v_a_1392_);
lean_dec(v_a_1390_);
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
lean_dec(v_goal_1339_);
v_a_1467_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1454_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1454_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
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
lean_object* v_a_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_a_1475_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1476_ = lean_box(0);
v___x_1477_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1475_, v___x_1476_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = l_Lean_Meta_Sym_shareCommon(v_a_1478_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1481_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc_n(v_a_1480_, 2);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1481_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__0___redArg(v_nm_1340_, v___x_1396_, v_eqn_1341_, v_a_1480_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v_fst_1400_ = v_a_1480_;
v_snd_1401_ = v_a_1482_;
v___y_1402_ = v_a_1343_;
v___y_1403_ = v_a_1344_;
v___y_1404_ = v_a_1345_;
v___y_1405_ = v_a_1346_;
v___y_1406_ = v_a_1347_;
v___y_1407_ = v_a_1348_;
v___y_1408_ = v_a_1349_;
v___y_1409_ = v_a_1350_;
v___y_1410_ = v_a_1351_;
v___y_1411_ = v_a_1352_;
v___y_1412_ = v_a_1353_;
goto v___jp_1399_;
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_a_1480_);
lean_dec(v_a_1398_);
lean_dec(v_a_1392_);
lean_dec(v_a_1390_);
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
lean_dec(v_goal_1339_);
v_a_1483_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1481_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1481_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_a_1398_);
lean_dec(v_a_1392_);
lean_dec(v_a_1390_);
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
lean_dec_ref(v_eqn_1341_);
lean_dec(v_nm_1340_);
lean_dec(v_goal_1339_);
v_a_1491_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1479_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1479_);
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
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_a_1398_);
lean_dec(v_a_1392_);
lean_dec(v_a_1390_);
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
lean_dec_ref(v_eqn_1341_);
lean_dec(v_nm_1340_);
lean_dec(v_goal_1339_);
v_a_1499_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1477_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1477_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v_a_1398_);
lean_dec(v_a_1392_);
lean_dec(v_a_1390_);
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
lean_dec_ref(v_eqn_1341_);
lean_dec(v_nm_1340_);
lean_dec(v_goal_1339_);
v_a_1507_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1451_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1451_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
v___jp_1399_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1413_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__3));
v___x_1414_ = lean_box(0);
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 1);
lean_ctor_set(v___x_1381_, 1, v___x_1414_);
lean_ctor_set(v___x_1381_, 0, v_a_1392_);
v___x_1416_ = v___x_1381_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1392_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v_toCold_1420_; lean_object* v_options_1421_; uint8_t v_hasTrace_1422_; 
v___x_1417_ = l_Lean_mkConst(v___x_1413_, v___x_1416_);
lean_inc(v_fst_1374_);
lean_inc(v_fst_1370_);
v___x_1418_ = l_Lean_mkApp5(v___x_1417_, v_a_1390_, v_fst_1370_, v_fst_1374_, v_a_1398_, v_snd_1401_);
v___x_1419_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f_spec__1___redArg(v_goal_1339_, v___x_1418_, v___y_1410_);
lean_dec_ref(v___x_1419_);
v_toCold_1420_ = lean_ctor_get(v___y_1411_, 0);
v_options_1421_ = lean_ctor_get(v_toCold_1420_, 2);
v_hasTrace_1422_ = lean_ctor_get_uint8(v_options_1421_, sizeof(void*)*1);
if (v_hasTrace_1422_ == 0)
{
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
v___y_1384_ = v_fst_1400_;
goto v___jp_1383_;
}
else
{
lean_object* v_inheritedTraceOptions_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v_inheritedTraceOptions_1423_ = lean_ctor_get(v_toCold_1420_, 11);
v___x_1424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__8));
v___x_1425_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__11);
v___x_1426_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1423_, v_options_1421_, v___x_1425_);
if (v___x_1426_ == 0)
{
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
v___y_1384_ = v_fst_1400_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1427_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__13);
v___x_1428_ = l_Lean_MessageData_ofExpr(v_fst_1370_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 7);
lean_ctor_set(v___x_1376_, 1, v___x_1428_);
lean_ctor_set(v___x_1376_, 0, v___x_1427_);
v___x_1430_ = v___x_1376_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1431_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15, &l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15_once, _init_l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___closed__15);
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 7);
lean_ctor_set(v___x_1372_, 1, v___x_1431_);
lean_ctor_set(v___x_1372_, 0, v___x_1430_);
v___x_1433_ = v___x_1372_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = l_Lean_MessageData_ofExpr(v_fst_1374_);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(v___x_1424_, v___x_1435_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_dec_ref_known(v___x_1436_, 1);
v___y_1384_ = v_fst_1400_;
goto v___jp_1383_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v_fst_1400_);
lean_dec(v_snd_1379_);
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
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
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec(v_a_1392_);
lean_dec(v_a_1390_);
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_dec(v_fst_1378_);
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
lean_dec_ref(v_eqn_1341_);
lean_dec(v_nm_1340_);
lean_dec(v_goal_1339_);
v_a_1515_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1397_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1397_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v_a_1392_);
lean_dec(v_a_1390_);
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_dec(v_fst_1378_);
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
lean_dec_ref(v_eqn_1341_);
lean_dec(v_nm_1340_);
lean_dec(v_goal_1339_);
v_a_1523_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1394_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1394_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
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
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_a_1390_);
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_dec(v_fst_1378_);
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
lean_dec_ref(v_eqn_1341_);
lean_dec(v_nm_1340_);
lean_dec(v_goal_1339_);
v_a_1531_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1391_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1391_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_dec(v_fst_1378_);
lean_del_object(v___x_1376_);
lean_dec(v_fst_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_fst_1370_);
lean_dec_ref(v_eqn_1341_);
lean_dec(v_nm_1340_);
lean_dec(v_goal_1339_);
v_a_1539_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1389_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1389_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
v___jp_1383_:
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = l_Lean_Expr_mvarId_x21(v___y_1384_);
lean_dec_ref(v___y_1384_);
v___x_1386_ = lean_unbox(v_snd_1379_);
lean_dec(v_snd_1379_);
if (v___x_1386_ == 0)
{
uint8_t v___x_1387_; 
v___x_1387_ = 1;
v___y_1356_ = v___x_1385_;
v___y_1357_ = v___x_1387_;
goto v___jp_1355_;
}
else
{
uint8_t v___x_1388_; 
v___x_1388_ = 0;
v___y_1356_ = v___x_1385_;
v___y_1357_ = v___x_1388_;
goto v___jp_1355_;
}
}
}
}
}
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_dec(v_a_1363_);
lean_dec_ref(v_eqn_1341_);
lean_dec(v_nm_1340_);
lean_dec(v_goal_1339_);
v___x_1552_ = lean_box(0);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1552_);
v___x_1554_ = v___x_1365_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
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
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v_eqn_1341_);
lean_dec(v_nm_1340_);
lean_dec(v_goal_1339_);
v_a_1557_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1362_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1362_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
v___jp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1358_ = lean_box(v___y_1357_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___y_1356_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___boxed(lean_object* v_goal_1565_, lean_object* v_nm_1566_, lean_object* v_eqn_1567_, lean_object* v_G_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f(v_goal_1565_, v_nm_1566_, v_eqn_1567_, v_G_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1(lean_object* v_cls_1582_, lean_object* v_msg_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___redArg(v_cls_1582_, v_msg_1583_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1___boxed(lean_object* v_cls_1597_, lean_object* v_msg_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f_spec__1(v_cls_1597_, v_msg_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0(lean_object* v_x_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___x_1625_; 
lean_inc(v___y_1619_);
lean_inc_ref(v___y_1618_);
lean_inc(v___y_1617_);
lean_inc_ref(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc(v___y_1614_);
lean_inc_ref(v___y_1613_);
v___x_1625_ = lean_apply_12(v_x_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, lean_box(0));
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0___boxed(lean_object* v_x_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0(v_x_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(lean_object* v_mvarId_1640_, lean_object* v_x_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___f_1654_; lean_object* v___x_1655_; 
lean_inc(v___y_1648_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
lean_inc(v___y_1644_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
v___f_1654_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1654_, 0, v_x_1641_);
lean_closure_set(v___f_1654_, 1, v___y_1642_);
lean_closure_set(v___f_1654_, 2, v___y_1643_);
lean_closure_set(v___f_1654_, 3, v___y_1644_);
lean_closure_set(v___f_1654_, 4, v___y_1645_);
lean_closure_set(v___f_1654_, 5, v___y_1646_);
lean_closure_set(v___f_1654_, 6, v___y_1647_);
lean_closure_set(v___f_1654_, 7, v___y_1648_);
v___x_1655_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1640_, v___f_1654_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
if (lean_obj_tag(v___x_1655_) == 0)
{
return v___x_1655_;
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg___boxed(lean_object* v_mvarId_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_mvarId_1664_, v_x_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0(lean_object* v_00_u03b1_1679_, lean_object* v_mvarId_1680_, lean_object* v_x_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_mvarId_1680_, v_x_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_mvarId_1696_, lean_object* v_x_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0(v_00_u03b1_1695_, v_mvarId_1696_, v_x_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(lean_object* v___x_1711_, lean_object* v___f_1712_, lean_object* v_____r_1713_, lean_object* v_goal_1714_, lean_object* v_pending_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
lean_inc(v___x_1711_);
v___x_1728_ = l_Lean_Elab_Tactic_VCGen_introsHygienicN(v_goal_1714_, v___x_1711_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc_n(v_a_1729_, 2);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1730_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_a_1729_, v___f_1712_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1755_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1755_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1755_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___y_1736_; lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_LocalContext_lastDecl(v_a_1731_);
lean_dec(v_a_1731_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_box(0);
v___y_1736_ = v___x_1745_;
goto v___jp_1735_;
}
else
{
lean_object* v_val_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1754_; 
v_val_1746_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1748_ = v___x_1744_;
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_val_1746_);
lean_dec(v___x_1744_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1754_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = l_Lean_LocalDecl_fvarId(v_val_1746_);
lean_dec(v_val_1746_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1750_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
v___y_1736_ = v___x_1752_;
goto v___jp_1735_;
}
}
}
v___jp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1737_ = lean_nat_sub(v_pending_1715_, v___x_1711_);
lean_dec(v___x_1711_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v___y_1736_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v_a_1729_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1740_);
v___x_1742_ = v___x_1733_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_a_1729_);
lean_dec(v___x_1711_);
v_a_1756_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1730_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1730_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v___f_1712_);
lean_dec(v___x_1711_);
v_a_1764_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1728_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1728_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1772_ = _args[0];
lean_object* v___f_1773_ = _args[1];
lean_object* v_____r_1774_ = _args[2];
lean_object* v_goal_1775_ = _args[3];
lean_object* v_pending_1776_ = _args[4];
lean_object* v___y_1777_ = _args[5];
lean_object* v___y_1778_ = _args[6];
lean_object* v___y_1779_ = _args[7];
lean_object* v___y_1780_ = _args[8];
lean_object* v___y_1781_ = _args[9];
lean_object* v___y_1782_ = _args[10];
lean_object* v___y_1783_ = _args[11];
lean_object* v___y_1784_ = _args[12];
lean_object* v___y_1785_ = _args[13];
lean_object* v___y_1786_ = _args[14];
lean_object* v___y_1787_ = _args[15];
lean_object* v___y_1788_ = _args[16];
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1772_, v___f_1773_, v_____r_1774_, v_goal_1775_, v_pending_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v_pending_1776_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0(lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_lctx_1802_; lean_object* v___x_1803_; 
v_lctx_1802_ = lean_ctor_get(v___y_1797_, 2);
lean_inc_ref(v_lctx_1802_);
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v_lctx_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0___boxed(lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__0(v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
return v_res_1816_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__1));
v___x_1820_ = l_Lean_stringToMessageData(v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(lean_object* v_a_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___y_1835_; lean_object* v_snd_1855_; lean_object* v_fst_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1965_; 
v_snd_1855_ = lean_ctor_get(v_a_1821_, 1);
v_fst_1856_ = lean_ctor_get(v_a_1821_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_a_1821_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1858_ = v_a_1821_;
v_isShared_1859_ = v_isSharedCheck_1965_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_snd_1855_);
lean_inc(v_fst_1856_);
lean_dec(v_a_1821_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1965_;
goto v_resetjp_1857_;
}
v___jp_1834_:
{
if (lean_obj_tag(v___y_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1846_; 
v_a_1836_ = lean_ctor_get(v___y_1835_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___y_1835_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1838_ = v___y_1835_;
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___y_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
if (lean_obj_tag(v_a_1836_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; 
v_a_1840_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v_a_1836_, 1);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v_a_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
else
{
lean_object* v_a_1844_; 
lean_del_object(v___x_1838_);
v_a_1844_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v_a_1836_, 1);
v_a_1821_ = v_a_1844_;
goto _start;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_a_1847_ = lean_ctor_get(v___y_1835_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___y_1835_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___y_1835_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___y_1835_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
v_resetjp_1857_:
{
lean_object* v_fst_1860_; lean_object* v_snd_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1964_; 
v_fst_1860_ = lean_ctor_get(v_snd_1855_, 0);
v_snd_1861_ = lean_ctor_get(v_snd_1855_, 1);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_snd_1855_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1863_ = v_snd_1855_;
v_isShared_1864_ = v_isSharedCheck_1964_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_snd_1861_);
lean_inc(v_fst_1860_);
lean_dec(v_snd_1855_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1964_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = lean_nat_dec_lt(v___x_1865_, v_fst_1860_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1868_; 
if (v_isShared_1864_ == 0)
{
v___x_1868_ = v___x_1863_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_fst_1860_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_snd_1861_);
v___x_1868_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1870_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v___x_1868_);
v___x_1870_ = v___x_1858_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_fst_1856_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
}
}
else
{
lean_object* v___f_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___f_1874_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__0));
v___x_1875_ = lean_unsigned_to_nat(1u);
lean_inc(v_fst_1856_);
v___x_1876_ = l_Lean_MVarId_getType(v_fst_1856_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
if (lean_obj_tag(v_a_1877_) == 7)
{
lean_object* v_binderName_1878_; lean_object* v_binderType_1879_; lean_object* v_body_1880_; uint8_t v___x_1881_; 
v_binderName_1878_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_binderName_1878_);
v_binderType_1879_ = lean_ctor_get(v_a_1877_, 1);
lean_inc_ref(v_binderType_1879_);
v_body_1880_ = lean_ctor_get(v_a_1877_, 2);
lean_inc_ref(v_body_1880_);
v___x_1881_ = l_Lean_Expr_hasLooseBVars(v_body_1880_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_inc_ref(v_body_1880_);
lean_inc_ref(v_binderType_1879_);
lean_inc(v_binderName_1878_);
lean_inc_n(v_fst_1856_, 2);
v___x_1882_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_splitConjHyp_x3f___boxed), 17, 5);
lean_closure_set(v___x_1882_, 0, v_fst_1856_);
lean_closure_set(v___x_1882_, 1, v_a_1877_);
lean_closure_set(v___x_1882_, 2, v_binderName_1878_);
lean_closure_set(v___x_1882_, 3, v_binderType_1879_);
lean_closure_set(v___x_1882_, 4, v_body_1880_);
v___x_1883_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_fst_1856_, v___x_1882_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
if (lean_obj_tag(v_a_1884_) == 1)
{
lean_object* v_val_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
lean_dec(v_fst_1856_);
v_val_1885_ = lean_ctor_get(v_a_1884_, 0);
lean_inc(v_val_1885_);
lean_dec_ref_known(v_a_1884_, 1);
v___x_1886_ = lean_nat_add(v_fst_1860_, v___x_1875_);
lean_dec(v_fst_1860_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1886_);
v___x_1888_ = v___x_1863_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_snd_1861_);
v___x_1888_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v___x_1888_);
lean_ctor_set(v___x_1858_, 0, v_val_1885_);
v___x_1890_ = v___x_1858_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_val_1885_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
v_a_1821_ = v___x_1890_;
goto _start;
}
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec(v_a_1884_);
lean_del_object(v___x_1858_);
lean_inc_n(v_fst_1856_, 2);
v___x_1894_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_substEqHyp_x3f___boxed), 16, 4);
lean_closure_set(v___x_1894_, 0, v_fst_1856_);
lean_closure_set(v___x_1894_, 1, v_binderName_1878_);
lean_closure_set(v___x_1894_, 2, v_binderType_1879_);
lean_closure_set(v___x_1894_, 3, v_body_1880_);
v___x_1895_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_introPre_spec__0___redArg(v_fst_1856_, v___x_1894_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
if (lean_obj_tag(v_a_1896_) == 1)
{
lean_object* v_val_1897_; lean_object* v_snd_1898_; uint8_t v___x_1899_; 
lean_dec(v_fst_1856_);
v_val_1897_ = lean_ctor_get(v_a_1896_, 0);
lean_inc(v_val_1897_);
lean_dec_ref_known(v_a_1896_, 1);
v_snd_1898_ = lean_ctor_get(v_val_1897_, 1);
v___x_1899_ = lean_unbox(v_snd_1898_);
if (v___x_1899_ == 0)
{
lean_object* v_fst_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1912_; 
v_fst_1900_ = lean_ctor_get(v_val_1897_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_val_1897_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v_val_1897_, 1);
lean_dec(v_unused_1913_);
v___x_1902_ = v_val_1897_;
v_isShared_1903_ = v_isSharedCheck_1912_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_fst_1900_);
lean_dec(v_val_1897_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1912_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = lean_nat_sub(v_fst_1860_, v___x_1875_);
lean_dec(v_fst_1860_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v_snd_1861_);
lean_ctor_set(v___x_1902_, 0, v___x_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_snd_1861_);
v___x_1906_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1908_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 1, v___x_1906_);
lean_ctor_set(v___x_1863_, 0, v_fst_1900_);
v___x_1908_ = v___x_1863_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_fst_1900_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
v_a_1821_ = v___x_1908_;
goto _start;
}
}
}
}
else
{
lean_object* v_fst_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_del_object(v___x_1863_);
lean_dec(v_snd_1861_);
v_fst_1914_ = lean_ctor_get(v_val_1897_, 0);
lean_inc(v_fst_1914_);
lean_dec(v_val_1897_);
v___x_1915_ = lean_box(0);
v___x_1916_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1875_, v___f_1874_, v___x_1915_, v_fst_1914_, v_fst_1860_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v_fst_1860_);
v___y_1835_ = v___x_1916_;
goto v___jp_1834_;
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec(v_a_1896_);
lean_del_object(v___x_1863_);
lean_dec(v_snd_1861_);
v___x_1917_ = lean_box(0);
v___x_1918_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1875_, v___f_1874_, v___x_1917_, v_fst_1856_, v_fst_1860_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v_fst_1860_);
v___y_1835_ = v___x_1918_;
goto v___jp_1834_;
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_del_object(v___x_1863_);
lean_dec(v_snd_1861_);
lean_dec(v_fst_1860_);
lean_dec(v_fst_1856_);
v_a_1919_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1895_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1895_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
lean_del_object(v___x_1863_);
lean_dec(v_snd_1861_);
lean_dec(v_fst_1860_);
lean_del_object(v___x_1858_);
lean_dec(v_fst_1856_);
v_a_1927_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1883_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1883_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_dec_ref(v_body_1880_);
lean_dec_ref(v_binderType_1879_);
lean_dec(v_binderName_1878_);
lean_dec_ref_known(v_a_1877_, 3);
lean_del_object(v___x_1863_);
lean_dec(v_snd_1861_);
lean_del_object(v___x_1858_);
v___x_1935_ = lean_box(0);
v___x_1936_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___lam__1(v___x_1875_, v___f_1874_, v___x_1935_, v_fst_1856_, v_fst_1860_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v_fst_1860_);
v___y_1835_ = v___x_1936_;
goto v___jp_1834_;
}
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_dec(v_a_1877_);
v___x_1937_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___closed__2);
lean_inc(v_fst_1856_);
v___x_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1938_, 0, v_fst_1856_);
v___x_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_1939_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v___x_1942_; 
lean_dec_ref_known(v___x_1940_, 1);
if (v_isShared_1864_ == 0)
{
v___x_1942_ = v___x_1863_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_fst_1860_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_snd_1861_);
v___x_1942_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1944_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v___x_1942_);
v___x_1944_ = v___x_1858_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_fst_1856_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
v_a_1821_ = v___x_1944_;
goto _start;
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_del_object(v___x_1863_);
lean_dec(v_snd_1861_);
lean_dec(v_fst_1860_);
lean_del_object(v___x_1858_);
lean_dec(v_fst_1856_);
v_a_1948_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1940_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1940_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_del_object(v___x_1863_);
lean_dec(v_snd_1861_);
lean_dec(v_fst_1860_);
lean_del_object(v___x_1858_);
lean_dec(v_fst_1856_);
v_a_1956_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1876_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1876_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg___boxed(lean_object* v_a_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(v_a_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1979_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_introPre___closed__1(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introPre___closed__0));
v___x_1982_ = l_Lean_stringToMessageData(v___x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre(lean_object* v_rule_1986_, lean_object* v_goal_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = lean_box(0);
lean_inc(v_goal_1987_);
v___x_2010_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_1986_, v_goal_1987_, v___x_2009_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
if (lean_obj_tag(v_a_2011_) == 1)
{
lean_object* v_mvarIds_2012_; 
v_mvarIds_2012_ = lean_ctor_get(v_a_2011_, 0);
lean_inc(v_mvarIds_2012_);
lean_dec_ref_known(v_a_2011_, 1);
if (lean_obj_tag(v_mvarIds_2012_) == 1)
{
lean_object* v_tail_2013_; 
v_tail_2013_ = lean_ctor_get(v_mvarIds_2012_, 1);
if (lean_obj_tag(v_tail_2013_) == 0)
{
lean_object* v_head_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_goal_1987_);
v_head_2014_ = lean_ctor_get(v_mvarIds_2012_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_mvarIds_2012_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v_mvarIds_2012_, 1);
lean_dec(v_unused_2051_);
v___x_2016_ = v_mvarIds_2012_;
v_isShared_2017_ = v_isSharedCheck_2050_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_head_2014_);
lean_dec(v_mvarIds_2012_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2050_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_introPre___closed__2));
if (v_isShared_2017_ == 0)
{
lean_ctor_set_tag(v___x_2016_, 0);
lean_ctor_set(v___x_2016_, 1, v___x_2018_);
v___x_2020_ = v___x_2016_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_head_2014_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; 
v___x_2021_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(v___x_2020_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2040_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2040_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2040_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v_snd_2026_; lean_object* v_fst_2027_; lean_object* v_snd_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2038_; 
v_snd_2026_ = lean_ctor_get(v_a_2022_, 1);
lean_inc(v_snd_2026_);
v_fst_2027_ = lean_ctor_get(v_a_2022_, 0);
lean_inc(v_fst_2027_);
lean_dec(v_a_2022_);
v_snd_2028_ = lean_ctor_get(v_snd_2026_, 1);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_snd_2026_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v_snd_2026_, 0);
lean_dec(v_unused_2039_);
v___x_2030_ = v_snd_2026_;
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_snd_2028_);
lean_dec(v_snd_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v_fst_2027_);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_fst_2027_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_snd_2028_);
v___x_2033_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2035_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2033_);
v___x_2035_ = v___x_2024_;
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
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
v_a_2041_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2021_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2021_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2012_, 2);
v___y_2001_ = v_a_1995_;
v___y_2002_ = v_a_1996_;
v___y_2003_ = v_a_1997_;
v___y_2004_ = v_a_1998_;
goto v___jp_2000_;
}
}
else
{
lean_dec(v_mvarIds_2012_);
v___y_2001_ = v_a_1995_;
v___y_2002_ = v_a_1996_;
v___y_2003_ = v_a_1997_;
v___y_2004_ = v_a_1998_;
goto v___jp_2000_;
}
}
else
{
lean_dec(v_a_2011_);
v___y_2001_ = v_a_1995_;
v___y_2002_ = v_a_1996_;
v___y_2003_ = v_a_1997_;
v___y_2004_ = v_a_1998_;
goto v___jp_2000_;
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_goal_1987_);
v_a_2052_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2010_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2010_);
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
v___jp_2000_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2005_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_introPre___closed__1, &l_Lean_Elab_Tactic_VCGen_introPre___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_introPre___closed__1);
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_goal_1987_);
v___x_2007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2005_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_2007_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
return v___x_2008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_introPre___boxed(lean_object* v_rule_2060_, lean_object* v_goal_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_Elab_Tactic_VCGen_introPre(v_rule_2060_, v_goal_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1(lean_object* v_inst_2075_, lean_object* v_a_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___redArg(v_a_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1___boxed(lean_object* v_inst_2090_, lean_object* v_a_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_introPre_spec__1(v_inst_2090_, v_a_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(lean_object* v_declName_2105_, lean_object* v_us_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = l_Lean_Expr_const___override(v_declName_2105_, v_us_2106_);
v___x_2110_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2109_, v___y_2107_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg___boxed(lean_object* v_declName_2111_, lean_object* v_us_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v_declName_2111_, v_us_2112_, v___y_2113_);
lean_dec(v___y_2113_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0(lean_object* v_declName_2116_, lean_object* v_us_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v_declName_2116_, v_us_2117_, v___y_2124_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___boxed(lean_object* v_declName_2131_, lean_object* v_us_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0(v_declName_2131_, v_us_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2___redArg(lean_object* v_f_2146_, lean_object* v_a_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v___y_2156_; lean_object* v___x_2159_; uint8_t v_debug_2160_; 
v___x_2159_ = lean_st_ref_get(v___y_2149_);
v_debug_2160_ = lean_ctor_get_uint8(v___x_2159_, sizeof(void*)*13);
lean_dec(v___x_2159_);
if (v_debug_2160_ == 0)
{
v___y_2156_ = v___y_2149_;
goto v___jp_2155_;
}
else
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2146_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2162_; 
lean_dec_ref_known(v___x_2161_, 1);
v___x_2162_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_dec_ref_known(v___x_2162_, 1);
v___y_2156_ = v___y_2149_;
goto v___jp_2155_;
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec_ref(v_a_2147_);
lean_dec_ref(v_f_2146_);
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v_a_2147_);
lean_dec_ref(v_f_2146_);
v_a_2171_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2161_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2161_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
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
v___jp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = l_Lean_Expr_app___override(v_f_2146_, v_a_2147_);
v___x_2158_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2157_, v___y_2156_);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_2179_, lean_object* v_a_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2___redArg(v_f_2179_, v_a_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1(lean_object* v_args_2189_, lean_object* v_endIdx_2190_, lean_object* v_b_2191_, lean_object* v_i_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
uint8_t v___x_2205_; 
v___x_2205_ = lean_nat_dec_le(v_endIdx_2190_, v_i_2192_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2206_ = l_Lean_instInhabitedExpr;
v___x_2207_ = lean_array_get_borrowed(v___x_2206_, v_args_2189_, v_i_2192_);
lean_inc(v___x_2207_);
v___x_2208_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2___redArg(v_b_2191_, v___x_2207_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v___x_2210_ = lean_unsigned_to_nat(1u);
v___x_2211_ = lean_nat_add(v_i_2192_, v___x_2210_);
lean_dec(v_i_2192_);
v_b_2191_ = v_a_2209_;
v_i_2192_ = v___x_2211_;
goto _start;
}
else
{
lean_dec(v_i_2192_);
return v___x_2208_;
}
}
else
{
lean_object* v___x_2213_; 
lean_dec(v_i_2192_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v_b_2191_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1___boxed(lean_object* v_args_2214_, lean_object* v_endIdx_2215_, lean_object* v_b_2216_, lean_object* v_i_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1(v_args_2214_, v_endIdx_2215_, v_b_2216_, v_i_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_endIdx_2215_);
lean_dec_ref(v_args_2214_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1(lean_object* v_f_2231_, lean_object* v_args_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_array_get_size(v_args_2232_);
v___x_2247_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1(v_args_2232_, v___x_2246_, v_f_2231_, v___x_2245_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1___boxed(lean_object* v_f_2248_, lean_object* v_args_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1(v_f_2248_, v_args_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v_args_2249_);
return v_res_2262_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8(void){
_start:
{
lean_object* v___x_2281_; lean_object* v_dummy_2282_; 
v___x_2281_ = lean_box(0);
v_dummy_2282_ = l_Lean_Expr_sort___override(v___x_2281_);
return v_dummy_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2(lean_object* v_goal_2283_, lean_object* v_x_2284_, lean_object* v_x_2285_, lean_object* v_x_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
if (lean_obj_tag(v_x_2284_) == 5)
{
lean_object* v_fn_2299_; lean_object* v_arg_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v_fn_2299_ = lean_ctor_get(v_x_2284_, 0);
lean_inc_ref(v_fn_2299_);
v_arg_2300_ = lean_ctor_get(v_x_2284_, 1);
lean_inc_ref(v_arg_2300_);
lean_dec_ref_known(v_x_2284_, 2);
v___x_2301_ = lean_array_set(v_x_2285_, v_x_2286_, v_arg_2300_);
v___x_2302_ = lean_unsigned_to_nat(1u);
v___x_2303_ = lean_nat_sub(v_x_2286_, v___x_2302_);
lean_dec(v_x_2286_);
v_x_2284_ = v_fn_2299_;
v_x_2285_ = v___x_2301_;
v_x_2286_ = v___x_2303_;
goto _start;
}
else
{
lean_object* v___x_2305_; uint8_t v___x_2306_; 
lean_dec(v_x_2286_);
v___x_2305_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__3));
v___x_2306_ = l_Lean_Expr_isConstOf(v_x_2284_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec_ref(v_x_2285_);
lean_dec_ref(v_x_2284_);
lean_dec(v_goal_2283_);
v___x_2307_ = lean_box(0);
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
return v___x_2308_;
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2309_ = lean_unsigned_to_nat(2u);
v___x_2310_ = lean_array_get_size(v_x_2285_);
v___x_2311_ = lean_nat_dec_lt(v___x_2309_, v___x_2310_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_dec_ref(v_x_2285_);
lean_dec_ref(v_x_2284_);
lean_dec(v_goal_2283_);
v___x_2312_ = lean_box(0);
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
return v___x_2313_;
}
else
{
lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2314_ = lean_array_fget_borrowed(v_x_2285_, v___x_2309_);
v___x_2315_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__5));
v___x_2316_ = l_Lean_Expr_isAppOf(v___x_2314_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec_ref(v_x_2285_);
lean_dec_ref(v_x_2284_);
lean_dec(v_goal_2283_);
v___x_2317_ = lean_box(0);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
else
{
lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2319_ = lean_unsigned_to_nat(3u);
v___x_2320_ = lean_nat_dec_lt(v___x_2319_, v___x_2310_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_dec_ref(v_x_2285_);
lean_dec_ref(v_x_2284_);
lean_dec(v_goal_2283_);
v___x_2321_ = lean_box(0);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2323_ = l_Lean_instInhabitedExpr;
v___x_2324_ = lean_array_fget_borrowed(v_x_2285_, v___x_2319_);
v___x_2325_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__7));
v___x_2326_ = l_Lean_Expr_constLevels_x21(v_x_2284_);
lean_dec_ref(v_x_2284_);
v___x_2327_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__0___redArg(v___x_2325_, v___x_2326_, v___y_2293_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = lean_unsigned_to_nat(0u);
v___x_2330_ = lean_array_get_borrowed(v___x_2323_, v_x_2285_, v___x_2329_);
v___x_2331_ = lean_unsigned_to_nat(1u);
v___x_2332_ = lean_array_get_borrowed(v___x_2323_, v_x_2285_, v___x_2331_);
v___x_2333_ = l_Lean_Expr_appArg_x21(v___x_2314_);
v___x_2334_ = lean_unsigned_to_nat(4u);
v___x_2335_ = lean_mk_empty_array_with_capacity(v___x_2334_);
lean_inc(v___x_2330_);
v___x_2336_ = lean_array_push(v___x_2335_, v___x_2330_);
lean_inc(v___x_2332_);
v___x_2337_ = lean_array_push(v___x_2336_, v___x_2332_);
v___x_2338_ = lean_array_push(v___x_2337_, v___x_2333_);
lean_inc(v___x_2324_);
v___x_2339_ = lean_array_push(v___x_2338_, v___x_2324_);
v___x_2340_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1(v_a_2328_, v___x_2339_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec_ref(v___x_2339_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___x_2342_ = l_Array_extract___redArg(v_x_2285_, v___x_2334_, v___x_2310_);
lean_dec_ref(v_x_2285_);
v___x_2343_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1(v_a_2341_, v___x_2342_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec_ref(v___x_2342_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
lean_inc(v_goal_2283_);
v___x_2345_ = l_Lean_MVarId_getType(v_goal_2283_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2347_; lean_object* v_dummy_2348_; lean_object* v_nargs_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2347_ = l_Lean_Expr_getAppFn(v_a_2346_);
v_dummy_2348_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8);
v_nargs_2349_ = l_Lean_Expr_getAppNumArgs(v_a_2346_);
lean_inc(v_nargs_2349_);
v___x_2350_ = lean_mk_array(v_nargs_2349_, v_dummy_2348_);
v___x_2351_ = lean_nat_sub(v_nargs_2349_, v___x_2331_);
lean_dec(v_nargs_2349_);
v___x_2352_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2346_, v___x_2350_, v___x_2351_);
lean_inc(v_a_2344_);
v___x_2353_ = lean_array_set(v___x_2352_, v___x_2319_, v_a_2344_);
v___x_2354_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1(v___x_2347_, v___x_2353_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec_ref(v___x_2353_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2356_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref_known(v___x_2354_, 1);
v___x_2356_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2283_, v_a_2355_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2366_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2366_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2366_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2361_, 0, v_a_2357_);
lean_ctor_set(v___x_2361_, 1, v_a_2344_);
v___x_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2362_);
v___x_2364_ = v___x_2359_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v_a_2344_);
v_a_2367_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2356_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2356_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v_a_2344_);
lean_dec(v_goal_2283_);
v_a_2375_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2354_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2354_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec(v_a_2344_);
lean_dec(v_goal_2283_);
v_a_2383_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2345_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2345_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec(v_goal_2283_);
v_a_2391_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2343_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2343_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v_x_2285_);
lean_dec(v_goal_2283_);
v_a_2399_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2340_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2340_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
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
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec_ref(v_x_2285_);
lean_dec(v_goal_2283_);
v_a_2407_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2327_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2327_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___boxed(lean_object* v_goal_2415_, lean_object* v_x_2416_, lean_object* v_x_2417_, lean_object* v_x_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2(v_goal_2415_, v_x_2416_, v_x_2417_, v_x_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(lean_object* v_goal_2432_, lean_object* v_rhs_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_dummy_2446_; lean_object* v_nargs_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_dummy_2446_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8);
v_nargs_2447_ = l_Lean_Expr_getAppNumArgs(v_rhs_2433_);
lean_inc(v_nargs_2447_);
v___x_2448_ = lean_mk_array(v_nargs_2447_, v_dummy_2446_);
v___x_2449_ = lean_unsigned_to_nat(1u);
v___x_2450_ = lean_nat_sub(v_nargs_2447_, v___x_2449_);
lean_dec(v_nargs_2447_);
v___x_2451_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2(v_goal_2432_, v_rhs_2433_, v___x_2448_, v___x_2450_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f___boxed(lean_object* v_goal_2452_, lean_object* v_rhs_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(v_goal_2452_, v_rhs_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2(lean_object* v_f_2467_, lean_object* v_a_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2___redArg(v_f_2467_, v_a_2468_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2___boxed(lean_object* v_f_2482_, lean_object* v_a_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__1_spec__1_spec__2(v_f_2482_, v_a_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(lean_object* v_a_2497_, lean_object* v_x_2498_){
_start:
{
if (lean_obj_tag(v_x_2498_) == 0)
{
lean_object* v___x_2499_; 
v___x_2499_ = lean_box(0);
return v___x_2499_;
}
else
{
lean_object* v_key_2500_; lean_object* v_value_2501_; lean_object* v_tail_2502_; uint8_t v___x_2503_; 
v_key_2500_ = lean_ctor_get(v_x_2498_, 0);
v_value_2501_ = lean_ctor_get(v_x_2498_, 1);
v_tail_2502_ = lean_ctor_get(v_x_2498_, 2);
v___x_2503_ = lean_name_eq(v_key_2500_, v_a_2497_);
if (v___x_2503_ == 0)
{
v_x_2498_ = v_tail_2502_;
goto _start;
}
else
{
lean_object* v___x_2505_; 
lean_inc(v_value_2501_);
v___x_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2505_, 0, v_value_2501_);
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_2506_, lean_object* v_x_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_2506_, v_x_2507_);
lean_dec(v_x_2507_);
lean_dec(v_a_2506_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(lean_object* v_m_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v_buckets_2511_; lean_object* v___x_2512_; uint64_t v___y_2514_; 
v_buckets_2511_ = lean_ctor_get(v_m_2509_, 1);
v___x_2512_ = lean_array_get_size(v_buckets_2511_);
if (lean_obj_tag(v_a_2510_) == 0)
{
uint64_t v___x_2528_; 
v___x_2528_ = 1723ULL;
v___y_2514_ = v___x_2528_;
goto v___jp_2513_;
}
else
{
uint64_t v_hash_2529_; 
v_hash_2529_ = lean_ctor_get_uint64(v_a_2510_, sizeof(void*)*2);
v___y_2514_ = v_hash_2529_;
goto v___jp_2513_;
}
v___jp_2513_:
{
uint64_t v___x_2515_; uint64_t v___x_2516_; uint64_t v_fold_2517_; uint64_t v___x_2518_; uint64_t v___x_2519_; uint64_t v___x_2520_; size_t v___x_2521_; size_t v___x_2522_; size_t v___x_2523_; size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2515_ = 32ULL;
v___x_2516_ = lean_uint64_shift_right(v___y_2514_, v___x_2515_);
v_fold_2517_ = lean_uint64_xor(v___y_2514_, v___x_2516_);
v___x_2518_ = 16ULL;
v___x_2519_ = lean_uint64_shift_right(v_fold_2517_, v___x_2518_);
v___x_2520_ = lean_uint64_xor(v_fold_2517_, v___x_2519_);
v___x_2521_ = lean_uint64_to_usize(v___x_2520_);
v___x_2522_ = lean_usize_of_nat(v___x_2512_);
v___x_2523_ = ((size_t)1ULL);
v___x_2524_ = lean_usize_sub(v___x_2522_, v___x_2523_);
v___x_2525_ = lean_usize_land(v___x_2521_, v___x_2524_);
v___x_2526_ = lean_array_uget_borrowed(v_buckets_2511_, v___x_2525_);
v___x_2527_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_2510_, v___x_2526_);
return v___x_2527_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg___boxed(lean_object* v_m_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v_m_2530_, v_a_2531_);
lean_dec(v_a_2531_);
lean_dec_ref(v_m_2530_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(lean_object* v_goal_2533_, lean_object* v_rhs_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v___x_2547_; 
lean_inc_ref(v_rhs_2534_);
lean_inc(v_goal_2533_);
v___x_2547_ = l___private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f(v_goal_2533_, v_rhs_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2618_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2618_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2618_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v_fst_2553_; lean_object* v_snd_2554_; 
if (lean_obj_tag(v_a_2548_) == 0)
{
v_fst_2553_ = v_goal_2533_;
v_snd_2554_ = v_rhs_2534_;
goto v___jp_2552_;
}
else
{
lean_object* v_val_2615_; lean_object* v_fst_2616_; lean_object* v_snd_2617_; 
lean_dec_ref(v_rhs_2534_);
lean_dec(v_goal_2533_);
v_val_2615_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_val_2615_);
lean_dec_ref_known(v_a_2548_, 1);
v_fst_2616_ = lean_ctor_get(v_val_2615_, 0);
lean_inc(v_fst_2616_);
v_snd_2617_ = lean_ctor_get(v_val_2615_, 1);
lean_inc(v_snd_2617_);
lean_dec(v_val_2615_);
v_fst_2553_ = v_fst_2616_;
v_snd_2554_ = v_snd_2617_;
goto v___jp_2552_;
}
v___jp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = l_Lean_Expr_getAppFn(v_snd_2554_);
v___x_2556_ = l_Lean_Expr_constName_x3f(v___x_2555_);
lean_dec_ref(v___x_2555_);
if (lean_obj_tag(v___x_2556_) == 1)
{
lean_object* v_val_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_val_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_val_2557_);
lean_dec_ref_known(v___x_2556_, 1);
v___x_2558_ = l_Lean_Elab_Tactic_VCGen_latticeOps;
v___x_2559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v___x_2558_, v_val_2557_);
lean_dec(v_val_2557_);
if (lean_obj_tag(v___x_2559_) == 1)
{
lean_object* v_val_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2606_; 
v_val_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2606_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_val_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2606_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v_applies_x3f_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v_applies_x3f_2564_ = lean_ctor_get(v_val_2560_, 4);
lean_inc_ref(v_applies_x3f_2564_);
lean_inc_ref(v_snd_2554_);
v___x_2565_ = lean_apply_1(v_applies_x3f_2564_, v_snd_2554_);
v___x_2566_ = lean_unbox(v___x_2565_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
lean_del_object(v___x_2562_);
lean_dec(v_val_2560_);
lean_dec_ref(v_snd_2554_);
lean_dec(v_fst_2553_);
v___x_2567_ = lean_box(0);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2567_);
v___x_2569_ = v___x_2550_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
else
{
lean_object* v___x_2571_; 
lean_del_object(v___x_2550_);
v___x_2571_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_snd_2554_, v_val_2560_, v_a_2536_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
v___x_2573_ = lean_box(0);
v___x_2574_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_2572_, v_fst_2553_, v___x_2573_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2589_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2589_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2589_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
if (lean_obj_tag(v_a_2575_) == 0)
{
lean_object* v___x_2580_; 
lean_del_object(v___x_2562_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2573_);
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2573_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
else
{
lean_object* v_mvarIds_2582_; lean_object* v___x_2584_; 
v_mvarIds_2582_ = lean_ctor_get(v_a_2575_, 0);
lean_inc(v_mvarIds_2582_);
lean_dec_ref_known(v_a_2575_, 1);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v_mvarIds_2582_);
v___x_2584_ = v___x_2562_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_mvarIds_2582_);
v___x_2584_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v___x_2586_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2584_);
v___x_2586_ = v___x_2577_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_del_object(v___x_2562_);
v_a_2590_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2574_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2574_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
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
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_del_object(v___x_2562_);
lean_dec(v_fst_2553_);
v_a_2598_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2571_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2571_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
lean_dec(v___x_2559_);
lean_dec_ref(v_snd_2554_);
lean_dec(v_fst_2553_);
v___x_2607_ = lean_box(0);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2607_);
v___x_2609_ = v___x_2550_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
lean_dec(v___x_2556_);
lean_dec_ref(v_snd_2554_);
lean_dec(v_fst_2553_);
v___x_2611_ = lean_box(0);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2611_);
v___x_2613_ = v___x_2550_;
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
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v_rhs_2534_);
lean_dec(v_goal_2533_);
v_a_2619_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2547_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2547_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f___boxed(lean_object* v_goal_2627_, lean_object* v_rhs_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f(v_goal_2627_, v_rhs_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0(lean_object* v_00_u03b2_2642_, lean_object* v_m_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___redArg(v_m_2643_, v_a_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0___boxed(lean_object* v_00_u03b2_2646_, lean_object* v_m_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0(v_00_u03b2_2646_, v_m_2647_, v_a_2648_);
lean_dec(v_a_2648_);
lean_dec_ref(v_m_2647_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0(lean_object* v_00_u03b2_2650_, lean_object* v_a_2651_, lean_object* v_x_2652_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___redArg(v_a_2651_, v_x_2652_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2654_, lean_object* v_a_2655_, lean_object* v_x_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_splitLatticeOp_x3f_spec__0_spec__0(v_00_u03b2_2654_, v_a_2655_, v_x_2656_);
lean_dec(v_x_2656_);
lean_dec(v_a_2655_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(lean_object* v_goal_2658_, lean_object* v_rhs_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
uint8_t v___x_2672_; 
v___x_2672_ = l_Lean_Expr_isForall(v_rhs_2659_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec(v_goal_2658_);
v___x_2673_ = lean_box(0);
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
return v___x_2674_;
}
else
{
lean_object* v_backwardRules_2675_; lean_object* v_forallIntro_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v_backwardRules_2675_ = lean_ctor_get(v_a_2660_, 0);
v_forallIntro_2676_ = lean_ctor_get(v_backwardRules_2675_, 11);
v___x_2677_ = lean_box(0);
lean_inc_ref(v_forallIntro_2676_);
v___x_2678_ = l_Lean_Elab_Tactic_VCGen_Lean_Meta_Sym_BackwardRule_applyChecked(v_forallIntro_2676_, v_goal_2658_, v___x_2677_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2697_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2697_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2697_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
if (lean_obj_tag(v_a_2679_) == 0)
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2677_);
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2677_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
else
{
lean_object* v_mvarIds_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2696_; 
v_mvarIds_2686_ = lean_ctor_get(v_a_2679_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_a_2679_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2688_ = v_a_2679_;
v_isShared_2689_ = v_isSharedCheck_2696_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_mvarIds_2686_);
lean_dec(v_a_2679_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2696_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_mvarIds_2686_);
v___x_2691_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2691_);
v___x_2693_ = v___x_2681_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
v_a_2698_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2678_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2678_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f___boxed(lean_object* v_goal_2706_, lean_object* v_rhs_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_Elab_Tactic_VCGen_splitForallLe_x3f(v_goal_2706_, v_rhs_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec_ref(v_rhs_2707_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(lean_object* v_as_2743_, size_t v_sz_2744_, size_t v_i_2745_, lean_object* v_b_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
uint8_t v___x_2754_; 
v___x_2754_ = lean_usize_dec_lt(v_i_2745_, v_sz_2744_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_b_2746_);
return v___x_2755_;
}
else
{
lean_object* v_snd_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_3000_; 
v_snd_2756_ = lean_ctor_get(v_b_2746_, 1);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_b_2746_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v_b_2746_, 0);
lean_dec(v_unused_3001_);
v___x_2758_ = v_b_2746_;
v_isShared_2759_ = v_isSharedCheck_3000_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_snd_2756_);
lean_dec(v_b_2746_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_3000_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v_snd_2760_; lean_object* v_snd_2761_; lean_object* v_snd_2762_; lean_object* v_fst_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2998_; 
v_snd_2760_ = lean_ctor_get(v_snd_2756_, 1);
lean_inc(v_snd_2760_);
v_snd_2761_ = lean_ctor_get(v_snd_2760_, 1);
lean_inc(v_snd_2761_);
v_snd_2762_ = lean_ctor_get(v_snd_2761_, 1);
lean_inc(v_snd_2762_);
v_fst_2763_ = lean_ctor_get(v_snd_2756_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_snd_2756_);
if (v_isSharedCheck_2998_ == 0)
{
lean_object* v_unused_2999_; 
v_unused_2999_ = lean_ctor_get(v_snd_2756_, 1);
lean_dec(v_unused_2999_);
v___x_2765_ = v_snd_2756_;
v_isShared_2766_ = v_isSharedCheck_2998_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_fst_2763_);
lean_dec(v_snd_2756_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2998_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v_fst_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2996_; 
v_fst_2767_ = lean_ctor_get(v_snd_2760_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_snd_2760_);
if (v_isSharedCheck_2996_ == 0)
{
lean_object* v_unused_2997_; 
v_unused_2997_ = lean_ctor_get(v_snd_2760_, 1);
lean_dec(v_unused_2997_);
v___x_2769_ = v_snd_2760_;
v_isShared_2770_ = v_isSharedCheck_2996_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_fst_2767_);
lean_dec(v_snd_2760_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2996_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v_fst_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2994_; 
v_fst_2771_ = lean_ctor_get(v_snd_2761_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_snd_2761_);
if (v_isSharedCheck_2994_ == 0)
{
lean_object* v_unused_2995_; 
v_unused_2995_ = lean_ctor_get(v_snd_2761_, 1);
lean_dec(v_unused_2995_);
v___x_2773_ = v_snd_2761_;
v_isShared_2774_ = v_isSharedCheck_2994_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_fst_2771_);
lean_dec(v_snd_2761_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2994_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v_fst_2775_; lean_object* v_snd_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2993_; 
v_fst_2775_ = lean_ctor_get(v_snd_2762_, 0);
v_snd_2776_ = lean_ctor_get(v_snd_2762_, 1);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_snd_2762_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2778_ = v_snd_2762_;
v_isShared_2779_ = v_isSharedCheck_2993_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_snd_2776_);
lean_inc(v_fst_2775_);
lean_dec(v_snd_2762_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2993_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v_a_2782_; lean_object* v___x_2783_; 
v___x_2780_ = lean_box(0);
v___x_2781_ = lean_box(0);
v_a_2782_ = lean_array_uget_borrowed(v_as_2743_, v_i_2745_);
lean_inc(v_fst_2775_);
v___x_2783_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_fst_2775_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2984_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2984_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2984_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
if (lean_obj_tag(v_a_2784_) == 7)
{
lean_object* v_binderType_2788_; lean_object* v_body_2789_; uint8_t v___x_2790_; 
v_binderType_2788_ = lean_ctor_get(v_a_2784_, 1);
lean_inc_ref(v_binderType_2788_);
v_body_2789_ = lean_ctor_get(v_a_2784_, 2);
lean_inc_ref(v_body_2789_);
lean_dec_ref_known(v_a_2784_, 3);
v___x_2790_ = l_Lean_Expr_hasLooseBVars(v_body_2789_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__1));
v___x_2792_ = l_Lean_Expr_isAppOf(v_snd_2776_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2795_; 
lean_dec_ref(v_body_2789_);
lean_dec_ref(v_binderType_2788_);
v___x_2793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2779_ == 0)
{
v___x_2795_ = v___x_2778_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_fst_2775_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_snd_2776_);
v___x_2795_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2797_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2795_);
v___x_2797_ = v___x_2773_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_fst_2771_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2799_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2797_);
v___x_2799_ = v___x_2769_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_fst_2767_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2801_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___x_2799_);
v___x_2801_ = v___x_2765_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_fst_2763_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2803_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___x_2801_);
lean_ctor_set(v___x_2758_, 0, v___x_2793_);
v___x_2803_ = v___x_2758_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
lean_object* v___x_2805_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v___x_2803_);
v___x_2805_ = v___x_2786_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2803_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_Expr_appArg_x21(v_snd_2776_);
if (lean_obj_tag(v___x_2812_) == 6)
{
lean_object* v_body_2813_; lean_object* v___x_2814_; 
lean_del_object(v___x_2786_);
v_body_2813_ = lean_ctor_get(v___x_2812_, 2);
lean_inc_ref(v_body_2813_);
lean_dec_ref_known(v___x_2812_, 3);
lean_inc_ref(v_binderType_2788_);
v___x_2814_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2788_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
lean_inc_ref(v_body_2789_);
v___x_2816_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2789_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
lean_inc(v_a_2815_);
v___x_2818_ = l_Lean_Meta_decLevel(v_a_2815_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
lean_inc(v_a_2817_);
v___x_2820_ = l_Lean_Meta_decLevel(v_a_2817_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__4));
v___x_2823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2823_, 0, v_a_2821_);
lean_ctor_set(v___x_2823_, 1, v___x_2780_);
v___x_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2824_, 0, v_a_2819_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = l_Lean_mkConst(v___x_2822_, v___x_2824_);
lean_inc(v_a_2782_);
lean_inc_ref(v_body_2813_);
lean_inc_ref(v_body_2789_);
lean_inc_ref(v_binderType_2788_);
v___x_2826_ = l_Lean_mkApp4(v___x_2825_, v_binderType_2788_, v_body_2789_, v_body_2813_, v_a_2782_);
lean_inc_ref(v___x_2826_);
v___x_2827_ = l_Lean_Meta_Sym_inferType(v___x_2826_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2886_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2886_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2886_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2832_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_fvarEq_x3f___closed__1));
v___x_2833_ = lean_unsigned_to_nat(3u);
v___x_2834_ = l_Lean_Expr_isAppOfArity(v_a_2828_, v___x_2832_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; lean_object* v___x_2837_; 
lean_dec(v_a_2828_);
lean_dec_ref(v___x_2826_);
lean_dec(v_a_2817_);
lean_dec(v_a_2815_);
lean_dec_ref(v_body_2813_);
lean_dec_ref(v_body_2789_);
lean_dec_ref(v_binderType_2788_);
v___x_2835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2779_ == 0)
{
v___x_2837_ = v___x_2778_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_fst_2775_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_snd_2776_);
v___x_2837_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2839_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2837_);
v___x_2839_ = v___x_2773_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_fst_2771_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2841_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2839_);
v___x_2841_ = v___x_2769_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_fst_2767_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2843_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___x_2841_);
v___x_2843_ = v___x_2765_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_fst_2763_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2845_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___x_2843_);
lean_ctor_set(v___x_2758_, 0, v___x_2835_);
v___x_2845_ = v___x_2758_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2847_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2845_);
v___x_2847_ = v___x_2830_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
lean_del_object(v___x_2830_);
lean_dec(v_snd_2776_);
lean_dec(v_fst_2775_);
v___x_2854_ = l_Lean_Expr_appArg_x21(v_a_2828_);
lean_dec(v_a_2828_);
v___x_2855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__6));
v___x_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_a_2817_);
lean_ctor_set(v___x_2856_, 1, v___x_2780_);
lean_inc_ref(v___x_2856_);
v___x_2857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2857_, 0, v_a_2815_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = l_Lean_mkConst(v___x_2855_, v___x_2857_);
v___x_2859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__8));
v___x_2860_ = 0;
lean_inc_ref_n(v_body_2789_, 2);
lean_inc_ref(v_binderType_2788_);
v___x_2861_ = l_Lean_Expr_lam___override(v___x_2859_, v_binderType_2788_, v_body_2789_, v___x_2860_);
lean_inc_n(v_a_2782_, 3);
lean_inc(v_fst_2771_);
lean_inc(v_fst_2767_);
v___x_2862_ = l_Lean_mkApp6(v___x_2858_, v_binderType_2788_, v___x_2861_, v_fst_2767_, v_fst_2771_, v_fst_2763_, v_a_2782_);
v___x_2863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__10));
v___x_2864_ = l_Lean_mkConst(v___x_2863_, v___x_2856_);
v___x_2865_ = l_Lean_Expr_app___override(v_fst_2767_, v_a_2782_);
v___x_2866_ = l_Lean_Expr_app___override(v_fst_2771_, v_a_2782_);
lean_inc_ref(v___x_2854_);
lean_inc_ref(v___x_2865_);
v___x_2867_ = l_Lean_mkApp6(v___x_2864_, v_body_2789_, v___x_2865_, v___x_2866_, v___x_2854_, v___x_2862_, v___x_2826_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 1, v_body_2813_);
lean_ctor_set(v___x_2778_, 0, v_body_2789_);
v___x_2869_ = v___x_2778_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_body_2789_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_body_2813_);
v___x_2869_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2871_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2869_);
lean_ctor_set(v___x_2773_, 0, v___x_2854_);
v___x_2871_ = v___x_2773_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2873_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2871_);
lean_ctor_set(v___x_2769_, 0, v___x_2865_);
v___x_2873_ = v___x_2769_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2865_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2875_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___x_2873_);
lean_ctor_set(v___x_2765_, 0, v___x_2867_);
v___x_2875_ = v___x_2765_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2877_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___x_2875_);
lean_ctor_set(v___x_2758_, 0, v___x_2781_);
v___x_2877_ = v___x_2758_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
size_t v___x_2878_; size_t v___x_2879_; 
v___x_2878_ = ((size_t)1ULL);
v___x_2879_ = lean_usize_add(v_i_2745_, v___x_2878_);
v_i_2745_ = v___x_2879_;
v_b_2746_ = v___x_2877_;
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
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec_ref(v___x_2826_);
lean_dec(v_a_2817_);
lean_dec(v_a_2815_);
lean_dec_ref(v_body_2813_);
lean_dec_ref(v_body_2789_);
lean_dec_ref(v_binderType_2788_);
lean_del_object(v___x_2778_);
lean_dec(v_snd_2776_);
lean_dec(v_fst_2775_);
lean_del_object(v___x_2773_);
lean_dec(v_fst_2771_);
lean_del_object(v___x_2769_);
lean_dec(v_fst_2767_);
lean_del_object(v___x_2765_);
lean_dec(v_fst_2763_);
lean_del_object(v___x_2758_);
v_a_2887_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2827_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2827_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v_a_2819_);
lean_dec(v_a_2817_);
lean_dec(v_a_2815_);
lean_dec_ref(v_body_2813_);
lean_dec_ref(v_body_2789_);
lean_dec_ref(v_binderType_2788_);
lean_del_object(v___x_2778_);
lean_dec(v_snd_2776_);
lean_dec(v_fst_2775_);
lean_del_object(v___x_2773_);
lean_dec(v_fst_2771_);
lean_del_object(v___x_2769_);
lean_dec(v_fst_2767_);
lean_del_object(v___x_2765_);
lean_dec(v_fst_2763_);
lean_del_object(v___x_2758_);
v_a_2895_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2820_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2820_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec(v_a_2817_);
lean_dec(v_a_2815_);
lean_dec_ref(v_body_2813_);
lean_dec_ref(v_body_2789_);
lean_dec_ref(v_binderType_2788_);
lean_del_object(v___x_2778_);
lean_dec(v_snd_2776_);
lean_dec(v_fst_2775_);
lean_del_object(v___x_2773_);
lean_dec(v_fst_2771_);
lean_del_object(v___x_2769_);
lean_dec(v_fst_2767_);
lean_del_object(v___x_2765_);
lean_dec(v_fst_2763_);
lean_del_object(v___x_2758_);
v_a_2903_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2818_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2818_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v_a_2815_);
lean_dec_ref(v_body_2813_);
lean_dec_ref(v_body_2789_);
lean_dec_ref(v_binderType_2788_);
lean_del_object(v___x_2778_);
lean_dec(v_snd_2776_);
lean_dec(v_fst_2775_);
lean_del_object(v___x_2773_);
lean_dec(v_fst_2771_);
lean_del_object(v___x_2769_);
lean_dec(v_fst_2767_);
lean_del_object(v___x_2765_);
lean_dec(v_fst_2763_);
lean_del_object(v___x_2758_);
v_a_2911_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2816_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2816_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
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
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref(v_body_2813_);
lean_dec_ref(v_body_2789_);
lean_dec_ref(v_binderType_2788_);
lean_del_object(v___x_2778_);
lean_dec(v_snd_2776_);
lean_dec(v_fst_2775_);
lean_del_object(v___x_2773_);
lean_dec(v_fst_2771_);
lean_del_object(v___x_2769_);
lean_dec(v_fst_2767_);
lean_del_object(v___x_2765_);
lean_dec(v_fst_2763_);
lean_del_object(v___x_2758_);
v_a_2919_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2814_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2814_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2929_; 
lean_dec_ref(v___x_2812_);
lean_dec_ref(v_body_2789_);
lean_dec_ref(v_binderType_2788_);
v___x_2927_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2779_ == 0)
{
v___x_2929_ = v___x_2778_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_fst_2775_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_snd_2776_);
v___x_2929_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_object* v___x_2931_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2929_);
v___x_2931_ = v___x_2773_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_fst_2771_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v___x_2929_);
v___x_2931_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
lean_object* v___x_2933_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2931_);
v___x_2933_ = v___x_2769_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_fst_2767_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2935_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___x_2933_);
v___x_2935_ = v___x_2765_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_fst_2763_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v___x_2933_);
v___x_2935_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
lean_object* v___x_2937_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___x_2935_);
lean_ctor_set(v___x_2758_, 0, v___x_2927_);
v___x_2937_ = v___x_2758_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2939_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v___x_2937_);
v___x_2939_ = v___x_2786_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
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
lean_object* v___x_2946_; lean_object* v___x_2948_; 
lean_dec_ref(v_body_2789_);
lean_dec_ref(v_binderType_2788_);
v___x_2946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2779_ == 0)
{
v___x_2948_ = v___x_2778_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_fst_2775_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_snd_2776_);
v___x_2948_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2950_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2948_);
v___x_2950_ = v___x_2773_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_fst_2771_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2952_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2950_);
v___x_2952_ = v___x_2769_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_fst_2767_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2954_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___x_2952_);
v___x_2954_ = v___x_2765_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_fst_2763_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2956_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___x_2954_);
lean_ctor_set(v___x_2758_, 0, v___x_2946_);
v___x_2956_ = v___x_2758_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2958_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v___x_2956_);
v___x_2958_ = v___x_2786_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
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
lean_object* v___x_2965_; lean_object* v___x_2967_; 
lean_dec(v_a_2784_);
v___x_2965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___closed__2));
if (v_isShared_2779_ == 0)
{
v___x_2967_ = v___x_2778_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_fst_2775_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_snd_2776_);
v___x_2967_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2969_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2967_);
v___x_2969_ = v___x_2773_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_fst_2771_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2971_; 
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2969_);
v___x_2971_ = v___x_2769_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_fst_2767_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2973_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v___x_2971_);
v___x_2973_ = v___x_2765_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_fst_2763_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2975_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___x_2973_);
lean_ctor_set(v___x_2758_, 0, v___x_2965_);
v___x_2975_ = v___x_2758_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2977_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v___x_2975_);
v___x_2977_ = v___x_2786_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
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
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_del_object(v___x_2778_);
lean_dec(v_snd_2776_);
lean_dec(v_fst_2775_);
lean_del_object(v___x_2773_);
lean_dec(v_fst_2771_);
lean_del_object(v___x_2769_);
lean_dec(v_fst_2767_);
lean_del_object(v___x_2765_);
lean_dec(v_fst_2763_);
lean_del_object(v___x_2758_);
v_a_2985_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2783_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2783_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0___boxed(lean_object* v_as_3002_, lean_object* v_sz_3003_, lean_object* v_i_3004_, lean_object* v_b_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
size_t v_sz_boxed_3013_; size_t v_i_boxed_3014_; lean_object* v_res_3015_; 
v_sz_boxed_3013_ = lean_unbox_usize(v_sz_3003_);
lean_dec(v_sz_3003_);
v_i_boxed_3014_ = lean_unbox_usize(v_i_3004_);
lean_dec(v_i_3004_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(v_as_3002_, v_sz_boxed_3013_, v_i_boxed_3014_, v_b_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec_ref(v_as_3002_);
return v_res_3015_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6(void){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = l_Lean_Expr_bvar___override(v___x_3028_);
return v___x_3029_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_box(0);
v___x_3034_ = l_Lean_Level_succ___override(v___x_3033_);
return v___x_3034_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = lean_box(0);
v___x_3036_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__9);
v___x_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3035_);
return v___x_3037_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = lean_box(0);
v___x_3039_ = l_Lean_mkSort(v___x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(lean_object* v_goal_3040_, lean_object* v_target_3041_, lean_object* v_pre_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___x_3053_; uint8_t v___x_3054_; 
v___x_3053_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1));
v___x_3054_ = l_Lean_Expr_isAppOf(v_pre_3042_, v___x_3053_);
if (v___x_3054_ == 0)
{
lean_dec_ref(v_pre_3042_);
lean_dec_ref(v_target_3041_);
lean_dec(v_goal_3040_);
goto v___jp_3050_;
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3055_ = lean_unsigned_to_nat(2u);
v___x_3056_ = l_Lean_Expr_getAppNumArgs(v_pre_3042_);
v___x_3057_ = lean_nat_dec_lt(v___x_3055_, v___x_3056_);
if (v___x_3057_ == 0)
{
lean_dec(v___x_3056_);
lean_dec_ref(v_pre_3042_);
lean_dec_ref(v_target_3041_);
lean_dec(v_goal_3040_);
goto v___jp_3050_;
}
else
{
lean_object* v_dummy_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v_args_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v_dummy_3058_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_VCGen_Entails_0__Lean_Elab_Tactic_VCGen_refoldHimpUpperAdjoint_x3f_spec__2___closed__8);
lean_inc(v___x_3056_);
v___x_3059_ = lean_mk_array(v___x_3056_, v_dummy_3058_);
v___x_3060_ = lean_unsigned_to_nat(1u);
v___x_3061_ = lean_nat_sub(v___x_3056_, v___x_3060_);
lean_dec(v___x_3056_);
lean_inc_ref(v_pre_3042_);
v_args_3062_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_pre_3042_, v___x_3059_, v___x_3061_);
v___x_3063_ = lean_unsigned_to_nat(0u);
v___x_3064_ = lean_array_get_size(v_args_3062_);
v___x_3065_ = lean_nat_dec_lt(v___x_3063_, v___x_3064_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_dec_ref(v_args_3062_);
lean_dec_ref(v_pre_3042_);
lean_dec_ref(v_target_3041_);
lean_dec(v_goal_3040_);
v___x_3066_ = lean_box(0);
v___x_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
return v___x_3067_;
}
else
{
uint8_t v___x_3068_; 
v___x_3068_ = lean_nat_dec_lt(v___x_3060_, v___x_3064_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_dec_ref(v_args_3062_);
lean_dec_ref(v_pre_3042_);
lean_dec_ref(v_target_3041_);
lean_dec(v_goal_3040_);
v___x_3069_ = lean_box(0);
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
return v___x_3070_;
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v_curTop_3074_; lean_object* v___x_3075_; 
v___x_3071_ = lean_array_fget(v_args_3062_, v___x_3063_);
v___x_3072_ = lean_array_fget(v_args_3062_, v___x_3060_);
v___x_3073_ = l_Lean_Expr_getAppFn(v_pre_3042_);
lean_inc(v___x_3072_);
lean_inc_n(v___x_3071_, 2);
v_curTop_3074_ = l_Lean_mkAppB(v___x_3073_, v___x_3071_, v___x_3072_);
v___x_3075_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_3071_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; size_t v_sz_3089_; size_t v___x_3090_; lean_object* v___x_3091_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref_known(v___x_3075_, 1);
v___x_3077_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__3));
v___x_3078_ = lean_box(0);
v___x_3079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3079_, 0, v_a_3076_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = l_Lean_mkConst(v___x_3077_, v___x_3079_);
lean_inc_ref_n(v_curTop_3074_, 2);
lean_inc(v___x_3071_);
v___x_3081_ = l_Lean_mkAppB(v___x_3080_, v___x_3071_, v_curTop_3074_);
v___x_3082_ = l_Array_extract___redArg(v_args_3062_, v___x_3055_, v___x_3064_);
lean_dec_ref(v_args_3062_);
v___x_3083_ = lean_box(0);
v___x_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3071_);
lean_ctor_set(v___x_3084_, 1, v___x_3072_);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v_curTop_3074_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
v___x_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3086_, 0, v_curTop_3074_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3081_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3083_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v_sz_3089_ = lean_array_size(v___x_3082_);
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f_spec__0(v___x_3082_, v_sz_3089_, v___x_3090_, v___x_3088_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
lean_dec_ref(v___x_3082_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3175_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3175_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3175_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v_fst_3096_; 
v_fst_3096_ = lean_ctor_get(v_a_3092_, 0);
if (lean_obj_tag(v_fst_3096_) == 0)
{
lean_object* v_snd_3097_; lean_object* v_nargs_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v_snd_3097_ = lean_ctor_get(v_a_3092_, 1);
lean_inc(v_snd_3097_);
lean_dec(v_a_3092_);
v_nargs_3098_ = l_Lean_Expr_getAppNumArgs(v_target_3041_);
lean_inc(v_nargs_3098_);
v___x_3099_ = lean_mk_array(v_nargs_3098_, v_dummy_3058_);
v___x_3100_ = lean_nat_sub(v_nargs_3098_, v___x_3060_);
lean_dec(v_nargs_3098_);
lean_inc_ref(v_target_3041_);
v___x_3101_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_target_3041_, v___x_3099_, v___x_3100_);
v___x_3102_ = lean_array_get_size(v___x_3101_);
v___x_3103_ = lean_nat_dec_lt(v___x_3063_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3105_; 
lean_dec_ref(v___x_3101_);
lean_dec(v_snd_3097_);
lean_dec_ref(v_pre_3042_);
lean_dec_ref(v_target_3041_);
lean_dec(v_goal_3040_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3083_);
v___x_3105_ = v___x_3094_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3083_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
else
{
uint8_t v___x_3107_; 
v___x_3107_ = lean_nat_dec_lt(v___x_3060_, v___x_3102_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3109_; 
lean_dec_ref(v___x_3101_);
lean_dec(v_snd_3097_);
lean_dec_ref(v_pre_3042_);
lean_dec_ref(v_target_3041_);
lean_dec(v_goal_3040_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3083_);
v___x_3109_ = v___x_3094_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3083_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
else
{
lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3111_ = lean_unsigned_to_nat(3u);
v___x_3112_ = lean_nat_dec_lt(v___x_3111_, v___x_3102_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3114_; 
lean_dec_ref(v___x_3101_);
lean_dec(v_snd_3097_);
lean_dec_ref(v_pre_3042_);
lean_dec_ref(v_target_3041_);
lean_dec(v_goal_3040_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3083_);
v___x_3114_ = v___x_3094_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3083_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
else
{
lean_object* v_snd_3116_; lean_object* v_snd_3117_; lean_object* v_fst_3118_; lean_object* v_fst_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3169_; 
lean_del_object(v___x_3094_);
v_snd_3116_ = lean_ctor_get(v_snd_3097_, 1);
v_snd_3117_ = lean_ctor_get(v_snd_3116_, 1);
lean_inc(v_snd_3117_);
v_fst_3118_ = lean_ctor_get(v_snd_3097_, 0);
lean_inc(v_fst_3118_);
lean_dec(v_snd_3097_);
v_fst_3119_ = lean_ctor_get(v_snd_3117_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_snd_3117_);
if (v_isSharedCheck_3169_ == 0)
{
lean_object* v_unused_3170_; 
v_unused_3170_ = lean_ctor_get(v_snd_3117_, 1);
lean_dec(v_unused_3170_);
v___x_3121_ = v_snd_3117_;
v_isShared_3122_ = v_isSharedCheck_3169_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_fst_3119_);
lean_dec(v_snd_3117_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3169_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3123_ = lean_array_fget(v___x_3101_, v___x_3063_);
v___x_3124_ = lean_array_fget(v___x_3101_, v___x_3060_);
v___x_3125_ = lean_array_fget(v___x_3101_, v___x_3111_);
lean_dec_ref(v___x_3101_);
lean_inc(v___x_3123_);
v___x_3126_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_3123_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3137_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref_known(v___x_3126_, 1);
v___x_3128_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__5));
v___x_3129_ = l_Lean_Expr_getAppFn(v_target_3041_);
lean_dec_ref(v_target_3041_);
v___x_3130_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__6);
lean_inc(v___x_3125_);
lean_inc(v___x_3124_);
lean_inc_n(v___x_3123_, 2);
lean_inc_ref(v___x_3129_);
v___x_3131_ = l_Lean_mkApp4(v___x_3129_, v___x_3123_, v___x_3124_, v___x_3130_, v___x_3125_);
v___x_3132_ = 0;
v___x_3133_ = l_Lean_Expr_lam___override(v___x_3128_, v___x_3123_, v___x_3131_, v___x_3132_);
v___x_3134_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__8));
v___x_3135_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__10);
if (v_isShared_3122_ == 0)
{
lean_ctor_set_tag(v___x_3121_, 1);
lean_ctor_set(v___x_3121_, 1, v___x_3135_);
lean_ctor_set(v___x_3121_, 0, v_a_3127_);
v___x_3137_ = v___x_3121_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3127_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3138_ = l_Lean_mkConst(v___x_3134_, v___x_3137_);
v___x_3139_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11, &l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11_once, _init_l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__11);
lean_inc(v_fst_3119_);
lean_inc(v___x_3123_);
v___x_3140_ = l_Lean_mkApp6(v___x_3138_, v___x_3123_, v___x_3139_, v_pre_3042_, v_fst_3119_, v___x_3133_, v_fst_3118_);
v___x_3141_ = l_Lean_mkApp4(v___x_3129_, v___x_3123_, v___x_3124_, v_fst_3119_, v___x_3125_);
v___x_3142_ = l_Lean_MVarId_replaceTargetEq(v_goal_3040_, v___x_3141_, v___x_3140_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3151_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3151_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3151_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_a_3143_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v___x_3147_);
v___x_3149_ = v___x_3145_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
v_a_3152_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3142_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3142_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v___x_3125_);
lean_dec(v___x_3124_);
lean_dec(v___x_3123_);
lean_del_object(v___x_3121_);
lean_dec(v_fst_3119_);
lean_dec(v_fst_3118_);
lean_dec_ref(v_pre_3042_);
lean_dec_ref(v_target_3041_);
lean_dec(v_goal_3040_);
v_a_3161_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3126_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3126_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
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
lean_object* v_val_3171_; lean_object* v___x_3173_; 
lean_inc_ref(v_fst_3096_);
lean_dec(v_a_3092_);
lean_dec_ref(v_pre_3042_);
lean_dec_ref(v_target_3041_);
lean_dec(v_goal_3040_);
v_val_3171_ = lean_ctor_get(v_fst_3096_, 0);
lean_inc(v_val_3171_);
lean_dec_ref_known(v_fst_3096_, 1);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v_val_3171_);
v___x_3173_ = v___x_3094_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_val_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec_ref(v_pre_3042_);
lean_dec_ref(v_target_3041_);
lean_dec(v_goal_3040_);
v_a_3176_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3091_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3091_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec_ref(v_curTop_3074_);
lean_dec(v___x_3072_);
lean_dec(v___x_3071_);
lean_dec_ref(v_args_3062_);
lean_dec_ref(v_pre_3042_);
lean_dec_ref(v_target_3041_);
lean_dec(v_goal_3040_);
v_a_3184_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3075_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3075_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
}
}
v___jp_3050_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = lean_box(0);
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___boxed(lean_object* v_goal_3192_, lean_object* v_target_3193_, lean_object* v_pre_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f(v_goal_3192_, v_target_3193_, v_pre_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
return v_res_3202_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__0));
v___x_3205_ = l_Lean_stringToMessageData(v___x_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(lean_object* v_goal_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___x_3231_; 
lean_inc(v_goal_3213_);
v___x_3231_ = l_Lean_MVarId_getType(v_goal_3213_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3295_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3295_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3295_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; uint8_t v___x_3238_; 
v___x_3236_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__4));
v___x_3237_ = lean_unsigned_to_nat(4u);
v___x_3238_ = l_Lean_Expr_isAppOfArity(v_a_3232_, v___x_3236_, v___x_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3240_; 
lean_dec(v_a_3232_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v_goal_3213_);
v___x_3240_ = v___x_3234_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_goal_3213_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
else
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3242_ = l_Lean_Expr_appFn_x21(v_a_3232_);
lean_dec(v_a_3232_);
v___x_3243_ = l_Lean_Expr_appFn_x21(v___x_3242_);
v___x_3244_ = l_Lean_Expr_appFn_x21(v___x_3243_);
lean_dec_ref(v___x_3243_);
v___x_3245_ = l_Lean_Expr_appArg_x21(v___x_3244_);
lean_dec_ref(v___x_3244_);
if (lean_obj_tag(v___x_3245_) == 3)
{
lean_object* v_u_3246_; 
v_u_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_u_3246_);
lean_dec_ref_known(v___x_3245_, 1);
if (lean_obj_tag(v_u_3246_) == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_del_object(v___x_3234_);
v___x_3247_ = l_Lean_Expr_appArg_x21(v___x_3242_);
lean_dec_ref(v___x_3242_);
v___x_3248_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v___x_3247_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3280_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3251_ = v___x_3248_;
v_isShared_3252_ = v_isSharedCheck_3280_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3280_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_reduceTopAppliedPre_x3f___closed__1));
v___x_3254_ = l_Lean_Expr_isAppOf(v_a_3249_, v___x_3253_);
lean_dec(v_a_3249_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3256_; 
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v_goal_3213_);
v___x_3256_ = v___x_3251_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_goal_3213_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
else
{
lean_object* v_backwardRules_3258_; lean_object* v_elimPre_3259_; lean_object* v___x_3260_; 
lean_del_object(v___x_3251_);
v_backwardRules_3258_ = lean_ctor_get(v_a_3214_, 0);
v_elimPre_3259_ = lean_ctor_get(v_backwardRules_3258_, 7);
lean_inc_ref(v_elimPre_3259_);
lean_inc(v_goal_3213_);
v___x_3260_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_3213_, v_elimPre_3259_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3271_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3271_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3271_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
if (lean_obj_tag(v_a_3261_) == 1)
{
lean_object* v_mvarIds_3265_; 
v_mvarIds_3265_ = lean_ctor_get(v_a_3261_, 0);
lean_inc(v_mvarIds_3265_);
lean_dec_ref_known(v_a_3261_, 1);
if (lean_obj_tag(v_mvarIds_3265_) == 1)
{
lean_object* v_tail_3266_; 
v_tail_3266_ = lean_ctor_get(v_mvarIds_3265_, 1);
if (lean_obj_tag(v_tail_3266_) == 0)
{
lean_object* v_head_3267_; lean_object* v___x_3269_; 
lean_dec(v_goal_3213_);
v_head_3267_ = lean_ctor_get(v_mvarIds_3265_, 0);
lean_inc(v_head_3267_);
lean_dec_ref_known(v_mvarIds_3265_, 2);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v_head_3267_);
v___x_3269_ = v___x_3263_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_head_3267_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
else
{
lean_dec_ref_known(v_mvarIds_3265_, 2);
lean_del_object(v___x_3263_);
v___y_3223_ = v_a_3217_;
v___y_3224_ = v_a_3218_;
v___y_3225_ = v_a_3219_;
v___y_3226_ = v_a_3220_;
goto v___jp_3222_;
}
}
else
{
lean_dec(v_mvarIds_3265_);
lean_del_object(v___x_3263_);
v___y_3223_ = v_a_3217_;
v___y_3224_ = v_a_3218_;
v___y_3225_ = v_a_3219_;
v___y_3226_ = v_a_3220_;
goto v___jp_3222_;
}
}
else
{
lean_del_object(v___x_3263_);
lean_dec(v_a_3261_);
v___y_3223_ = v_a_3217_;
v___y_3224_ = v_a_3218_;
v___y_3225_ = v_a_3219_;
v___y_3226_ = v_a_3220_;
goto v___jp_3222_;
}
}
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_dec(v_goal_3213_);
v_a_3272_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3260_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3260_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec(v_goal_3213_);
v_a_3281_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3248_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3248_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
else
{
lean_object* v___x_3290_; 
lean_dec(v_u_3246_);
lean_dec_ref(v___x_3242_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v_goal_3213_);
v___x_3290_ = v___x_3234_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_goal_3213_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
else
{
lean_object* v___x_3293_; 
lean_dec_ref(v___x_3245_);
lean_dec_ref(v___x_3242_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v_goal_3213_);
v___x_3293_ = v___x_3234_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_goal_3213_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec(v_goal_3213_);
v_a_3296_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3231_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3231_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
v___jp_3222_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3227_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1, &l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___closed__1);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v_goal_3213_);
v___x_3229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3227_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = l_Lean_throwError___at___00Lean_Elab_Tactic_VCGen_unfoldTriple_spec__0___redArg(v___x_3229_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
return v___x_3230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg___boxed(lean_object* v_goal_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_goal_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_);
lean_dec(v_a_3311_);
lean_dec_ref(v_a_3310_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec_ref(v_a_3305_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre(lean_object* v_goal_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_goal_3314_, v_a_3315_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___boxed(lean_object* v_goal_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_Elab_Tactic_VCGen_elimTopPre(v_goal_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
lean_dec(v_a_3331_);
lean_dec(v_a_3330_);
lean_dec_ref(v_a_3329_);
return v_res_3341_;
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
