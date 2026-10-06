// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Refine
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.Assumption
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_MRefinePat_parse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Neither a conjunction nor an existential quantifier "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "exists_intro'"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 53, .m_data = "pattern does not elaborate to a term to instantiate ψ"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "exists"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "and_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value),LEAN_SCALAR_PTR_LITERAL(216, 97, 27, 109, 96, 85, 230, 202)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value),LEAN_SCALAR_PTR_LITERAL(96, 234, 54, 186, 23, 232, 175, 83)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "f: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", args: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "could not solve "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " by assumption"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unknown hypothesis `"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mrefine"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 147, 116, 116, 185, 89, 229, 87)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabMRefine"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(173, 23, 115, 46, 68, 127, 144, 74)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "mrefinePat⟨_⟩"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 252, 110, 106, 145, 210, 7, 196)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mrefinePats"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(112, 173, 91, 190, 46, 156, 169, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "mrefinePat⌜_⌝"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 247, 138, 95, 101, 152, 141, 145)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⌜"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⌝"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mexists"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 170, 199, 22, 25, 76, 35, 23)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "massumption"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13_value),LEAN_SCALAR_PTR_LITERAL(115, 248, 144, 74, 231, 227, 47, 25)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrefinePat\?_"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16_value),LEAN_SCALAR_PTR_LITERAL(29, 112, 196, 176, 199, 255, 59, 175)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabMExists"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 207, 228, 32, 148, 252, 22, 112)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(lean_object* v_pat_9_, lean_object* v_expected_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
switch(lean_obj_tag(v_pat_9_))
{
case 2:
{
lean_object* v_h_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_45_; 
v_h_20_ = lean_ctor_get(v_pat_9_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v_pat_9_);
if (v_isSharedCheck_45_ == 0)
{
v___x_22_ = v_pat_9_;
v_isShared_23_ = v_isSharedCheck_45_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_h_20_);
lean_dec(v_pat_9_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_45_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
uint8_t v___x_24_; lean_object* v___x_25_; 
v___x_24_ = 0;
v___x_25_ = l_Lean_Elab_Tactic_elabTerm(v_h_20_, v_expected_10_, v___x_24_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_25_) == 0)
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_36_; 
v_a_26_ = lean_ctor_get(v___x_25_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_36_ == 0)
{
v___x_28_ = v___x_25_;
v_isShared_29_ = v_isSharedCheck_36_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_25_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_36_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set_tag(v___x_22_, 1);
lean_ctor_set(v___x_22_, 0, v_a_26_);
v___x_31_ = v___x_22_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_a_26_);
v___x_31_ = v_reuseFailAlloc_35_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_33_; 
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v___x_31_);
v___x_33_ = v___x_28_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
else
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
lean_del_object(v___x_22_);
v_a_37_ = lean_ctor_get(v___x_25_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_25_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_25_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
case 0:
{
lean_object* v_name_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_85_; 
v_name_46_ = lean_ctor_get(v_pat_9_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v_pat_9_);
if (v_isSharedCheck_85_ == 0)
{
v___x_48_ = v_pat_9_;
v_isShared_49_ = v_isSharedCheck_85_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_name_46_);
lean_dec(v_pat_9_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_85_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2));
lean_inc(v_name_46_);
v___x_51_ = l_Lean_Syntax_isOfKind(v_name_46_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_54_; 
lean_dec(v_name_46_);
lean_dec(v_expected_10_);
v___x_52_ = lean_box(0);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_52_);
v___x_54_ = v___x_48_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = l_Lean_Syntax_getArg(v_name_46_, v___x_56_);
lean_dec(v_name_46_);
v___x_58_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4));
lean_inc(v___x_57_);
v___x_59_ = l_Lean_Syntax_isOfKind(v___x_57_, v___x_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_62_; 
lean_dec(v___x_57_);
lean_dec(v_expected_10_);
v___x_60_ = lean_box(0);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_60_);
v___x_62_ = v___x_48_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_60_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
else
{
uint8_t v___x_64_; lean_object* v___x_65_; 
v___x_64_ = 0;
v___x_65_ = l_Lean_Elab_Tactic_elabTerm(v___x_57_, v_expected_10_, v___x_64_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_76_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_76_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_76_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_76_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_71_; 
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 1);
lean_ctor_set(v___x_48_, 0, v_a_66_);
v___x_71_ = v___x_48_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_66_);
v___x_71_ = v_reuseFailAlloc_75_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_73_; 
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_71_);
v___x_73_ = v___x_68_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_del_object(v___x_48_);
v_a_77_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_65_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_65_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
}
}
default: 
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_expected_10_);
lean_dec_ref(v_pat_9_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___boxed(lean_object* v_pat_88_, lean_object* v_expected_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(v_pat_88_, v_expected_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
return v_res_99_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_box(0);
v___x_101_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg(){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___boxed(lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0(lean_object* v_00_u03b1_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___boxed(lean_object* v_00_u03b1_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0(v_00_u03b1_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_129_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(lean_object* v___x_130_, lean_object* v_00___131_){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_132_ = lean_unsigned_to_nat(3u);
v___x_133_ = lean_array_get_size(v___x_130_);
v___x_134_ = lean_nat_dec_le(v___x_132_, v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0___boxed(lean_object* v___x_135_, lean_object* v_00___136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(v___x_135_, v_00___136_);
lean_dec_ref(v___x_135_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__2(lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
if (lean_obj_tag(v_a_139_) == 0)
{
lean_object* v___x_141_; 
v___x_141_ = l_List_reverse___redArg(v_a_140_);
return v___x_141_;
}
else
{
lean_object* v_head_142_; lean_object* v_tail_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_152_; 
v_head_142_ = lean_ctor_get(v_a_139_, 0);
v_tail_143_ = lean_ctor_get(v_a_139_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_a_139_);
if (v_isSharedCheck_152_ == 0)
{
v___x_145_ = v_a_139_;
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_tail_143_);
lean_inc(v_head_142_);
lean_dec(v_a_139_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = l_Lean_MessageData_ofExpr(v_head_142_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v_a_140_);
lean_ctor_set(v___x_145_, 0, v___x_147_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_a_140_);
v___x_149_ = v_reuseFailAlloc_151_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
v_a_139_ = v_tail_143_;
v_a_140_ = v___x_149_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(lean_object* v_msgData_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; lean_object* v_env_160_; uint8_t v___x_161_; lean_object* v_env_162_; lean_object* v___x_163_; lean_object* v_toCold_164_; lean_object* v_mctx_165_; lean_object* v_lctx_166_; lean_object* v_options_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_159_ = lean_st_ref_get(v___y_157_);
v_env_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc_ref(v_env_160_);
lean_dec(v___x_159_);
v___x_161_ = 0;
v_env_162_ = l_Lean_Environment_setRecordingDeps(v_env_160_, v___x_161_);
v___x_163_ = lean_st_ref_get(v___y_155_);
v_toCold_164_ = lean_ctor_get(v___y_156_, 0);
v_mctx_165_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_mctx_165_);
lean_dec(v___x_163_);
v_lctx_166_ = lean_ctor_get(v___y_154_, 2);
v_options_167_ = lean_ctor_get(v_toCold_164_, 2);
lean_inc_ref(v_options_167_);
lean_inc_ref(v_lctx_166_);
v___x_168_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_168_, 0, v_env_162_);
lean_ctor_set(v___x_168_, 1, v_mctx_165_);
lean_ctor_set(v___x_168_, 2, v_lctx_166_);
lean_ctor_set(v___x_168_, 3, v_options_167_);
v___x_169_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_msgData_153_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1___boxed(lean_object* v_msgData_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msgData_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(lean_object* v_msg_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_ref_184_; lean_object* v___x_185_; lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_194_; 
v_ref_184_ = lean_ctor_get(v___y_181_, 2);
v___x_185_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_194_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_194_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_inc(v_ref_184_);
v___x_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_190_, 0, v_ref_184_);
lean_ctor_set(v___x_190_, 1, v_a_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 1);
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg___boxed(lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v_msg_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_201_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_202_; double v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_float_of_nat(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(lean_object* v_cls_207_, lean_object* v_msg_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_ref_214_; lean_object* v___x_215_; lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_261_; 
v_ref_214_ = lean_ctor_get(v___y_211_, 2);
v___x_215_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_261_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_261_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_261_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v_traceState_221_; lean_object* v_env_222_; lean_object* v_nextMacroScope_223_; lean_object* v_ngen_224_; lean_object* v_auxDeclNGen_225_; lean_object* v_cache_226_; lean_object* v_recordedDeps_227_; lean_object* v_messages_228_; lean_object* v_infoState_229_; lean_object* v_snapshotTasks_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_260_; 
v___x_220_ = lean_st_ref_take(v___y_212_);
v_traceState_221_ = lean_ctor_get(v___x_220_, 4);
v_env_222_ = lean_ctor_get(v___x_220_, 0);
v_nextMacroScope_223_ = lean_ctor_get(v___x_220_, 1);
v_ngen_224_ = lean_ctor_get(v___x_220_, 2);
v_auxDeclNGen_225_ = lean_ctor_get(v___x_220_, 3);
v_cache_226_ = lean_ctor_get(v___x_220_, 5);
v_recordedDeps_227_ = lean_ctor_get(v___x_220_, 6);
v_messages_228_ = lean_ctor_get(v___x_220_, 7);
v_infoState_229_ = lean_ctor_get(v___x_220_, 8);
v_snapshotTasks_230_ = lean_ctor_get(v___x_220_, 9);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_260_ == 0)
{
v___x_232_ = v___x_220_;
v_isShared_233_ = v_isSharedCheck_260_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_snapshotTasks_230_);
lean_inc(v_infoState_229_);
lean_inc(v_messages_228_);
lean_inc(v_recordedDeps_227_);
lean_inc(v_cache_226_);
lean_inc(v_traceState_221_);
lean_inc(v_auxDeclNGen_225_);
lean_inc(v_ngen_224_);
lean_inc(v_nextMacroScope_223_);
lean_inc(v_env_222_);
lean_dec(v___x_220_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_260_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
uint64_t v_tid_234_; lean_object* v_traces_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_259_; 
v_tid_234_ = lean_ctor_get_uint64(v_traceState_221_, sizeof(void*)*1);
v_traces_235_ = lean_ctor_get(v_traceState_221_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v_traceState_221_);
if (v_isSharedCheck_259_ == 0)
{
v___x_237_ = v_traceState_221_;
v_isShared_238_ = v_isSharedCheck_259_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_traces_235_);
lean_dec(v_traceState_221_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_259_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; double v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_239_ = lean_box(0);
v___x_240_ = lean_box(0);
v___x_241_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0);
v___x_242_ = 0;
v___x_243_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1));
v___x_244_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_244_, 0, v_cls_207_);
lean_ctor_set(v___x_244_, 1, v___x_240_);
lean_ctor_set(v___x_244_, 2, v___x_243_);
lean_ctor_set_float(v___x_244_, sizeof(void*)*3, v___x_241_);
lean_ctor_set_float(v___x_244_, sizeof(void*)*3 + 8, v___x_241_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*3 + 16, v___x_242_);
v___x_245_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2));
v___x_246_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v_a_216_);
lean_ctor_set(v___x_246_, 2, v___x_245_);
lean_inc(v_ref_214_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_ref_214_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = l_Lean_PersistentArray_push___redArg(v_traces_235_, v___x_247_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_248_);
v___x_250_ = v___x_237_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_248_);
lean_ctor_set_uint64(v_reuseFailAlloc_258_, sizeof(void*)*1, v_tid_234_);
v___x_250_ = v_reuseFailAlloc_258_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 4, v___x_250_);
v___x_252_ = v___x_232_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_env_222_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_nextMacroScope_223_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_ngen_224_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v_auxDeclNGen_225_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_257_, 5, v_cache_226_);
lean_ctor_set(v_reuseFailAlloc_257_, 6, v_recordedDeps_227_);
lean_ctor_set(v_reuseFailAlloc_257_, 7, v_messages_228_);
lean_ctor_set(v_reuseFailAlloc_257_, 8, v_infoState_229_);
lean_ctor_set(v_reuseFailAlloc_257_, 9, v_snapshotTasks_230_);
v___x_252_ = v_reuseFailAlloc_257_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = lean_st_ref_put(v___y_212_, v___x_252_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_239_);
v___x_255_ = v___x_218_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_239_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___boxed(lean_object* v_cls_262_, lean_object* v_msg_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_cls_262_, v_msg_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(lean_object* v_msg_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_ref_276_; lean_object* v___x_277_; lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_286_; 
v_ref_276_ = lean_ctor_get(v___y_273_, 2);
v___x_277_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_286_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
lean_inc(v_ref_276_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v_ref_276_);
lean_ctor_set(v___x_282_, 1, v_a_278_);
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 1);
lean_ctor_set(v___x_280_, 0, v___x_282_);
v___x_284_ = v___x_280_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg___boxed(lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v_msg_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0(void){
_start:
{
lean_object* v___x_294_; lean_object* v_dummy_295_; 
v___x_294_ = lean_box(0);
v_dummy_295_ = l_Lean_Expr_sort___override(v___x_294_);
return v_dummy_295_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1));
v___x_298_ = l_Lean_stringToMessageData(v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15));
v___x_323_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17));
v___x_324_ = l_Lean_Name_append(v___x_323_, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19));
v___x_327_ = l_Lean_stringToMessageData(v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21));
v___x_330_ = l_Lean_stringToMessageData(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23));
v___x_333_ = l_Lean_stringToMessageData(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25));
v___x_336_ = l_Lean_stringToMessageData(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27));
v___x_339_ = l_Lean_stringToMessageData(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___boxed(lean_object* v_goal_343_, lean_object* v_pat_344_, lean_object* v_k_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v_goal_343_, v_pat_344_, v_k_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(lean_object* v_goal_356_, lean_object* v_pat_357_, lean_object* v_k_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
switch(lean_obj_tag(v_pat_357_))
{
case 0:
{
lean_object* v_name_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_424_; 
v_name_368_ = lean_ctor_get(v_pat_357_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v_pat_357_);
if (v_isSharedCheck_424_ == 0)
{
v___x_370_ = v_pat_357_;
v_isShared_371_ = v_isSharedCheck_424_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_name_368_);
lean_dec(v_pat_357_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_424_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2));
lean_inc(v_name_368_);
v___x_373_ = l_Lean_Syntax_isOfKind(v_name_368_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_375_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 3);
v___x_375_ = v___x_370_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_name_368_);
v___x_375_ = v_reuseFailAlloc_377_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
v_pat_357_ = v___x_375_;
goto _start;
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = l_Lean_Syntax_getArg(v_name_368_, v___x_378_);
v___x_380_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4));
v___x_381_ = l_Lean_Syntax_isOfKind(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_383_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 3);
v___x_383_ = v___x_370_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_name_368_);
v___x_383_ = v_reuseFailAlloc_385_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
v_pat_357_ = v___x_383_;
goto _start;
}
}
else
{
lean_object* v___x_387_; 
lean_inc(v_name_368_);
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 2);
v___x_387_ = v___x_370_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_name_368_);
v___x_387_ = v_reuseFailAlloc_423_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
lean_inc_ref(v_k_358_);
lean_inc_ref(v_goal_356_);
v___x_388_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___boxed), 12, 3);
lean_closure_set(v___x_388_, 0, v_goal_356_);
lean_closure_set(v___x_388_, 1, v___x_387_);
lean_closure_set(v___x_388_, 2, v_k_358_);
v___x_389_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_360_, v_a_362_, v_a_364_, v_a_366_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_391_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
v___x_391_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_388_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_dec(v_a_390_);
lean_dec(v_name_368_);
lean_dec_ref(v_k_358_);
lean_dec_ref(v_goal_356_);
return v___x_391_;
}
else
{
lean_object* v_a_392_; uint8_t v___y_394_; uint8_t v___x_413_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v___x_413_ = l_Lean_Exception_isInterrupt(v_a_392_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; 
lean_inc(v_a_392_);
v___x_414_ = l_Lean_Exception_isRuntime(v_a_392_);
v___y_394_ = v___x_414_;
goto v___jp_393_;
}
else
{
v___y_394_ = v___x_413_;
goto v___jp_393_;
}
v___jp_393_:
{
if (v___y_394_ == 0)
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_411_; 
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_391_, 0);
lean_dec(v_unused_412_);
v___x_396_ = v___x_391_;
v_isShared_397_ = v_isSharedCheck_411_;
goto v_resetjp_395_;
}
else
{
lean_dec(v___x_391_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_411_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_390_, v___y_394_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_400_; 
lean_dec_ref_known(v___x_398_, 1);
if (v_isShared_397_ == 0)
{
lean_ctor_set_tag(v___x_396_, 3);
lean_ctor_set(v___x_396_, 0, v_name_368_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_name_368_);
v___x_400_ = v_reuseFailAlloc_402_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
v_pat_357_ = v___x_400_;
goto _start;
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_del_object(v___x_396_);
lean_dec(v_name_368_);
lean_dec_ref(v_k_358_);
lean_dec_ref(v_goal_356_);
v_a_403_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_398_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_398_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
else
{
lean_dec(v_a_390_);
lean_dec(v_name_368_);
lean_dec_ref(v_k_358_);
lean_dec_ref(v_goal_356_);
return v___x_391_;
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec_ref(v___x_388_);
lean_dec(v_name_368_);
lean_dec_ref(v_k_358_);
lean_dec_ref(v_goal_356_);
v_a_415_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_389_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_389_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
}
}
case 1:
{
lean_object* v_args_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_635_; 
v_args_425_ = lean_ctor_get(v_pat_357_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v_pat_357_);
if (v_isSharedCheck_635_ == 0)
{
v___x_427_ = v_pat_357_;
v_isShared_428_ = v_isSharedCheck_635_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_args_425_);
lean_dec(v_pat_357_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_635_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
if (lean_obj_tag(v_args_425_) == 0)
{
lean_object* v___x_429_; 
lean_del_object(v___x_427_);
lean_dec_ref(v_k_358_);
lean_dec_ref(v_goal_356_);
v___x_429_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_429_;
}
else
{
lean_object* v_tail_430_; 
v_tail_430_ = lean_ctor_get(v_args_425_, 1);
if (lean_obj_tag(v_tail_430_) == 0)
{
lean_object* v_head_431_; 
lean_del_object(v___x_427_);
v_head_431_ = lean_ctor_get(v_args_425_, 0);
lean_inc(v_head_431_);
lean_dec_ref_known(v_args_425_, 2);
v_pat_357_ = v_head_431_;
goto _start;
}
else
{
lean_object* v_head_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_633_; 
lean_inc(v_tail_430_);
v_head_433_ = lean_ctor_get(v_args_425_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v_args_425_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v_args_425_, 1);
lean_dec(v_unused_634_);
v___x_435_ = v_args_425_;
v_isShared_436_ = v_isSharedCheck_633_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_head_433_);
lean_dec(v_args_425_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_633_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_u_437_; lean_object* v_00_u03c3s_438_; lean_object* v_hyps_439_; lean_object* v_target_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_632_; 
v_u_437_ = lean_ctor_get(v_goal_356_, 0);
v_00_u03c3s_438_ = lean_ctor_get(v_goal_356_, 1);
v_hyps_439_ = lean_ctor_get(v_goal_356_, 2);
v_target_440_ = lean_ctor_get(v_goal_356_, 3);
v_isSharedCheck_632_ = !lean_is_exclusive(v_goal_356_);
if (v_isSharedCheck_632_ == 0)
{
v___x_442_ = v_goal_356_;
v_isShared_443_ = v_isSharedCheck_632_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_target_440_);
lean_inc(v_hyps_439_);
lean_inc(v_00_u03c3s_438_);
lean_inc(v_u_437_);
lean_dec(v_goal_356_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_632_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = l_Lean_instInhabitedExpr;
v___x_445_ = l_Lean_Meta_whnfR(v_target_440_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_toCold_446_; lean_object* v_options_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_631_; 
v_toCold_446_ = lean_ctor_get(v_a_365_, 0);
v_options_447_ = lean_ctor_get(v_toCold_446_, 2);
v_a_448_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_631_ == 0)
{
v___x_450_ = v___x_445_;
v_isShared_451_ = v_isSharedCheck_631_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_445_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_631_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_inheritedTraceOptions_452_; uint8_t v_hasTrace_453_; lean_object* v___x_454_; lean_object* v_nargs_455_; lean_object* v_dummy_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; uint8_t v___y_473_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; uint8_t v___y_552_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; 
v_inheritedTraceOptions_452_ = lean_ctor_get(v_toCold_446_, 11);
v_hasTrace_453_ = lean_ctor_get_uint8(v_options_447_, sizeof(void*)*1);
v___x_454_ = l_Lean_Expr_getAppFn_x27(v_a_448_);
v_nargs_455_ = l_Lean_Expr_getAppNumArgs(v_a_448_);
v_dummy_456_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0);
lean_inc(v_nargs_455_);
v___x_457_ = lean_mk_array(v_nargs_455_, v_dummy_456_);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = lean_nat_sub(v_nargs_455_, v___x_458_);
lean_dec(v_nargs_455_);
lean_inc(v_a_448_);
v___x_460_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_448_, v___x_457_, v___x_459_);
if (v_hasTrace_453_ == 0)
{
v___y_594_ = v_a_359_;
v___y_595_ = v_a_360_;
v___y_596_ = v_a_361_;
v___y_597_ = v_a_362_;
v___y_598_ = v_a_363_;
v___y_599_ = v_a_364_;
v___y_600_ = v_a_365_;
v___y_601_ = v_a_366_;
goto v___jp_593_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15));
v___x_610_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18);
v___x_611_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_452_, v_options_447_, v___x_610_);
if (v___x_611_ == 0)
{
v___y_594_ = v_a_359_;
v___y_595_ = v_a_360_;
v___y_596_ = v_a_361_;
v___y_597_ = v_a_362_;
v___y_598_ = v_a_363_;
v___y_599_ = v_a_364_;
v___y_600_ = v_a_365_;
v___y_601_ = v_a_366_;
goto v___jp_593_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_612_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20);
lean_inc_ref(v___x_454_);
v___x_613_ = l_Lean_MessageData_ofExpr(v___x_454_);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
lean_inc_ref(v___x_460_);
v___x_617_ = lean_array_to_list(v___x_460_);
v___x_618_ = lean_box(0);
v___x_619_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__2(v___x_617_, v___x_618_);
v___x_620_ = l_Lean_MessageData_ofList(v___x_619_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_616_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v___x_609_, v___x_621_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_dec_ref_known(v___x_622_, 1);
v___y_594_ = v_a_359_;
v___y_595_ = v_a_360_;
v___y_596_ = v_a_361_;
v___y_597_ = v_a_362_;
v___y_598_ = v_a_363_;
v___y_599_ = v_a_364_;
v___y_600_ = v_a_365_;
v___y_601_ = v_a_366_;
goto v___jp_593_;
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v___x_460_);
lean_dec_ref(v___x_454_);
lean_del_object(v___x_450_);
lean_dec(v_a_448_);
lean_del_object(v___x_442_);
lean_dec_ref(v_hyps_439_);
lean_dec_ref(v_00_u03c3s_438_);
lean_dec(v_u_437_);
lean_del_object(v___x_435_);
lean_dec(v_head_433_);
lean_dec(v_tail_430_);
lean_del_object(v___x_427_);
lean_dec_ref(v_k_358_);
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
v___jp_461_:
{
if (v___y_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec_ref(v___x_460_);
lean_del_object(v___x_450_);
lean_del_object(v___x_442_);
lean_dec_ref(v_hyps_439_);
lean_dec_ref(v_00_u03c3s_438_);
lean_dec(v_u_437_);
lean_del_object(v___x_435_);
lean_dec(v_head_433_);
lean_dec(v_tail_430_);
lean_del_object(v___x_427_);
lean_dec_ref(v_k_358_);
v___x_474_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2);
v___x_475_ = l_Lean_MessageData_ofExpr(v_a_448_);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v___x_476_, v___y_465_, v___y_470_, v___y_467_, v___y_469_);
return v___x_477_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
lean_dec(v_a_448_);
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_array_get(v___x_444_, v___x_460_, v___x_478_);
v___x_480_ = lean_unsigned_to_nat(2u);
v___x_481_ = lean_array_get(v___x_444_, v___x_460_, v___x_480_);
lean_inc(v___x_479_);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 1);
lean_ctor_set(v___x_450_, 0, v___x_479_);
v___x_483_ = v___x_450_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_479_);
v___x_483_ = v_reuseFailAlloc_539_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(v_head_433_, v___x_483_, v___y_472_, v___y_463_, v___y_464_, v___y_466_, v___y_465_, v___y_470_, v___y_467_, v___y_469_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
if (lean_obj_tag(v_a_485_) == 1)
{
lean_object* v_val_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v_val_486_ = lean_ctor_get(v_a_485_, 0);
lean_inc_n(v_val_486_, 2);
lean_dec_ref_known(v_a_485_, 1);
v___x_487_ = lean_mk_empty_array_with_capacity(v___x_458_);
v___x_488_ = lean_array_push(v___x_487_, v_val_486_);
v___x_489_ = lean_unsigned_to_nat(3u);
v___x_490_ = lean_array_get_size(v___x_460_);
v___x_491_ = l_Array_toSubarray___redArg(v___x_460_, v___x_489_, v___x_490_);
v___x_492_ = l_Subarray_copy___redArg(v___x_491_);
v___x_493_ = l_Array_append___redArg(v___x_488_, v___x_492_);
lean_dec_ref(v___x_492_);
lean_inc(v___x_481_);
v___x_494_ = l_Lean_Expr_beta(v___x_481_, v___x_493_);
lean_inc_ref(v_hyps_439_);
lean_inc_ref(v_00_u03c3s_438_);
lean_inc(v_u_437_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 3, v___x_494_);
v___x_496_ = v___x_442_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_u_437_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_00_u03c3s_438_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_hyps_439_);
lean_ctor_set(v_reuseFailAlloc_528_, 3, v___x_494_);
v___x_496_ = v_reuseFailAlloc_528_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_498_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v_tail_430_);
v___x_498_ = v___x_427_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_tail_430_);
v___x_498_ = v_reuseFailAlloc_527_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v___x_496_, v___x_498_, v_k_358_, v___y_472_, v___y_463_, v___y_464_, v___y_466_, v___y_465_, v___y_470_, v___y_467_, v___y_469_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_501_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
lean_inc(v___x_479_);
v___x_501_ = l_Lean_Meta_getLevel(v___x_479_, v___y_465_, v___y_470_, v___y_467_, v___y_469_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_518_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_518_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_518_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_518_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_506_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3));
lean_inc_ref(v___y_468_);
lean_inc_ref(v___y_471_);
lean_inc_ref(v___y_462_);
v___x_507_ = l_Lean_Name_mkStr4(v___y_462_, v___y_471_, v___y_468_, v___x_506_);
v___x_508_ = lean_box(0);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_508_);
lean_ctor_set(v___x_435_, 0, v_u_437_);
v___x_510_ = v___x_435_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_u_437_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_517_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_511_, 0, v_a_502_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = l_Lean_mkConst(v___x_507_, v___x_511_);
v___x_513_ = l_Lean_mkApp6(v___x_512_, v___x_479_, v_00_u03c3s_438_, v_hyps_439_, v___x_481_, v_val_486_, v_a_500_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_513_);
v___x_515_ = v___x_504_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
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
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_a_500_);
lean_dec(v_val_486_);
lean_dec(v___x_481_);
lean_dec(v___x_479_);
lean_dec_ref(v_hyps_439_);
lean_dec_ref(v_00_u03c3s_438_);
lean_dec(v_u_437_);
lean_del_object(v___x_435_);
v_a_519_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_501_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_501_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_dec(v_val_486_);
lean_dec(v___x_481_);
lean_dec(v___x_479_);
lean_dec_ref(v_hyps_439_);
lean_dec_ref(v_00_u03c3s_438_);
lean_dec(v_u_437_);
lean_del_object(v___x_435_);
return v___x_499_;
}
}
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_a_485_);
lean_dec(v___x_481_);
lean_dec(v___x_479_);
lean_dec_ref(v___x_460_);
lean_del_object(v___x_442_);
lean_dec_ref(v_hyps_439_);
lean_dec_ref(v_00_u03c3s_438_);
lean_dec(v_u_437_);
lean_del_object(v___x_435_);
lean_dec(v_tail_430_);
lean_del_object(v___x_427_);
lean_dec_ref(v_k_358_);
v___x_529_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5);
v___x_530_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v___x_529_, v___y_465_, v___y_470_, v___y_467_, v___y_469_);
return v___x_530_;
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v___x_481_);
lean_dec(v___x_479_);
lean_dec_ref(v___x_460_);
lean_del_object(v___x_442_);
lean_dec_ref(v_hyps_439_);
lean_dec_ref(v_00_u03c3s_438_);
lean_dec(v_u_437_);
lean_del_object(v___x_435_);
lean_dec(v_tail_430_);
lean_del_object(v___x_427_);
lean_dec_ref(v_k_358_);
v_a_531_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_484_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_484_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
v___jp_540_:
{
if (v___y_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_553_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6));
lean_inc_ref(v___y_548_);
lean_inc_ref(v___y_550_);
lean_inc_ref(v___y_542_);
v___x_554_ = l_Lean_Name_mkStr4(v___y_542_, v___y_550_, v___y_548_, v___x_553_);
v___x_555_ = l_Lean_Expr_isConstOf(v___x_454_, v___x_554_);
lean_dec(v___x_554_);
lean_dec_ref(v___x_454_);
if (v___x_555_ == 0)
{
v___y_462_ = v___y_542_;
v___y_463_ = v___y_541_;
v___y_464_ = v___y_543_;
v___y_465_ = v___y_545_;
v___y_466_ = v___y_544_;
v___y_467_ = v___y_546_;
v___y_468_ = v___y_548_;
v___y_469_ = v___y_547_;
v___y_470_ = v___y_549_;
v___y_471_ = v___y_550_;
v___y_472_ = v___y_551_;
v___y_473_ = v___x_555_;
goto v___jp_461_;
}
else
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_box(0);
v___x_557_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(v___x_460_, v___x_556_);
v___y_462_ = v___y_542_;
v___y_463_ = v___y_541_;
v___y_464_ = v___y_543_;
v___y_465_ = v___y_545_;
v___y_466_ = v___y_544_;
v___y_467_ = v___y_546_;
v___y_468_ = v___y_548_;
v___y_469_ = v___y_547_;
v___y_470_ = v___y_549_;
v___y_471_ = v___y_550_;
v___y_472_ = v___y_551_;
v___y_473_ = v___x_557_;
goto v___jp_461_;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref(v___x_454_);
lean_del_object(v___x_450_);
lean_dec(v_a_448_);
lean_del_object(v___x_442_);
lean_del_object(v___x_435_);
lean_del_object(v___x_427_);
v___x_558_ = lean_array_get_borrowed(v___x_444_, v___x_460_, v___x_458_);
v___x_559_ = lean_unsigned_to_nat(3u);
v___x_560_ = lean_array_get_size(v___x_460_);
lean_inc_ref(v___x_460_);
v___x_561_ = l_Array_toSubarray___redArg(v___x_460_, v___x_559_, v___x_560_);
v___x_562_ = l_Subarray_copy___redArg(v___x_561_);
lean_inc_ref(v___x_562_);
lean_inc(v___x_558_);
v___x_563_ = l_Lean_Expr_beta(v___x_558_, v___x_562_);
v___x_564_ = lean_unsigned_to_nat(2u);
v___x_565_ = lean_array_get(v___x_444_, v___x_460_, v___x_564_);
lean_dec_ref(v___x_460_);
v___x_566_ = l_Lean_Expr_beta(v___x_565_, v___x_562_);
lean_inc_ref(v___x_563_);
lean_inc_ref(v_hyps_439_);
lean_inc_ref(v_00_u03c3s_438_);
lean_inc(v_u_437_);
v___x_567_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_567_, 0, v_u_437_);
lean_ctor_set(v___x_567_, 1, v_00_u03c3s_438_);
lean_ctor_set(v___x_567_, 2, v_hyps_439_);
lean_ctor_set(v___x_567_, 3, v___x_563_);
lean_inc_ref(v_k_358_);
v___x_568_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v___x_567_, v_head_433_, v_k_358_, v___y_551_, v___y_541_, v___y_543_, v___y_544_, v___y_545_, v___y_549_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_592_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_592_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_592_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_592_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_575_; 
lean_inc_ref(v___x_566_);
lean_inc_ref(v_hyps_439_);
lean_inc_ref(v_00_u03c3s_438_);
lean_inc(v_u_437_);
v___x_573_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_573_, 0, v_u_437_);
lean_ctor_set(v___x_573_, 1, v_00_u03c3s_438_);
lean_ctor_set(v___x_573_, 2, v_hyps_439_);
lean_ctor_set(v___x_573_, 3, v___x_566_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 1);
lean_ctor_set(v___x_571_, 0, v_tail_430_);
v___x_575_ = v___x_571_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_tail_430_);
v___x_575_ = v_reuseFailAlloc_591_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v___x_573_, v___x_575_, v_k_358_, v___y_551_, v___y_541_, v___y_543_, v___y_544_, v___y_545_, v___y_549_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_590_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_590_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_581_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7));
lean_inc_ref(v___y_548_);
lean_inc_ref(v___y_550_);
lean_inc_ref(v___y_542_);
v___x_582_ = l_Lean_Name_mkStr4(v___y_542_, v___y_550_, v___y_548_, v___x_581_);
v___x_583_ = lean_box(0);
v___x_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_584_, 0, v_u_437_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = l_Lean_mkConst(v___x_582_, v___x_584_);
v___x_586_ = l_Lean_mkApp6(v___x_585_, v_00_u03c3s_438_, v_hyps_439_, v___x_563_, v___x_566_, v_a_569_, v_a_577_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_586_);
v___x_588_ = v___x_579_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_dec(v_a_569_);
lean_dec_ref(v___x_566_);
lean_dec_ref(v___x_563_);
lean_dec_ref(v_hyps_439_);
lean_dec_ref(v_00_u03c3s_438_);
lean_dec(v_u_437_);
return v___x_576_;
}
}
}
}
else
{
lean_dec_ref(v___x_566_);
lean_dec_ref(v___x_563_);
lean_dec_ref(v_hyps_439_);
lean_dec_ref(v_00_u03c3s_438_);
lean_dec(v_u_437_);
lean_dec(v_tail_430_);
lean_dec_ref(v_k_358_);
return v___x_568_;
}
}
}
v___jp_593_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_602_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8));
v___x_603_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9));
v___x_604_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10));
v___x_605_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12));
v___x_606_ = l_Lean_Expr_isConstOf(v___x_454_, v___x_605_);
if (v___x_606_ == 0)
{
v___y_541_ = v___y_595_;
v___y_542_ = v___x_602_;
v___y_543_ = v___y_596_;
v___y_544_ = v___y_597_;
v___y_545_ = v___y_598_;
v___y_546_ = v___y_600_;
v___y_547_ = v___y_601_;
v___y_548_ = v___x_604_;
v___y_549_ = v___y_599_;
v___y_550_ = v___x_603_;
v___y_551_ = v___y_594_;
v___y_552_ = v___x_606_;
goto v___jp_540_;
}
else
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_box(0);
v___x_608_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(v___x_460_, v___x_607_);
v___y_541_ = v___y_595_;
v___y_542_ = v___x_602_;
v___y_543_ = v___y_596_;
v___y_544_ = v___y_597_;
v___y_545_ = v___y_598_;
v___y_546_ = v___y_600_;
v___y_547_ = v___y_601_;
v___y_548_ = v___x_604_;
v___y_549_ = v___y_599_;
v___y_550_ = v___x_603_;
v___y_551_ = v___y_594_;
v___y_552_ = v___x_608_;
goto v___jp_540_;
}
}
}
}
else
{
lean_del_object(v___x_442_);
lean_dec_ref(v_hyps_439_);
lean_dec_ref(v_00_u03c3s_438_);
lean_dec(v_u_437_);
lean_del_object(v___x_435_);
lean_dec(v_head_433_);
lean_dec(v_tail_430_);
lean_del_object(v___x_427_);
lean_dec_ref(v_k_358_);
return v___x_445_;
}
}
}
}
}
}
}
case 2:
{
lean_object* v_h_636_; lean_object* v___x_637_; 
lean_dec_ref(v_k_358_);
v_h_636_ = lean_ctor_get(v_pat_357_, 0);
lean_inc(v_h_636_);
lean_dec_ref_known(v_pat_357_, 1);
v___x_637_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(v_goal_356_, v_h_636_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_637_;
}
case 3:
{
lean_object* v_h_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
lean_dec_ref(v_k_358_);
v_h_638_ = lean_ctor_get(v_pat_357_, 0);
lean_inc_n(v_h_638_, 2);
lean_dec_ref_known(v_pat_357_, 1);
v___x_639_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2));
v___x_640_ = l_Lean_Syntax_isOfKind(v_h_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec(v_h_638_);
lean_inc_ref(v_goal_356_);
v___x_641_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v_goal_356_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_657_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_657_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_657_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_657_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
if (lean_obj_tag(v_a_642_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_648_; 
lean_dec_ref(v_goal_356_);
v_val_646_ = lean_ctor_get(v_a_642_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v_a_642_, 1);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_val_646_);
v___x_648_ = v___x_644_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_val_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
else
{
lean_object* v_target_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
lean_del_object(v___x_644_);
lean_dec(v_a_642_);
v_target_650_ = lean_ctor_get(v_goal_356_, 3);
lean_inc_ref(v_target_650_);
lean_dec_ref(v_goal_356_);
v___x_651_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24);
v___x_652_ = l_Lean_MessageData_ofExpr(v_target_650_);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26);
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_655_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_656_;
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_goal_356_);
v_a_658_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_641_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_641_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
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
lean_object* v___x_666_; lean_object* v_name_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_666_ = lean_unsigned_to_nat(0u);
v_name_667_ = l_Lean_Syntax_getArg(v_h_638_, v___x_666_);
lean_dec(v_h_638_);
v___x_668_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4));
lean_inc(v_name_667_);
v___x_669_ = l_Lean_Syntax_isOfKind(v_name_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v_name_667_);
lean_inc_ref(v_goal_356_);
v___x_670_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v_goal_356_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_686_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_686_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_686_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_686_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
if (lean_obj_tag(v_a_671_) == 1)
{
lean_object* v_val_675_; lean_object* v___x_677_; 
lean_dec_ref(v_goal_356_);
v_val_675_ = lean_ctor_get(v_a_671_, 0);
lean_inc(v_val_675_);
lean_dec_ref_known(v_a_671_, 1);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v_val_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_val_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
else
{
lean_object* v_target_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
lean_del_object(v___x_673_);
lean_dec(v_a_671_);
v_target_679_ = lean_ctor_get(v_goal_356_, 3);
lean_inc_ref(v_target_679_);
lean_dec_ref(v_goal_356_);
v___x_680_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24);
v___x_681_ = l_Lean_MessageData_ofExpr(v_target_679_);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_684_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_685_;
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v_goal_356_);
v_a_687_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_670_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_670_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v___x_695_; 
lean_inc(v_name_667_);
v___x_695_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(v_goal_356_, v_name_667_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_711_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_711_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_711_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_711_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
if (lean_obj_tag(v_a_696_) == 1)
{
lean_object* v_val_700_; lean_object* v___x_702_; 
lean_dec(v_name_667_);
v_val_700_ = lean_ctor_get(v_a_696_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v_a_696_, 1);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_val_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_val_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
lean_del_object(v___x_698_);
lean_dec(v_a_696_);
v___x_704_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28);
v___x_705_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_667_);
v___x_706_ = l_Lean_MessageData_ofFormat(v___x_705_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_704_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_709_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_710_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_name_667_);
v_a_712_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_695_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_695_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
}
default: 
{
lean_object* v_name_720_; lean_object* v___x_721_; 
v_name_720_ = lean_ctor_get(v_pat_357_, 0);
lean_inc(v_name_720_);
lean_dec_ref_known(v_pat_357_, 1);
lean_inc(v_a_366_);
lean_inc_ref(v_a_365_);
lean_inc(v_a_364_);
lean_inc_ref(v_a_363_);
lean_inc(v_a_362_);
lean_inc_ref(v_a_361_);
lean_inc(v_a_360_);
lean_inc_ref(v_a_359_);
v___x_721_ = lean_apply_11(v_k_358_, v_goal_356_, v_name_720_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, lean_box(0));
return v___x_721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1(lean_object* v_00_u03b1_722_, lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v_msg_723_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___boxed(lean_object* v_00_u03b1_734_, lean_object* v_msg_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1(v_00_u03b1_734_, v_msg_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3(lean_object* v_cls_746_, lean_object* v_msg_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_cls_746_, v_msg_747_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___boxed(lean_object* v_cls_758_, lean_object* v_msg_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3(v_cls_758_, v_msg_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4(lean_object* v_00_u03b1_770_, lean_object* v_msg_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v_msg_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___boxed(lean_object* v_00_u03b1_778_, lean_object* v_msg_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4(v_00_u03b1_778_, v_msg_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0(lean_object* v_x_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
v___x_796_ = lean_apply_9(v_x_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, lean_box(0));
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0___boxed(lean_object* v_x_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0(v_x_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(lean_object* v_mvarId_808_, lean_object* v_x_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___f_819_; lean_object* v___x_820_; 
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
v___f_819_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_819_, 0, v_x_809_);
lean_closure_set(v___f_819_, 1, v___y_810_);
lean_closure_set(v___f_819_, 2, v___y_811_);
lean_closure_set(v___f_819_, 3, v___y_812_);
lean_closure_set(v___f_819_, 4, v___y_813_);
v___x_820_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_808_, v___f_819_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_820_) == 0)
{
return v___x_820_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___boxed(lean_object* v_mvarId_829_, lean_object* v_x_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_mvarId_829_, v_x_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2(lean_object* v_00_u03b1_841_, lean_object* v_mvarId_842_, lean_object* v_x_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_mvarId_842_, v_x_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___boxed(lean_object* v_00_u03b1_854_, lean_object* v_mvarId_855_, lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2(v_00_u03b1_854_, v_mvarId_855_, v_x_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(lean_object* v_val_867_, lean_object* v_goal_868_, lean_object* v_name_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_868_);
v___x_880_ = l_Lean_Syntax_getId(v_name_869_);
v___x_881_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_879_, v___x_880_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_893_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_893_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_893_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_893_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_886_ = lean_st_ref_take(v_val_867_);
v___x_887_ = l_Lean_Expr_mvarId_x21(v_a_882_);
v___x_888_ = lean_array_push(v___x_886_, v___x_887_);
v___x_889_ = lean_st_ref_put(v_val_867_, v___x_888_);
if (v_isShared_885_ == 0)
{
v___x_891_ = v___x_884_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_882_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
else
{
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed(lean_object* v_val_894_, lean_object* v_goal_895_, lean_object* v_name_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(v_val_894_, v_goal_895_, v_name_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v_name_896_);
lean_dec(v_val_894_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
lean_object* v_ks_911_; lean_object* v_vs_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_936_; 
v_ks_911_ = lean_ctor_get(v_x_907_, 0);
v_vs_912_ = lean_ctor_get(v_x_907_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_x_907_);
if (v_isSharedCheck_936_ == 0)
{
v___x_914_ = v_x_907_;
v_isShared_915_ = v_isSharedCheck_936_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_vs_912_);
lean_inc(v_ks_911_);
lean_dec(v_x_907_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_936_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = lean_array_get_size(v_ks_911_);
v___x_917_ = lean_nat_dec_lt(v_x_908_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
lean_dec(v_x_908_);
v___x_918_ = lean_array_push(v_ks_911_, v_x_909_);
v___x_919_ = lean_array_push(v_vs_912_, v_x_910_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v___x_919_);
lean_ctor_set(v___x_914_, 0, v___x_918_);
v___x_921_ = v___x_914_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
else
{
lean_object* v_k_x27_923_; uint8_t v___x_924_; 
v_k_x27_923_ = lean_array_fget_borrowed(v_ks_911_, v_x_908_);
v___x_924_ = l_Lean_instBEqMVarId_beq(v_x_909_, v_k_x27_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_926_; 
if (v_isShared_915_ == 0)
{
v___x_926_ = v___x_914_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_ks_911_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_vs_912_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_unsigned_to_nat(1u);
v___x_928_ = lean_nat_add(v_x_908_, v___x_927_);
lean_dec(v_x_908_);
v_x_907_ = v___x_926_;
v_x_908_ = v___x_928_;
goto _start;
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_931_ = lean_array_fset(v_ks_911_, v_x_908_, v_x_909_);
v___x_932_ = lean_array_fset(v_vs_912_, v_x_908_, v_x_910_);
lean_dec(v_x_908_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v___x_932_);
lean_ctor_set(v___x_914_, 0, v___x_931_);
v___x_934_ = v___x_914_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(lean_object* v_n_937_, lean_object* v_k_938_, lean_object* v_v_939_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(v_n_937_, v___x_940_, v_k_938_, v_v_939_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(lean_object* v_x_943_, size_t v_x_944_, size_t v_x_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_object* v_es_948_; size_t v___x_949_; size_t v___x_950_; lean_object* v_j_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_es_948_ = lean_ctor_get(v_x_943_, 0);
v___x_949_ = ((size_t)31ULL);
v___x_950_ = lean_usize_land(v_x_944_, v___x_949_);
v_j_951_ = lean_usize_to_nat(v___x_950_);
v___x_952_ = lean_array_get_size(v_es_948_);
v___x_953_ = lean_nat_dec_lt(v_j_951_, v___x_952_);
if (v___x_953_ == 0)
{
lean_dec(v_j_951_);
lean_dec(v_x_947_);
lean_dec(v_x_946_);
return v_x_943_;
}
else
{
lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_992_; 
lean_inc_ref(v_es_948_);
v_isSharedCheck_992_ = !lean_is_exclusive(v_x_943_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v_x_943_, 0);
lean_dec(v_unused_993_);
v___x_955_ = v_x_943_;
v_isShared_956_ = v_isSharedCheck_992_;
goto v_resetjp_954_;
}
else
{
lean_dec(v_x_943_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_992_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_v_957_; lean_object* v___x_958_; lean_object* v_xs_x27_959_; lean_object* v___y_961_; 
v_v_957_ = lean_array_fget(v_es_948_, v_j_951_);
v___x_958_ = lean_box(0);
v_xs_x27_959_ = lean_array_fset(v_es_948_, v_j_951_, v___x_958_);
switch(lean_obj_tag(v_v_957_))
{
case 0:
{
lean_object* v_key_966_; lean_object* v_val_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_977_; 
v_key_966_ = lean_ctor_get(v_v_957_, 0);
v_val_967_ = lean_ctor_get(v_v_957_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_v_957_);
if (v_isSharedCheck_977_ == 0)
{
v___x_969_ = v_v_957_;
v_isShared_970_ = v_isSharedCheck_977_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_val_967_);
lean_inc(v_key_966_);
lean_dec(v_v_957_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_977_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
uint8_t v___x_971_; 
v___x_971_ = l_Lean_instBEqMVarId_beq(v_x_946_, v_key_966_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; 
lean_del_object(v___x_969_);
v___x_972_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_966_, v_val_967_, v_x_946_, v_x_947_);
v___x_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
v___y_961_ = v___x_973_;
goto v___jp_960_;
}
else
{
lean_object* v___x_975_; 
lean_dec(v_val_967_);
lean_dec(v_key_966_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v_x_947_);
lean_ctor_set(v___x_969_, 0, v_x_946_);
v___x_975_ = v___x_969_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_x_946_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_x_947_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
v___y_961_ = v___x_975_;
goto v___jp_960_;
}
}
}
}
case 1:
{
lean_object* v_node_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_990_; 
v_node_978_ = lean_ctor_get(v_v_957_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v_v_957_);
if (v_isSharedCheck_990_ == 0)
{
v___x_980_ = v_v_957_;
v_isShared_981_ = v_isSharedCheck_990_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_node_978_);
lean_dec(v_v_957_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_990_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
size_t v___x_982_; size_t v___x_983_; size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_982_ = ((size_t)5ULL);
v___x_983_ = lean_usize_shift_right(v_x_944_, v___x_982_);
v___x_984_ = ((size_t)1ULL);
v___x_985_ = lean_usize_add(v_x_945_, v___x_984_);
v___x_986_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_node_978_, v___x_983_, v___x_985_, v_x_946_, v_x_947_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_986_);
v___x_988_ = v___x_980_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
v___y_961_ = v___x_988_;
goto v___jp_960_;
}
}
}
default: 
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_x_946_);
lean_ctor_set(v___x_991_, 1, v_x_947_);
v___y_961_ = v___x_991_;
goto v___jp_960_;
}
}
v___jp_960_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = lean_array_fset(v_xs_x27_959_, v_j_951_, v___y_961_);
lean_dec(v_j_951_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_962_);
v___x_964_ = v___x_955_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
else
{
lean_object* v_ks_994_; lean_object* v_vs_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1013_; 
v_ks_994_ = lean_ctor_get(v_x_943_, 0);
v_vs_995_ = lean_ctor_get(v_x_943_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_x_943_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_997_ = v_x_943_;
v_isShared_998_ = v_isSharedCheck_1013_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_vs_995_);
lean_inc(v_ks_994_);
lean_dec(v_x_943_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1013_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_ks_994_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_vs_995_);
v___x_1000_ = v_reuseFailAlloc_1012_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v_newNode_1001_; size_t v___x_1002_; uint8_t v___x_1003_; 
v_newNode_1001_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(v___x_1000_, v_x_946_, v_x_947_);
v___x_1002_ = ((size_t)7ULL);
v___x_1003_ = lean_usize_dec_le(v___x_1002_, v_x_945_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1001_);
v___x_1005_ = lean_unsigned_to_nat(4u);
v___x_1006_ = lean_nat_dec_lt(v___x_1004_, v___x_1005_);
lean_dec(v___x_1004_);
if (v___x_1006_ == 0)
{
lean_object* v_ks_1007_; lean_object* v_vs_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_ks_1007_ = lean_ctor_get(v_newNode_1001_, 0);
lean_inc_ref(v_ks_1007_);
v_vs_1008_ = lean_ctor_get(v_newNode_1001_, 1);
lean_inc_ref(v_vs_1008_);
lean_dec_ref(v_newNode_1001_);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0);
v___x_1011_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_x_945_, v_ks_1007_, v_vs_1008_, v___x_1009_, v___x_1010_);
lean_dec_ref(v_vs_1008_);
lean_dec_ref(v_ks_1007_);
return v___x_1011_;
}
else
{
return v_newNode_1001_;
}
}
else
{
return v_newNode_1001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(size_t v_depth_1014_, lean_object* v_keys_1015_, lean_object* v_vals_1016_, lean_object* v_i_1017_, lean_object* v_entries_1018_){
_start:
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1019_ = lean_array_get_size(v_keys_1015_);
v___x_1020_ = lean_nat_dec_lt(v_i_1017_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_dec(v_i_1017_);
return v_entries_1018_;
}
else
{
lean_object* v_k_1021_; lean_object* v_v_1022_; uint64_t v___x_1023_; size_t v_h_1024_; size_t v___x_1025_; lean_object* v___x_1026_; size_t v___x_1027_; size_t v___x_1028_; size_t v___x_1029_; size_t v_h_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_k_1021_ = lean_array_fget_borrowed(v_keys_1015_, v_i_1017_);
v_v_1022_ = lean_array_fget_borrowed(v_vals_1016_, v_i_1017_);
v___x_1023_ = l_Lean_instHashableMVarId_hash(v_k_1021_);
v_h_1024_ = lean_uint64_to_usize(v___x_1023_);
v___x_1025_ = ((size_t)5ULL);
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = ((size_t)1ULL);
v___x_1028_ = lean_usize_sub(v_depth_1014_, v___x_1027_);
v___x_1029_ = lean_usize_mul(v___x_1025_, v___x_1028_);
v_h_1030_ = lean_usize_shift_right(v_h_1024_, v___x_1029_);
v___x_1031_ = lean_nat_add(v_i_1017_, v___x_1026_);
lean_dec(v_i_1017_);
lean_inc(v_v_1022_);
lean_inc(v_k_1021_);
v___x_1032_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_entries_1018_, v_h_1030_, v_depth_1014_, v_k_1021_, v_v_1022_);
v_i_1017_ = v___x_1031_;
v_entries_1018_ = v___x_1032_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg___boxed(lean_object* v_depth_1034_, lean_object* v_keys_1035_, lean_object* v_vals_1036_, lean_object* v_i_1037_, lean_object* v_entries_1038_){
_start:
{
size_t v_depth_boxed_1039_; lean_object* v_res_1040_; 
v_depth_boxed_1039_ = lean_unbox_usize(v_depth_1034_);
lean_dec(v_depth_1034_);
v_res_1040_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_depth_boxed_1039_, v_keys_1035_, v_vals_1036_, v_i_1037_, v_entries_1038_);
lean_dec_ref(v_vals_1036_);
lean_dec_ref(v_keys_1035_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___boxed(lean_object* v_x_1041_, lean_object* v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
size_t v_x_17333__boxed_1046_; size_t v_x_17334__boxed_1047_; lean_object* v_res_1048_; 
v_x_17333__boxed_1046_ = lean_unbox_usize(v_x_1042_);
lean_dec(v_x_1042_);
v_x_17334__boxed_1047_ = lean_unbox_usize(v_x_1043_);
lean_dec(v_x_1043_);
v_res_1048_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_1041_, v_x_17333__boxed_1046_, v_x_17334__boxed_1047_, v_x_1044_, v_x_1045_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
uint64_t v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_1055_; 
v___x_1052_ = l_Lean_instHashableMVarId_hash(v_x_1050_);
v___x_1053_ = lean_uint64_to_usize(v___x_1052_);
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_1049_, v___x_1053_, v___x_1054_, v_x_1050_, v_x_1051_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(lean_object* v_mvarId_1056_, lean_object* v_val_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; lean_object* v_mctx_1061_; lean_object* v_cache_1062_; lean_object* v_zetaDeltaFVarIds_1063_; lean_object* v_postponed_1064_; lean_object* v_diag_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1095_; 
v___x_1060_ = lean_st_ref_take(v___y_1058_);
v_mctx_1061_ = lean_ctor_get(v___x_1060_, 0);
v_cache_1062_ = lean_ctor_get(v___x_1060_, 1);
v_zetaDeltaFVarIds_1063_ = lean_ctor_get(v___x_1060_, 2);
v_postponed_1064_ = lean_ctor_get(v___x_1060_, 3);
v_diag_1065_ = lean_ctor_get(v___x_1060_, 4);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1067_ = v___x_1060_;
v_isShared_1068_ = v_isSharedCheck_1095_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_diag_1065_);
lean_inc(v_postponed_1064_);
lean_inc(v_zetaDeltaFVarIds_1063_);
lean_inc(v_cache_1062_);
lean_inc(v_mctx_1061_);
lean_dec(v___x_1060_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1095_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_depth_1069_; lean_object* v_levelAssignDepth_1070_; lean_object* v_lmvarCounter_1071_; lean_object* v_mvarCounter_1072_; lean_object* v_lDecls_1073_; lean_object* v_decls_1074_; lean_object* v_userNames_1075_; lean_object* v_lAssignment_1076_; lean_object* v_eAssignment_1077_; lean_object* v_dAssignment_1078_; lean_object* v_instanceTypedMVars_1079_; lean_object* v_synthNormMemo_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1094_; 
v_depth_1069_ = lean_ctor_get(v_mctx_1061_, 0);
v_levelAssignDepth_1070_ = lean_ctor_get(v_mctx_1061_, 1);
v_lmvarCounter_1071_ = lean_ctor_get(v_mctx_1061_, 2);
v_mvarCounter_1072_ = lean_ctor_get(v_mctx_1061_, 3);
v_lDecls_1073_ = lean_ctor_get(v_mctx_1061_, 4);
v_decls_1074_ = lean_ctor_get(v_mctx_1061_, 5);
v_userNames_1075_ = lean_ctor_get(v_mctx_1061_, 6);
v_lAssignment_1076_ = lean_ctor_get(v_mctx_1061_, 7);
v_eAssignment_1077_ = lean_ctor_get(v_mctx_1061_, 8);
v_dAssignment_1078_ = lean_ctor_get(v_mctx_1061_, 9);
v_instanceTypedMVars_1079_ = lean_ctor_get(v_mctx_1061_, 10);
v_synthNormMemo_1080_ = lean_ctor_get(v_mctx_1061_, 11);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_mctx_1061_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1082_ = v_mctx_1061_;
v_isShared_1083_ = v_isSharedCheck_1094_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_synthNormMemo_1080_);
lean_inc(v_instanceTypedMVars_1079_);
lean_inc(v_dAssignment_1078_);
lean_inc(v_eAssignment_1077_);
lean_inc(v_lAssignment_1076_);
lean_inc(v_userNames_1075_);
lean_inc(v_decls_1074_);
lean_inc(v_lDecls_1073_);
lean_inc(v_mvarCounter_1072_);
lean_inc(v_lmvarCounter_1071_);
lean_inc(v_levelAssignDepth_1070_);
lean_inc(v_depth_1069_);
lean_dec(v_mctx_1061_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1094_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1084_ = lean_box(0);
v___x_1085_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(v_eAssignment_1077_, v_mvarId_1056_, v_val_1057_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 8, v___x_1085_);
v___x_1087_ = v___x_1082_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_depth_1069_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_levelAssignDepth_1070_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_lmvarCounter_1071_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_mvarCounter_1072_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v_lDecls_1073_);
lean_ctor_set(v_reuseFailAlloc_1093_, 5, v_decls_1074_);
lean_ctor_set(v_reuseFailAlloc_1093_, 6, v_userNames_1075_);
lean_ctor_set(v_reuseFailAlloc_1093_, 7, v_lAssignment_1076_);
lean_ctor_set(v_reuseFailAlloc_1093_, 8, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1093_, 9, v_dAssignment_1078_);
lean_ctor_set(v_reuseFailAlloc_1093_, 10, v_instanceTypedMVars_1079_);
lean_ctor_set(v_reuseFailAlloc_1093_, 11, v_synthNormMemo_1080_);
v___x_1087_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1089_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1087_);
v___x_1089_ = v___x_1067_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_cache_1062_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_zetaDeltaFVarIds_1063_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_postponed_1064_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_diag_1065_);
v___x_1089_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_st_ref_put(v___y_1058_, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1084_);
return v___x_1091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg___boxed(lean_object* v_mvarId_1096_, lean_object* v_val_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(v_mvarId_1096_, v_val_1097_, v___y_1098_);
lean_dec(v___y_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(lean_object* v___x_1101_, lean_object* v_snd_1102_, lean_object* v_a_1103_, lean_object* v_fst_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v___f_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_st_mk_ref(v___x_1101_);
lean_inc(v___x_1114_);
v___f_1115_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1115_, 0, v___x_1114_);
v___x_1116_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v_snd_1102_, v_a_1103_, v___f_1115_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(v_fst_1104_, v_a_1117_, v___y_1110_);
lean_dec_ref(v___x_1118_);
v___x_1119_ = lean_st_ref_get(v___x_1114_);
lean_dec(v___x_1114_);
v___x_1120_ = lean_array_to_list(v___x_1119_);
v___x_1121_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1120_, v___y_1106_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1121_;
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v___x_1114_);
lean_dec(v_fst_1104_);
v_a_1122_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1116_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1116_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1___boxed(lean_object* v___x_1130_, lean_object* v_snd_1131_, lean_object* v_a_1132_, lean_object* v_fst_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(v___x_1130_, v_snd_1131_, v_a_1132_, v_fst_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(lean_object* v_ref_1144_, lean_object* v_msg_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_toCold_1151_; lean_object* v_currRecDepth_1152_; lean_object* v_ref_1153_; uint16_t v_optionFlags_1154_; uint8_t v_suppressElabErrors_1155_; uint8_t v_isRecordingDeps_1156_; lean_object* v_ref_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_toCold_1151_ = lean_ctor_get(v___y_1148_, 0);
v_currRecDepth_1152_ = lean_ctor_get(v___y_1148_, 1);
v_ref_1153_ = lean_ctor_get(v___y_1148_, 2);
v_optionFlags_1154_ = lean_ctor_get_uint16(v___y_1148_, sizeof(void*)*3);
v_suppressElabErrors_1155_ = lean_ctor_get_uint8(v___y_1148_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1156_ = lean_ctor_get_uint8(v___y_1148_, sizeof(void*)*3 + 3);
v_ref_1157_ = l_Lean_replaceRef(v_ref_1144_, v_ref_1153_);
lean_inc(v_currRecDepth_1152_);
lean_inc_ref(v_toCold_1151_);
v___x_1158_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1158_, 0, v_toCold_1151_);
lean_ctor_set(v___x_1158_, 1, v_currRecDepth_1152_);
lean_ctor_set(v___x_1158_, 2, v_ref_1157_);
lean_ctor_set_uint16(v___x_1158_, sizeof(void*)*3, v_optionFlags_1154_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*3 + 2, v_suppressElabErrors_1155_);
lean_ctor_set_uint8(v___x_1158_, sizeof(void*)*3 + 3, v_isRecordingDeps_1156_);
v___x_1159_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v_msg_1145_, v___y_1146_, v___y_1147_, v___x_1158_, v___y_1149_);
lean_dec_ref_known(v___x_1158_, 3);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1160_, lean_object* v_msg_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_ref_1160_, v_msg_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v_ref_1160_);
return v_res_1167_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = l_Lean_maxRecDepthErrorMessage;
v___x_1174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3);
v___x_1176_ = l_Lean_MessageData_ofFormat(v___x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4);
v___x_1178_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2));
v___x_1179_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v___x_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(lean_object* v_ref_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_ref_1180_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_ref_1185_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(lean_object* v_a_1188_, lean_object* v_x_1189_){
_start:
{
if (lean_obj_tag(v_x_1189_) == 0)
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_box(0);
return v___x_1190_;
}
else
{
lean_object* v_key_1191_; lean_object* v_value_1192_; lean_object* v_tail_1193_; uint8_t v___x_1194_; 
v_key_1191_ = lean_ctor_get(v_x_1189_, 0);
v_value_1192_ = lean_ctor_get(v_x_1189_, 1);
v_tail_1193_ = lean_ctor_get(v_x_1189_, 2);
v___x_1194_ = lean_name_eq(v_key_1191_, v_a_1188_);
if (v___x_1194_ == 0)
{
v_x_1189_ = v_tail_1193_;
goto _start;
}
else
{
lean_object* v___x_1196_; 
lean_inc(v_value_1192_);
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_value_1192_);
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg___boxed(lean_object* v_a_1197_, lean_object* v_x_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_1197_, v_x_1198_);
lean_dec(v_x_1198_);
lean_dec(v_a_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(lean_object* v_m_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_buckets_1202_; lean_object* v___x_1203_; uint64_t v___y_1205_; 
v_buckets_1202_ = lean_ctor_get(v_m_1200_, 1);
v___x_1203_ = lean_array_get_size(v_buckets_1202_);
if (lean_obj_tag(v_a_1201_) == 0)
{
uint64_t v___x_1219_; 
v___x_1219_ = 1723ULL;
v___y_1205_ = v___x_1219_;
goto v___jp_1204_;
}
else
{
uint64_t v_hash_1220_; 
v_hash_1220_ = lean_ctor_get_uint64(v_a_1201_, sizeof(void*)*2);
v___y_1205_ = v_hash_1220_;
goto v___jp_1204_;
}
v___jp_1204_:
{
uint64_t v___x_1206_; uint64_t v___x_1207_; uint64_t v_fold_1208_; uint64_t v___x_1209_; uint64_t v___x_1210_; uint64_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1206_ = 32ULL;
v___x_1207_ = lean_uint64_shift_right(v___y_1205_, v___x_1206_);
v_fold_1208_ = lean_uint64_xor(v___y_1205_, v___x_1207_);
v___x_1209_ = 16ULL;
v___x_1210_ = lean_uint64_shift_right(v_fold_1208_, v___x_1209_);
v___x_1211_ = lean_uint64_xor(v_fold_1208_, v___x_1210_);
v___x_1212_ = lean_uint64_to_usize(v___x_1211_);
v___x_1213_ = lean_usize_of_nat(v___x_1203_);
v___x_1214_ = ((size_t)1ULL);
v___x_1215_ = lean_usize_sub(v___x_1213_, v___x_1214_);
v___x_1216_ = lean_usize_land(v___x_1212_, v___x_1215_);
v___x_1217_ = lean_array_uget_borrowed(v_buckets_1202_, v___x_1216_);
v___x_1218_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_1201_, v___x_1217_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_m_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v_m_1221_, v_a_1222_);
lean_dec(v_a_1222_);
lean_dec_ref(v_m_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___lam__0(lean_object* v___x_1224_, lean_object* v_entry_1225_, lean_object* v_s_1226_){
_start:
{
lean_object* v_addEntryFn_1227_; lean_object* v_importedEntries_1228_; lean_object* v_state_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1237_; 
v_addEntryFn_1227_ = lean_ctor_get(v___x_1224_, 3);
lean_inc(v_addEntryFn_1227_);
lean_dec_ref(v___x_1224_);
v_importedEntries_1228_ = lean_ctor_get(v_s_1226_, 0);
v_state_1229_ = lean_ctor_get(v_s_1226_, 1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_s_1226_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1231_ = v_s_1226_;
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_state_1229_);
lean_inc(v_importedEntries_1228_);
lean_dec(v_s_1226_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_state_1233_; lean_object* v___x_1235_; 
v_state_1233_ = lean_apply_2(v_addEntryFn_1227_, v_state_1229_, v_entry_1225_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v_state_1233_);
v___x_1235_ = v___x_1231_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_importedEntries_1228_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_state_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(lean_object* v_keys_1238_, lean_object* v_i_1239_, lean_object* v_k_1240_){
_start:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_array_get_size(v_keys_1238_);
v___x_1242_ = lean_nat_dec_lt(v_i_1239_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_dec(v_i_1239_);
return v___x_1242_;
}
else
{
lean_object* v_k_x27_1243_; uint8_t v___x_1244_; 
v_k_x27_1243_ = lean_array_fget_borrowed(v_keys_1238_, v_i_1239_);
v___x_1244_ = l_Lean_instBEqExtraModUse_beq(v_k_1240_, v_k_x27_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_unsigned_to_nat(1u);
v___x_1246_ = lean_nat_add(v_i_1239_, v___x_1245_);
lean_dec(v_i_1239_);
v_i_1239_ = v___x_1246_;
goto _start;
}
else
{
lean_dec(v_i_1239_);
return v___x_1242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg___boxed(lean_object* v_keys_1248_, lean_object* v_i_1249_, lean_object* v_k_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_keys_1248_, v_i_1249_, v_k_1250_);
lean_dec_ref(v_k_1250_);
lean_dec_ref(v_keys_1248_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(lean_object* v_x_1253_, size_t v_x_1254_, lean_object* v_x_1255_){
_start:
{
if (lean_obj_tag(v_x_1253_) == 0)
{
lean_object* v_es_1256_; lean_object* v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; lean_object* v_j_1260_; lean_object* v___x_1261_; 
v_es_1256_ = lean_ctor_get(v_x_1253_, 0);
v___x_1257_ = lean_box(2);
v___x_1258_ = ((size_t)31ULL);
v___x_1259_ = lean_usize_land(v_x_1254_, v___x_1258_);
v_j_1260_ = lean_usize_to_nat(v___x_1259_);
v___x_1261_ = lean_array_get_borrowed(v___x_1257_, v_es_1256_, v_j_1260_);
lean_dec(v_j_1260_);
switch(lean_obj_tag(v___x_1261_))
{
case 0:
{
lean_object* v_key_1262_; uint8_t v___x_1263_; 
v_key_1262_ = lean_ctor_get(v___x_1261_, 0);
v___x_1263_ = l_Lean_instBEqExtraModUse_beq(v_x_1255_, v_key_1262_);
return v___x_1263_;
}
case 1:
{
lean_object* v_node_1264_; size_t v___x_1265_; size_t v___x_1266_; 
v_node_1264_ = lean_ctor_get(v___x_1261_, 0);
v___x_1265_ = ((size_t)5ULL);
v___x_1266_ = lean_usize_shift_right(v_x_1254_, v___x_1265_);
v_x_1253_ = v_node_1264_;
v_x_1254_ = v___x_1266_;
goto _start;
}
default: 
{
uint8_t v___x_1268_; 
v___x_1268_ = 0;
return v___x_1268_;
}
}
}
else
{
lean_object* v_ks_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_ks_1269_ = lean_ctor_get(v_x_1253_, 0);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_ks_1269_, v___x_1270_, v_x_1255_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg___boxed(lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_){
_start:
{
size_t v_x_17760__boxed_1275_; uint8_t v_res_1276_; lean_object* v_r_1277_; 
v_x_17760__boxed_1275_ = lean_unbox_usize(v_x_1273_);
lean_dec(v_x_1273_);
v_res_1276_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_1272_, v_x_17760__boxed_1275_, v_x_1274_);
lean_dec_ref(v_x_1274_);
lean_dec_ref(v_x_1272_);
v_r_1277_ = lean_box(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_1278_, lean_object* v_x_1279_){
_start:
{
uint64_t v___x_1280_; size_t v___x_1281_; uint8_t v___x_1282_; 
v___x_1280_ = l_Lean_instHashableExtraModUse_hash(v_x_1279_);
v___x_1281_ = lean_uint64_to_usize(v___x_1280_);
v___x_1282_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_1278_, v___x_1281_, v_x_1279_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
uint8_t v_res_1285_; lean_object* v_r_1286_; 
v_res_1285_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v_x_1283_, v_x_1284_);
lean_dec_ref(v_x_1284_);
lean_dec_ref(v_x_1283_);
v_r_1286_ = lean_box(v_res_1285_);
return v_r_1286_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1287_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1293_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
lean_ctor_set(v___x_1293_, 2, v___x_1292_);
lean_ctor_set(v___x_1293_, 3, v___x_1292_);
lean_ctor_set(v___x_1293_, 4, v___x_1292_);
lean_ctor_set(v___x_1293_, 5, v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1294_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1));
v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
return v___x_1305_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12(void){
_start:
{
lean_object* v_cls_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_cls_1306_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6));
v___x_1307_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17));
v___x_1308_ = l_Lean_Name_append(v___x_1307_, v_cls_1306_);
return v___x_1308_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13));
v___x_1311_ = l_Lean_stringToMessageData(v___x_1310_);
return v___x_1311_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15));
v___x_1314_ = l_Lean_stringToMessageData(v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(lean_object* v_mod_1319_, uint8_t v_isMeta_1320_, lean_object* v_hint_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_env_1361_; uint8_t v_isExporting_1362_; lean_object* v_entry_1363_; lean_object* v___x_1364_; lean_object* v_env_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1359_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4);
v___x_1360_ = lean_st_ref_get(v___y_1325_);
v_env_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc_ref(v_env_1361_);
lean_dec(v___x_1360_);
v_isExporting_1362_ = lean_ctor_get_uint8(v_env_1361_, sizeof(void*)*13);
lean_dec_ref(v_env_1361_);
lean_inc(v_mod_1319_);
v_entry_1363_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1363_, 0, v_mod_1319_);
lean_ctor_set_uint8(v_entry_1363_, sizeof(void*)*1, v_isExporting_1362_);
lean_ctor_set_uint8(v_entry_1363_, sizeof(void*)*1 + 1, v_isMeta_1320_);
v___x_1364_ = lean_st_ref_get(v___y_1325_);
v_env_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc_ref(v_env_1365_);
lean_dec(v___x_1364_);
v___x_1366_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1367_ = lean_box(1);
v___x_1368_ = lean_box(0);
v___x_1369_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1359_, v___x_1366_, v_env_1365_, v___x_1367_, v___x_1368_);
v___x_1370_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v___x_1369_, v_entry_1363_);
lean_dec(v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v_toCold_1371_; lean_object* v_options_1372_; lean_object* v_inheritedTraceOptions_1373_; uint8_t v_hasTrace_1374_; lean_object* v___f_1375_; uint8_t v___x_1376_; lean_object* v___y_1378_; lean_object* v___y_1379_; 
v_toCold_1371_ = lean_ctor_get(v___y_1324_, 0);
v_options_1372_ = lean_ctor_get(v_toCold_1371_, 2);
v_inheritedTraceOptions_1373_ = lean_ctor_get(v_toCold_1371_, 11);
v_hasTrace_1374_ = lean_ctor_get_uint8(v_options_1372_, sizeof(void*)*1);
v___f_1375_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1375_, 0, v___x_1366_);
lean_closure_set(v___f_1375_, 1, v_entry_1363_);
v___x_1376_ = 1;
if (v_hasTrace_1374_ == 0)
{
lean_dec(v_hint_1321_);
lean_dec(v_mod_1319_);
v___y_1378_ = v___y_1323_;
v___y_1379_ = v___y_1325_;
goto v___jp_1377_;
}
else
{
lean_object* v_cls_1406_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_cls_1406_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6));
v___x_1426_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12);
v___x_1427_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1373_, v_options_1372_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_dec(v_hint_1321_);
lean_dec(v_mod_1319_);
v___y_1378_ = v___y_1323_;
v___y_1379_ = v___y_1325_;
goto v___jp_1377_;
}
else
{
lean_object* v___x_1428_; lean_object* v___y_1430_; 
v___x_1428_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14);
if (v_isExporting_1362_ == 0)
{
lean_object* v___x_1437_; 
v___x_1437_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19));
v___y_1430_ = v___x_1437_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1438_; 
v___x_1438_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20));
v___y_1430_ = v___x_1438_;
goto v___jp_1429_;
}
v___jp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_inc_ref(v___y_1430_);
v___x_1431_ = l_Lean_stringToMessageData(v___y_1430_);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1428_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
if (v_isMeta_1320_ == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17));
v___y_1413_ = v___x_1434_;
v___y_1414_ = v___x_1435_;
goto v___jp_1412_;
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18));
v___y_1413_ = v___x_1434_;
v___y_1414_ = v___x_1436_;
goto v___jp_1412_;
}
}
}
v___jp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___y_1408_);
lean_ctor_set(v___x_1410_, 1, v___y_1409_);
v___x_1411_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_cls_1406_, v___x_1410_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_dec_ref_known(v___x_1411_, 1);
v___y_1378_ = v___y_1323_;
v___y_1379_ = v___y_1325_;
goto v___jp_1377_;
}
else
{
lean_dec_ref(v___f_1375_);
return v___x_1411_;
}
}
v___jp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
lean_inc_ref(v___y_1414_);
v___x_1415_ = l_Lean_stringToMessageData(v___y_1414_);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___y_1413_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8);
v___x_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = l_Lean_MessageData_ofName(v_mod_1319_);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = l_Lean_Name_isAnonymous(v_hint_1321_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10);
v___x_1423_ = l_Lean_MessageData_ofName(v_hint_1321_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___y_1408_ = v___x_1420_;
v___y_1409_ = v___x_1424_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_hint_1321_);
v___x_1425_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11);
v___y_1408_ = v___x_1420_;
v___y_1409_ = v___x_1425_;
goto v___jp_1407_;
}
}
}
v___jp_1377_:
{
lean_object* v___x_1380_; lean_object* v_toEnvExtension_1381_; uint8_t v_logWrites_1382_; 
v___x_1380_ = lean_st_ref_take(v___y_1379_);
v_toEnvExtension_1381_ = lean_ctor_get(v___x_1366_, 0);
v_logWrites_1382_ = lean_ctor_get_uint8(v_toEnvExtension_1381_, sizeof(void*)*6);
if (v_logWrites_1382_ == 0)
{
lean_object* v_env_1383_; lean_object* v_nextMacroScope_1384_; lean_object* v_ngen_1385_; lean_object* v_auxDeclNGen_1386_; lean_object* v_traceState_1387_; lean_object* v_recordedDeps_1388_; lean_object* v_messages_1389_; lean_object* v_infoState_1390_; lean_object* v_snapshotTasks_1391_; lean_object* v_asyncMode_1392_; lean_object* v___x_1393_; 
v_env_1383_ = lean_ctor_get(v___x_1380_, 0);
lean_inc_ref(v_env_1383_);
v_nextMacroScope_1384_ = lean_ctor_get(v___x_1380_, 1);
lean_inc(v_nextMacroScope_1384_);
v_ngen_1385_ = lean_ctor_get(v___x_1380_, 2);
lean_inc_ref(v_ngen_1385_);
v_auxDeclNGen_1386_ = lean_ctor_get(v___x_1380_, 3);
lean_inc_ref(v_auxDeclNGen_1386_);
v_traceState_1387_ = lean_ctor_get(v___x_1380_, 4);
lean_inc_ref(v_traceState_1387_);
v_recordedDeps_1388_ = lean_ctor_get(v___x_1380_, 6);
lean_inc_ref(v_recordedDeps_1388_);
v_messages_1389_ = lean_ctor_get(v___x_1380_, 7);
lean_inc_ref(v_messages_1389_);
v_infoState_1390_ = lean_ctor_get(v___x_1380_, 8);
lean_inc_ref(v_infoState_1390_);
v_snapshotTasks_1391_ = lean_ctor_get(v___x_1380_, 9);
lean_inc_ref(v_snapshotTasks_1391_);
lean_dec(v___x_1380_);
v_asyncMode_1392_ = lean_ctor_get(v_toEnvExtension_1381_, 2);
lean_inc_ref(v_toEnvExtension_1381_);
v___x_1393_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1381_, v_env_1383_, v___f_1375_, v_asyncMode_1392_, v___x_1368_, v___x_1376_);
v___y_1328_ = v_auxDeclNGen_1386_;
v___y_1329_ = v_infoState_1390_;
v___y_1330_ = v_recordedDeps_1388_;
v___y_1331_ = v_ngen_1385_;
v___y_1332_ = v_traceState_1387_;
v___y_1333_ = v___y_1379_;
v___y_1334_ = v_nextMacroScope_1384_;
v___y_1335_ = v_snapshotTasks_1391_;
v___y_1336_ = v_messages_1389_;
v___y_1337_ = v___y_1378_;
v___y_1338_ = v___x_1393_;
goto v___jp_1327_;
}
else
{
lean_object* v_env_1394_; lean_object* v_nextMacroScope_1395_; lean_object* v_ngen_1396_; lean_object* v_auxDeclNGen_1397_; lean_object* v_traceState_1398_; lean_object* v_recordedDeps_1399_; lean_object* v_messages_1400_; lean_object* v_infoState_1401_; lean_object* v_snapshotTasks_1402_; lean_object* v_asyncMode_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_env_1394_ = lean_ctor_get(v___x_1380_, 0);
lean_inc_ref(v_env_1394_);
v_nextMacroScope_1395_ = lean_ctor_get(v___x_1380_, 1);
lean_inc(v_nextMacroScope_1395_);
v_ngen_1396_ = lean_ctor_get(v___x_1380_, 2);
lean_inc_ref(v_ngen_1396_);
v_auxDeclNGen_1397_ = lean_ctor_get(v___x_1380_, 3);
lean_inc_ref(v_auxDeclNGen_1397_);
v_traceState_1398_ = lean_ctor_get(v___x_1380_, 4);
lean_inc_ref(v_traceState_1398_);
v_recordedDeps_1399_ = lean_ctor_get(v___x_1380_, 6);
lean_inc_ref(v_recordedDeps_1399_);
v_messages_1400_ = lean_ctor_get(v___x_1380_, 7);
lean_inc_ref(v_messages_1400_);
v_infoState_1401_ = lean_ctor_get(v___x_1380_, 8);
lean_inc_ref(v_infoState_1401_);
v_snapshotTasks_1402_ = lean_ctor_get(v___x_1380_, 9);
lean_inc_ref(v_snapshotTasks_1402_);
lean_dec(v___x_1380_);
v_asyncMode_1403_ = lean_ctor_get(v_toEnvExtension_1381_, 2);
lean_inc_ref_n(v_toEnvExtension_1381_, 2);
v___x_1404_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1381_, v_env_1394_);
lean_dec_ref(v_env_1394_);
v___x_1405_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1381_, v___x_1404_, v___f_1375_, v_asyncMode_1403_, v___x_1368_, v___x_1376_);
v___y_1328_ = v_auxDeclNGen_1397_;
v___y_1329_ = v_infoState_1401_;
v___y_1330_ = v_recordedDeps_1399_;
v___y_1331_ = v_ngen_1396_;
v___y_1332_ = v_traceState_1398_;
v___y_1333_ = v___y_1379_;
v___y_1334_ = v_nextMacroScope_1395_;
v___y_1335_ = v_snapshotTasks_1402_;
v___y_1336_ = v_messages_1400_;
v___y_1337_ = v___y_1378_;
v___y_1338_ = v___x_1405_;
goto v___jp_1327_;
}
}
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec_ref_known(v_entry_1363_, 1);
lean_dec(v_hint_1321_);
lean_dec(v_mod_1319_);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
return v___x_1440_;
}
v___jp_1327_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v_mctx_1343_; lean_object* v_zetaDeltaFVarIds_1344_; lean_object* v_postponed_1345_; lean_object* v_diag_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1357_; 
v___x_1339_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2);
v___x_1340_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1340_, 0, v___y_1338_);
lean_ctor_set(v___x_1340_, 1, v___y_1334_);
lean_ctor_set(v___x_1340_, 2, v___y_1331_);
lean_ctor_set(v___x_1340_, 3, v___y_1328_);
lean_ctor_set(v___x_1340_, 4, v___y_1332_);
lean_ctor_set(v___x_1340_, 5, v___x_1339_);
lean_ctor_set(v___x_1340_, 6, v___y_1330_);
lean_ctor_set(v___x_1340_, 7, v___y_1336_);
lean_ctor_set(v___x_1340_, 8, v___y_1329_);
lean_ctor_set(v___x_1340_, 9, v___y_1335_);
v___x_1341_ = lean_st_ref_put(v___y_1333_, v___x_1340_);
v___x_1342_ = lean_st_ref_take(v___y_1337_);
v_mctx_1343_ = lean_ctor_get(v___x_1342_, 0);
v_zetaDeltaFVarIds_1344_ = lean_ctor_get(v___x_1342_, 2);
v_postponed_1345_ = lean_ctor_get(v___x_1342_, 3);
v_diag_1346_ = lean_ctor_get(v___x_1342_, 4);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; 
v_unused_1358_ = lean_ctor_get(v___x_1342_, 1);
lean_dec(v_unused_1358_);
v___x_1348_ = v___x_1342_;
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_diag_1346_);
lean_inc(v_postponed_1345_);
lean_inc(v_zetaDeltaFVarIds_1344_);
lean_inc(v_mctx_1343_);
lean_dec(v___x_1342_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v___x_1351_);
v___x_1353_ = v___x_1348_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_mctx_1343_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_zetaDeltaFVarIds_1344_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_postponed_1345_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_diag_1346_);
v___x_1353_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_st_ref_put(v___y_1337_, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1350_);
return v___x_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_mod_1441_, lean_object* v_isMeta_1442_, lean_object* v_hint_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v_isMeta_boxed_1449_; lean_object* v_res_1450_; 
v_isMeta_boxed_1449_ = lean_unbox(v_isMeta_1442_);
v_res_1450_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_mod_1441_, v_isMeta_boxed_1449_, v_hint_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(lean_object* v___x_1451_, lean_object* v_declName_1452_, lean_object* v_as_1453_, size_t v_sz_1454_, size_t v_i_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
uint8_t v___x_1466_; 
v___x_1466_ = lean_usize_dec_lt(v_i_1455_, v_sz_1454_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; 
lean_dec(v_declName_1452_);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_b_1456_);
return v___x_1467_;
}
else
{
lean_object* v___x_1468_; lean_object* v_modules_1469_; lean_object* v___x_1470_; lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v_toImport_1473_; lean_object* v_module_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; 
v___x_1468_ = l_Lean_Environment_header(v___x_1451_);
v_modules_1469_ = lean_ctor_get(v___x_1468_, 3);
lean_inc_ref(v_modules_1469_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1471_ = lean_array_uget_borrowed(v_as_1453_, v_i_1455_);
v___x_1472_ = lean_array_get(v___x_1470_, v_modules_1469_, v_a_1471_);
lean_dec_ref(v_modules_1469_);
v_toImport_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc_ref(v_toImport_1473_);
lean_dec(v___x_1472_);
v_module_1474_ = lean_ctor_get(v_toImport_1473_, 0);
lean_inc(v_module_1474_);
lean_dec_ref(v_toImport_1473_);
v___x_1475_ = lean_box(0);
v___x_1476_ = 0;
lean_inc(v_declName_1452_);
v___x_1477_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_module_1474_, v___x_1476_, v_declName_1452_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1477_) == 0)
{
size_t v___x_1478_; size_t v___x_1479_; 
lean_dec_ref_known(v___x_1477_, 1);
v___x_1478_ = ((size_t)1ULL);
v___x_1479_ = lean_usize_add(v_i_1455_, v___x_1478_);
v_i_1455_ = v___x_1479_;
v_b_1456_ = v___x_1475_;
goto _start;
}
else
{
lean_dec(v_declName_1452_);
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4___boxed(lean_object* v___x_1481_, lean_object* v_declName_1482_, lean_object* v_as_1483_, lean_object* v_sz_1484_, lean_object* v_i_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
size_t v_sz_boxed_1496_; size_t v_i_boxed_1497_; lean_object* v_res_1498_; 
v_sz_boxed_1496_ = lean_unbox_usize(v_sz_1484_);
lean_dec(v_sz_1484_);
v_i_boxed_1497_ = lean_unbox_usize(v_i_1485_);
lean_dec(v_i_1485_);
v_res_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(v___x_1481_, v_declName_1482_, v_as_1483_, v_sz_boxed_1496_, v_i_boxed_1497_, v_b_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec_ref(v_as_1483_);
lean_dec_ref(v___x_1481_);
return v_res_1498_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(lean_object* v_declName_1502_, uint8_t v_isMeta_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v_env_1518_; lean_object* v___y_1520_; lean_object* v___x_1533_; 
v___x_1513_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0);
v___x_1514_ = lean_st_ref_get(v___y_1511_);
v_env_1518_ = lean_ctor_get(v___x_1514_, 0);
lean_inc_ref(v_env_1518_);
lean_dec(v___x_1514_);
v___x_1533_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1518_, v_declName_1502_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_dec_ref(v_env_1518_);
lean_dec(v_declName_1502_);
goto v___jp_1515_;
}
else
{
lean_object* v_val_1534_; lean_object* v___x_1535_; lean_object* v_modules_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_val_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = l_Lean_Environment_header(v_env_1518_);
v_modules_1536_ = lean_ctor_get(v___x_1535_, 3);
lean_inc_ref(v_modules_1536_);
lean_dec_ref(v___x_1535_);
v___x_1537_ = lean_array_get_size(v_modules_1536_);
v___x_1538_ = lean_nat_dec_lt(v_val_1534_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_dec_ref(v_modules_1536_);
lean_dec(v_val_1534_);
lean_dec_ref(v_env_1518_);
lean_dec(v_declName_1502_);
goto v___jp_1515_;
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___y_1542_; 
v___x_1539_ = lean_array_fget(v_modules_1536_, v_val_1534_);
lean_dec(v_val_1534_);
lean_dec_ref(v_modules_1536_);
v___x_1540_ = lean_st_ref_get(v___y_1511_);
if (v_isMeta_1503_ == 0)
{
lean_dec(v___x_1540_);
v___y_1542_ = v_isMeta_1503_;
goto v___jp_1541_;
}
else
{
lean_object* v_env_1553_; uint8_t v___x_1554_; 
v_env_1553_ = lean_ctor_get(v___x_1540_, 0);
lean_inc_ref(v_env_1553_);
lean_dec(v___x_1540_);
lean_inc(v_declName_1502_);
v___x_1554_ = l_Lean_isMarkedMeta(v_env_1553_, v_declName_1502_);
if (v___x_1554_ == 0)
{
v___y_1542_ = v_isMeta_1503_;
goto v___jp_1541_;
}
else
{
uint8_t v___x_1555_; 
v___x_1555_ = 0;
v___y_1542_ = v___x_1555_;
goto v___jp_1541_;
}
}
v___jp_1541_:
{
lean_object* v_toImport_1543_; lean_object* v_module_1544_; lean_object* v___x_1545_; 
v_toImport_1543_ = lean_ctor_get(v___x_1539_, 0);
lean_inc_ref(v_toImport_1543_);
lean_dec(v___x_1539_);
v_module_1544_ = lean_ctor_get(v_toImport_1543_, 0);
lean_inc(v_module_1544_);
lean_dec_ref(v_toImport_1543_);
lean_inc(v_declName_1502_);
v___x_1545_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_module_1544_, v___y_1542_, v_declName_1502_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec_ref_known(v___x_1545_, 1);
v___x_1546_ = l_Lean_indirectModUseExt;
v___x_1547_ = lean_box(1);
v___x_1548_ = lean_box(0);
lean_inc_ref(v_env_1518_);
v___x_1549_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1513_, v___x_1546_, v_env_1518_, v___x_1547_, v___x_1548_);
v___x_1550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v___x_1549_, v_declName_1502_);
lean_dec(v___x_1549_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; 
v___x_1551_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1));
v___y_1520_ = v___x_1551_;
goto v___jp_1519_;
}
else
{
lean_object* v_val_1552_; 
v_val_1552_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1550_, 1);
v___y_1520_ = v_val_1552_;
goto v___jp_1519_;
}
}
else
{
lean_dec_ref(v_env_1518_);
lean_dec(v_declName_1502_);
return v___x_1545_;
}
}
}
}
v___jp_1515_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_box(0);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
return v___x_1517_;
}
v___jp_1519_:
{
lean_object* v___x_1521_; size_t v_sz_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1521_ = lean_box(0);
v_sz_1522_ = lean_array_size(v___y_1520_);
v___x_1523_ = ((size_t)0ULL);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(v_env_1518_, v_declName_1502_, v___y_1520_, v_sz_1522_, v___x_1523_, v___x_1521_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec_ref(v___y_1520_);
lean_dec_ref(v_env_1518_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v___x_1524_, 0);
lean_dec(v_unused_1532_);
v___x_1526_ = v___x_1524_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_dec(v___x_1524_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1521_);
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1521_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
return v___x_1524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___boxed(lean_object* v_declName_1556_, lean_object* v_isMeta_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
uint8_t v_isMeta_boxed_1567_; lean_object* v_res_1568_; 
v_isMeta_boxed_1567_ = lean_unbox(v_isMeta_1557_);
v_res_1568_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(v_declName_1556_, v_isMeta_boxed_1567_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(lean_object* v_as_x27_1569_, lean_object* v_b_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
if (lean_obj_tag(v_as_x27_1569_) == 0)
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_b_1570_);
return v___x_1580_;
}
else
{
lean_object* v_head_1581_; lean_object* v_tail_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; 
v_head_1581_ = lean_ctor_get(v_as_x27_1569_, 0);
v_tail_1582_ = lean_ctor_get(v_as_x27_1569_, 1);
v___x_1583_ = lean_box(0);
v___x_1584_ = 1;
lean_inc(v_head_1581_);
v___x_1585_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(v_head_1581_, v___x_1584_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_dec_ref_known(v___x_1585_, 1);
v_as_x27_1569_ = v_tail_1582_;
v_b_1570_ = v___x_1583_;
goto _start;
}
else
{
return v___x_1585_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg___boxed(lean_object* v_as_x27_1587_, lean_object* v_b_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_as_x27_1587_, v_b_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v_as_x27_1587_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(lean_object* v_env_1599_, lean_object* v___x_1600_, lean_object* v_currNamespace_1601_, lean_object* v_openDecls_1602_, lean_object* v_n_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = l_Lean_ResolveName_resolveGlobalName(v_env_1599_, v___x_1600_, v_currNamespace_1601_, v_openDecls_1602_, v_n_1603_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v___y_1605_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed(lean_object* v_env_1608_, lean_object* v___x_1609_, lean_object* v_currNamespace_1610_, lean_object* v_openDecls_1611_, lean_object* v_n_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(v_env_1608_, v___x_1609_, v_currNamespace_1610_, v_openDecls_1611_, v_n_1612_, v___y_1613_, v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec_ref(v___x_1609_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(lean_object* v_env_1616_, lean_object* v_currNamespace_1617_, lean_object* v_openDecls_1618_, lean_object* v_n_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = l_Lean_ResolveName_resolveNamespace(v_env_1616_, v_currNamespace_1617_, v_openDecls_1618_, v_n_1619_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v___y_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed(lean_object* v_env_1624_, lean_object* v_currNamespace_1625_, lean_object* v_openDecls_1626_, lean_object* v_n_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(v_env_1624_, v_currNamespace_1625_, v_openDecls_1626_, v_n_1627_, v___y_1628_, v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(lean_object* v_env_1631_, lean_object* v_declName_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
uint8_t v___x_1635_; lean_object* v_env_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1635_ = 0;
v_env_1636_ = l_Lean_Environment_setExporting(v_env_1631_, v___x_1635_);
lean_inc(v_declName_1632_);
v___x_1637_ = l_Lean_mkPrivateName(v_env_1636_, v_declName_1632_);
v___x_1638_ = 1;
lean_inc_ref(v_env_1636_);
v___x_1639_ = l_Lean_Environment_contains(v_env_1636_, v___x_1637_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1640_ = l_Lean_privateToUserName(v_declName_1632_);
v___x_1641_ = l_Lean_Environment_contains(v_env_1636_, v___x_1640_, v___x_1638_);
v___x_1642_ = lean_box(v___x_1641_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v___y_1634_);
return v___x_1643_;
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec_ref(v_env_1636_);
lean_dec(v_declName_1632_);
v___x_1644_ = lean_box(v___x_1639_);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v___y_1634_);
return v___x_1645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed(lean_object* v_env_1646_, lean_object* v_declName_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(v_env_1646_, v_declName_1647_, v___y_1648_, v___y_1649_);
lean_dec_ref(v___y_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(lean_object* v_as_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
if (lean_obj_tag(v_as_1651_) == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
else
{
lean_object* v_toCold_1659_; lean_object* v_options_1660_; uint8_t v_hasTrace_1661_; 
v_toCold_1659_ = lean_ctor_get(v___y_1654_, 0);
v_options_1660_ = lean_ctor_get(v_toCold_1659_, 2);
v_hasTrace_1661_ = lean_ctor_get_uint8(v_options_1660_, sizeof(void*)*1);
if (v_hasTrace_1661_ == 0)
{
lean_object* v_tail_1662_; 
v_tail_1662_ = lean_ctor_get(v_as_1651_, 1);
lean_inc(v_tail_1662_);
lean_dec_ref_known(v_as_1651_, 2);
v_as_1651_ = v_tail_1662_;
goto _start;
}
else
{
lean_object* v_head_1664_; lean_object* v_tail_1665_; lean_object* v_fst_1666_; lean_object* v_snd_1667_; lean_object* v_inheritedTraceOptions_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v_head_1664_ = lean_ctor_get(v_as_1651_, 0);
lean_inc(v_head_1664_);
v_tail_1665_ = lean_ctor_get(v_as_1651_, 1);
lean_inc(v_tail_1665_);
lean_dec_ref_known(v_as_1651_, 2);
v_fst_1666_ = lean_ctor_get(v_head_1664_, 0);
lean_inc_n(v_fst_1666_, 2);
v_snd_1667_ = lean_ctor_get(v_head_1664_, 1);
lean_inc(v_snd_1667_);
lean_dec(v_head_1664_);
v_inheritedTraceOptions_1668_ = lean_ctor_get(v_toCold_1659_, 11);
v___x_1669_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17));
v___x_1670_ = l_Lean_Name_append(v___x_1669_, v_fst_1666_);
v___x_1671_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1668_, v_options_1660_, v___x_1670_);
lean_dec(v___x_1670_);
if (v___x_1671_ == 0)
{
lean_dec(v_snd_1667_);
lean_dec(v_fst_1666_);
v_as_1651_ = v_tail_1665_;
goto _start;
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_snd_1667_);
v___x_1674_ = l_Lean_MessageData_ofFormat(v___x_1673_);
v___x_1675_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_fst_1666_, v___x_1674_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_dec_ref_known(v___x_1675_, 1);
v_as_1651_ = v_tail_1665_;
goto _start;
}
else
{
lean_dec(v_tail_1665_);
return v___x_1675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg___boxed(lean_object* v_as_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v_as_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(lean_object* v_x_1684_, lean_object* v___y_1685_){
_start:
{
if (lean_obj_tag(v_x_1684_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; 
v_a_1686_ = lean_ctor_get(v_x_1684_, 0);
lean_inc(v_a_1686_);
v___x_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_a_1686_);
lean_ctor_set(v___x_1687_, 1, v___y_1685_);
return v___x_1687_;
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1689_; 
v_a_1688_ = lean_ctor_get(v_x_1684_, 0);
lean_inc(v_a_1688_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_a_1688_);
lean_ctor_set(v___x_1689_, 1, v___y_1685_);
return v___x_1689_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg___boxed(lean_object* v_x_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v_x_1690_, v___y_1691_);
lean_dec_ref(v_x_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(lean_object* v_env_1693_, lean_object* v_stx_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1693_, v_stx_1694_, v___y_1695_, v___y_1696_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
if (lean_obj_tag(v_a_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1707_; 
v_a_1699_ = lean_ctor_get(v___x_1697_, 1);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; 
v_unused_1708_ = lean_ctor_get(v___x_1697_, 0);
lean_dec(v_unused_1708_);
v___x_1701_ = v___x_1697_;
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1703_ = lean_box(0);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1703_);
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_a_1699_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
else
{
lean_object* v_val_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1737_; 
v_val_1709_ = lean_ctor_get(v_a_1698_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_a_1698_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1711_ = v_a_1698_;
v_isShared_1712_ = v_isSharedCheck_1737_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_val_1709_);
lean_dec(v_a_1698_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1737_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_snd_1713_; 
v_snd_1713_ = lean_ctor_get(v_val_1709_, 1);
lean_inc(v_snd_1713_);
lean_dec(v_val_1709_);
if (lean_obj_tag(v_snd_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1723_; 
lean_del_object(v___x_1711_);
v_a_1714_ = lean_ctor_get(v___x_1697_, 1);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1697_, 2);
v_a_1715_ = lean_ctor_get(v_snd_1713_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_snd_1713_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1717_ = v_snd_1713_;
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v_snd_1713_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v___x_1720_, v_a_1714_);
lean_dec_ref(v___x_1720_);
return v___x_1721_;
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1736_; 
v_a_1724_ = lean_ctor_get(v___x_1697_, 1);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1697_, 2);
v_a_1725_ = lean_ctor_get(v_snd_1713_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_snd_1713_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1727_ = v_snd_1713_;
v_isShared_1728_ = v_isSharedCheck_1736_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v_snd_1713_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1736_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v_a_1725_);
v___x_1730_ = v___x_1711_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1732_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1730_);
v___x_1732_ = v___x_1727_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v___x_1732_, v_a_1724_);
lean_dec_ref(v___x_1732_);
return v___x_1733_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1738_ = lean_ctor_get(v___x_1697_, 0);
v_a_1739_ = lean_ctor_get(v___x_1697_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1697_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_inc(v_a_1738_);
lean_dec(v___x_1697_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1738_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed(lean_object* v_env_1747_, lean_object* v_stx_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(v_env_1747_, v_stx_1748_, v___y_1749_, v___y_1750_);
lean_dec_ref(v___y_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(lean_object* v_currNamespace_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v_currNamespace_1752_);
lean_ctor_set(v___x_1755_, 1, v___y_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(v_currNamespace_1756_, v___y_1757_, v___y_1758_);
lean_dec_ref(v___y_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(lean_object* v_x_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v_toCold_1772_; lean_object* v_env_1773_; lean_object* v_currRecDepth_1774_; lean_object* v_ref_1775_; lean_object* v_maxRecDepth_1776_; lean_object* v_currNamespace_1777_; lean_object* v_openDecls_1778_; lean_object* v_quotContext_1779_; lean_object* v_currMacroScope_1780_; lean_object* v___f_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; lean_object* v___f_1784_; lean_object* v___f_1785_; lean_object* v___f_1786_; lean_object* v_methods_1787_; lean_object* v___x_1788_; lean_object* v_nextMacroScope_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1771_ = lean_st_ref_get(v___y_1769_);
v_toCold_1772_ = lean_ctor_get(v___y_1768_, 0);
v_env_1773_ = lean_ctor_get(v___x_1771_, 0);
lean_inc_ref_n(v_env_1773_, 4);
lean_dec(v___x_1771_);
v_currRecDepth_1774_ = lean_ctor_get(v___y_1768_, 1);
v_ref_1775_ = lean_ctor_get(v___y_1768_, 2);
v_maxRecDepth_1776_ = lean_ctor_get(v_toCold_1772_, 3);
v_currNamespace_1777_ = lean_ctor_get(v_toCold_1772_, 4);
v_openDecls_1778_ = lean_ctor_get(v_toCold_1772_, 5);
v_quotContext_1779_ = lean_ctor_get(v_toCold_1772_, 8);
v_currMacroScope_1780_ = lean_ctor_get(v_toCold_1772_, 9);
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1781_, 0, v_env_1773_);
v___f_1782_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1782_, 0, v_env_1773_);
v___x_1783_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1768_);
lean_inc_n(v_currNamespace_1777_, 3);
v___f_1784_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1784_, 0, v_currNamespace_1777_);
lean_inc_n(v_openDecls_1778_, 2);
v___f_1785_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1785_, 0, v_env_1773_);
lean_closure_set(v___f_1785_, 1, v___x_1783_);
lean_closure_set(v___f_1785_, 2, v_currNamespace_1777_);
lean_closure_set(v___f_1785_, 3, v_openDecls_1778_);
v___f_1786_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1786_, 0, v_env_1773_);
lean_closure_set(v___f_1786_, 1, v_currNamespace_1777_);
lean_closure_set(v___f_1786_, 2, v_openDecls_1778_);
v_methods_1787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1787_, 0, v___f_1782_);
lean_ctor_set(v_methods_1787_, 1, v___f_1784_);
lean_ctor_set(v_methods_1787_, 2, v___f_1781_);
lean_ctor_set(v_methods_1787_, 3, v___f_1786_);
lean_ctor_set(v_methods_1787_, 4, v___f_1785_);
v___x_1788_ = lean_st_ref_get(v___y_1769_);
v_nextMacroScope_1789_ = lean_ctor_get(v___x_1788_, 1);
lean_inc(v_nextMacroScope_1789_);
lean_dec(v___x_1788_);
lean_inc(v_ref_1775_);
lean_inc(v_maxRecDepth_1776_);
lean_inc(v_currRecDepth_1774_);
lean_inc(v_currMacroScope_1780_);
lean_inc(v_quotContext_1779_);
v___x_1790_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1790_, 0, v_methods_1787_);
lean_ctor_set(v___x_1790_, 1, v_quotContext_1779_);
lean_ctor_set(v___x_1790_, 2, v_currMacroScope_1780_);
lean_ctor_set(v___x_1790_, 3, v_currRecDepth_1774_);
lean_ctor_set(v___x_1790_, 4, v_maxRecDepth_1776_);
lean_ctor_set(v___x_1790_, 5, v_ref_1775_);
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1792_, 0, v_nextMacroScope_1789_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
lean_ctor_set(v___x_1792_, 2, v___x_1791_);
v___x_1793_ = lean_apply_2(v_x_1761_, v___x_1790_, v___x_1792_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v_a_1795_; lean_object* v_macroScope_1796_; lean_object* v_traceMsgs_1797_; lean_object* v_expandedMacroDecls_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 1);
lean_inc(v_a_1794_);
v_a_1795_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1793_, 2);
v_macroScope_1796_ = lean_ctor_get(v_a_1794_, 0);
lean_inc(v_macroScope_1796_);
v_traceMsgs_1797_ = lean_ctor_get(v_a_1794_, 1);
lean_inc(v_traceMsgs_1797_);
v_expandedMacroDecls_1798_ = lean_ctor_get(v_a_1794_, 2);
lean_inc(v_expandedMacroDecls_1798_);
lean_dec(v_a_1794_);
v___x_1799_ = lean_box(0);
v___x_1800_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_expandedMacroDecls_1798_, v___x_1799_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v_expandedMacroDecls_1798_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v___x_1801_; lean_object* v_env_1802_; lean_object* v_ngen_1803_; lean_object* v_auxDeclNGen_1804_; lean_object* v_traceState_1805_; lean_object* v_cache_1806_; lean_object* v_recordedDeps_1807_; lean_object* v_messages_1808_; lean_object* v_infoState_1809_; lean_object* v_snapshotTasks_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref_known(v___x_1800_, 1);
v___x_1801_ = lean_st_ref_take(v___y_1769_);
v_env_1802_ = lean_ctor_get(v___x_1801_, 0);
v_ngen_1803_ = lean_ctor_get(v___x_1801_, 2);
v_auxDeclNGen_1804_ = lean_ctor_get(v___x_1801_, 3);
v_traceState_1805_ = lean_ctor_get(v___x_1801_, 4);
v_cache_1806_ = lean_ctor_get(v___x_1801_, 5);
v_recordedDeps_1807_ = lean_ctor_get(v___x_1801_, 6);
v_messages_1808_ = lean_ctor_get(v___x_1801_, 7);
v_infoState_1809_ = lean_ctor_get(v___x_1801_, 8);
v_snapshotTasks_1810_ = lean_ctor_get(v___x_1801_, 9);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; 
v_unused_1837_ = lean_ctor_get(v___x_1801_, 1);
lean_dec(v_unused_1837_);
v___x_1812_ = v___x_1801_;
v_isShared_1813_ = v_isSharedCheck_1836_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_snapshotTasks_1810_);
lean_inc(v_infoState_1809_);
lean_inc(v_messages_1808_);
lean_inc(v_recordedDeps_1807_);
lean_inc(v_cache_1806_);
lean_inc(v_traceState_1805_);
lean_inc(v_auxDeclNGen_1804_);
lean_inc(v_ngen_1803_);
lean_inc(v_env_1802_);
lean_dec(v___x_1801_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1836_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 1, v_macroScope_1796_);
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_env_1802_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_macroScope_1796_);
lean_ctor_set(v_reuseFailAlloc_1835_, 2, v_ngen_1803_);
lean_ctor_set(v_reuseFailAlloc_1835_, 3, v_auxDeclNGen_1804_);
lean_ctor_set(v_reuseFailAlloc_1835_, 4, v_traceState_1805_);
lean_ctor_set(v_reuseFailAlloc_1835_, 5, v_cache_1806_);
lean_ctor_set(v_reuseFailAlloc_1835_, 6, v_recordedDeps_1807_);
lean_ctor_set(v_reuseFailAlloc_1835_, 7, v_messages_1808_);
lean_ctor_set(v_reuseFailAlloc_1835_, 8, v_infoState_1809_);
lean_ctor_set(v_reuseFailAlloc_1835_, 9, v_snapshotTasks_1810_);
v___x_1815_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = lean_st_ref_put(v___y_1769_, v___x_1815_);
v___x_1817_ = l_List_reverse___redArg(v_traceMsgs_1797_);
v___x_1818_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v___x_1817_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v___x_1818_, 0);
lean_dec(v_unused_1826_);
v___x_1820_ = v___x_1818_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v___x_1818_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v_a_1795_);
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1795_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec(v_a_1795_);
v_a_1827_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1818_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1818_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_traceMsgs_1797_);
lean_dec(v_macroScope_1796_);
lean_dec(v_a_1795_);
v_a_1838_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1800_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1800_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v_a_1846_; 
v_a_1846_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1793_, 2);
if (lean_obj_tag(v_a_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v_a_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v_a_1847_ = lean_ctor_get(v_a_1846_, 0);
lean_inc(v_a_1847_);
v_a_1848_ = lean_ctor_get(v_a_1846_, 1);
lean_inc_ref(v_a_1848_);
lean_dec_ref_known(v_a_1846_, 2);
v___x_1849_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0));
v___x_1850_ = lean_string_dec_eq(v_a_1848_, v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_a_1848_);
v___x_1852_ = l_Lean_MessageData_ofFormat(v___x_1851_);
v___x_1853_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_a_1847_, v___x_1852_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v_a_1847_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; 
lean_dec_ref(v_a_1848_);
v___x_1854_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_a_1847_);
return v___x_1854_;
}
}
else
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_1855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___boxed(lean_object* v_x_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(v_x_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(lean_object* v_x_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1887_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3));
lean_inc(v_x_1877_);
v___x_1888_ = l_Lean_Syntax_isOfKind(v_x_1877_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; 
lean_dec(v_x_1877_);
v___x_1889_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; lean_object* v_pat_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1890_ = lean_unsigned_to_nat(1u);
v_pat_1891_ = l_Lean_Syntax_getArg(v_x_1877_, v___x_1890_);
lean_dec(v_x_1877_);
v___x_1892_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_MRefinePat_parse___boxed), 3, 1);
lean_closure_set(v___x_1892_, 0, v_pat_1891_);
v___x_1893_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(v___x_1892_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1895_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v___x_1895_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1879_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v_fst_1897_; lean_object* v_snd_1898_; lean_object* v___x_1899_; lean_object* v___f_1900_; lean_object* v___x_1901_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v_fst_1897_ = lean_ctor_get(v_a_1896_, 0);
lean_inc_n(v_fst_1897_, 2);
v_snd_1898_ = lean_ctor_get(v_a_1896_, 1);
lean_inc(v_snd_1898_);
lean_dec(v_a_1896_);
v___x_1899_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4));
v___f_1900_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1___boxed), 13, 4);
lean_closure_set(v___f_1900_, 0, v___x_1899_);
lean_closure_set(v___f_1900_, 1, v_snd_1898_);
lean_closure_set(v___f_1900_, 2, v_a_1894_);
lean_closure_set(v___f_1900_, 3, v_fst_1897_);
v___x_1901_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_fst_1897_, v___f_1900_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
return v___x_1901_;
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1894_);
v_a_1902_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1895_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1895_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_a_1910_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1893_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1893_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___boxed(lean_object* v_x_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(v_x_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0(lean_object* v_00_u03b1_1929_, lean_object* v_x_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v_x_1930_, v___y_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1934_, lean_object* v_x_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0(v_00_u03b1_1934_, v_x_1935_, v___y_1936_, v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec_ref(v_x_1935_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5(lean_object* v_00_u03b1_1939_, lean_object* v_ref_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_ref_1940_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1951_, lean_object* v_ref_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5(v_00_u03b1_1951_, v_ref_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0(lean_object* v_00_u03b1_1963_, lean_object* v_x_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(v_x_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_x_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0(v_00_u03b1_1975_, v_x_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1(lean_object* v_mvarId_1987_, lean_object* v_val_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(v_mvarId_1987_, v_val_1988_, v___y_1994_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___boxed(lean_object* v_mvarId_1999_, lean_object* v_val_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1(v_mvarId_1999_, v_val_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2(lean_object* v_as_2011_, lean_object* v_as_x27_2012_, lean_object* v_b_2013_, lean_object* v_a_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_as_x27_2012_, v_b_2013_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___boxed(lean_object* v_as_2025_, lean_object* v_as_x27_2026_, lean_object* v_b_2027_, lean_object* v_a_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2(v_as_2025_, v_as_x27_2026_, v_b_2027_, v_a_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v_as_x27_2026_);
lean_dec(v_as_2025_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3(lean_object* v_as_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v_as_2039_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___boxed(lean_object* v_as_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3(v_as_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4(lean_object* v_00_u03b1_2061_, lean_object* v_ref_2062_, lean_object* v_msg_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_ref_2062_, v_msg_2063_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2074_, lean_object* v_ref_2075_, lean_object* v_msg_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4(v_00_u03b1_2074_, v_ref_2075_, v_msg_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v_ref_2075_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7(lean_object* v_00_u03b2_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_, lean_object* v_x_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(v_x_2088_, v_x_2089_, v_x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3(lean_object* v_mod_2092_, uint8_t v_isMeta_2093_, lean_object* v_hint_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_mod_2092_, v_isMeta_2093_, v_hint_2094_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___boxed(lean_object* v_mod_2105_, lean_object* v_isMeta_2106_, lean_object* v_hint_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
uint8_t v_isMeta_boxed_2117_; lean_object* v_res_2118_; 
v_isMeta_boxed_2117_ = lean_unbox(v_isMeta_2106_);
v_res_2118_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3(v_mod_2105_, v_isMeta_boxed_2117_, v_hint_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_2119_, lean_object* v_m_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v_m_2120_, v_a_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_2123_, lean_object* v_m_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5(v_00_u03b2_2123_, v_m_2124_, v_a_2125_);
lean_dec(v_a_2125_);
lean_dec_ref(v_m_2124_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2127_, lean_object* v_x_2128_, size_t v_x_2129_, size_t v_x_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_2128_, v_x_2129_, v_x_2130_, v_x_2131_, v_x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___boxed(lean_object* v_00_u03b2_2134_, lean_object* v_x_2135_, lean_object* v_x_2136_, lean_object* v_x_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_){
_start:
{
size_t v_x_19023__boxed_2140_; size_t v_x_19024__boxed_2141_; lean_object* v_res_2142_; 
v_x_19023__boxed_2140_ = lean_unbox_usize(v_x_2136_);
lean_dec(v_x_2136_);
v_x_19024__boxed_2141_ = lean_unbox_usize(v_x_2137_);
lean_dec(v_x_2137_);
v_res_2142_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12(v_00_u03b2_2134_, v_x_2135_, v_x_19023__boxed_2140_, v_x_19024__boxed_2141_, v_x_2138_, v_x_2139_);
return v_res_2142_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2143_, lean_object* v_x_2144_, lean_object* v_x_2145_){
_start:
{
uint8_t v___x_2146_; 
v___x_2146_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v_x_2144_, v_x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_){
_start:
{
uint8_t v_res_2150_; lean_object* v_r_2151_; 
v_res_2150_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6(v_00_u03b2_2147_, v_x_2148_, v_x_2149_);
lean_dec_ref(v_x_2149_);
lean_dec_ref(v_x_2148_);
v_r_2151_ = lean_box(v_res_2150_);
return v_r_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03b2_2152_, lean_object* v_a_2153_, lean_object* v_x_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_2153_, v_x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2156_, lean_object* v_a_2157_, lean_object* v_x_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9(v_00_u03b2_2156_, v_a_2157_, v_x_2158_);
lean_dec(v_x_2158_);
lean_dec(v_a_2157_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15(lean_object* v_00_u03b2_2160_, lean_object* v_n_2161_, lean_object* v_k_2162_, lean_object* v_v_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(v_n_2161_, v_k_2162_, v_v_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16(lean_object* v_00_u03b2_2165_, size_t v_depth_2166_, lean_object* v_keys_2167_, lean_object* v_vals_2168_, lean_object* v_heq_2169_, lean_object* v_i_2170_, lean_object* v_entries_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_depth_2166_, v_keys_2167_, v_vals_2168_, v_i_2170_, v_entries_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___boxed(lean_object* v_00_u03b2_2173_, lean_object* v_depth_2174_, lean_object* v_keys_2175_, lean_object* v_vals_2176_, lean_object* v_heq_2177_, lean_object* v_i_2178_, lean_object* v_entries_2179_){
_start:
{
size_t v_depth_boxed_2180_; lean_object* v_res_2181_; 
v_depth_boxed_2180_ = lean_unbox_usize(v_depth_2174_);
lean_dec(v_depth_2174_);
v_res_2181_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16(v_00_u03b2_2173_, v_depth_boxed_2180_, v_keys_2175_, v_vals_2176_, v_heq_2177_, v_i_2178_, v_entries_2179_);
lean_dec_ref(v_vals_2176_);
lean_dec_ref(v_keys_2175_);
return v_res_2181_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(lean_object* v_00_u03b2_2182_, lean_object* v_x_2183_, size_t v_x_2184_, lean_object* v_x_2185_){
_start:
{
uint8_t v___x_2186_; 
v___x_2186_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_2183_, v_x_2184_, v_x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___boxed(lean_object* v_00_u03b2_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_, lean_object* v_x_2190_){
_start:
{
size_t v_x_19057__boxed_2191_; uint8_t v_res_2192_; lean_object* v_r_2193_; 
v_x_19057__boxed_2191_ = lean_unbox_usize(v_x_2189_);
lean_dec(v_x_2189_);
v_res_2192_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(v_00_u03b2_2187_, v_x_2188_, v_x_19057__boxed_2191_, v_x_2190_);
lean_dec_ref(v_x_2190_);
lean_dec_ref(v_x_2188_);
v_r_2193_ = lean_box(v_res_2192_);
return v_r_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17(lean_object* v_00_u03b2_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(v_x_2195_, v_x_2196_, v_x_2197_, v_x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15(lean_object* v_00_u03b2_2200_, lean_object* v_keys_2201_, lean_object* v_vals_2202_, lean_object* v_heq_2203_, lean_object* v_i_2204_, lean_object* v_k_2205_){
_start:
{
uint8_t v___x_2206_; 
v___x_2206_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_keys_2201_, v_i_2204_, v_k_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2207_, lean_object* v_keys_2208_, lean_object* v_vals_2209_, lean_object* v_heq_2210_, lean_object* v_i_2211_, lean_object* v_k_2212_){
_start:
{
uint8_t v_res_2213_; lean_object* v_r_2214_; 
v_res_2213_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15(v_00_u03b2_2207_, v_keys_2208_, v_vals_2209_, v_heq_2210_, v_i_2211_, v_k_2212_);
lean_dec_ref(v_k_2212_);
lean_dec_ref(v_vals_2209_);
lean_dec_ref(v_keys_2208_);
v_r_2214_ = lean_box(v_res_2213_);
return v_r_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1(){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2226_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2227_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3));
v___x_2228_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3));
v___x_2229_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___boxed), 10, 0);
v___x_2230_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2226_, v___x_2227_, v___x_2228_, v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___boxed(lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1();
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(lean_object* v_as_2251_, size_t v_i_2252_, size_t v_stop_2253_, lean_object* v_b_2254_, lean_object* v___y_2255_){
_start:
{
uint8_t v___x_2257_; 
v___x_2257_ = lean_usize_dec_eq(v_i_2252_, v_stop_2253_);
if (v___x_2257_ == 0)
{
lean_object* v_ref_2258_; lean_object* v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v_ref_2258_ = lean_ctor_get(v___y_2255_, 2);
v___x_2259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0));
v___x_2260_ = ((size_t)1ULL);
v___x_2261_ = lean_usize_sub(v_i_2252_, v___x_2260_);
v___x_2262_ = lean_array_uget_borrowed(v_as_2251_, v___x_2261_);
v___x_2263_ = l_Lean_SourceInfo_fromRef(v_ref_2258_, v___x_2257_);
v___x_2264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2));
v___x_2265_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3));
lean_inc_n(v___x_2263_, 5);
v___x_2266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2263_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5));
v___x_2268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7));
v___x_2269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2263_);
lean_ctor_set(v___x_2269_, 1, v___x_2259_);
lean_inc(v___x_2262_);
v___x_2270_ = l_Lean_Syntax_node3(v___x_2263_, v___x_2268_, v___x_2262_, v___x_2269_, v_b_2254_);
v___x_2271_ = l_Lean_Syntax_node1(v___x_2263_, v___x_2267_, v___x_2270_);
v___x_2272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8));
v___x_2273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2263_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = l_Lean_Syntax_node3(v___x_2263_, v___x_2264_, v___x_2266_, v___x_2271_, v___x_2273_);
v_i_2252_ = v___x_2261_;
v_b_2254_ = v___x_2274_;
goto _start;
}
else
{
lean_object* v___x_2276_; 
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v_b_2254_);
return v___x_2276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___boxed(lean_object* v_as_2277_, lean_object* v_i_2278_, lean_object* v_stop_2279_, lean_object* v_b_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
size_t v_i_boxed_2283_; size_t v_stop_boxed_2284_; lean_object* v_res_2285_; 
v_i_boxed_2283_ = lean_unbox_usize(v_i_2278_);
lean_dec(v_i_2278_);
v_stop_boxed_2284_ = lean_unbox_usize(v_stop_2279_);
lean_dec(v_stop_2279_);
v_res_2285_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_2277_, v_i_boxed_2283_, v_stop_boxed_2284_, v_b_2280_, v___y_2281_);
lean_dec_ref(v___y_2281_);
lean_dec_ref(v_as_2277_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(lean_object* v_as_2286_, size_t v_i_2287_, size_t v_stop_2288_, lean_object* v_b_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
uint8_t v___x_2299_; 
v___x_2299_ = lean_usize_dec_eq(v_i_2287_, v_stop_2288_);
if (v___x_2299_ == 0)
{
lean_object* v_ref_2300_; lean_object* v___x_2301_; size_t v___x_2302_; size_t v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_ref_2300_ = lean_ctor_get(v___y_2296_, 2);
v___x_2301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0));
v___x_2302_ = ((size_t)1ULL);
v___x_2303_ = lean_usize_sub(v_i_2287_, v___x_2302_);
v___x_2304_ = lean_array_uget_borrowed(v_as_2286_, v___x_2303_);
v___x_2305_ = l_Lean_SourceInfo_fromRef(v_ref_2300_, v___x_2299_);
v___x_2306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2));
v___x_2307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3));
lean_inc_n(v___x_2305_, 5);
v___x_2308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2305_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5));
v___x_2310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7));
v___x_2311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2305_);
lean_ctor_set(v___x_2311_, 1, v___x_2301_);
lean_inc(v___x_2304_);
v___x_2312_ = l_Lean_Syntax_node3(v___x_2305_, v___x_2310_, v___x_2304_, v___x_2311_, v_b_2289_);
v___x_2313_ = l_Lean_Syntax_node1(v___x_2305_, v___x_2309_, v___x_2312_);
v___x_2314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8));
v___x_2315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2305_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = l_Lean_Syntax_node3(v___x_2305_, v___x_2306_, v___x_2308_, v___x_2313_, v___x_2315_);
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_2286_, v___x_2303_, v_stop_2288_, v___x_2316_, v___y_2296_);
return v___x_2317_;
}
else
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_b_2289_);
return v___x_2318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___boxed(lean_object* v_as_2319_, lean_object* v_i_2320_, lean_object* v_stop_2321_, lean_object* v_b_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
size_t v_i_boxed_2332_; size_t v_stop_boxed_2333_; lean_object* v_res_2334_; 
v_i_boxed_2332_ = lean_unbox_usize(v_i_2320_);
lean_dec(v_i_2320_);
v_stop_boxed_2333_ = lean_unbox_usize(v_stop_2321_);
lean_dec(v_stop_2321_);
v_res_2334_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(v_as_2319_, v_i_boxed_2332_, v_stop_boxed_2333_, v_b_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec_ref(v_as_2319_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(size_t v_sz_2343_, size_t v_i_2344_, lean_object* v_bs_2345_, lean_object* v___y_2346_){
_start:
{
uint8_t v___x_2348_; 
v___x_2348_ = lean_usize_dec_lt(v_i_2344_, v_sz_2343_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v_bs_2345_);
return v___x_2349_;
}
else
{
lean_object* v_ref_2350_; lean_object* v_v_2351_; lean_object* v___x_2352_; lean_object* v_bs_x27_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; size_t v___x_2362_; size_t v___x_2363_; lean_object* v___x_2364_; 
v_ref_2350_ = lean_ctor_get(v___y_2346_, 2);
v_v_2351_ = lean_array_uget(v_bs_2345_, v_i_2344_);
v___x_2352_ = lean_unsigned_to_nat(0u);
v_bs_x27_2353_ = lean_array_uset(v_bs_2345_, v_i_2344_, v___x_2352_);
v___x_2354_ = 0;
v___x_2355_ = l_Lean_SourceInfo_fromRef(v_ref_2350_, v___x_2354_);
v___x_2356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1));
v___x_2357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2));
lean_inc_n(v___x_2355_, 2);
v___x_2358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2355_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3));
v___x_2360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2355_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = l_Lean_Syntax_node3(v___x_2355_, v___x_2356_, v___x_2358_, v_v_2351_, v___x_2360_);
v___x_2362_ = ((size_t)1ULL);
v___x_2363_ = lean_usize_add(v_i_2344_, v___x_2362_);
v___x_2364_ = lean_array_uset(v_bs_x27_2353_, v_i_2344_, v___x_2361_);
v_i_2344_ = v___x_2363_;
v_bs_2345_ = v___x_2364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___boxed(lean_object* v_sz_2366_, lean_object* v_i_2367_, lean_object* v_bs_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
size_t v_sz_boxed_2371_; size_t v_i_boxed_2372_; lean_object* v_res_2373_; 
v_sz_boxed_2371_ = lean_unbox_usize(v_sz_2366_);
lean_dec(v_sz_2366_);
v_i_boxed_2372_ = lean_unbox_usize(v_i_2367_);
lean_dec(v_i_2367_);
v_res_2373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_boxed_2371_, v_i_boxed_2372_, v_bs_2368_, v___y_2369_);
lean_dec_ref(v___y_2369_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(lean_object* v_x_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1));
lean_inc(v_x_2429_);
v___x_2440_ = l_Lean_Syntax_isOfKind(v_x_2429_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; 
lean_dec(v_x_2429_);
v___x_2441_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_2441_;
}
else
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_args_2445_; lean_object* v___x_2446_; size_t v_sz_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2442_ = lean_unsigned_to_nat(0u);
v___x_2443_ = lean_unsigned_to_nat(1u);
v___x_2444_ = l_Lean_Syntax_getArg(v_x_2429_, v___x_2443_);
lean_dec(v_x_2429_);
v_args_2445_ = l_Lean_Syntax_getArgs(v___x_2444_);
lean_dec(v___x_2444_);
v___x_2446_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_args_2445_);
lean_dec_ref(v_args_2445_);
v_sz_2447_ = lean_array_size(v___x_2446_);
v___x_2448_ = ((size_t)0ULL);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_2447_, v___x_2448_, v___x_2446_, v_a_2436_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v_ref_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; lean_object* v_a_2455_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v_ref_2451_ = lean_ctor_get(v_a_2436_, 2);
v___x_2452_ = 0;
v___x_2453_ = l_Lean_SourceInfo_fromRef(v_ref_2451_, v___x_2452_);
v___x_2486_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17));
v___x_2487_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18));
lean_inc_n(v___x_2453_, 5);
v___x_2488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2453_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2));
v___x_2490_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21));
v___x_2491_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22));
v___x_2492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2453_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = l_Lean_Syntax_node1(v___x_2453_, v___x_2490_, v___x_2492_);
v___x_2494_ = l_Lean_Syntax_node1(v___x_2453_, v___x_2489_, v___x_2493_);
v___x_2495_ = l_Lean_Syntax_node2(v___x_2453_, v___x_2486_, v___x_2488_, v___x_2494_);
v___x_2496_ = lean_array_get_size(v_a_2450_);
v___x_2497_ = lean_nat_dec_lt(v___x_2442_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_dec(v_a_2450_);
v_a_2455_ = v___x_2495_;
goto v___jp_2454_;
}
else
{
size_t v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = lean_usize_of_nat(v___x_2496_);
v___x_2499_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(v_a_2450_, v___x_2498_, v___x_2448_, v___x_2495_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2450_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v_a_2455_ = v_a_2500_;
goto v___jp_2454_;
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v___x_2453_);
v_a_2501_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2499_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2499_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
v___jp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2456_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3));
v___x_2457_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4));
lean_inc_n(v___x_2453_, 15);
v___x_2458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2453_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6));
v___x_2460_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8));
v___x_2461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7));
v___x_2462_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2));
v___x_2463_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3));
v___x_2464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2453_);
lean_ctor_set(v___x_2464_, 1, v___x_2462_);
v___x_2465_ = l_Lean_Syntax_node2(v___x_2453_, v___x_2463_, v___x_2464_, v_a_2455_);
v___x_2466_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9));
v___x_2467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2453_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11));
v___x_2469_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12));
v___x_2470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2453_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13));
v___x_2472_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14));
v___x_2473_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2453_);
lean_ctor_set(v___x_2473_, 1, v___x_2471_);
v___x_2474_ = l_Lean_Syntax_node1(v___x_2453_, v___x_2472_, v___x_2473_);
v___x_2475_ = l_Lean_Syntax_node1(v___x_2453_, v___x_2461_, v___x_2474_);
v___x_2476_ = l_Lean_Syntax_node1(v___x_2453_, v___x_2460_, v___x_2475_);
v___x_2477_ = l_Lean_Syntax_node1(v___x_2453_, v___x_2459_, v___x_2476_);
v___x_2478_ = l_Lean_Syntax_node2(v___x_2453_, v___x_2468_, v___x_2470_, v___x_2477_);
v___x_2479_ = l_Lean_Syntax_node3(v___x_2453_, v___x_2461_, v___x_2465_, v___x_2467_, v___x_2478_);
v___x_2480_ = l_Lean_Syntax_node1(v___x_2453_, v___x_2460_, v___x_2479_);
v___x_2481_ = l_Lean_Syntax_node1(v___x_2453_, v___x_2459_, v___x_2480_);
v___x_2482_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15));
v___x_2483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2453_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = l_Lean_Syntax_node3(v___x_2453_, v___x_2456_, v___x_2458_, v___x_2481_, v___x_2483_);
v___x_2485_ = l_Lean_Elab_Tactic_evalTactic(v___x_2484_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
return v___x_2485_;
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_a_2509_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2449_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2449_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___boxed(lean_object* v_x_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(v_x_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(size_t v_sz_2528_, size_t v_i_2529_, lean_object* v_bs_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_2528_, v_i_2529_, v_bs_2530_, v___y_2537_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___boxed(lean_object* v_sz_2541_, lean_object* v_i_2542_, lean_object* v_bs_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
size_t v_sz_boxed_2553_; size_t v_i_boxed_2554_; lean_object* v_res_2555_; 
v_sz_boxed_2553_ = lean_unbox_usize(v_sz_2541_);
lean_dec(v_sz_2541_);
v_i_boxed_2554_ = lean_unbox_usize(v_i_2542_);
lean_dec(v_i_2542_);
v_res_2555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(v_sz_boxed_2553_, v_i_boxed_2554_, v_bs_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1(lean_object* v_as_2556_, size_t v_i_2557_, size_t v_stop_2558_, lean_object* v_b_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_2556_, v_i_2557_, v_stop_2558_, v_b_2559_, v___y_2566_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___boxed(lean_object* v_as_2570_, lean_object* v_i_2571_, lean_object* v_stop_2572_, lean_object* v_b_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
size_t v_i_boxed_2583_; size_t v_stop_boxed_2584_; lean_object* v_res_2585_; 
v_i_boxed_2583_ = lean_unbox_usize(v_i_2571_);
lean_dec(v_i_2571_);
v_stop_boxed_2584_ = lean_unbox_usize(v_stop_2572_);
lean_dec(v_stop_2572_);
v_res_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1(v_as_2570_, v_i_boxed_2583_, v_stop_boxed_2584_, v_b_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v_as_2570_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1(){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2595_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2596_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1));
v___x_2597_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1));
v___x_2598_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___boxed), 10, 0);
v___x_2599_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2595_, v___x_2596_, v___x_2597_, v___x_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___boxed(lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1();
return v_res_2601_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
}
#ifdef __cplusplus
}
#endif
