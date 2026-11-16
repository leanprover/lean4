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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
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
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Neither a conjunction nor an existential quantifier "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "exists"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "exists_intro'"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 53, .m_data = "pattern does not elaborate to a term to instantiate ψ"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(216, 97, 27, 109, 96, 85, 230, 202)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "and_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value),LEAN_SCALAR_PTR_LITERAL(248, 10, 80, 59, 91, 116, 13, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value),LEAN_SCALAR_PTR_LITERAL(96, 234, 54, 186, 23, 232, 175, 83)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "f: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", args: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "could not solve "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " by assumption"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unknown hypothesis `"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__31;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22_value;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
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
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2(void){
_start:
{
lean_object* v___x_297_; lean_object* v_dummy_298_; 
v___x_297_ = lean_box(0);
v_dummy_298_ = l_Lean_Expr_sort___override(v___x_297_);
return v_dummy_298_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5));
v___x_303_ = l_Lean_stringToMessageData(v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16));
v___x_328_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18));
v___x_329_ = l_Lean_Name_append(v___x_328_, v___x_327_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20));
v___x_332_ = l_Lean_stringToMessageData(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22));
v___x_335_ = l_Lean_stringToMessageData(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24));
v___x_338_ = l_Lean_stringToMessageData(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26));
v___x_341_ = l_Lean_stringToMessageData(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__31(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30));
v___x_347_ = l_Lean_stringToMessageData(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___boxed(lean_object* v_goal_348_, lean_object* v_pat_349_, lean_object* v_k_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v_goal_348_, v_pat_349_, v_k_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
lean_dec_ref(v_a_351_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(lean_object* v_goal_361_, lean_object* v_pat_362_, lean_object* v_k_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
switch(lean_obj_tag(v_pat_362_))
{
case 0:
{
lean_object* v_name_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_427_; 
v_name_373_ = lean_ctor_get(v_pat_362_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_pat_362_);
if (v_isSharedCheck_427_ == 0)
{
v___x_375_ = v_pat_362_;
v_isShared_376_ = v_isSharedCheck_427_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_name_373_);
lean_dec(v_pat_362_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_427_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2));
lean_inc(v_name_373_);
v___x_378_ = l_Lean_Syntax_isOfKind(v_name_373_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_380_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 3);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_name_373_);
v___x_380_ = v_reuseFailAlloc_382_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
v_pat_362_ = v___x_380_;
goto _start;
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = l_Lean_Syntax_getArg(v_name_373_, v___x_383_);
v___x_385_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4));
v___x_386_ = l_Lean_Syntax_isOfKind(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_388_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 3);
v___x_388_ = v___x_375_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_name_373_);
v___x_388_ = v_reuseFailAlloc_390_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
v_pat_362_ = v___x_388_;
goto _start;
}
}
else
{
lean_object* v___x_392_; 
lean_inc(v_name_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 2);
v___x_392_ = v___x_375_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_name_373_);
v___x_392_ = v_reuseFailAlloc_426_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_inc_ref(v_k_363_);
lean_inc_ref(v_goal_361_);
v___x_393_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___boxed), 12, 3);
lean_closure_set(v___x_393_, 0, v_goal_361_);
lean_closure_set(v___x_393_, 1, v___x_392_);
lean_closure_set(v___x_393_, 2, v_k_363_);
v___x_394_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_365_, v_a_367_, v_a_369_, v_a_371_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_396_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_396_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_393_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_dec(v_a_395_);
lean_dec(v_name_373_);
lean_dec_ref(v_k_363_);
lean_dec_ref(v_goal_361_);
return v___x_396_;
}
else
{
lean_object* v_a_397_; uint8_t v___x_398_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v___x_398_ = l_Lean_Exception_isInterrupt(v_a_397_);
if (v___x_398_ == 0)
{
uint8_t v___x_399_; 
lean_inc(v_a_397_);
v___x_399_ = l_Lean_Exception_isRuntime(v_a_397_);
if (v___x_399_ == 0)
{
lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_416_; 
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; 
v_unused_417_ = lean_ctor_get(v___x_396_, 0);
lean_dec(v_unused_417_);
v___x_401_ = v___x_396_;
v_isShared_402_ = v_isSharedCheck_416_;
goto v_resetjp_400_;
}
else
{
lean_dec(v___x_396_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_416_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_395_, v___x_399_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_405_; 
lean_dec_ref_known(v___x_403_, 1);
if (v_isShared_402_ == 0)
{
lean_ctor_set_tag(v___x_401_, 3);
lean_ctor_set(v___x_401_, 0, v_name_373_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_name_373_);
v___x_405_ = v_reuseFailAlloc_407_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
v_pat_362_ = v___x_405_;
goto _start;
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_del_object(v___x_401_);
lean_dec(v_name_373_);
lean_dec_ref(v_k_363_);
lean_dec_ref(v_goal_361_);
v_a_408_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_403_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_403_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
else
{
lean_dec(v_a_395_);
lean_dec(v_name_373_);
lean_dec_ref(v_k_363_);
lean_dec_ref(v_goal_361_);
return v___x_396_;
}
}
else
{
lean_dec(v_a_395_);
lean_dec(v_name_373_);
lean_dec_ref(v_k_363_);
lean_dec_ref(v_goal_361_);
return v___x_396_;
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v___x_393_);
lean_dec(v_name_373_);
lean_dec_ref(v_k_363_);
lean_dec_ref(v_goal_361_);
v_a_418_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_394_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_394_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
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
lean_object* v_args_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_632_; 
v_args_428_ = lean_ctor_get(v_pat_362_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_pat_362_);
if (v_isSharedCheck_632_ == 0)
{
v___x_430_ = v_pat_362_;
v_isShared_431_ = v_isSharedCheck_632_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_args_428_);
lean_dec(v_pat_362_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_632_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
if (lean_obj_tag(v_args_428_) == 0)
{
lean_object* v___x_432_; 
lean_del_object(v___x_430_);
lean_dec_ref(v_k_363_);
lean_dec_ref(v_goal_361_);
v___x_432_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_432_;
}
else
{
lean_object* v_tail_433_; 
v_tail_433_ = lean_ctor_get(v_args_428_, 1);
if (lean_obj_tag(v_tail_433_) == 0)
{
lean_object* v_head_434_; 
lean_del_object(v___x_430_);
v_head_434_ = lean_ctor_get(v_args_428_, 0);
lean_inc(v_head_434_);
lean_dec_ref_known(v_args_428_, 2);
v_pat_362_ = v_head_434_;
goto _start;
}
else
{
lean_object* v_head_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_630_; 
lean_inc(v_tail_433_);
v_head_436_ = lean_ctor_get(v_args_428_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_args_428_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v_args_428_, 1);
lean_dec(v_unused_631_);
v___x_438_ = v_args_428_;
v_isShared_439_ = v_isSharedCheck_630_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_head_436_);
lean_dec(v_args_428_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_630_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_u_440_; lean_object* v_00_u03c3s_441_; lean_object* v_hyps_442_; lean_object* v_target_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_629_; 
v_u_440_ = lean_ctor_get(v_goal_361_, 0);
v_00_u03c3s_441_ = lean_ctor_get(v_goal_361_, 1);
v_hyps_442_ = lean_ctor_get(v_goal_361_, 2);
v_target_443_ = lean_ctor_get(v_goal_361_, 3);
v_isSharedCheck_629_ = !lean_is_exclusive(v_goal_361_);
if (v_isSharedCheck_629_ == 0)
{
v___x_445_ = v_goal_361_;
v_isShared_446_ = v_isSharedCheck_629_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_target_443_);
lean_inc(v_hyps_442_);
lean_inc(v_00_u03c3s_441_);
lean_inc(v_u_440_);
lean_dec(v_goal_361_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_629_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = l_Lean_instInhabitedExpr;
v___x_448_ = l_Lean_Meta_whnfR(v_target_443_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_628_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_628_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_628_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_628_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v_toCold_466_; lean_object* v_options_467_; lean_object* v_inheritedTraceOptions_468_; uint8_t v_hasTrace_469_; lean_object* v___x_470_; lean_object* v_nargs_471_; lean_object* v_dummy_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; 
v_toCold_466_ = lean_ctor_get(v_a_370_, 0);
v_options_467_ = lean_ctor_get(v_toCold_466_, 2);
v_inheritedTraceOptions_468_ = lean_ctor_get(v_toCold_466_, 11);
v_hasTrace_469_ = lean_ctor_get_uint8(v_options_467_, sizeof(void*)*1);
v___x_470_ = l_Lean_Expr_getAppFn_x27(v_a_449_);
v_nargs_471_ = l_Lean_Expr_getAppNumArgs(v_a_449_);
v_dummy_472_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2);
lean_inc(v_nargs_471_);
v___x_473_ = lean_mk_array(v_nargs_471_, v_dummy_472_);
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_sub(v_nargs_471_, v___x_474_);
lean_dec(v_nargs_471_);
lean_inc(v_a_449_);
v___x_476_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_449_, v___x_473_, v___x_475_);
if (v_hasTrace_469_ == 0)
{
v___y_557_ = v_a_364_;
v___y_558_ = v_a_365_;
v___y_559_ = v_a_366_;
v___y_560_ = v_a_367_;
v___y_561_ = v_a_368_;
v___y_562_ = v_a_369_;
v___y_563_ = v_a_370_;
v___y_564_ = v_a_371_;
goto v___jp_556_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16));
v___x_607_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19);
v___x_608_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_468_, v_options_467_, v___x_607_);
if (v___x_608_ == 0)
{
v___y_557_ = v_a_364_;
v___y_558_ = v_a_365_;
v___y_559_ = v_a_366_;
v___y_560_ = v_a_367_;
v___y_561_ = v_a_368_;
v___y_562_ = v_a_369_;
v___y_563_ = v_a_370_;
v___y_564_ = v_a_371_;
goto v___jp_556_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_609_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21);
lean_inc_ref(v___x_470_);
v___x_610_ = l_Lean_MessageData_ofExpr(v___x_470_);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
lean_inc_ref(v___x_476_);
v___x_614_ = lean_array_to_list(v___x_476_);
v___x_615_ = lean_box(0);
v___x_616_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__2(v___x_614_, v___x_615_);
v___x_617_ = l_Lean_MessageData_ofList(v___x_616_);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_613_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v___x_606_, v___x_618_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_dec_ref_known(v___x_619_, 1);
v___y_557_ = v_a_364_;
v___y_558_ = v_a_365_;
v___y_559_ = v_a_366_;
v___y_560_ = v_a_367_;
v___y_561_ = v_a_368_;
v___y_562_ = v_a_369_;
v___y_563_ = v_a_370_;
v___y_564_ = v_a_371_;
goto v___jp_556_;
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v___x_476_);
lean_dec_ref(v___x_470_);
lean_del_object(v___x_451_);
lean_dec(v_a_449_);
lean_del_object(v___x_445_);
lean_dec_ref(v_hyps_442_);
lean_dec_ref(v_00_u03c3s_441_);
lean_dec(v_u_440_);
lean_del_object(v___x_438_);
lean_dec(v_head_436_);
lean_dec(v_tail_433_);
lean_del_object(v___x_430_);
lean_dec_ref(v_k_363_);
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
v___jp_453_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1);
v___x_463_ = l_Lean_MessageData_ofExpr(v_a_449_);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v___x_464_, v___y_458_, v___y_456_, v___y_454_, v___y_459_);
return v___x_465_;
}
v___jp_477_:
{
lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_489_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3));
lean_inc_ref(v___y_481_);
lean_inc_ref(v___y_479_);
lean_inc_ref(v___y_482_);
v___x_490_ = l_Lean_Name_mkStr4(v___y_482_, v___y_479_, v___y_481_, v___x_489_);
v___x_491_ = l_Lean_Expr_isConstOf(v___x_470_, v___x_490_);
lean_dec(v___x_490_);
lean_dec_ref(v___x_470_);
if (v___x_491_ == 0)
{
lean_dec_ref(v___x_476_);
lean_del_object(v___x_451_);
lean_del_object(v___x_445_);
lean_dec_ref(v_hyps_442_);
lean_dec_ref(v_00_u03c3s_441_);
lean_dec(v_u_440_);
lean_del_object(v___x_438_);
lean_dec(v_head_436_);
lean_dec(v_tail_433_);
lean_del_object(v___x_430_);
lean_dec_ref(v_k_363_);
v___y_454_ = v___y_478_;
v___y_455_ = v___y_480_;
v___y_456_ = v___y_483_;
v___y_457_ = v___y_484_;
v___y_458_ = v___y_485_;
v___y_459_ = v___y_487_;
v___y_460_ = v___y_486_;
v___y_461_ = v___y_488_;
goto v___jp_453_;
}
else
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = lean_box(0);
v___x_493_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(v___x_476_, v___x_492_);
if (v___x_493_ == 0)
{
lean_dec_ref(v___x_476_);
lean_del_object(v___x_451_);
lean_del_object(v___x_445_);
lean_dec_ref(v_hyps_442_);
lean_dec_ref(v_00_u03c3s_441_);
lean_dec(v_u_440_);
lean_del_object(v___x_438_);
lean_dec(v_head_436_);
lean_dec(v_tail_433_);
lean_del_object(v___x_430_);
lean_dec_ref(v_k_363_);
v___y_454_ = v___y_478_;
v___y_455_ = v___y_480_;
v___y_456_ = v___y_483_;
v___y_457_ = v___y_484_;
v___y_458_ = v___y_485_;
v___y_459_ = v___y_487_;
v___y_460_ = v___y_486_;
v___y_461_ = v___y_488_;
goto v___jp_453_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec(v_a_449_);
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_array_get(v___x_447_, v___x_476_, v___x_494_);
v___x_496_ = lean_unsigned_to_nat(2u);
v___x_497_ = lean_array_get(v___x_447_, v___x_476_, v___x_496_);
lean_inc(v___x_495_);
if (v_isShared_452_ == 0)
{
lean_ctor_set_tag(v___x_451_, 1);
lean_ctor_set(v___x_451_, 0, v___x_495_);
v___x_499_ = v___x_451_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_495_);
v___x_499_ = v_reuseFailAlloc_555_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(v_head_436_, v___x_499_, v___y_484_, v___y_486_, v___y_480_, v___y_488_, v___y_485_, v___y_483_, v___y_478_, v___y_487_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
if (lean_obj_tag(v_a_501_) == 1)
{
lean_object* v_val_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v_val_502_ = lean_ctor_get(v_a_501_, 0);
lean_inc_n(v_val_502_, 2);
lean_dec_ref_known(v_a_501_, 1);
v___x_503_ = lean_mk_empty_array_with_capacity(v___x_474_);
v___x_504_ = lean_array_push(v___x_503_, v_val_502_);
v___x_505_ = lean_unsigned_to_nat(3u);
v___x_506_ = lean_array_get_size(v___x_476_);
v___x_507_ = l_Array_toSubarray___redArg(v___x_476_, v___x_505_, v___x_506_);
v___x_508_ = l_Subarray_copy___redArg(v___x_507_);
v___x_509_ = l_Array_append___redArg(v___x_504_, v___x_508_);
lean_dec_ref(v___x_508_);
lean_inc(v___x_497_);
v___x_510_ = l_Lean_Expr_beta(v___x_497_, v___x_509_);
lean_inc_ref(v_hyps_442_);
lean_inc_ref(v_00_u03c3s_441_);
lean_inc(v_u_440_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 3, v___x_510_);
v___x_512_ = v___x_445_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_u_440_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_00_u03c3s_441_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_hyps_442_);
lean_ctor_set(v_reuseFailAlloc_544_, 3, v___x_510_);
v___x_512_ = v_reuseFailAlloc_544_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v_tail_433_);
v___x_514_ = v___x_430_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_tail_433_);
v___x_514_ = v_reuseFailAlloc_543_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v___x_512_, v___x_514_, v_k_363_, v___y_484_, v___y_486_, v___y_480_, v___y_488_, v___y_485_, v___y_483_, v___y_478_, v___y_487_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
lean_inc(v___x_495_);
v___x_517_ = l_Lean_Meta_getLevel(v___x_495_, v___y_485_, v___y_483_, v___y_478_, v___y_487_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_534_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_534_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_534_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_534_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_522_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4));
lean_inc_ref(v___y_481_);
lean_inc_ref(v___y_479_);
lean_inc_ref(v___y_482_);
v___x_523_ = l_Lean_Name_mkStr4(v___y_482_, v___y_479_, v___y_481_, v___x_522_);
v___x_524_ = lean_box(0);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_524_);
lean_ctor_set(v___x_438_, 0, v_u_440_);
v___x_526_ = v___x_438_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_u_440_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_533_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_527_, 0, v_a_518_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_mkConst(v___x_523_, v___x_527_);
v___x_529_ = l_Lean_mkApp6(v___x_528_, v___x_495_, v_00_u03c3s_441_, v_hyps_442_, v___x_497_, v_val_502_, v_a_516_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_529_);
v___x_531_ = v___x_520_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_516_);
lean_dec(v_val_502_);
lean_dec(v___x_497_);
lean_dec(v___x_495_);
lean_dec_ref(v_hyps_442_);
lean_dec_ref(v_00_u03c3s_441_);
lean_dec(v_u_440_);
lean_del_object(v___x_438_);
v_a_535_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_517_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_517_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_dec(v_val_502_);
lean_dec(v___x_497_);
lean_dec(v___x_495_);
lean_dec_ref(v_hyps_442_);
lean_dec_ref(v_00_u03c3s_441_);
lean_dec(v_u_440_);
lean_del_object(v___x_438_);
return v___x_515_;
}
}
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v_a_501_);
lean_dec(v___x_497_);
lean_dec(v___x_495_);
lean_dec_ref(v___x_476_);
lean_del_object(v___x_445_);
lean_dec_ref(v_hyps_442_);
lean_dec_ref(v_00_u03c3s_441_);
lean_dec(v_u_440_);
lean_del_object(v___x_438_);
lean_dec(v_tail_433_);
lean_del_object(v___x_430_);
lean_dec_ref(v_k_363_);
v___x_545_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6);
v___x_546_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v___x_545_, v___y_485_, v___y_483_, v___y_478_, v___y_487_);
return v___x_546_;
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v___x_497_);
lean_dec(v___x_495_);
lean_dec_ref(v___x_476_);
lean_del_object(v___x_445_);
lean_dec_ref(v_hyps_442_);
lean_dec_ref(v_00_u03c3s_441_);
lean_dec(v_u_440_);
lean_del_object(v___x_438_);
lean_dec(v_tail_433_);
lean_del_object(v___x_430_);
lean_dec_ref(v_k_363_);
v_a_547_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_500_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_500_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
}
v___jp_556_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_565_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7));
v___x_566_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8));
v___x_567_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9));
v___x_568_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11));
v___x_569_ = l_Lean_Expr_isConstOf(v___x_470_, v___x_568_);
if (v___x_569_ == 0)
{
v___y_478_ = v___y_563_;
v___y_479_ = v___x_566_;
v___y_480_ = v___y_559_;
v___y_481_ = v___x_567_;
v___y_482_ = v___x_565_;
v___y_483_ = v___y_562_;
v___y_484_ = v___y_557_;
v___y_485_ = v___y_561_;
v___y_486_ = v___y_558_;
v___y_487_ = v___y_564_;
v___y_488_ = v___y_560_;
goto v___jp_477_;
}
else
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_box(0);
v___x_571_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(v___x_476_, v___x_570_);
if (v___x_571_ == 0)
{
v___y_478_ = v___y_563_;
v___y_479_ = v___x_566_;
v___y_480_ = v___y_559_;
v___y_481_ = v___x_567_;
v___y_482_ = v___x_565_;
v___y_483_ = v___y_562_;
v___y_484_ = v___y_557_;
v___y_485_ = v___y_561_;
v___y_486_ = v___y_558_;
v___y_487_ = v___y_564_;
v___y_488_ = v___y_560_;
goto v___jp_477_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec_ref(v___x_470_);
lean_del_object(v___x_451_);
lean_dec(v_a_449_);
lean_del_object(v___x_445_);
lean_del_object(v___x_438_);
lean_del_object(v___x_430_);
v___x_572_ = lean_array_get_borrowed(v___x_447_, v___x_476_, v___x_474_);
v___x_573_ = lean_unsigned_to_nat(3u);
v___x_574_ = lean_array_get_size(v___x_476_);
lean_inc_ref(v___x_476_);
v___x_575_ = l_Array_toSubarray___redArg(v___x_476_, v___x_573_, v___x_574_);
v___x_576_ = l_Subarray_copy___redArg(v___x_575_);
lean_inc_ref(v___x_576_);
lean_inc(v___x_572_);
v___x_577_ = l_Lean_Expr_beta(v___x_572_, v___x_576_);
v___x_578_ = lean_unsigned_to_nat(2u);
v___x_579_ = lean_array_get(v___x_447_, v___x_476_, v___x_578_);
lean_dec_ref(v___x_476_);
v___x_580_ = l_Lean_Expr_beta(v___x_579_, v___x_576_);
lean_inc_ref(v___x_577_);
lean_inc_ref(v_hyps_442_);
lean_inc_ref(v_00_u03c3s_441_);
lean_inc(v_u_440_);
v___x_581_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_581_, 0, v_u_440_);
lean_ctor_set(v___x_581_, 1, v_00_u03c3s_441_);
lean_ctor_set(v___x_581_, 2, v_hyps_442_);
lean_ctor_set(v___x_581_, 3, v___x_577_);
lean_inc_ref(v_k_363_);
v___x_582_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v___x_581_, v_head_436_, v_k_363_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_605_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_605_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_605_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_605_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
lean_inc_ref(v___x_580_);
lean_inc_ref(v_hyps_442_);
lean_inc_ref(v_00_u03c3s_441_);
lean_inc(v_u_440_);
v___x_587_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_587_, 0, v_u_440_);
lean_ctor_set(v___x_587_, 1, v_00_u03c3s_441_);
lean_ctor_set(v___x_587_, 2, v_hyps_442_);
lean_ctor_set(v___x_587_, 3, v___x_580_);
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 1);
lean_ctor_set(v___x_585_, 0, v_tail_433_);
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_tail_433_);
v___x_589_ = v_reuseFailAlloc_604_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v___x_587_, v___x_589_, v_k_363_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_603_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_603_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_603_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_603_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_595_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13));
v___x_596_ = lean_box(0);
v___x_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_597_, 0, v_u_440_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_mkConst(v___x_595_, v___x_597_);
v___x_599_ = l_Lean_mkApp6(v___x_598_, v_00_u03c3s_441_, v_hyps_442_, v___x_577_, v___x_580_, v_a_583_, v_a_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_599_);
v___x_601_ = v___x_593_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
lean_dec(v_a_583_);
lean_dec_ref(v___x_580_);
lean_dec_ref(v___x_577_);
lean_dec_ref(v_hyps_442_);
lean_dec_ref(v_00_u03c3s_441_);
lean_dec(v_u_440_);
return v___x_590_;
}
}
}
}
else
{
lean_dec_ref(v___x_580_);
lean_dec_ref(v___x_577_);
lean_dec_ref(v_hyps_442_);
lean_dec_ref(v_00_u03c3s_441_);
lean_dec(v_u_440_);
lean_dec(v_tail_433_);
lean_dec_ref(v_k_363_);
return v___x_582_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_445_);
lean_dec_ref(v_hyps_442_);
lean_dec_ref(v_00_u03c3s_441_);
lean_dec(v_u_440_);
lean_del_object(v___x_438_);
lean_dec(v_head_436_);
lean_dec(v_tail_433_);
lean_del_object(v___x_430_);
lean_dec_ref(v_k_363_);
return v___x_448_;
}
}
}
}
}
}
}
case 2:
{
lean_object* v_h_633_; lean_object* v___x_634_; 
lean_dec_ref(v_k_363_);
v_h_633_ = lean_ctor_get(v_pat_362_, 0);
lean_inc(v_h_633_);
lean_dec_ref_known(v_pat_362_, 1);
v___x_634_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(v_goal_361_, v_h_633_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
return v___x_634_;
}
case 3:
{
lean_object* v_h_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
lean_dec_ref(v_k_363_);
v_h_635_ = lean_ctor_get(v_pat_362_, 0);
lean_inc_n(v_h_635_, 2);
lean_dec_ref_known(v_pat_362_, 1);
v___x_636_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2));
v___x_637_ = l_Lean_Syntax_isOfKind(v_h_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec(v_h_635_);
lean_inc_ref(v_goal_361_);
v___x_638_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v_goal_361_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_654_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_654_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_654_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_654_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
if (lean_obj_tag(v_a_639_) == 1)
{
lean_object* v_val_643_; lean_object* v___x_645_; 
lean_dec_ref(v_goal_361_);
v_val_643_ = lean_ctor_get(v_a_639_, 0);
lean_inc(v_val_643_);
lean_dec_ref_known(v_a_639_, 1);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v_val_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_val_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v_target_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_del_object(v___x_641_);
lean_dec(v_a_639_);
v_target_647_ = lean_ctor_get(v_goal_361_, 3);
lean_inc_ref(v_target_647_);
lean_dec_ref(v_goal_361_);
v___x_648_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25);
v___x_649_ = l_Lean_MessageData_ofExpr(v_target_647_);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_652_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
return v___x_653_;
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_goal_361_);
v_a_655_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_638_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_638_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v___x_663_; lean_object* v_name_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_663_ = lean_unsigned_to_nat(0u);
v_name_664_ = l_Lean_Syntax_getArg(v_h_635_, v___x_663_);
lean_dec(v_h_635_);
v___x_665_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4));
lean_inc(v_name_664_);
v___x_666_ = l_Lean_Syntax_isOfKind(v_name_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_dec(v_name_664_);
lean_inc_ref(v_goal_361_);
v___x_667_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v_goal_361_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_683_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_683_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_683_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_683_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
if (lean_obj_tag(v_a_668_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_674_; 
lean_dec_ref(v_goal_361_);
v_val_672_ = lean_ctor_get(v_a_668_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v_a_668_, 1);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v_val_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_val_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
else
{
lean_object* v_target_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_del_object(v___x_670_);
lean_dec(v_a_668_);
v_target_676_ = lean_ctor_get(v_goal_361_, 3);
lean_inc_ref(v_target_676_);
lean_dec_ref(v_goal_361_);
v___x_677_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25);
v___x_678_ = l_Lean_MessageData_ofExpr(v_target_676_);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_681_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
return v___x_682_;
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v_goal_361_);
v_a_684_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_667_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_667_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v___x_692_; 
lean_inc(v_name_664_);
v___x_692_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(v_goal_361_, v_name_664_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_708_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_708_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_708_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_708_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
if (lean_obj_tag(v_a_693_) == 1)
{
lean_object* v_val_697_; lean_object* v___x_699_; 
lean_dec(v_name_664_);
v_val_697_ = lean_ctor_get(v_a_693_, 0);
lean_inc(v_val_697_);
lean_dec_ref_known(v_a_693_, 1);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v_val_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_val_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_del_object(v___x_695_);
lean_dec(v_a_693_);
v___x_701_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29);
v___x_702_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_664_);
v___x_703_ = l_Lean_MessageData_ofFormat(v___x_702_);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_701_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__31, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__31_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__31);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_706_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
return v___x_707_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_name_664_);
v_a_709_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_692_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_692_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
}
default: 
{
lean_object* v_name_717_; lean_object* v___x_718_; 
v_name_717_ = lean_ctor_get(v_pat_362_, 0);
lean_inc(v_name_717_);
lean_dec_ref_known(v_pat_362_, 1);
lean_inc(v_a_371_);
lean_inc_ref(v_a_370_);
lean_inc(v_a_369_);
lean_inc_ref(v_a_368_);
lean_inc(v_a_367_);
lean_inc_ref(v_a_366_);
lean_inc(v_a_365_);
lean_inc_ref(v_a_364_);
v___x_718_ = lean_apply_11(v_k_363_, v_goal_361_, v_name_717_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, lean_box(0));
return v___x_718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1(lean_object* v_00_u03b1_719_, lean_object* v_msg_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v_msg_720_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___boxed(lean_object* v_00_u03b1_731_, lean_object* v_msg_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1(v_00_u03b1_731_, v_msg_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3(lean_object* v_cls_743_, lean_object* v_msg_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_cls_743_, v_msg_744_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___boxed(lean_object* v_cls_755_, lean_object* v_msg_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3(v_cls_755_, v_msg_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4(lean_object* v_00_u03b1_767_, lean_object* v_msg_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v_msg_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___boxed(lean_object* v_00_u03b1_775_, lean_object* v_msg_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4(v_00_u03b1_775_, v_msg_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0(lean_object* v_x_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; 
lean_inc(v___y_787_);
lean_inc_ref(v___y_786_);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
v___x_793_ = lean_apply_9(v_x_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, lean_box(0));
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0___boxed(lean_object* v_x_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0(v_x_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(lean_object* v_mvarId_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___f_816_; lean_object* v___x_817_; 
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
v___f_816_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_816_, 0, v_x_806_);
lean_closure_set(v___f_816_, 1, v___y_807_);
lean_closure_set(v___f_816_, 2, v___y_808_);
lean_closure_set(v___f_816_, 3, v___y_809_);
lean_closure_set(v___f_816_, 4, v___y_810_);
v___x_817_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_805_, v___f_816_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_817_) == 0)
{
return v___x_817_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___boxed(lean_object* v_mvarId_826_, lean_object* v_x_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_mvarId_826_, v_x_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2(lean_object* v_00_u03b1_838_, lean_object* v_mvarId_839_, lean_object* v_x_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_mvarId_839_, v_x_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___boxed(lean_object* v_00_u03b1_851_, lean_object* v_mvarId_852_, lean_object* v_x_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2(v_00_u03b1_851_, v_mvarId_852_, v_x_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(lean_object* v_val_864_, lean_object* v_goal_865_, lean_object* v_name_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_865_);
v___x_877_ = l_Lean_Syntax_getId(v_name_866_);
v___x_878_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_876_, v___x_877_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_890_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_890_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_883_ = lean_st_ref_take(v_val_864_);
v___x_884_ = l_Lean_Expr_mvarId_x21(v_a_879_);
v___x_885_ = lean_array_push(v___x_883_, v___x_884_);
v___x_886_ = lean_st_ref_put(v_val_864_, v___x_885_);
if (v_isShared_882_ == 0)
{
v___x_888_ = v___x_881_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_879_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed(lean_object* v_val_891_, lean_object* v_goal_892_, lean_object* v_name_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(v_val_891_, v_goal_892_, v_name_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v_name_893_);
lean_dec(v_val_891_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16_spec__19___redArg(lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v_ks_908_; lean_object* v_vs_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_933_; 
v_ks_908_ = lean_ctor_get(v_x_904_, 0);
v_vs_909_ = lean_ctor_get(v_x_904_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_x_904_);
if (v_isSharedCheck_933_ == 0)
{
v___x_911_ = v_x_904_;
v_isShared_912_ = v_isSharedCheck_933_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_vs_909_);
lean_inc(v_ks_908_);
lean_dec(v_x_904_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_933_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_array_get_size(v_ks_908_);
v___x_914_ = lean_nat_dec_lt(v_x_905_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
lean_dec(v_x_905_);
v___x_915_ = lean_array_push(v_ks_908_, v_x_906_);
v___x_916_ = lean_array_push(v_vs_909_, v_x_907_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v___x_916_);
lean_ctor_set(v___x_911_, 0, v___x_915_);
v___x_918_ = v___x_911_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_916_);
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
lean_object* v_k_x27_920_; uint8_t v___x_921_; 
v_k_x27_920_ = lean_array_fget_borrowed(v_ks_908_, v_x_905_);
v___x_921_ = l_Lean_instBEqMVarId_beq(v_x_906_, v_k_x27_920_);
if (v___x_921_ == 0)
{
lean_object* v___x_923_; 
if (v_isShared_912_ == 0)
{
v___x_923_ = v___x_911_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_ks_908_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_vs_909_);
v___x_923_ = v_reuseFailAlloc_927_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_unsigned_to_nat(1u);
v___x_925_ = lean_nat_add(v_x_905_, v___x_924_);
lean_dec(v_x_905_);
v_x_904_ = v___x_923_;
v_x_905_ = v___x_925_;
goto _start;
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_928_ = lean_array_fset(v_ks_908_, v_x_905_, v_x_906_);
v___x_929_ = lean_array_fset(v_vs_909_, v_x_905_, v_x_907_);
lean_dec(v_x_905_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v___x_929_);
lean_ctor_set(v___x_911_, 0, v___x_928_);
v___x_931_ = v___x_911_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(lean_object* v_n_934_, lean_object* v_k_935_, lean_object* v_v_936_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16_spec__19___redArg(v_n_934_, v___x_937_, v_k_935_, v_v_936_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(lean_object* v_x_940_, size_t v_x_941_, size_t v_x_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
if (lean_obj_tag(v_x_940_) == 0)
{
lean_object* v_es_945_; size_t v___x_946_; size_t v___x_947_; lean_object* v_j_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_es_945_ = lean_ctor_get(v_x_940_, 0);
v___x_946_ = ((size_t)31ULL);
v___x_947_ = lean_usize_land(v_x_941_, v___x_946_);
v_j_948_ = lean_usize_to_nat(v___x_947_);
v___x_949_ = lean_array_get_size(v_es_945_);
v___x_950_ = lean_nat_dec_lt(v_j_948_, v___x_949_);
if (v___x_950_ == 0)
{
lean_dec(v_j_948_);
lean_dec(v_x_944_);
lean_dec(v_x_943_);
return v_x_940_;
}
else
{
lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_989_; 
lean_inc_ref(v_es_945_);
v_isSharedCheck_989_ = !lean_is_exclusive(v_x_940_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v_x_940_, 0);
lean_dec(v_unused_990_);
v___x_952_ = v_x_940_;
v_isShared_953_ = v_isSharedCheck_989_;
goto v_resetjp_951_;
}
else
{
lean_dec(v_x_940_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_989_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_v_954_; lean_object* v___x_955_; lean_object* v_xs_x27_956_; lean_object* v___y_958_; 
v_v_954_ = lean_array_fget(v_es_945_, v_j_948_);
v___x_955_ = lean_box(0);
v_xs_x27_956_ = lean_array_fset(v_es_945_, v_j_948_, v___x_955_);
switch(lean_obj_tag(v_v_954_))
{
case 0:
{
lean_object* v_key_963_; lean_object* v_val_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_974_; 
v_key_963_ = lean_ctor_get(v_v_954_, 0);
v_val_964_ = lean_ctor_get(v_v_954_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_v_954_);
if (v_isSharedCheck_974_ == 0)
{
v___x_966_ = v_v_954_;
v_isShared_967_ = v_isSharedCheck_974_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_val_964_);
lean_inc(v_key_963_);
lean_dec(v_v_954_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_974_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
uint8_t v___x_968_; 
v___x_968_ = l_Lean_instBEqMVarId_beq(v_x_943_, v_key_963_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_del_object(v___x_966_);
v___x_969_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_963_, v_val_964_, v_x_943_, v_x_944_);
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
v___y_958_ = v___x_970_;
goto v___jp_957_;
}
else
{
lean_object* v___x_972_; 
lean_dec(v_val_964_);
lean_dec(v_key_963_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v_x_944_);
lean_ctor_set(v___x_966_, 0, v_x_943_);
v___x_972_ = v___x_966_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_x_943_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_x_944_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
v___y_958_ = v___x_972_;
goto v___jp_957_;
}
}
}
}
case 1:
{
lean_object* v_node_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_987_; 
v_node_975_ = lean_ctor_get(v_v_954_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v_v_954_);
if (v_isSharedCheck_987_ == 0)
{
v___x_977_ = v_v_954_;
v_isShared_978_ = v_isSharedCheck_987_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_node_975_);
lean_dec(v_v_954_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_987_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
size_t v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_979_ = ((size_t)5ULL);
v___x_980_ = lean_usize_shift_right(v_x_941_, v___x_979_);
v___x_981_ = ((size_t)1ULL);
v___x_982_ = lean_usize_add(v_x_942_, v___x_981_);
v___x_983_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_node_975_, v___x_980_, v___x_982_, v_x_943_, v_x_944_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_983_);
v___x_985_ = v___x_977_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
v___y_958_ = v___x_985_;
goto v___jp_957_;
}
}
}
default: 
{
lean_object* v___x_988_; 
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v_x_943_);
lean_ctor_set(v___x_988_, 1, v_x_944_);
v___y_958_ = v___x_988_;
goto v___jp_957_;
}
}
v___jp_957_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_array_fset(v_xs_x27_956_, v_j_948_, v___y_958_);
lean_dec(v_j_948_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_959_);
v___x_961_ = v___x_952_;
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
}
else
{
lean_object* v_ks_991_; lean_object* v_vs_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1010_; 
v_ks_991_ = lean_ctor_get(v_x_940_, 0);
v_vs_992_ = lean_ctor_get(v_x_940_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_x_940_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_994_ = v_x_940_;
v_isShared_995_ = v_isSharedCheck_1010_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_vs_992_);
lean_inc(v_ks_991_);
lean_dec(v_x_940_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1010_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_ks_991_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_vs_992_);
v___x_997_ = v_reuseFailAlloc_1009_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v_newNode_998_; size_t v___x_999_; uint8_t v___x_1000_; 
v_newNode_998_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v___x_997_, v_x_943_, v_x_944_);
v___x_999_ = ((size_t)7ULL);
v___x_1000_ = lean_usize_dec_le(v___x_999_, v_x_942_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1001_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_998_);
v___x_1002_ = lean_unsigned_to_nat(4u);
v___x_1003_ = lean_nat_dec_lt(v___x_1001_, v___x_1002_);
lean_dec(v___x_1001_);
if (v___x_1003_ == 0)
{
lean_object* v_ks_1004_; lean_object* v_vs_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_ks_1004_ = lean_ctor_get(v_newNode_998_, 0);
lean_inc_ref(v_ks_1004_);
v_vs_1005_ = lean_ctor_get(v_newNode_998_, 1);
lean_inc_ref(v_vs_1005_);
lean_dec_ref(v_newNode_998_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0);
v___x_1008_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17___redArg(v_x_942_, v_ks_1004_, v_vs_1005_, v___x_1006_, v___x_1007_);
lean_dec_ref(v_vs_1005_);
lean_dec_ref(v_ks_1004_);
return v___x_1008_;
}
else
{
return v_newNode_998_;
}
}
else
{
return v_newNode_998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17___redArg(size_t v_depth_1011_, lean_object* v_keys_1012_, lean_object* v_vals_1013_, lean_object* v_i_1014_, lean_object* v_entries_1015_){
_start:
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_array_get_size(v_keys_1012_);
v___x_1017_ = lean_nat_dec_lt(v_i_1014_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v_i_1014_);
return v_entries_1015_;
}
else
{
lean_object* v_k_1018_; lean_object* v_v_1019_; uint64_t v___x_1020_; size_t v_h_1021_; size_t v___x_1022_; lean_object* v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; size_t v___x_1026_; size_t v_h_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_k_1018_ = lean_array_fget_borrowed(v_keys_1012_, v_i_1014_);
v_v_1019_ = lean_array_fget_borrowed(v_vals_1013_, v_i_1014_);
v___x_1020_ = l_Lean_instHashableMVarId_hash(v_k_1018_);
v_h_1021_ = lean_uint64_to_usize(v___x_1020_);
v___x_1022_ = ((size_t)5ULL);
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = ((size_t)1ULL);
v___x_1025_ = lean_usize_sub(v_depth_1011_, v___x_1024_);
v___x_1026_ = lean_usize_mul(v___x_1022_, v___x_1025_);
v_h_1027_ = lean_usize_shift_right(v_h_1021_, v___x_1026_);
v___x_1028_ = lean_nat_add(v_i_1014_, v___x_1023_);
lean_dec(v_i_1014_);
lean_inc(v_v_1019_);
lean_inc(v_k_1018_);
v___x_1029_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_entries_1015_, v_h_1027_, v_depth_1011_, v_k_1018_, v_v_1019_);
v_i_1014_ = v___x_1028_;
v_entries_1015_ = v___x_1029_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17___redArg___boxed(lean_object* v_depth_1031_, lean_object* v_keys_1032_, lean_object* v_vals_1033_, lean_object* v_i_1034_, lean_object* v_entries_1035_){
_start:
{
size_t v_depth_boxed_1036_; lean_object* v_res_1037_; 
v_depth_boxed_1036_ = lean_unbox_usize(v_depth_1031_);
lean_dec(v_depth_1031_);
v_res_1037_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17___redArg(v_depth_boxed_1036_, v_keys_1032_, v_vals_1033_, v_i_1034_, v_entries_1035_);
lean_dec_ref(v_vals_1033_);
lean_dec_ref(v_keys_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___boxed(lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
size_t v_x_17844__boxed_1043_; size_t v_x_17845__boxed_1044_; lean_object* v_res_1045_; 
v_x_17844__boxed_1043_ = lean_unbox_usize(v_x_1039_);
lean_dec(v_x_1039_);
v_x_17845__boxed_1044_ = lean_unbox_usize(v_x_1040_);
lean_dec(v_x_1040_);
v_res_1045_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_1038_, v_x_17844__boxed_1043_, v_x_17845__boxed_1044_, v_x_1041_, v_x_1042_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
uint64_t v___x_1049_; size_t v___x_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = l_Lean_instHashableMVarId_hash(v_x_1047_);
v___x_1050_ = lean_uint64_to_usize(v___x_1049_);
v___x_1051_ = ((size_t)1ULL);
v___x_1052_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_1046_, v___x_1050_, v___x_1051_, v_x_1047_, v_x_1048_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(lean_object* v_mvarId_1053_, lean_object* v_val_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; lean_object* v_mctx_1058_; lean_object* v_cache_1059_; lean_object* v_zetaDeltaFVarIds_1060_; lean_object* v_postponed_1061_; lean_object* v_diag_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1091_; 
v___x_1057_ = lean_st_ref_take(v___y_1055_);
v_mctx_1058_ = lean_ctor_get(v___x_1057_, 0);
v_cache_1059_ = lean_ctor_get(v___x_1057_, 1);
v_zetaDeltaFVarIds_1060_ = lean_ctor_get(v___x_1057_, 2);
v_postponed_1061_ = lean_ctor_get(v___x_1057_, 3);
v_diag_1062_ = lean_ctor_get(v___x_1057_, 4);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1064_ = v___x_1057_;
v_isShared_1065_ = v_isSharedCheck_1091_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_diag_1062_);
lean_inc(v_postponed_1061_);
lean_inc(v_zetaDeltaFVarIds_1060_);
lean_inc(v_cache_1059_);
lean_inc(v_mctx_1058_);
lean_dec(v___x_1057_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1091_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_depth_1066_; lean_object* v_levelAssignDepth_1067_; lean_object* v_lmvarCounter_1068_; lean_object* v_mvarCounter_1069_; lean_object* v_lDecls_1070_; lean_object* v_decls_1071_; lean_object* v_userNames_1072_; lean_object* v_lAssignment_1073_; lean_object* v_eAssignment_1074_; lean_object* v_dAssignment_1075_; lean_object* v_instanceTypedMVars_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1090_; 
v_depth_1066_ = lean_ctor_get(v_mctx_1058_, 0);
v_levelAssignDepth_1067_ = lean_ctor_get(v_mctx_1058_, 1);
v_lmvarCounter_1068_ = lean_ctor_get(v_mctx_1058_, 2);
v_mvarCounter_1069_ = lean_ctor_get(v_mctx_1058_, 3);
v_lDecls_1070_ = lean_ctor_get(v_mctx_1058_, 4);
v_decls_1071_ = lean_ctor_get(v_mctx_1058_, 5);
v_userNames_1072_ = lean_ctor_get(v_mctx_1058_, 6);
v_lAssignment_1073_ = lean_ctor_get(v_mctx_1058_, 7);
v_eAssignment_1074_ = lean_ctor_get(v_mctx_1058_, 8);
v_dAssignment_1075_ = lean_ctor_get(v_mctx_1058_, 9);
v_instanceTypedMVars_1076_ = lean_ctor_get(v_mctx_1058_, 10);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_mctx_1058_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1078_ = v_mctx_1058_;
v_isShared_1079_ = v_isSharedCheck_1090_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_instanceTypedMVars_1076_);
lean_inc(v_dAssignment_1075_);
lean_inc(v_eAssignment_1074_);
lean_inc(v_lAssignment_1073_);
lean_inc(v_userNames_1072_);
lean_inc(v_decls_1071_);
lean_inc(v_lDecls_1070_);
lean_inc(v_mvarCounter_1069_);
lean_inc(v_lmvarCounter_1068_);
lean_inc(v_levelAssignDepth_1067_);
lean_inc(v_depth_1066_);
lean_dec(v_mctx_1058_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1090_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(v_eAssignment_1074_, v_mvarId_1053_, v_val_1054_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 8, v___x_1081_);
v___x_1083_ = v___x_1078_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_depth_1066_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_levelAssignDepth_1067_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_lmvarCounter_1068_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_mvarCounter_1069_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_lDecls_1070_);
lean_ctor_set(v_reuseFailAlloc_1089_, 5, v_decls_1071_);
lean_ctor_set(v_reuseFailAlloc_1089_, 6, v_userNames_1072_);
lean_ctor_set(v_reuseFailAlloc_1089_, 7, v_lAssignment_1073_);
lean_ctor_set(v_reuseFailAlloc_1089_, 8, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1089_, 9, v_dAssignment_1075_);
lean_ctor_set(v_reuseFailAlloc_1089_, 10, v_instanceTypedMVars_1076_);
v___x_1083_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1083_);
v___x_1085_ = v___x_1064_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_cache_1059_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_zetaDeltaFVarIds_1060_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_postponed_1061_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_diag_1062_);
v___x_1085_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_st_ref_put(v___y_1055_, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1080_);
return v___x_1087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg___boxed(lean_object* v_mvarId_1092_, lean_object* v_val_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(v_mvarId_1092_, v_val_1093_, v___y_1094_);
lean_dec(v___y_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(lean_object* v___x_1097_, lean_object* v_snd_1098_, lean_object* v_a_1099_, lean_object* v_fst_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_st_mk_ref(v___x_1097_);
lean_inc(v___x_1110_);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1111_, 0, v___x_1110_);
v___x_1112_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v_snd_1098_, v_a_1099_, v___f_1111_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v___x_1114_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(v_fst_1100_, v_a_1113_, v___y_1106_);
lean_dec_ref(v___x_1114_);
v___x_1115_ = lean_st_ref_get(v___x_1110_);
lean_dec(v___x_1110_);
v___x_1116_ = lean_array_to_list(v___x_1115_);
v___x_1117_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1116_, v___y_1102_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
return v___x_1117_;
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v___x_1110_);
lean_dec(v_fst_1100_);
v_a_1118_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1112_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1112_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1___boxed(lean_object* v___x_1126_, lean_object* v_snd_1127_, lean_object* v_a_1128_, lean_object* v_fst_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(v___x_1126_, v_snd_1127_, v_a_1128_, v_fst_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(lean_object* v_ref_1140_, lean_object* v_msg_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_toCold_1147_; lean_object* v_currRecDepth_1148_; lean_object* v_ref_1149_; uint16_t v_optionFlags_1150_; uint8_t v_suppressElabErrors_1151_; uint8_t v_checkDeprecated_1152_; uint8_t v_isRecordingDeps_1153_; lean_object* v_ref_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_toCold_1147_ = lean_ctor_get(v___y_1144_, 0);
v_currRecDepth_1148_ = lean_ctor_get(v___y_1144_, 1);
v_ref_1149_ = lean_ctor_get(v___y_1144_, 2);
v_optionFlags_1150_ = lean_ctor_get_uint16(v___y_1144_, sizeof(void*)*3);
v_suppressElabErrors_1151_ = lean_ctor_get_uint8(v___y_1144_, sizeof(void*)*3 + 2);
v_checkDeprecated_1152_ = lean_ctor_get_uint8(v___y_1144_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1153_ = lean_ctor_get_uint8(v___y_1144_, sizeof(void*)*3 + 4);
v_ref_1154_ = l_Lean_replaceRef(v_ref_1140_, v_ref_1149_);
lean_inc(v_currRecDepth_1148_);
lean_inc_ref(v_toCold_1147_);
v___x_1155_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1155_, 0, v_toCold_1147_);
lean_ctor_set(v___x_1155_, 1, v_currRecDepth_1148_);
lean_ctor_set(v___x_1155_, 2, v_ref_1154_);
lean_ctor_set_uint16(v___x_1155_, sizeof(void*)*3, v_optionFlags_1150_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 2, v_suppressElabErrors_1151_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 3, v_checkDeprecated_1152_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 4, v_isRecordingDeps_1153_);
v___x_1156_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v_msg_1141_, v___y_1142_, v___y_1143_, v___x_1155_, v___y_1145_);
lean_dec_ref_known(v___x_1155_, 3);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1157_, lean_object* v_msg_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_ref_1157_, v_msg_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v_ref_1157_);
return v_res_1164_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = l_Lean_maxRecDepthErrorMessage;
v___x_1171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3);
v___x_1173_ = l_Lean_MessageData_ofFormat(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4);
v___x_1175_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2));
v___x_1176_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___x_1174_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(lean_object* v_ref_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1179_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v_ref_1177_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_ref_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10___redArg(lean_object* v_a_1185_, lean_object* v_x_1186_){
_start:
{
if (lean_obj_tag(v_x_1186_) == 0)
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_box(0);
return v___x_1187_;
}
else
{
lean_object* v_key_1188_; lean_object* v_value_1189_; lean_object* v_tail_1190_; uint8_t v___x_1191_; 
v_key_1188_ = lean_ctor_get(v_x_1186_, 0);
v_value_1189_ = lean_ctor_get(v_x_1186_, 1);
v_tail_1190_ = lean_ctor_get(v_x_1186_, 2);
v___x_1191_ = lean_name_eq(v_key_1188_, v_a_1185_);
if (v___x_1191_ == 0)
{
v_x_1186_ = v_tail_1190_;
goto _start;
}
else
{
lean_object* v___x_1193_; 
lean_inc(v_value_1189_);
v___x_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_value_1189_);
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10___redArg___boxed(lean_object* v_a_1194_, lean_object* v_x_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10___redArg(v_a_1194_, v_x_1195_);
lean_dec(v_x_1195_);
lean_dec(v_a_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(lean_object* v_m_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_buckets_1199_; lean_object* v___x_1200_; uint64_t v___y_1202_; 
v_buckets_1199_ = lean_ctor_get(v_m_1197_, 1);
v___x_1200_ = lean_array_get_size(v_buckets_1199_);
if (lean_obj_tag(v_a_1198_) == 0)
{
uint64_t v___x_1216_; 
v___x_1216_ = 1723ULL;
v___y_1202_ = v___x_1216_;
goto v___jp_1201_;
}
else
{
uint64_t v_hash_1217_; 
v_hash_1217_ = lean_ctor_get_uint64(v_a_1198_, sizeof(void*)*2);
v___y_1202_ = v_hash_1217_;
goto v___jp_1201_;
}
v___jp_1201_:
{
uint64_t v___x_1203_; uint64_t v___x_1204_; uint64_t v_fold_1205_; uint64_t v___x_1206_; uint64_t v___x_1207_; uint64_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1203_ = 32ULL;
v___x_1204_ = lean_uint64_shift_right(v___y_1202_, v___x_1203_);
v_fold_1205_ = lean_uint64_xor(v___y_1202_, v___x_1204_);
v___x_1206_ = 16ULL;
v___x_1207_ = lean_uint64_shift_right(v_fold_1205_, v___x_1206_);
v___x_1208_ = lean_uint64_xor(v_fold_1205_, v___x_1207_);
v___x_1209_ = lean_uint64_to_usize(v___x_1208_);
v___x_1210_ = lean_usize_of_nat(v___x_1200_);
v___x_1211_ = ((size_t)1ULL);
v___x_1212_ = lean_usize_sub(v___x_1210_, v___x_1211_);
v___x_1213_ = lean_usize_land(v___x_1209_, v___x_1212_);
v___x_1214_ = lean_array_uget_borrowed(v_buckets_1199_, v___x_1213_);
v___x_1215_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10___redArg(v_a_1198_, v___x_1214_);
return v___x_1215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_m_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v_m_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_m_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___lam__0(lean_object* v___x_1221_, lean_object* v_entry_1222_, lean_object* v_s_1223_){
_start:
{
lean_object* v_addEntryFn_1224_; lean_object* v_importedEntries_1225_; lean_object* v_state_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1234_; 
v_addEntryFn_1224_ = lean_ctor_get(v___x_1221_, 3);
lean_inc(v_addEntryFn_1224_);
lean_dec_ref(v___x_1221_);
v_importedEntries_1225_ = lean_ctor_get(v_s_1223_, 0);
v_state_1226_ = lean_ctor_get(v_s_1223_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_s_1223_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1228_ = v_s_1223_;
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_state_1226_);
lean_inc(v_importedEntries_1225_);
lean_dec(v_s_1223_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_state_1230_; lean_object* v___x_1232_; 
v_state_1230_ = lean_apply_2(v_addEntryFn_1224_, v_state_1226_, v_entry_1222_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v_state_1230_);
v___x_1232_ = v___x_1228_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_importedEntries_1225_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_state_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(lean_object* v_keys_1235_, lean_object* v_i_1236_, lean_object* v_k_1237_){
_start:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = lean_array_get_size(v_keys_1235_);
v___x_1239_ = lean_nat_dec_lt(v_i_1236_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec(v_i_1236_);
return v___x_1239_;
}
else
{
lean_object* v_k_x27_1240_; uint8_t v___x_1241_; 
v_k_x27_1240_ = lean_array_fget_borrowed(v_keys_1235_, v_i_1236_);
v___x_1241_ = l_Lean_instBEqExtraModUse_beq(v_k_1237_, v_k_x27_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = lean_nat_add(v_i_1236_, v___x_1242_);
lean_dec(v_i_1236_);
v_i_1236_ = v___x_1243_;
goto _start;
}
else
{
lean_dec(v_i_1236_);
return v___x_1239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg___boxed(lean_object* v_keys_1245_, lean_object* v_i_1246_, lean_object* v_k_1247_){
_start:
{
uint8_t v_res_1248_; lean_object* v_r_1249_; 
v_res_1248_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_keys_1245_, v_i_1246_, v_k_1247_);
lean_dec_ref(v_k_1247_);
lean_dec_ref(v_keys_1245_);
v_r_1249_ = lean_box(v_res_1248_);
return v_r_1249_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(lean_object* v_x_1250_, size_t v_x_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 0)
{
lean_object* v_es_1253_; lean_object* v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; lean_object* v_j_1257_; lean_object* v___x_1258_; 
v_es_1253_ = lean_ctor_get(v_x_1250_, 0);
v___x_1254_ = lean_box(2);
v___x_1255_ = ((size_t)31ULL);
v___x_1256_ = lean_usize_land(v_x_1251_, v___x_1255_);
v_j_1257_ = lean_usize_to_nat(v___x_1256_);
v___x_1258_ = lean_array_get_borrowed(v___x_1254_, v_es_1253_, v_j_1257_);
lean_dec(v_j_1257_);
switch(lean_obj_tag(v___x_1258_))
{
case 0:
{
lean_object* v_key_1259_; uint8_t v___x_1260_; 
v_key_1259_ = lean_ctor_get(v___x_1258_, 0);
v___x_1260_ = l_Lean_instBEqExtraModUse_beq(v_x_1252_, v_key_1259_);
return v___x_1260_;
}
case 1:
{
lean_object* v_node_1261_; size_t v___x_1262_; size_t v___x_1263_; 
v_node_1261_ = lean_ctor_get(v___x_1258_, 0);
v___x_1262_ = ((size_t)5ULL);
v___x_1263_ = lean_usize_shift_right(v_x_1251_, v___x_1262_);
v_x_1250_ = v_node_1261_;
v_x_1251_ = v___x_1263_;
goto _start;
}
default: 
{
uint8_t v___x_1265_; 
v___x_1265_ = 0;
return v___x_1265_;
}
}
}
else
{
lean_object* v_ks_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_ks_1266_ = lean_ctor_get(v_x_1250_, 0);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_ks_1266_, v___x_1267_, v_x_1252_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg___boxed(lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
size_t v_x_18271__boxed_1272_; uint8_t v_res_1273_; lean_object* v_r_1274_; 
v_x_18271__boxed_1272_ = lean_unbox_usize(v_x_1270_);
lean_dec(v_x_1270_);
v_res_1273_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_1269_, v_x_18271__boxed_1272_, v_x_1271_);
lean_dec_ref(v_x_1271_);
lean_dec_ref(v_x_1269_);
v_r_1274_ = lean_box(v_res_1273_);
return v_r_1274_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
uint64_t v___x_1277_; size_t v___x_1278_; uint8_t v___x_1279_; 
v___x_1277_ = l_Lean_instHashableExtraModUse_hash(v_x_1276_);
v___x_1278_ = lean_uint64_to_usize(v___x_1277_);
v___x_1279_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_1275_, v___x_1278_, v_x_1276_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
uint8_t v_res_1282_; lean_object* v_r_1283_; 
v_res_1282_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v_x_1280_, v_x_1281_);
lean_dec_ref(v_x_1281_);
lean_dec_ref(v_x_1280_);
v_r_1283_ = lean_box(v_res_1282_);
return v_r_1283_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__0);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg(){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__1);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___boxed(lean_object* v___dummy_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg();
return v_res_1290_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg___closed__0);
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13___redArg();
return v___x_1295_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
lean_ctor_set(v___x_1300_, 2, v___x_1298_);
return v___x_1300_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1301_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4);
v___x_1302_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3);
v___x_1303_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_1304_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2);
v___x_1305_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
lean_ctor_set(v___x_1305_, 2, v___x_1302_);
lean_ctor_set(v___x_1305_, 3, v___x_1303_);
lean_ctor_set(v___x_1305_, 4, v___x_1303_);
lean_ctor_set(v___x_1305_, 5, v___x_1303_);
lean_ctor_set(v___x_1305_, 6, v___x_1303_);
lean_ctor_set(v___x_1305_, 7, v___x_1301_);
return v___x_1305_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6(void){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1306_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1));
v___x_1317_ = l_Lean_stringToMessageData(v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14(void){
_start:
{
lean_object* v_cls_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_cls_1318_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8));
v___x_1319_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18));
v___x_1320_ = l_Lean_Name_append(v___x_1319_, v_cls_1318_);
return v___x_1320_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15));
v___x_1323_ = l_Lean_stringToMessageData(v___x_1322_);
return v___x_1323_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17));
v___x_1326_ = l_Lean_stringToMessageData(v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(lean_object* v_mod_1331_, uint8_t v_isMeta_1332_, lean_object* v_hint_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_env_1373_; uint8_t v_isExporting_1374_; lean_object* v_entry_1375_; lean_object* v___x_1376_; lean_object* v_env_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1371_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6);
v___x_1372_ = lean_st_ref_get(v___y_1337_);
v_env_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc_ref(v_env_1373_);
lean_dec(v___x_1372_);
v_isExporting_1374_ = lean_ctor_get_uint8(v_env_1373_, sizeof(void*)*13);
lean_dec_ref(v_env_1373_);
lean_inc(v_mod_1331_);
v_entry_1375_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1375_, 0, v_mod_1331_);
lean_ctor_set_uint8(v_entry_1375_, sizeof(void*)*1, v_isExporting_1374_);
lean_ctor_set_uint8(v_entry_1375_, sizeof(void*)*1 + 1, v_isMeta_1332_);
v___x_1376_ = lean_st_ref_get(v___y_1337_);
v_env_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_ref(v_env_1377_);
lean_dec(v___x_1376_);
v___x_1378_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1379_ = lean_box(1);
v___x_1380_ = lean_box(0);
v___x_1381_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1371_, v___x_1378_, v_env_1377_, v___x_1379_, v___x_1380_);
v___x_1382_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v___x_1381_, v_entry_1375_);
lean_dec(v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v_toCold_1383_; lean_object* v_options_1384_; lean_object* v_inheritedTraceOptions_1385_; uint8_t v_hasTrace_1386_; lean_object* v___f_1387_; uint8_t v___x_1388_; lean_object* v___y_1390_; lean_object* v___y_1391_; 
v_toCold_1383_ = lean_ctor_get(v___y_1336_, 0);
v_options_1384_ = lean_ctor_get(v_toCold_1383_, 2);
v_inheritedTraceOptions_1385_ = lean_ctor_get(v_toCold_1383_, 11);
v_hasTrace_1386_ = lean_ctor_get_uint8(v_options_1384_, sizeof(void*)*1);
v___f_1387_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1387_, 0, v___x_1378_);
lean_closure_set(v___f_1387_, 1, v_entry_1375_);
v___x_1388_ = 1;
if (v_hasTrace_1386_ == 0)
{
lean_dec(v_hint_1333_);
lean_dec(v_mod_1331_);
v___y_1390_ = v___y_1335_;
v___y_1391_ = v___y_1337_;
goto v___jp_1389_;
}
else
{
lean_object* v_cls_1418_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_cls_1418_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8));
v___x_1438_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14);
v___x_1439_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1385_, v_options_1384_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_dec(v_hint_1333_);
lean_dec(v_mod_1331_);
v___y_1390_ = v___y_1335_;
v___y_1391_ = v___y_1337_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1440_; lean_object* v___y_1442_; 
v___x_1440_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16);
if (v_isExporting_1374_ == 0)
{
lean_object* v___x_1449_; 
v___x_1449_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21));
v___y_1442_ = v___x_1449_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1450_; 
v___x_1450_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22));
v___y_1442_ = v___x_1450_;
goto v___jp_1441_;
}
v___jp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_inc_ref(v___y_1442_);
v___x_1443_ = l_Lean_stringToMessageData(v___y_1442_);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1440_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
if (v_isMeta_1332_ == 0)
{
lean_object* v___x_1447_; 
v___x_1447_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19));
v___y_1425_ = v___x_1446_;
v___y_1426_ = v___x_1447_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1448_; 
v___x_1448_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20));
v___y_1425_ = v___x_1446_;
v___y_1426_ = v___x_1448_;
goto v___jp_1424_;
}
}
}
v___jp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___y_1420_);
lean_ctor_set(v___x_1422_, 1, v___y_1421_);
v___x_1423_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_cls_1418_, v___x_1422_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_dec_ref_known(v___x_1423_, 1);
v___y_1390_ = v___y_1335_;
v___y_1391_ = v___y_1337_;
goto v___jp_1389_;
}
else
{
lean_dec_ref(v___f_1387_);
return v___x_1423_;
}
}
v___jp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
lean_inc_ref(v___y_1426_);
v___x_1427_ = l_Lean_stringToMessageData(v___y_1426_);
v___x_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1425_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
v___x_1429_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1428_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = l_Lean_MessageData_ofName(v_mod_1331_);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = l_Lean_Name_isAnonymous(v_hint_1333_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12);
v___x_1435_ = l_Lean_MessageData_ofName(v_hint_1333_);
v___x_1436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1434_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___y_1420_ = v___x_1432_;
v___y_1421_ = v___x_1436_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1437_; 
lean_dec(v_hint_1333_);
v___x_1437_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13);
v___y_1420_ = v___x_1432_;
v___y_1421_ = v___x_1437_;
goto v___jp_1419_;
}
}
}
v___jp_1389_:
{
lean_object* v___x_1392_; lean_object* v_toEnvExtension_1393_; uint8_t v_logWrites_1394_; 
v___x_1392_ = lean_st_ref_take(v___y_1391_);
v_toEnvExtension_1393_ = lean_ctor_get(v___x_1378_, 0);
v_logWrites_1394_ = lean_ctor_get_uint8(v_toEnvExtension_1393_, sizeof(void*)*6);
if (v_logWrites_1394_ == 0)
{
lean_object* v_env_1395_; lean_object* v_nextMacroScope_1396_; lean_object* v_ngen_1397_; lean_object* v_auxDeclNGen_1398_; lean_object* v_traceState_1399_; lean_object* v_recordedDeps_1400_; lean_object* v_messages_1401_; lean_object* v_infoState_1402_; lean_object* v_snapshotTasks_1403_; lean_object* v_asyncMode_1404_; lean_object* v___x_1405_; 
v_env_1395_ = lean_ctor_get(v___x_1392_, 0);
lean_inc_ref(v_env_1395_);
v_nextMacroScope_1396_ = lean_ctor_get(v___x_1392_, 1);
lean_inc(v_nextMacroScope_1396_);
v_ngen_1397_ = lean_ctor_get(v___x_1392_, 2);
lean_inc_ref(v_ngen_1397_);
v_auxDeclNGen_1398_ = lean_ctor_get(v___x_1392_, 3);
lean_inc_ref(v_auxDeclNGen_1398_);
v_traceState_1399_ = lean_ctor_get(v___x_1392_, 4);
lean_inc_ref(v_traceState_1399_);
v_recordedDeps_1400_ = lean_ctor_get(v___x_1392_, 6);
lean_inc_ref(v_recordedDeps_1400_);
v_messages_1401_ = lean_ctor_get(v___x_1392_, 7);
lean_inc_ref(v_messages_1401_);
v_infoState_1402_ = lean_ctor_get(v___x_1392_, 8);
lean_inc_ref(v_infoState_1402_);
v_snapshotTasks_1403_ = lean_ctor_get(v___x_1392_, 9);
lean_inc_ref(v_snapshotTasks_1403_);
lean_dec(v___x_1392_);
v_asyncMode_1404_ = lean_ctor_get(v_toEnvExtension_1393_, 2);
lean_inc_ref(v_toEnvExtension_1393_);
v___x_1405_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1393_, v_env_1395_, v___f_1387_, v_asyncMode_1404_, v___x_1380_, v___x_1388_);
v___y_1340_ = v_ngen_1397_;
v___y_1341_ = v_nextMacroScope_1396_;
v___y_1342_ = v_traceState_1399_;
v___y_1343_ = v_auxDeclNGen_1398_;
v___y_1344_ = v_snapshotTasks_1403_;
v___y_1345_ = v_recordedDeps_1400_;
v___y_1346_ = v___y_1390_;
v___y_1347_ = v___y_1391_;
v___y_1348_ = v_messages_1401_;
v___y_1349_ = v_infoState_1402_;
v___y_1350_ = v___x_1405_;
goto v___jp_1339_;
}
else
{
lean_object* v_env_1406_; lean_object* v_nextMacroScope_1407_; lean_object* v_ngen_1408_; lean_object* v_auxDeclNGen_1409_; lean_object* v_traceState_1410_; lean_object* v_recordedDeps_1411_; lean_object* v_messages_1412_; lean_object* v_infoState_1413_; lean_object* v_snapshotTasks_1414_; lean_object* v_asyncMode_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_env_1406_ = lean_ctor_get(v___x_1392_, 0);
lean_inc_ref(v_env_1406_);
v_nextMacroScope_1407_ = lean_ctor_get(v___x_1392_, 1);
lean_inc(v_nextMacroScope_1407_);
v_ngen_1408_ = lean_ctor_get(v___x_1392_, 2);
lean_inc_ref(v_ngen_1408_);
v_auxDeclNGen_1409_ = lean_ctor_get(v___x_1392_, 3);
lean_inc_ref(v_auxDeclNGen_1409_);
v_traceState_1410_ = lean_ctor_get(v___x_1392_, 4);
lean_inc_ref(v_traceState_1410_);
v_recordedDeps_1411_ = lean_ctor_get(v___x_1392_, 6);
lean_inc_ref(v_recordedDeps_1411_);
v_messages_1412_ = lean_ctor_get(v___x_1392_, 7);
lean_inc_ref(v_messages_1412_);
v_infoState_1413_ = lean_ctor_get(v___x_1392_, 8);
lean_inc_ref(v_infoState_1413_);
v_snapshotTasks_1414_ = lean_ctor_get(v___x_1392_, 9);
lean_inc_ref(v_snapshotTasks_1414_);
lean_dec(v___x_1392_);
v_asyncMode_1415_ = lean_ctor_get(v_toEnvExtension_1393_, 2);
lean_inc_ref_n(v_toEnvExtension_1393_, 2);
v___x_1416_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1393_, v_env_1406_);
lean_dec_ref(v_env_1406_);
v___x_1417_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1393_, v___x_1416_, v___f_1387_, v_asyncMode_1415_, v___x_1380_, v___x_1388_);
v___y_1340_ = v_ngen_1408_;
v___y_1341_ = v_nextMacroScope_1407_;
v___y_1342_ = v_traceState_1410_;
v___y_1343_ = v_auxDeclNGen_1409_;
v___y_1344_ = v_snapshotTasks_1414_;
v___y_1345_ = v_recordedDeps_1411_;
v___y_1346_ = v___y_1390_;
v___y_1347_ = v___y_1391_;
v___y_1348_ = v_messages_1412_;
v___y_1349_ = v_infoState_1413_;
v___y_1350_ = v___x_1417_;
goto v___jp_1339_;
}
}
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec_ref_known(v_entry_1375_, 1);
lean_dec(v_hint_1333_);
lean_dec(v_mod_1331_);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
v___jp_1339_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_mctx_1355_; lean_object* v_zetaDeltaFVarIds_1356_; lean_object* v_postponed_1357_; lean_object* v_diag_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1369_; 
v___x_1351_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_1352_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1352_, 0, v___y_1350_);
lean_ctor_set(v___x_1352_, 1, v___y_1341_);
lean_ctor_set(v___x_1352_, 2, v___y_1340_);
lean_ctor_set(v___x_1352_, 3, v___y_1343_);
lean_ctor_set(v___x_1352_, 4, v___y_1342_);
lean_ctor_set(v___x_1352_, 5, v___x_1351_);
lean_ctor_set(v___x_1352_, 6, v___y_1345_);
lean_ctor_set(v___x_1352_, 7, v___y_1348_);
lean_ctor_set(v___x_1352_, 8, v___y_1349_);
lean_ctor_set(v___x_1352_, 9, v___y_1344_);
v___x_1353_ = lean_st_ref_put(v___y_1347_, v___x_1352_);
v___x_1354_ = lean_st_ref_take(v___y_1346_);
v_mctx_1355_ = lean_ctor_get(v___x_1354_, 0);
v_zetaDeltaFVarIds_1356_ = lean_ctor_get(v___x_1354_, 2);
v_postponed_1357_ = lean_ctor_get(v___x_1354_, 3);
v_diag_1358_ = lean_ctor_get(v___x_1354_, 4);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; 
v_unused_1370_ = lean_ctor_get(v___x_1354_, 1);
lean_dec(v_unused_1370_);
v___x_1360_ = v___x_1354_;
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_diag_1358_);
lean_inc(v_postponed_1357_);
lean_inc(v_zetaDeltaFVarIds_1356_);
lean_inc(v_mctx_1355_);
lean_dec(v___x_1354_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1369_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v___x_1363_);
v___x_1365_ = v___x_1360_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_mctx_1355_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_zetaDeltaFVarIds_1356_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v_postponed_1357_);
lean_ctor_set(v_reuseFailAlloc_1368_, 4, v_diag_1358_);
v___x_1365_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_st_ref_put(v___y_1346_, v___x_1365_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1362_);
return v___x_1367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_mod_1453_, lean_object* v_isMeta_1454_, lean_object* v_hint_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v_isMeta_boxed_1461_; lean_object* v_res_1462_; 
v_isMeta_boxed_1461_ = lean_unbox(v_isMeta_1454_);
v_res_1462_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_mod_1453_, v_isMeta_boxed_1461_, v_hint_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(lean_object* v___x_1463_, lean_object* v_declName_1464_, lean_object* v_as_1465_, size_t v_sz_1466_, size_t v_i_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
uint8_t v___x_1478_; 
v___x_1478_ = lean_usize_dec_lt(v_i_1467_, v_sz_1466_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; 
lean_dec(v_declName_1464_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v_b_1468_);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; lean_object* v_modules_1481_; lean_object* v___x_1482_; lean_object* v_a_1483_; lean_object* v___x_1484_; lean_object* v_toImport_1485_; lean_object* v_module_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; lean_object* v___x_1489_; 
v___x_1480_ = l_Lean_Environment_header(v___x_1463_);
v_modules_1481_ = lean_ctor_get(v___x_1480_, 3);
lean_inc_ref(v_modules_1481_);
lean_dec_ref(v___x_1480_);
v___x_1482_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1483_ = lean_array_uget_borrowed(v_as_1465_, v_i_1467_);
v___x_1484_ = lean_array_get(v___x_1482_, v_modules_1481_, v_a_1483_);
lean_dec_ref(v_modules_1481_);
v_toImport_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc_ref(v_toImport_1485_);
lean_dec(v___x_1484_);
v_module_1486_ = lean_ctor_get(v_toImport_1485_, 0);
lean_inc(v_module_1486_);
lean_dec_ref(v_toImport_1485_);
v___x_1487_ = lean_box(0);
v___x_1488_ = 0;
lean_inc(v_declName_1464_);
v___x_1489_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_module_1486_, v___x_1488_, v_declName_1464_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
if (lean_obj_tag(v___x_1489_) == 0)
{
size_t v___x_1490_; size_t v___x_1491_; 
lean_dec_ref_known(v___x_1489_, 1);
v___x_1490_ = ((size_t)1ULL);
v___x_1491_ = lean_usize_add(v_i_1467_, v___x_1490_);
v_i_1467_ = v___x_1491_;
v_b_1468_ = v___x_1487_;
goto _start;
}
else
{
lean_dec(v_declName_1464_);
return v___x_1489_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4___boxed(lean_object* v___x_1493_, lean_object* v_declName_1494_, lean_object* v_as_1495_, lean_object* v_sz_1496_, lean_object* v_i_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
size_t v_sz_boxed_1508_; size_t v_i_boxed_1509_; lean_object* v_res_1510_; 
v_sz_boxed_1508_ = lean_unbox_usize(v_sz_1496_);
lean_dec(v_sz_1496_);
v_i_boxed_1509_ = lean_unbox_usize(v_i_1497_);
lean_dec(v_i_1497_);
v_res_1510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(v___x_1493_, v_declName_1494_, v_as_1495_, v_sz_boxed_1508_, v_i_boxed_1509_, v_b_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec_ref(v_as_1495_);
lean_dec_ref(v___x_1493_);
return v_res_1510_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(lean_object* v_declName_1514_, uint8_t v_isMeta_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_env_1530_; lean_object* v___y_1532_; lean_object* v___x_1545_; 
v___x_1525_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0);
v___x_1526_ = lean_st_ref_get(v___y_1523_);
v_env_1530_ = lean_ctor_get(v___x_1526_, 0);
lean_inc_ref(v_env_1530_);
lean_dec(v___x_1526_);
v___x_1545_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1530_, v_declName_1514_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_dec_ref(v_env_1530_);
lean_dec(v_declName_1514_);
goto v___jp_1527_;
}
else
{
lean_object* v_val_1546_; lean_object* v___x_1547_; lean_object* v_modules_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_val_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_val_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = l_Lean_Environment_header(v_env_1530_);
v_modules_1548_ = lean_ctor_get(v___x_1547_, 3);
lean_inc_ref(v_modules_1548_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = lean_array_get_size(v_modules_1548_);
v___x_1550_ = lean_nat_dec_lt(v_val_1546_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_dec_ref(v_modules_1548_);
lean_dec(v_val_1546_);
lean_dec_ref(v_env_1530_);
lean_dec(v_declName_1514_);
goto v___jp_1527_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___y_1554_; 
v___x_1551_ = lean_array_fget(v_modules_1548_, v_val_1546_);
lean_dec(v_val_1546_);
lean_dec_ref(v_modules_1548_);
v___x_1552_ = lean_st_ref_get(v___y_1523_);
if (v_isMeta_1515_ == 0)
{
lean_dec(v___x_1552_);
v___y_1554_ = v_isMeta_1515_;
goto v___jp_1553_;
}
else
{
lean_object* v_env_1565_; uint8_t v___x_1566_; 
v_env_1565_ = lean_ctor_get(v___x_1552_, 0);
lean_inc_ref(v_env_1565_);
lean_dec(v___x_1552_);
lean_inc(v_declName_1514_);
v___x_1566_ = l_Lean_isMarkedMeta(v_env_1565_, v_declName_1514_);
if (v___x_1566_ == 0)
{
v___y_1554_ = v_isMeta_1515_;
goto v___jp_1553_;
}
else
{
uint8_t v___x_1567_; 
v___x_1567_ = 0;
v___y_1554_ = v___x_1567_;
goto v___jp_1553_;
}
}
v___jp_1553_:
{
lean_object* v_toImport_1555_; lean_object* v_module_1556_; lean_object* v___x_1557_; 
v_toImport_1555_ = lean_ctor_get(v___x_1551_, 0);
lean_inc_ref(v_toImport_1555_);
lean_dec(v___x_1551_);
v_module_1556_ = lean_ctor_get(v_toImport_1555_, 0);
lean_inc(v_module_1556_);
lean_dec_ref(v_toImport_1555_);
lean_inc(v_declName_1514_);
v___x_1557_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_module_1556_, v___y_1554_, v_declName_1514_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec_ref_known(v___x_1557_, 1);
v___x_1558_ = l_Lean_indirectModUseExt;
v___x_1559_ = lean_box(1);
v___x_1560_ = lean_box(0);
lean_inc_ref(v_env_1530_);
v___x_1561_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1525_, v___x_1558_, v_env_1530_, v___x_1559_, v___x_1560_);
v___x_1562_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v___x_1561_, v_declName_1514_);
lean_dec(v___x_1561_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1));
v___y_1532_ = v___x_1563_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1564_; 
v_val_1564_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v___x_1562_, 1);
v___y_1532_ = v_val_1564_;
goto v___jp_1531_;
}
}
else
{
lean_dec_ref(v_env_1530_);
lean_dec(v_declName_1514_);
return v___x_1557_;
}
}
}
}
v___jp_1527_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_box(0);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
v___jp_1531_:
{
lean_object* v___x_1533_; size_t v_sz_1534_; size_t v___x_1535_; lean_object* v___x_1536_; 
v___x_1533_ = lean_box(0);
v_sz_1534_ = lean_array_size(v___y_1532_);
v___x_1535_ = ((size_t)0ULL);
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(v_env_1530_, v_declName_1514_, v___y_1532_, v_sz_1534_, v___x_1535_, v___x_1533_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec_ref(v___y_1532_);
lean_dec_ref(v_env_1530_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v___x_1536_, 0);
lean_dec(v_unused_1544_);
v___x_1538_ = v___x_1536_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_dec(v___x_1536_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1533_);
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1533_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
else
{
return v___x_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___boxed(lean_object* v_declName_1568_, lean_object* v_isMeta_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
uint8_t v_isMeta_boxed_1579_; lean_object* v_res_1580_; 
v_isMeta_boxed_1579_ = lean_unbox(v_isMeta_1569_);
v_res_1580_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(v_declName_1568_, v_isMeta_boxed_1579_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(lean_object* v_as_x27_1581_, lean_object* v_b_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
if (lean_obj_tag(v_as_x27_1581_) == 0)
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v_b_1582_);
return v___x_1592_;
}
else
{
lean_object* v_head_1593_; lean_object* v_tail_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; lean_object* v___x_1597_; 
v_head_1593_ = lean_ctor_get(v_as_x27_1581_, 0);
v_tail_1594_ = lean_ctor_get(v_as_x27_1581_, 1);
v___x_1595_ = lean_box(0);
v___x_1596_ = 1;
lean_inc(v_head_1593_);
v___x_1597_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(v_head_1593_, v___x_1596_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_dec_ref_known(v___x_1597_, 1);
v_as_x27_1581_ = v_tail_1594_;
v_b_1582_ = v___x_1595_;
goto _start;
}
else
{
return v___x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg___boxed(lean_object* v_as_x27_1599_, lean_object* v_b_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_as_x27_1599_, v_b_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v_as_x27_1599_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(lean_object* v_env_1611_, lean_object* v___x_1612_, lean_object* v_currNamespace_1613_, lean_object* v_openDecls_1614_, lean_object* v_n_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = l_Lean_ResolveName_resolveGlobalName(v_env_1611_, v___x_1612_, v_currNamespace_1613_, v_openDecls_1614_, v_n_1615_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v___y_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed(lean_object* v_env_1620_, lean_object* v___x_1621_, lean_object* v_currNamespace_1622_, lean_object* v_openDecls_1623_, lean_object* v_n_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(v_env_1620_, v___x_1621_, v_currNamespace_1622_, v_openDecls_1623_, v_n_1624_, v___y_1625_, v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec_ref(v___x_1621_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(lean_object* v_env_1628_, lean_object* v_currNamespace_1629_, lean_object* v_openDecls_1630_, lean_object* v_n_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = l_Lean_ResolveName_resolveNamespace(v_env_1628_, v_currNamespace_1629_, v_openDecls_1630_, v_n_1631_);
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
lean_ctor_set(v___x_1635_, 1, v___y_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed(lean_object* v_env_1636_, lean_object* v_currNamespace_1637_, lean_object* v_openDecls_1638_, lean_object* v_n_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(v_env_1636_, v_currNamespace_1637_, v_openDecls_1638_, v_n_1639_, v___y_1640_, v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(lean_object* v_env_1643_, lean_object* v_declName_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
uint8_t v___x_1647_; lean_object* v_env_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; uint8_t v___x_1651_; 
v___x_1647_ = 0;
v_env_1648_ = l_Lean_Environment_setExporting(v_env_1643_, v___x_1647_);
lean_inc(v_declName_1644_);
v___x_1649_ = l_Lean_mkPrivateName(v_env_1648_, v_declName_1644_);
v___x_1650_ = 1;
lean_inc_ref(v_env_1648_);
v___x_1651_ = l_Lean_Environment_contains(v_env_1648_, v___x_1649_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1652_ = l_Lean_privateToUserName(v_declName_1644_);
v___x_1653_ = l_Lean_Environment_contains(v_env_1648_, v___x_1652_, v___x_1650_);
v___x_1654_ = lean_box(v___x_1653_);
v___x_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___y_1646_);
return v___x_1655_;
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_dec_ref(v_env_1648_);
lean_dec(v_declName_1644_);
v___x_1656_ = lean_box(v___x_1651_);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v___y_1646_);
return v___x_1657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed(lean_object* v_env_1658_, lean_object* v_declName_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(v_env_1658_, v_declName_1659_, v___y_1660_, v___y_1661_);
lean_dec_ref(v___y_1660_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(lean_object* v_as_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
if (lean_obj_tag(v_as_1663_) == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
else
{
lean_object* v_toCold_1671_; lean_object* v_options_1672_; uint8_t v_hasTrace_1673_; 
v_toCold_1671_ = lean_ctor_get(v___y_1666_, 0);
v_options_1672_ = lean_ctor_get(v_toCold_1671_, 2);
v_hasTrace_1673_ = lean_ctor_get_uint8(v_options_1672_, sizeof(void*)*1);
if (v_hasTrace_1673_ == 0)
{
lean_object* v_tail_1674_; 
v_tail_1674_ = lean_ctor_get(v_as_1663_, 1);
lean_inc(v_tail_1674_);
lean_dec_ref_known(v_as_1663_, 2);
v_as_1663_ = v_tail_1674_;
goto _start;
}
else
{
lean_object* v_head_1676_; lean_object* v_tail_1677_; lean_object* v_fst_1678_; lean_object* v_snd_1679_; lean_object* v_inheritedTraceOptions_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v_head_1676_ = lean_ctor_get(v_as_1663_, 0);
lean_inc(v_head_1676_);
v_tail_1677_ = lean_ctor_get(v_as_1663_, 1);
lean_inc(v_tail_1677_);
lean_dec_ref_known(v_as_1663_, 2);
v_fst_1678_ = lean_ctor_get(v_head_1676_, 0);
lean_inc_n(v_fst_1678_, 2);
v_snd_1679_ = lean_ctor_get(v_head_1676_, 1);
lean_inc(v_snd_1679_);
lean_dec(v_head_1676_);
v_inheritedTraceOptions_1680_ = lean_ctor_get(v_toCold_1671_, 11);
v___x_1681_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18));
v___x_1682_ = l_Lean_Name_append(v___x_1681_, v_fst_1678_);
v___x_1683_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1680_, v_options_1672_, v___x_1682_);
lean_dec(v___x_1682_);
if (v___x_1683_ == 0)
{
lean_dec(v_snd_1679_);
lean_dec(v_fst_1678_);
v_as_1663_ = v_tail_1677_;
goto _start;
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_snd_1679_);
v___x_1686_ = l_Lean_MessageData_ofFormat(v___x_1685_);
v___x_1687_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_fst_1678_, v___x_1686_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_dec_ref_known(v___x_1687_, 1);
v_as_1663_ = v_tail_1677_;
goto _start;
}
else
{
lean_dec(v_tail_1677_);
return v___x_1687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg___boxed(lean_object* v_as_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v_as_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(lean_object* v_x_1696_, lean_object* v___y_1697_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1699_; 
v_a_1698_ = lean_ctor_get(v_x_1696_, 0);
lean_inc(v_a_1698_);
v___x_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_a_1698_);
lean_ctor_set(v___x_1699_, 1, v___y_1697_);
return v___x_1699_;
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1701_; 
v_a_1700_ = lean_ctor_get(v_x_1696_, 0);
lean_inc(v_a_1700_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_a_1700_);
lean_ctor_set(v___x_1701_, 1, v___y_1697_);
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg___boxed(lean_object* v_x_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v_x_1702_, v___y_1703_);
lean_dec_ref(v_x_1702_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(lean_object* v_env_1705_, lean_object* v_stx_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1705_, v_stx_1706_, v___y_1707_, v___y_1708_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
if (lean_obj_tag(v_a_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1719_; 
v_a_1711_ = lean_ctor_get(v___x_1709_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; 
v_unused_1720_ = lean_ctor_get(v___x_1709_, 0);
lean_dec(v_unused_1720_);
v___x_1713_ = v___x_1709_;
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1709_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = lean_box(0);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1715_);
v___x_1717_ = v___x_1713_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_a_1711_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
else
{
lean_object* v_val_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1749_; 
v_val_1721_ = lean_ctor_get(v_a_1710_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_a_1710_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1723_ = v_a_1710_;
v_isShared_1724_ = v_isSharedCheck_1749_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_val_1721_);
lean_dec(v_a_1710_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1749_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_snd_1725_; 
v_snd_1725_ = lean_ctor_get(v_val_1721_, 1);
lean_inc(v_snd_1725_);
lean_dec(v_val_1721_);
if (lean_obj_tag(v_snd_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1735_; 
lean_del_object(v___x_1723_);
v_a_1726_ = lean_ctor_get(v___x_1709_, 1);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1709_, 2);
v_a_1727_ = lean_ctor_get(v_snd_1725_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_snd_1725_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1729_ = v_snd_1725_;
v_isShared_1730_ = v_isSharedCheck_1735_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v_snd_1725_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1735_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v___x_1732_, v_a_1726_);
lean_dec_ref(v___x_1732_);
return v___x_1733_;
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1748_; 
v_a_1736_ = lean_ctor_get(v___x_1709_, 1);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1709_, 2);
v_a_1737_ = lean_ctor_get(v_snd_1725_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_snd_1725_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1739_ = v_snd_1725_;
v_isShared_1740_ = v_isSharedCheck_1748_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v_snd_1725_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1748_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v_a_1737_);
v___x_1742_ = v___x_1723_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1744_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1742_);
v___x_1744_ = v___x_1739_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v___x_1744_, v_a_1736_);
lean_dec_ref(v___x_1744_);
return v___x_1745_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
v_a_1750_ = lean_ctor_get(v___x_1709_, 0);
v_a_1751_ = lean_ctor_get(v___x_1709_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1709_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_inc(v_a_1750_);
lean_dec(v___x_1709_);
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
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1750_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_a_1751_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed(lean_object* v_env_1759_, lean_object* v_stx_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(v_env_1759_, v_stx_1760_, v___y_1761_, v___y_1762_);
lean_dec_ref(v___y_1761_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(lean_object* v_currNamespace_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_currNamespace_1764_);
lean_ctor_set(v___x_1767_, 1, v___y_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(v_currNamespace_1768_, v___y_1769_, v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(lean_object* v_x_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; lean_object* v_toCold_1784_; lean_object* v_env_1785_; lean_object* v_currRecDepth_1786_; lean_object* v_ref_1787_; lean_object* v_maxRecDepth_1788_; lean_object* v_currNamespace_1789_; lean_object* v_openDecls_1790_; lean_object* v_quotContext_1791_; lean_object* v_currMacroScope_1792_; lean_object* v___f_1793_; lean_object* v___f_1794_; lean_object* v___x_1795_; lean_object* v___f_1796_; lean_object* v___f_1797_; lean_object* v___f_1798_; lean_object* v_methods_1799_; lean_object* v___x_1800_; lean_object* v_nextMacroScope_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1783_ = lean_st_ref_get(v___y_1781_);
v_toCold_1784_ = lean_ctor_get(v___y_1780_, 0);
v_env_1785_ = lean_ctor_get(v___x_1783_, 0);
lean_inc_ref_n(v_env_1785_, 4);
lean_dec(v___x_1783_);
v_currRecDepth_1786_ = lean_ctor_get(v___y_1780_, 1);
v_ref_1787_ = lean_ctor_get(v___y_1780_, 2);
v_maxRecDepth_1788_ = lean_ctor_get(v_toCold_1784_, 3);
v_currNamespace_1789_ = lean_ctor_get(v_toCold_1784_, 4);
v_openDecls_1790_ = lean_ctor_get(v_toCold_1784_, 5);
v_quotContext_1791_ = lean_ctor_get(v_toCold_1784_, 8);
v_currMacroScope_1792_ = lean_ctor_get(v_toCold_1784_, 9);
v___f_1793_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1793_, 0, v_env_1785_);
v___f_1794_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1794_, 0, v_env_1785_);
v___x_1795_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1780_);
lean_inc_n(v_currNamespace_1789_, 3);
v___f_1796_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1796_, 0, v_currNamespace_1789_);
lean_inc_n(v_openDecls_1790_, 2);
v___f_1797_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1797_, 0, v_env_1785_);
lean_closure_set(v___f_1797_, 1, v___x_1795_);
lean_closure_set(v___f_1797_, 2, v_currNamespace_1789_);
lean_closure_set(v___f_1797_, 3, v_openDecls_1790_);
v___f_1798_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1798_, 0, v_env_1785_);
lean_closure_set(v___f_1798_, 1, v_currNamespace_1789_);
lean_closure_set(v___f_1798_, 2, v_openDecls_1790_);
v_methods_1799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1799_, 0, v___f_1794_);
lean_ctor_set(v_methods_1799_, 1, v___f_1796_);
lean_ctor_set(v_methods_1799_, 2, v___f_1793_);
lean_ctor_set(v_methods_1799_, 3, v___f_1798_);
lean_ctor_set(v_methods_1799_, 4, v___f_1797_);
v___x_1800_ = lean_st_ref_get(v___y_1781_);
v_nextMacroScope_1801_ = lean_ctor_get(v___x_1800_, 1);
lean_inc(v_nextMacroScope_1801_);
lean_dec(v___x_1800_);
lean_inc(v_ref_1787_);
lean_inc(v_maxRecDepth_1788_);
lean_inc(v_currRecDepth_1786_);
lean_inc(v_currMacroScope_1792_);
lean_inc(v_quotContext_1791_);
v___x_1802_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1802_, 0, v_methods_1799_);
lean_ctor_set(v___x_1802_, 1, v_quotContext_1791_);
lean_ctor_set(v___x_1802_, 2, v_currMacroScope_1792_);
lean_ctor_set(v___x_1802_, 3, v_currRecDepth_1786_);
lean_ctor_set(v___x_1802_, 4, v_maxRecDepth_1788_);
lean_ctor_set(v___x_1802_, 5, v_ref_1787_);
v___x_1803_ = lean_box(0);
v___x_1804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1804_, 0, v_nextMacroScope_1801_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
lean_ctor_set(v___x_1804_, 2, v___x_1803_);
v___x_1805_ = lean_apply_2(v_x_1773_, v___x_1802_, v___x_1804_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v_a_1807_; lean_object* v_macroScope_1808_; lean_object* v_traceMsgs_1809_; lean_object* v_expandedMacroDecls_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 1);
lean_inc(v_a_1806_);
v_a_1807_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1807_);
lean_dec_ref_known(v___x_1805_, 2);
v_macroScope_1808_ = lean_ctor_get(v_a_1806_, 0);
lean_inc(v_macroScope_1808_);
v_traceMsgs_1809_ = lean_ctor_get(v_a_1806_, 1);
lean_inc(v_traceMsgs_1809_);
v_expandedMacroDecls_1810_ = lean_ctor_get(v_a_1806_, 2);
lean_inc(v_expandedMacroDecls_1810_);
lean_dec(v_a_1806_);
v___x_1811_ = lean_box(0);
v___x_1812_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_expandedMacroDecls_1810_, v___x_1811_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v_expandedMacroDecls_1810_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1813_; lean_object* v_env_1814_; lean_object* v_ngen_1815_; lean_object* v_auxDeclNGen_1816_; lean_object* v_traceState_1817_; lean_object* v_cache_1818_; lean_object* v_recordedDeps_1819_; lean_object* v_messages_1820_; lean_object* v_infoState_1821_; lean_object* v_snapshotTasks_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1848_; 
lean_dec_ref_known(v___x_1812_, 1);
v___x_1813_ = lean_st_ref_take(v___y_1781_);
v_env_1814_ = lean_ctor_get(v___x_1813_, 0);
v_ngen_1815_ = lean_ctor_get(v___x_1813_, 2);
v_auxDeclNGen_1816_ = lean_ctor_get(v___x_1813_, 3);
v_traceState_1817_ = lean_ctor_get(v___x_1813_, 4);
v_cache_1818_ = lean_ctor_get(v___x_1813_, 5);
v_recordedDeps_1819_ = lean_ctor_get(v___x_1813_, 6);
v_messages_1820_ = lean_ctor_get(v___x_1813_, 7);
v_infoState_1821_ = lean_ctor_get(v___x_1813_, 8);
v_snapshotTasks_1822_ = lean_ctor_get(v___x_1813_, 9);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v___x_1813_, 1);
lean_dec(v_unused_1849_);
v___x_1824_ = v___x_1813_;
v_isShared_1825_ = v_isSharedCheck_1848_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_snapshotTasks_1822_);
lean_inc(v_infoState_1821_);
lean_inc(v_messages_1820_);
lean_inc(v_recordedDeps_1819_);
lean_inc(v_cache_1818_);
lean_inc(v_traceState_1817_);
lean_inc(v_auxDeclNGen_1816_);
lean_inc(v_ngen_1815_);
lean_inc(v_env_1814_);
lean_dec(v___x_1813_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1848_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 1, v_macroScope_1808_);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_env_1814_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_macroScope_1808_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_ngen_1815_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_auxDeclNGen_1816_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v_traceState_1817_);
lean_ctor_set(v_reuseFailAlloc_1847_, 5, v_cache_1818_);
lean_ctor_set(v_reuseFailAlloc_1847_, 6, v_recordedDeps_1819_);
lean_ctor_set(v_reuseFailAlloc_1847_, 7, v_messages_1820_);
lean_ctor_set(v_reuseFailAlloc_1847_, 8, v_infoState_1821_);
lean_ctor_set(v_reuseFailAlloc_1847_, 9, v_snapshotTasks_1822_);
v___x_1827_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = lean_st_ref_put(v___y_1781_, v___x_1827_);
v___x_1829_ = l_List_reverse___redArg(v_traceMsgs_1809_);
v___x_1830_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v___x_1829_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v___x_1830_, 0);
lean_dec(v_unused_1838_);
v___x_1832_ = v___x_1830_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_dec(v___x_1830_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v_a_1807_);
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1807_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_a_1807_);
v_a_1839_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1830_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1830_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec(v_traceMsgs_1809_);
lean_dec(v_macroScope_1808_);
lean_dec(v_a_1807_);
v_a_1850_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1812_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1812_);
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
else
{
lean_object* v_a_1858_; 
v_a_1858_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1805_, 2);
if (lean_obj_tag(v_a_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v_a_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v_a_1859_ = lean_ctor_get(v_a_1858_, 0);
lean_inc(v_a_1859_);
v_a_1860_ = lean_ctor_get(v_a_1858_, 1);
lean_inc_ref(v_a_1860_);
lean_dec_ref_known(v_a_1858_, 2);
v___x_1861_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0));
v___x_1862_ = lean_string_dec_eq(v_a_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_a_1860_);
v___x_1864_ = l_Lean_MessageData_ofFormat(v___x_1863_);
v___x_1865_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_a_1859_, v___x_1864_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v_a_1859_);
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; 
lean_dec_ref(v_a_1860_);
v___x_1866_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_a_1859_);
return v___x_1866_;
}
}
else
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_1867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___boxed(lean_object* v_x_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(v_x_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(lean_object* v_x_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3));
lean_inc(v_x_1889_);
v___x_1900_ = l_Lean_Syntax_isOfKind(v_x_1889_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; 
lean_dec(v_x_1889_);
v___x_1901_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_1901_;
}
else
{
lean_object* v___x_1902_; lean_object* v_pat_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1902_ = lean_unsigned_to_nat(1u);
v_pat_1903_ = l_Lean_Syntax_getArg(v_x_1889_, v___x_1902_);
lean_dec(v_x_1889_);
v___x_1904_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_MRefinePat_parse___boxed), 3, 1);
lean_closure_set(v___x_1904_, 0, v_pat_1903_);
v___x_1905_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(v___x_1904_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1907_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1891_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v_fst_1909_; lean_object* v_snd_1910_; lean_object* v___x_1911_; lean_object* v___f_1912_; lean_object* v___x_1913_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v_fst_1909_ = lean_ctor_get(v_a_1908_, 0);
lean_inc_n(v_fst_1909_, 2);
v_snd_1910_ = lean_ctor_get(v_a_1908_, 1);
lean_inc(v_snd_1910_);
lean_dec(v_a_1908_);
v___x_1911_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4));
v___f_1912_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1___boxed), 13, 4);
lean_closure_set(v___f_1912_, 0, v___x_1911_);
lean_closure_set(v___f_1912_, 1, v_snd_1910_);
lean_closure_set(v___f_1912_, 2, v_a_1906_);
lean_closure_set(v___f_1912_, 3, v_fst_1909_);
v___x_1913_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_fst_1909_, v___f_1912_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
return v___x_1913_;
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_a_1906_);
v_a_1914_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1907_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1907_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
v_a_1922_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1905_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1905_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___boxed(lean_object* v_x_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(v_x_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0(lean_object* v_00_u03b1_1941_, lean_object* v_x_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v_x_1942_, v___y_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_x_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0(v_00_u03b1_1946_, v_x_1947_, v___y_1948_, v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec_ref(v_x_1947_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5(lean_object* v_00_u03b1_1951_, lean_object* v_ref_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_ref_1952_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1963_, lean_object* v_ref_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5(v_00_u03b1_1963_, v_ref_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0(lean_object* v_00_u03b1_1975_, lean_object* v_x_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(v_x_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___boxed(lean_object* v_00_u03b1_1987_, lean_object* v_x_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0(v_00_u03b1_1987_, v_x_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1(lean_object* v_mvarId_1999_, lean_object* v_val_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(v_mvarId_1999_, v_val_2000_, v___y_2006_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___boxed(lean_object* v_mvarId_2011_, lean_object* v_val_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1(v_mvarId_2011_, v_val_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2(lean_object* v_as_2023_, lean_object* v_as_x27_2024_, lean_object* v_b_2025_, lean_object* v_a_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_as_x27_2024_, v_b_2025_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___boxed(lean_object* v_as_2037_, lean_object* v_as_x27_2038_, lean_object* v_b_2039_, lean_object* v_a_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2(v_as_2037_, v_as_x27_2038_, v_b_2039_, v_a_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v_as_x27_2038_);
lean_dec(v_as_2037_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3(lean_object* v_as_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v_as_2051_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___boxed(lean_object* v_as_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3(v_as_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4(lean_object* v_00_u03b1_2073_, lean_object* v_ref_2074_, lean_object* v_msg_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_ref_2074_, v_msg_2075_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2086_, lean_object* v_ref_2087_, lean_object* v_msg_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4(v_00_u03b1_2086_, v_ref_2087_, v_msg_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v_ref_2087_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7(lean_object* v_00_u03b2_2099_, lean_object* v_x_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(v_x_2100_, v_x_2101_, v_x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3(lean_object* v_mod_2104_, uint8_t v_isMeta_2105_, lean_object* v_hint_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_mod_2104_, v_isMeta_2105_, v_hint_2106_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___boxed(lean_object* v_mod_2117_, lean_object* v_isMeta_2118_, lean_object* v_hint_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
uint8_t v_isMeta_boxed_2129_; lean_object* v_res_2130_; 
v_isMeta_boxed_2129_ = lean_unbox(v_isMeta_2118_);
v_res_2130_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3(v_mod_2117_, v_isMeta_boxed_2129_, v_hint_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_2131_, lean_object* v_m_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v_m_2132_, v_a_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_2135_, lean_object* v_m_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5(v_00_u03b2_2135_, v_m_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_m_2136_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2139_, lean_object* v_x_2140_, size_t v_x_2141_, size_t v_x_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_2140_, v_x_2141_, v_x_2142_, v_x_2143_, v_x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___boxed(lean_object* v_00_u03b2_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_, lean_object* v_x_2151_){
_start:
{
size_t v_x_19572__boxed_2152_; size_t v_x_19573__boxed_2153_; lean_object* v_res_2154_; 
v_x_19572__boxed_2152_ = lean_unbox_usize(v_x_2148_);
lean_dec(v_x_2148_);
v_x_19573__boxed_2153_ = lean_unbox_usize(v_x_2149_);
lean_dec(v_x_2149_);
v_res_2154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12(v_00_u03b2_2146_, v_x_2147_, v_x_19572__boxed_2152_, v_x_19573__boxed_2153_, v_x_2150_, v_x_2151_);
return v_res_2154_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_){
_start:
{
uint8_t v___x_2158_; 
v___x_2158_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v_x_2156_, v_x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_){
_start:
{
uint8_t v_res_2162_; lean_object* v_r_2163_; 
v_res_2162_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6(v_00_u03b2_2159_, v_x_2160_, v_x_2161_);
lean_dec_ref(v_x_2161_);
lean_dec_ref(v_x_2160_);
v_r_2163_ = lean_box(v_res_2162_);
return v_r_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7_spec__13(lean_object* v_00_u03b2_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7___redArg(){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v___dummy_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7___redArg();
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_2172_, lean_object* v_a_2173_, lean_object* v_x_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10___redArg(v_a_2173_, v_x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2176_, lean_object* v_a_2177_, lean_object* v_x_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__10(v_00_u03b2_2176_, v_a_2177_, v_x_2178_);
lean_dec(v_x_2178_);
lean_dec(v_a_2177_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16(lean_object* v_00_u03b2_2180_, lean_object* v_n_2181_, lean_object* v_k_2182_, lean_object* v_v_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_n_2181_, v_k_2182_, v_v_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17(lean_object* v_00_u03b2_2185_, size_t v_depth_2186_, lean_object* v_keys_2187_, lean_object* v_vals_2188_, lean_object* v_heq_2189_, lean_object* v_i_2190_, lean_object* v_entries_2191_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17___redArg(v_depth_2186_, v_keys_2187_, v_vals_2188_, v_i_2190_, v_entries_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17___boxed(lean_object* v_00_u03b2_2193_, lean_object* v_depth_2194_, lean_object* v_keys_2195_, lean_object* v_vals_2196_, lean_object* v_heq_2197_, lean_object* v_i_2198_, lean_object* v_entries_2199_){
_start:
{
size_t v_depth_boxed_2200_; lean_object* v_res_2201_; 
v_depth_boxed_2200_ = lean_unbox_usize(v_depth_2194_);
lean_dec(v_depth_2194_);
v_res_2201_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__17(v_00_u03b2_2193_, v_depth_boxed_2200_, v_keys_2195_, v_vals_2196_, v_heq_2197_, v_i_2198_, v_entries_2199_);
lean_dec_ref(v_vals_2196_);
lean_dec_ref(v_keys_2195_);
return v_res_2201_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(lean_object* v_00_u03b2_2202_, lean_object* v_x_2203_, size_t v_x_2204_, lean_object* v_x_2205_){
_start:
{
uint8_t v___x_2206_; 
v___x_2206_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_2203_, v_x_2204_, v_x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___boxed(lean_object* v_00_u03b2_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
size_t v_x_19615__boxed_2211_; uint8_t v_res_2212_; lean_object* v_r_2213_; 
v_x_19615__boxed_2211_ = lean_unbox_usize(v_x_2209_);
lean_dec(v_x_2209_);
v_res_2212_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(v_00_u03b2_2207_, v_x_2208_, v_x_19615__boxed_2211_, v_x_2210_);
lean_dec_ref(v_x_2210_);
lean_dec_ref(v_x_2208_);
v_r_2213_ = lean_box(v_res_2212_);
return v_r_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16_spec__19(lean_object* v_00_u03b2_2214_, lean_object* v_x_2215_, lean_object* v_x_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16_spec__19___redArg(v_x_2215_, v_x_2216_, v_x_2217_, v_x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15(lean_object* v_00_u03b2_2220_, lean_object* v_keys_2221_, lean_object* v_vals_2222_, lean_object* v_heq_2223_, lean_object* v_i_2224_, lean_object* v_k_2225_){
_start:
{
uint8_t v___x_2226_; 
v___x_2226_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_keys_2221_, v_i_2224_, v_k_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2227_, lean_object* v_keys_2228_, lean_object* v_vals_2229_, lean_object* v_heq_2230_, lean_object* v_i_2231_, lean_object* v_k_2232_){
_start:
{
uint8_t v_res_2233_; lean_object* v_r_2234_; 
v_res_2233_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15(v_00_u03b2_2227_, v_keys_2228_, v_vals_2229_, v_heq_2230_, v_i_2231_, v_k_2232_);
lean_dec_ref(v_k_2232_);
lean_dec_ref(v_vals_2229_);
lean_dec_ref(v_keys_2228_);
v_r_2234_ = lean_box(v_res_2233_);
return v_r_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1(){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2246_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2247_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3));
v___x_2248_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3));
v___x_2249_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___boxed), 10, 0);
v___x_2250_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2246_, v___x_2247_, v___x_2248_, v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___boxed(lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1();
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(lean_object* v_as_2271_, size_t v_i_2272_, size_t v_stop_2273_, lean_object* v_b_2274_, lean_object* v___y_2275_){
_start:
{
uint8_t v___x_2277_; 
v___x_2277_ = lean_usize_dec_eq(v_i_2272_, v_stop_2273_);
if (v___x_2277_ == 0)
{
lean_object* v_ref_2278_; lean_object* v___x_2279_; size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_ref_2278_ = lean_ctor_get(v___y_2275_, 2);
v___x_2279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0));
v___x_2280_ = ((size_t)1ULL);
v___x_2281_ = lean_usize_sub(v_i_2272_, v___x_2280_);
v___x_2282_ = lean_array_uget_borrowed(v_as_2271_, v___x_2281_);
v___x_2283_ = l_Lean_SourceInfo_fromRef(v_ref_2278_, v___x_2277_);
v___x_2284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2));
v___x_2285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3));
lean_inc_n(v___x_2283_, 5);
v___x_2286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2283_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5));
v___x_2288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7));
v___x_2289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2283_);
lean_ctor_set(v___x_2289_, 1, v___x_2279_);
lean_inc(v___x_2282_);
v___x_2290_ = l_Lean_Syntax_node3(v___x_2283_, v___x_2288_, v___x_2282_, v___x_2289_, v_b_2274_);
v___x_2291_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2287_, v___x_2290_);
v___x_2292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8));
v___x_2293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2283_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_Syntax_node3(v___x_2283_, v___x_2284_, v___x_2286_, v___x_2291_, v___x_2293_);
v_i_2272_ = v___x_2281_;
v_b_2274_ = v___x_2294_;
goto _start;
}
else
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v_b_2274_);
return v___x_2296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___boxed(lean_object* v_as_2297_, lean_object* v_i_2298_, lean_object* v_stop_2299_, lean_object* v_b_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
size_t v_i_boxed_2303_; size_t v_stop_boxed_2304_; lean_object* v_res_2305_; 
v_i_boxed_2303_ = lean_unbox_usize(v_i_2298_);
lean_dec(v_i_2298_);
v_stop_boxed_2304_ = lean_unbox_usize(v_stop_2299_);
lean_dec(v_stop_2299_);
v_res_2305_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_2297_, v_i_boxed_2303_, v_stop_boxed_2304_, v_b_2300_, v___y_2301_);
lean_dec_ref(v___y_2301_);
lean_dec_ref(v_as_2297_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(lean_object* v_as_2306_, size_t v_i_2307_, size_t v_stop_2308_, lean_object* v_b_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_usize_dec_eq(v_i_2307_, v_stop_2308_);
if (v___x_2319_ == 0)
{
lean_object* v_ref_2320_; lean_object* v___x_2321_; size_t v___x_2322_; size_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_ref_2320_ = lean_ctor_get(v___y_2316_, 2);
v___x_2321_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0));
v___x_2322_ = ((size_t)1ULL);
v___x_2323_ = lean_usize_sub(v_i_2307_, v___x_2322_);
v___x_2324_ = lean_array_uget_borrowed(v_as_2306_, v___x_2323_);
v___x_2325_ = l_Lean_SourceInfo_fromRef(v_ref_2320_, v___x_2319_);
v___x_2326_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2));
v___x_2327_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3));
lean_inc_n(v___x_2325_, 5);
v___x_2328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2325_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5));
v___x_2330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7));
v___x_2331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2325_);
lean_ctor_set(v___x_2331_, 1, v___x_2321_);
lean_inc(v___x_2324_);
v___x_2332_ = l_Lean_Syntax_node3(v___x_2325_, v___x_2330_, v___x_2324_, v___x_2331_, v_b_2309_);
v___x_2333_ = l_Lean_Syntax_node1(v___x_2325_, v___x_2329_, v___x_2332_);
v___x_2334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8));
v___x_2335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2325_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = l_Lean_Syntax_node3(v___x_2325_, v___x_2326_, v___x_2328_, v___x_2333_, v___x_2335_);
v___x_2337_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_2306_, v___x_2323_, v_stop_2308_, v___x_2336_, v___y_2316_);
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v_b_2309_);
return v___x_2338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___boxed(lean_object* v_as_2339_, lean_object* v_i_2340_, lean_object* v_stop_2341_, lean_object* v_b_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
size_t v_i_boxed_2352_; size_t v_stop_boxed_2353_; lean_object* v_res_2354_; 
v_i_boxed_2352_ = lean_unbox_usize(v_i_2340_);
lean_dec(v_i_2340_);
v_stop_boxed_2353_ = lean_unbox_usize(v_stop_2341_);
lean_dec(v_stop_2341_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(v_as_2339_, v_i_boxed_2352_, v_stop_boxed_2353_, v_b_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec_ref(v_as_2339_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(size_t v_sz_2363_, size_t v_i_2364_, lean_object* v_bs_2365_, lean_object* v___y_2366_){
_start:
{
uint8_t v___x_2368_; 
v___x_2368_ = lean_usize_dec_lt(v_i_2364_, v_sz_2363_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v_bs_2365_);
return v___x_2369_;
}
else
{
lean_object* v_ref_2370_; lean_object* v_v_2371_; lean_object* v___x_2372_; lean_object* v_bs_x27_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; size_t v___x_2382_; size_t v___x_2383_; lean_object* v___x_2384_; 
v_ref_2370_ = lean_ctor_get(v___y_2366_, 2);
v_v_2371_ = lean_array_uget(v_bs_2365_, v_i_2364_);
v___x_2372_ = lean_unsigned_to_nat(0u);
v_bs_x27_2373_ = lean_array_uset(v_bs_2365_, v_i_2364_, v___x_2372_);
v___x_2374_ = 0;
v___x_2375_ = l_Lean_SourceInfo_fromRef(v_ref_2370_, v___x_2374_);
v___x_2376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1));
v___x_2377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2));
lean_inc_n(v___x_2375_, 2);
v___x_2378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2375_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3));
v___x_2380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2375_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = l_Lean_Syntax_node3(v___x_2375_, v___x_2376_, v___x_2378_, v_v_2371_, v___x_2380_);
v___x_2382_ = ((size_t)1ULL);
v___x_2383_ = lean_usize_add(v_i_2364_, v___x_2382_);
v___x_2384_ = lean_array_uset(v_bs_x27_2373_, v_i_2364_, v___x_2381_);
v_i_2364_ = v___x_2383_;
v_bs_2365_ = v___x_2384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___boxed(lean_object* v_sz_2386_, lean_object* v_i_2387_, lean_object* v_bs_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
size_t v_sz_boxed_2391_; size_t v_i_boxed_2392_; lean_object* v_res_2393_; 
v_sz_boxed_2391_ = lean_unbox_usize(v_sz_2386_);
lean_dec(v_sz_2386_);
v_i_boxed_2392_ = lean_unbox_usize(v_i_2387_);
lean_dec(v_i_2387_);
v_res_2393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_boxed_2391_, v_i_boxed_2392_, v_bs_2388_, v___y_2389_);
lean_dec_ref(v___y_2389_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(lean_object* v_x_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2459_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1));
lean_inc(v_x_2449_);
v___x_2460_ = l_Lean_Syntax_isOfKind(v_x_2449_, v___x_2459_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
lean_dec(v_x_2449_);
v___x_2461_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_2461_;
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v_args_2465_; lean_object* v___x_2466_; size_t v_sz_2467_; size_t v___x_2468_; lean_object* v___x_2469_; 
v___x_2462_ = lean_unsigned_to_nat(0u);
v___x_2463_ = lean_unsigned_to_nat(1u);
v___x_2464_ = l_Lean_Syntax_getArg(v_x_2449_, v___x_2463_);
lean_dec(v_x_2449_);
v_args_2465_ = l_Lean_Syntax_getArgs(v___x_2464_);
lean_dec(v___x_2464_);
v___x_2466_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_args_2465_);
lean_dec_ref(v_args_2465_);
v_sz_2467_ = lean_array_size(v___x_2466_);
v___x_2468_ = ((size_t)0ULL);
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_2467_, v___x_2468_, v___x_2466_, v_a_2456_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v_ref_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; lean_object* v_a_2475_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
v_ref_2471_ = lean_ctor_get(v_a_2456_, 2);
v___x_2472_ = 0;
v___x_2473_ = l_Lean_SourceInfo_fromRef(v_ref_2471_, v___x_2472_);
v___x_2506_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17));
v___x_2507_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18));
lean_inc_n(v___x_2473_, 5);
v___x_2508_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2473_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2));
v___x_2510_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21));
v___x_2511_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22));
v___x_2512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2473_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = l_Lean_Syntax_node1(v___x_2473_, v___x_2510_, v___x_2512_);
v___x_2514_ = l_Lean_Syntax_node1(v___x_2473_, v___x_2509_, v___x_2513_);
v___x_2515_ = l_Lean_Syntax_node2(v___x_2473_, v___x_2506_, v___x_2508_, v___x_2514_);
v___x_2516_ = lean_array_get_size(v_a_2470_);
v___x_2517_ = lean_nat_dec_lt(v___x_2462_, v___x_2516_);
if (v___x_2517_ == 0)
{
lean_dec(v_a_2470_);
v_a_2475_ = v___x_2515_;
goto v___jp_2474_;
}
else
{
size_t v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = lean_usize_of_nat(v___x_2516_);
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(v_a_2470_, v___x_2518_, v___x_2468_, v___x_2515_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
lean_dec(v_a_2470_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v_a_2475_ = v_a_2520_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec(v___x_2473_);
v_a_2521_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2519_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2519_);
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
v___jp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2476_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3));
v___x_2477_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4));
lean_inc_n(v___x_2473_, 15);
v___x_2478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2473_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6));
v___x_2480_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8));
v___x_2481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7));
v___x_2482_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2));
v___x_2483_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3));
v___x_2484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2473_);
lean_ctor_set(v___x_2484_, 1, v___x_2482_);
v___x_2485_ = l_Lean_Syntax_node2(v___x_2473_, v___x_2483_, v___x_2484_, v_a_2475_);
v___x_2486_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9));
v___x_2487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2473_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11));
v___x_2489_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12));
v___x_2490_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2473_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13));
v___x_2492_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14));
v___x_2493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2473_);
lean_ctor_set(v___x_2493_, 1, v___x_2491_);
v___x_2494_ = l_Lean_Syntax_node1(v___x_2473_, v___x_2492_, v___x_2493_);
v___x_2495_ = l_Lean_Syntax_node1(v___x_2473_, v___x_2481_, v___x_2494_);
v___x_2496_ = l_Lean_Syntax_node1(v___x_2473_, v___x_2480_, v___x_2495_);
v___x_2497_ = l_Lean_Syntax_node1(v___x_2473_, v___x_2479_, v___x_2496_);
v___x_2498_ = l_Lean_Syntax_node2(v___x_2473_, v___x_2488_, v___x_2490_, v___x_2497_);
v___x_2499_ = l_Lean_Syntax_node3(v___x_2473_, v___x_2481_, v___x_2485_, v___x_2487_, v___x_2498_);
v___x_2500_ = l_Lean_Syntax_node1(v___x_2473_, v___x_2480_, v___x_2499_);
v___x_2501_ = l_Lean_Syntax_node1(v___x_2473_, v___x_2479_, v___x_2500_);
v___x_2502_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15));
v___x_2503_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2473_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l_Lean_Syntax_node3(v___x_2473_, v___x_2476_, v___x_2478_, v___x_2501_, v___x_2503_);
v___x_2505_ = l_Lean_Elab_Tactic_evalTactic(v___x_2504_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
return v___x_2505_;
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
v_a_2529_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2469_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2469_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___boxed(lean_object* v_x_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(v_x_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(size_t v_sz_2548_, size_t v_i_2549_, lean_object* v_bs_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_2548_, v_i_2549_, v_bs_2550_, v___y_2557_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___boxed(lean_object* v_sz_2561_, lean_object* v_i_2562_, lean_object* v_bs_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
size_t v_sz_boxed_2573_; size_t v_i_boxed_2574_; lean_object* v_res_2575_; 
v_sz_boxed_2573_ = lean_unbox_usize(v_sz_2561_);
lean_dec(v_sz_2561_);
v_i_boxed_2574_ = lean_unbox_usize(v_i_2562_);
lean_dec(v_i_2562_);
v_res_2575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(v_sz_boxed_2573_, v_i_boxed_2574_, v_bs_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1(lean_object* v_as_2576_, size_t v_i_2577_, size_t v_stop_2578_, lean_object* v_b_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_2576_, v_i_2577_, v_stop_2578_, v_b_2579_, v___y_2586_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___boxed(lean_object* v_as_2590_, lean_object* v_i_2591_, lean_object* v_stop_2592_, lean_object* v_b_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
size_t v_i_boxed_2603_; size_t v_stop_boxed_2604_; lean_object* v_res_2605_; 
v_i_boxed_2603_ = lean_unbox_usize(v_i_2591_);
lean_dec(v_i_2591_);
v_stop_boxed_2604_ = lean_unbox_usize(v_stop_2592_);
lean_dec(v_stop_2592_);
v_res_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1(v_as_2590_, v_i_boxed_2603_, v_stop_boxed_2604_, v_b_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec_ref(v_as_2590_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1(){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2615_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2616_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1));
v___x_2617_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1));
v___x_2618_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___boxed), 10, 0);
v___x_2619_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2615_, v___x_2616_, v___x_2617_, v___x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___boxed(lean_object* v_a_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1();
return v_res_2621_;
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
