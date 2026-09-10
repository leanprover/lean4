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
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1_value;
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
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_t_21_; lean_object* v___y_22_; lean_object* v___y_23_; lean_object* v___y_24_; lean_object* v___y_25_; lean_object* v___y_26_; lean_object* v___y_27_; lean_object* v___y_28_; lean_object* v___y_29_; 
switch(lean_obj_tag(v_pat_9_))
{
case 2:
{
lean_object* v_h_49_; 
v_h_49_ = lean_ctor_get(v_pat_9_, 0);
lean_inc(v_h_49_);
lean_dec_ref_known(v_pat_9_, 1);
v_t_21_ = v_h_49_;
v___y_22_ = v_a_11_;
v___y_23_ = v_a_12_;
v___y_24_ = v_a_13_;
v___y_25_ = v_a_14_;
v___y_26_ = v_a_15_;
v___y_27_ = v_a_16_;
v___y_28_ = v_a_17_;
v___y_29_ = v_a_18_;
goto v___jp_20_;
}
case 0:
{
lean_object* v_name_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_68_; 
v_name_50_ = lean_ctor_get(v_pat_9_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v_pat_9_);
if (v_isSharedCheck_68_ == 0)
{
v___x_52_ = v_pat_9_;
v_isShared_53_ = v_isSharedCheck_68_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_name_50_);
lean_dec(v_pat_9_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_68_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2));
lean_inc(v_name_50_);
v___x_55_ = l_Lean_Syntax_isOfKind(v_name_50_, v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_58_; 
lean_dec(v_name_50_);
lean_dec(v_expected_10_);
v___x_56_ = lean_box(0);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 0, v___x_56_);
v___x_58_ = v___x_52_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
else
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = l_Lean_Syntax_getArg(v_name_50_, v___x_60_);
lean_dec(v_name_50_);
v___x_62_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4));
lean_inc(v___x_61_);
v___x_63_ = l_Lean_Syntax_isOfKind(v___x_61_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_66_; 
lean_dec(v___x_61_);
lean_dec(v_expected_10_);
v___x_64_ = lean_box(0);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 0, v___x_64_);
v___x_66_ = v___x_52_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
else
{
lean_del_object(v___x_52_);
v_t_21_ = v___x_61_;
v___y_22_ = v_a_11_;
v___y_23_ = v_a_12_;
v___y_24_ = v_a_13_;
v___y_25_ = v_a_14_;
v___y_26_ = v_a_15_;
v___y_27_ = v_a_16_;
v___y_28_ = v_a_17_;
v___y_29_ = v_a_18_;
goto v___jp_20_;
}
}
}
}
default: 
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_expected_10_);
lean_dec_ref(v_pat_9_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
v___jp_20_:
{
uint8_t v___x_30_; lean_object* v___x_31_; 
v___x_30_ = 0;
v___x_31_ = l_Lean_Elab_Tactic_elabTerm(v_t_21_, v_expected_10_, v___x_30_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_40_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_36_, 0, v_a_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
else
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
v_a_41_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_31_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_31_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___boxed(lean_object* v_pat_71_, lean_object* v_expected_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(v_pat_71_, v_expected_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
return v_res_82_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_box(0);
v___x_84_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg(){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0);
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___boxed(lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0(lean_object* v_00_u03b1_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___boxed(lean_object* v_00_u03b1_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0(v_00_u03b1_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(lean_object* v___x_113_, lean_object* v_00___114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = lean_unsigned_to_nat(3u);
v___x_116_ = lean_array_get_size(v___x_113_);
v___x_117_ = lean_nat_dec_le(v___x_115_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0___boxed(lean_object* v___x_118_, lean_object* v_00___119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(v___x_118_, v_00___119_);
lean_dec_ref(v___x_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__2(lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
if (lean_obj_tag(v_a_122_) == 0)
{
lean_object* v___x_124_; 
v___x_124_ = l_List_reverse___redArg(v_a_123_);
return v___x_124_;
}
else
{
lean_object* v_head_125_; lean_object* v_tail_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_135_; 
v_head_125_ = lean_ctor_get(v_a_122_, 0);
v_tail_126_ = lean_ctor_get(v_a_122_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_a_122_);
if (v_isSharedCheck_135_ == 0)
{
v___x_128_ = v_a_122_;
v_isShared_129_ = v_isSharedCheck_135_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_tail_126_);
lean_inc(v_head_125_);
lean_dec(v_a_122_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_135_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_130_ = l_Lean_MessageData_ofExpr(v_head_125_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 1, v_a_123_);
lean_ctor_set(v___x_128_, 0, v___x_130_);
v___x_132_ = v___x_128_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_a_123_);
v___x_132_ = v_reuseFailAlloc_134_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
v_a_122_ = v_tail_126_;
v_a_123_ = v___x_132_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(lean_object* v_msgData_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; lean_object* v_env_143_; lean_object* v___x_144_; lean_object* v_toCold_145_; lean_object* v_mctx_146_; lean_object* v_lctx_147_; lean_object* v_options_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_142_ = lean_st_ref_get(v___y_140_);
v_env_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc_ref(v_env_143_);
lean_dec(v___x_142_);
v___x_144_ = lean_st_ref_get(v___y_138_);
v_toCold_145_ = lean_ctor_get(v___y_139_, 0);
v_mctx_146_ = lean_ctor_get(v___x_144_, 0);
lean_inc_ref(v_mctx_146_);
lean_dec(v___x_144_);
v_lctx_147_ = lean_ctor_get(v___y_137_, 2);
v_options_148_ = lean_ctor_get(v_toCold_145_, 2);
lean_inc_ref(v_options_148_);
lean_inc_ref(v_lctx_147_);
v___x_149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_149_, 0, v_env_143_);
lean_ctor_set(v___x_149_, 1, v_mctx_146_);
lean_ctor_set(v___x_149_, 2, v_lctx_147_);
lean_ctor_set(v___x_149_, 3, v_options_148_);
v___x_150_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_msgData_136_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1___boxed(lean_object* v_msgData_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msgData_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(lean_object* v_msg_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_ref_165_; lean_object* v___x_166_; lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
v_ref_165_ = lean_ctor_get(v___y_162_, 2);
v___x_166_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_175_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
lean_inc(v_ref_165_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_ref_165_);
lean_ctor_set(v___x_171_, 1, v_a_167_);
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 1);
lean_ctor_set(v___x_169_, 0, v___x_171_);
v___x_173_ = v___x_169_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg___boxed(lean_object* v_msg_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v_msg_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_182_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_183_; double v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_float_of_nat(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(lean_object* v_cls_188_, lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_ref_195_; lean_object* v___x_196_; lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_241_; 
v_ref_195_ = lean_ctor_get(v___y_192_, 2);
v___x_196_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_241_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_241_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_241_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v_traceState_202_; lean_object* v_env_203_; lean_object* v_nextMacroScope_204_; lean_object* v_ngen_205_; lean_object* v_auxDeclNGen_206_; lean_object* v_cache_207_; lean_object* v_messages_208_; lean_object* v_infoState_209_; lean_object* v_snapshotTasks_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_240_; 
v___x_201_ = lean_st_ref_take(v___y_193_);
v_traceState_202_ = lean_ctor_get(v___x_201_, 4);
v_env_203_ = lean_ctor_get(v___x_201_, 0);
v_nextMacroScope_204_ = lean_ctor_get(v___x_201_, 1);
v_ngen_205_ = lean_ctor_get(v___x_201_, 2);
v_auxDeclNGen_206_ = lean_ctor_get(v___x_201_, 3);
v_cache_207_ = lean_ctor_get(v___x_201_, 5);
v_messages_208_ = lean_ctor_get(v___x_201_, 6);
v_infoState_209_ = lean_ctor_get(v___x_201_, 7);
v_snapshotTasks_210_ = lean_ctor_get(v___x_201_, 8);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_240_ == 0)
{
v___x_212_ = v___x_201_;
v_isShared_213_ = v_isSharedCheck_240_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_snapshotTasks_210_);
lean_inc(v_infoState_209_);
lean_inc(v_messages_208_);
lean_inc(v_cache_207_);
lean_inc(v_traceState_202_);
lean_inc(v_auxDeclNGen_206_);
lean_inc(v_ngen_205_);
lean_inc(v_nextMacroScope_204_);
lean_inc(v_env_203_);
lean_dec(v___x_201_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_240_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
uint64_t v_tid_214_; lean_object* v_traces_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_239_; 
v_tid_214_ = lean_ctor_get_uint64(v_traceState_202_, sizeof(void*)*1);
v_traces_215_ = lean_ctor_get(v_traceState_202_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v_traceState_202_);
if (v_isSharedCheck_239_ == 0)
{
v___x_217_ = v_traceState_202_;
v_isShared_218_ = v_isSharedCheck_239_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_traces_215_);
lean_dec(v_traceState_202_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_239_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; double v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_219_ = lean_box(0);
v___x_220_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0);
v___x_221_ = 0;
v___x_222_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1));
v___x_223_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_223_, 0, v_cls_188_);
lean_ctor_set(v___x_223_, 1, v___x_219_);
lean_ctor_set(v___x_223_, 2, v___x_222_);
lean_ctor_set_float(v___x_223_, sizeof(void*)*3, v___x_220_);
lean_ctor_set_float(v___x_223_, sizeof(void*)*3 + 8, v___x_220_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*3 + 16, v___x_221_);
v___x_224_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2));
v___x_225_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v_a_197_);
lean_ctor_set(v___x_225_, 2, v___x_224_);
lean_inc(v_ref_195_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_ref_195_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = l_Lean_PersistentArray_push___redArg(v_traces_215_, v___x_226_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_227_);
v___x_229_ = v___x_217_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_227_);
lean_ctor_set_uint64(v_reuseFailAlloc_238_, sizeof(void*)*1, v_tid_214_);
v___x_229_ = v_reuseFailAlloc_238_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_231_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 4, v___x_229_);
v___x_231_ = v___x_212_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_env_203_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_nextMacroScope_204_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_ngen_205_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_auxDeclNGen_206_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_237_, 5, v_cache_207_);
lean_ctor_set(v_reuseFailAlloc_237_, 6, v_messages_208_);
lean_ctor_set(v_reuseFailAlloc_237_, 7, v_infoState_209_);
lean_ctor_set(v_reuseFailAlloc_237_, 8, v_snapshotTasks_210_);
v___x_231_ = v_reuseFailAlloc_237_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_232_ = lean_st_ref_put(v___y_193_, v___x_231_);
v___x_233_ = lean_box(0);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_233_);
v___x_235_ = v___x_199_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___boxed(lean_object* v_cls_242_, lean_object* v_msg_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_cls_242_, v_msg_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_ref_256_; lean_object* v___x_257_; lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_ref_256_ = lean_ctor_get(v___y_253_, 2);
v___x_257_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_266_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
lean_inc(v_ref_256_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_ref_256_);
lean_ctor_set(v___x_262_, 1, v_a_258_);
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 1);
lean_ctor_set(v___x_260_, 0, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg___boxed(lean_object* v_msg_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v_msg_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_273_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0(void){
_start:
{
lean_object* v___x_274_; lean_object* v_dummy_275_; 
v___x_274_ = lean_box(0);
v_dummy_275_ = l_Lean_Expr_sort___override(v___x_274_);
return v_dummy_275_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1));
v___x_278_ = l_Lean_stringToMessageData(v___x_277_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4));
v___x_282_ = l_Lean_stringToMessageData(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15));
v___x_303_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17));
v___x_304_ = l_Lean_Name_append(v___x_303_, v___x_302_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19));
v___x_307_ = l_Lean_stringToMessageData(v___x_306_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21));
v___x_310_ = l_Lean_stringToMessageData(v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23));
v___x_313_ = l_Lean_stringToMessageData(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25));
v___x_316_ = l_Lean_stringToMessageData(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27));
v___x_319_ = l_Lean_stringToMessageData(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29));
v___x_322_ = l_Lean_stringToMessageData(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___boxed(lean_object* v_goal_323_, lean_object* v_pat_324_, lean_object* v_k_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v_goal_323_, v_pat_324_, v_k_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(lean_object* v_goal_336_, lean_object* v_pat_337_, lean_object* v_k_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
switch(lean_obj_tag(v_pat_337_))
{
case 0:
{
lean_object* v_name_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_404_; 
v_name_348_ = lean_ctor_get(v_pat_337_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v_pat_337_);
if (v_isSharedCheck_404_ == 0)
{
v___x_350_ = v_pat_337_;
v_isShared_351_ = v_isSharedCheck_404_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_name_348_);
lean_dec(v_pat_337_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_404_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2));
lean_inc(v_name_348_);
v___x_353_ = l_Lean_Syntax_isOfKind(v_name_348_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_355_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 3);
v___x_355_ = v___x_350_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_name_348_);
v___x_355_ = v_reuseFailAlloc_357_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
v_pat_337_ = v___x_355_;
goto _start;
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = l_Lean_Syntax_getArg(v_name_348_, v___x_358_);
v___x_360_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4));
v___x_361_ = l_Lean_Syntax_isOfKind(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_363_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 3);
v___x_363_ = v___x_350_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_name_348_);
v___x_363_ = v_reuseFailAlloc_365_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
v_pat_337_ = v___x_363_;
goto _start;
}
}
else
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Elab_Tactic_saveState___redArg(v_a_340_, v_a_342_, v_a_344_, v_a_346_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_366_, 1);
lean_inc(v_name_348_);
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 2);
v___x_369_ = v___x_350_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_name_348_);
v___x_369_ = v_reuseFailAlloc_395_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_inc_ref(v_k_338_);
lean_inc_ref(v_goal_336_);
v___x_370_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___boxed), 12, 3);
lean_closure_set(v___x_370_, 0, v_goal_336_);
lean_closure_set(v___x_370_, 1, v___x_369_);
lean_closure_set(v___x_370_, 2, v_k_338_);
v___x_371_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_370_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_dec(v_a_367_);
lean_dec(v_name_348_);
lean_dec_ref(v_k_338_);
lean_dec_ref(v_goal_336_);
return v___x_371_;
}
else
{
lean_object* v_a_372_; uint8_t v___y_374_; uint8_t v___x_393_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
v___x_393_ = l_Lean_Exception_isInterrupt(v_a_372_);
if (v___x_393_ == 0)
{
uint8_t v___x_394_; 
v___x_394_ = l_Lean_Exception_isRuntime(v_a_372_);
v___y_374_ = v___x_394_;
goto v___jp_373_;
}
else
{
lean_dec(v_a_372_);
v___y_374_ = v___x_393_;
goto v___jp_373_;
}
v___jp_373_:
{
if (v___y_374_ == 0)
{
lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_391_; 
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v___x_371_, 0);
lean_dec(v_unused_392_);
v___x_376_ = v___x_371_;
v_isShared_377_ = v_isSharedCheck_391_;
goto v_resetjp_375_;
}
else
{
lean_dec(v___x_371_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_391_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_367_, v___y_374_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v___x_380_; 
lean_dec_ref_known(v___x_378_, 1);
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 3);
lean_ctor_set(v___x_376_, 0, v_name_348_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_name_348_);
v___x_380_ = v_reuseFailAlloc_382_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
v_pat_337_ = v___x_380_;
goto _start;
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_del_object(v___x_376_);
lean_dec(v_name_348_);
lean_dec_ref(v_k_338_);
lean_dec_ref(v_goal_336_);
v_a_383_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_378_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_378_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
else
{
lean_dec(v_a_367_);
lean_dec(v_name_348_);
lean_dec_ref(v_k_338_);
lean_dec_ref(v_goal_336_);
return v___x_371_;
}
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_del_object(v___x_350_);
lean_dec(v_name_348_);
lean_dec_ref(v_k_338_);
lean_dec_ref(v_goal_336_);
v_a_396_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_366_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_366_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_args_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_615_; 
v_args_405_ = lean_ctor_get(v_pat_337_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_pat_337_);
if (v_isSharedCheck_615_ == 0)
{
v___x_407_ = v_pat_337_;
v_isShared_408_ = v_isSharedCheck_615_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_args_405_);
lean_dec(v_pat_337_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_615_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
if (lean_obj_tag(v_args_405_) == 0)
{
lean_object* v___x_409_; 
lean_del_object(v___x_407_);
lean_dec_ref(v_k_338_);
lean_dec_ref(v_goal_336_);
v___x_409_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_409_;
}
else
{
lean_object* v_tail_410_; 
v_tail_410_ = lean_ctor_get(v_args_405_, 1);
if (lean_obj_tag(v_tail_410_) == 0)
{
lean_object* v_head_411_; 
lean_del_object(v___x_407_);
v_head_411_ = lean_ctor_get(v_args_405_, 0);
lean_inc(v_head_411_);
lean_dec_ref_known(v_args_405_, 2);
v_pat_337_ = v_head_411_;
goto _start;
}
else
{
lean_object* v_head_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_613_; 
lean_inc(v_tail_410_);
v_head_413_ = lean_ctor_get(v_args_405_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v_args_405_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v_args_405_, 1);
lean_dec(v_unused_614_);
v___x_415_ = v_args_405_;
v_isShared_416_ = v_isSharedCheck_613_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_head_413_);
lean_dec(v_args_405_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_613_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_u_417_; lean_object* v_00_u03c3s_418_; lean_object* v_hyps_419_; lean_object* v_target_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_612_; 
v_u_417_ = lean_ctor_get(v_goal_336_, 0);
v_00_u03c3s_418_ = lean_ctor_get(v_goal_336_, 1);
v_hyps_419_ = lean_ctor_get(v_goal_336_, 2);
v_target_420_ = lean_ctor_get(v_goal_336_, 3);
v_isSharedCheck_612_ = !lean_is_exclusive(v_goal_336_);
if (v_isSharedCheck_612_ == 0)
{
v___x_422_ = v_goal_336_;
v_isShared_423_ = v_isSharedCheck_612_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_target_420_);
lean_inc(v_hyps_419_);
lean_inc(v_00_u03c3s_418_);
lean_inc(v_u_417_);
lean_dec(v_goal_336_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_612_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_whnfR(v_target_420_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_toCold_425_; lean_object* v_options_426_; lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_611_; 
v_toCold_425_ = lean_ctor_get(v_a_345_, 0);
v_options_426_ = lean_ctor_get(v_toCold_425_, 2);
v_a_427_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_611_ == 0)
{
v___x_429_ = v___x_424_;
v_isShared_430_ = v_isSharedCheck_611_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_424_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_611_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_inheritedTraceOptions_431_; uint8_t v_hasTrace_432_; lean_object* v___x_433_; lean_object* v_nargs_434_; lean_object* v___x_435_; lean_object* v_dummy_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; uint8_t v___y_453_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; uint8_t v___y_532_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; 
v_inheritedTraceOptions_431_ = lean_ctor_get(v_toCold_425_, 11);
v_hasTrace_432_ = lean_ctor_get_uint8(v_options_426_, sizeof(void*)*1);
v___x_433_ = l_Lean_Expr_getAppFn_x27(v_a_427_);
v_nargs_434_ = l_Lean_Expr_getAppNumArgs(v_a_427_);
v___x_435_ = l_Lean_instInhabitedExpr;
v_dummy_436_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0);
lean_inc(v_nargs_434_);
v___x_437_ = lean_mk_array(v_nargs_434_, v_dummy_436_);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_sub(v_nargs_434_, v___x_438_);
lean_dec(v_nargs_434_);
lean_inc(v_a_427_);
v___x_440_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_427_, v___x_437_, v___x_439_);
if (v_hasTrace_432_ == 0)
{
v___y_574_ = v_a_339_;
v___y_575_ = v_a_340_;
v___y_576_ = v_a_341_;
v___y_577_ = v_a_342_;
v___y_578_ = v_a_343_;
v___y_579_ = v_a_344_;
v___y_580_ = v_a_345_;
v___y_581_ = v_a_346_;
goto v___jp_573_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15));
v___x_590_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18);
v___x_591_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_431_, v_options_426_, v___x_590_);
if (v___x_591_ == 0)
{
v___y_574_ = v_a_339_;
v___y_575_ = v_a_340_;
v___y_576_ = v_a_341_;
v___y_577_ = v_a_342_;
v___y_578_ = v_a_343_;
v___y_579_ = v_a_344_;
v___y_580_ = v_a_345_;
v___y_581_ = v_a_346_;
goto v___jp_573_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_592_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20);
lean_inc_ref(v___x_433_);
v___x_593_ = l_Lean_MessageData_ofExpr(v___x_433_);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
lean_inc_ref(v___x_440_);
v___x_597_ = lean_array_to_list(v___x_440_);
v___x_598_ = lean_box(0);
v___x_599_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__2(v___x_597_, v___x_598_);
v___x_600_ = l_Lean_MessageData_ofList(v___x_599_);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_596_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v___x_589_, v___x_601_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_dec_ref_known(v___x_602_, 1);
v___y_574_ = v_a_339_;
v___y_575_ = v_a_340_;
v___y_576_ = v_a_341_;
v___y_577_ = v_a_342_;
v___y_578_ = v_a_343_;
v___y_579_ = v_a_344_;
v___y_580_ = v_a_345_;
v___y_581_ = v_a_346_;
goto v___jp_573_;
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref(v___x_440_);
lean_dec_ref(v___x_433_);
lean_del_object(v___x_429_);
lean_dec(v_a_427_);
lean_del_object(v___x_422_);
lean_dec_ref(v_hyps_419_);
lean_dec_ref(v_00_u03c3s_418_);
lean_dec(v_u_417_);
lean_del_object(v___x_415_);
lean_dec(v_head_413_);
lean_dec(v_tail_410_);
lean_del_object(v___x_407_);
lean_dec_ref(v_k_338_);
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
v___jp_441_:
{
if (v___y_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec_ref(v___x_440_);
lean_del_object(v___x_429_);
lean_del_object(v___x_422_);
lean_dec_ref(v_hyps_419_);
lean_dec_ref(v_00_u03c3s_418_);
lean_dec(v_u_417_);
lean_del_object(v___x_415_);
lean_dec(v_head_413_);
lean_dec(v_tail_410_);
lean_del_object(v___x_407_);
lean_dec_ref(v_k_338_);
v___x_454_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2);
v___x_455_ = l_Lean_MessageData_ofExpr(v_a_427_);
v___x_456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v___x_456_, v___y_445_, v___y_442_, v___y_452_, v___y_451_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
lean_dec(v_a_427_);
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_array_get(v___x_435_, v___x_440_, v___x_458_);
lean_inc(v___x_459_);
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 1);
lean_ctor_set(v___x_429_, 0, v___x_459_);
v___x_461_ = v___x_429_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_519_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(v_head_413_, v___x_461_, v___y_446_, v___y_448_, v___y_443_, v___y_444_, v___y_445_, v___y_442_, v___y_452_, v___y_451_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
if (lean_obj_tag(v_a_463_) == 1)
{
lean_object* v_val_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v_val_464_ = lean_ctor_get(v_a_463_, 0);
lean_inc_n(v_val_464_, 2);
lean_dec_ref_known(v_a_463_, 1);
v___x_465_ = lean_unsigned_to_nat(2u);
v___x_466_ = lean_array_get(v___x_435_, v___x_440_, v___x_465_);
v___x_467_ = lean_mk_empty_array_with_capacity(v___x_438_);
v___x_468_ = lean_array_push(v___x_467_, v_val_464_);
v___x_469_ = lean_unsigned_to_nat(3u);
v___x_470_ = lean_array_get_size(v___x_440_);
v___x_471_ = l_Array_toSubarray___redArg(v___x_440_, v___x_469_, v___x_470_);
v___x_472_ = l_Subarray_copy___redArg(v___x_471_);
v___x_473_ = l_Array_append___redArg(v___x_468_, v___x_472_);
lean_dec_ref(v___x_472_);
lean_inc(v___x_466_);
v___x_474_ = l_Lean_Expr_beta(v___x_466_, v___x_473_);
lean_inc_ref(v_hyps_419_);
lean_inc_ref(v_00_u03c3s_418_);
lean_inc(v_u_417_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 3, v___x_474_);
v___x_476_ = v___x_422_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_u_417_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_00_u03c3s_418_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_hyps_419_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v___x_474_);
v___x_476_ = v_reuseFailAlloc_508_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_478_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v_tail_410_);
v___x_478_ = v___x_407_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_tail_410_);
v___x_478_ = v_reuseFailAlloc_507_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v___x_476_, v___x_478_, v_k_338_, v___y_446_, v___y_448_, v___y_443_, v___y_444_, v___y_445_, v___y_442_, v___y_452_, v___y_451_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_481_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
lean_inc(v___x_459_);
v___x_481_ = l_Lean_Meta_getLevel(v___x_459_, v___y_445_, v___y_442_, v___y_452_, v___y_451_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_498_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_498_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_498_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_498_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_486_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3));
lean_inc_ref(v___y_449_);
lean_inc_ref(v___y_447_);
lean_inc_ref(v___y_450_);
v___x_487_ = l_Lean_Name_mkStr4(v___y_450_, v___y_447_, v___y_449_, v___x_486_);
v___x_488_ = lean_box(0);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_488_);
lean_ctor_set(v___x_415_, 0, v_u_417_);
v___x_490_ = v___x_415_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_u_417_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v___x_488_);
v___x_490_ = v_reuseFailAlloc_497_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_491_, 0, v_a_482_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = l_Lean_mkConst(v___x_487_, v___x_491_);
v___x_493_ = l_Lean_mkApp6(v___x_492_, v___x_459_, v_00_u03c3s_418_, v_hyps_419_, v___x_466_, v_val_464_, v_a_480_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_493_);
v___x_495_ = v___x_484_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_a_480_);
lean_dec(v___x_466_);
lean_dec(v_val_464_);
lean_dec(v___x_459_);
lean_dec_ref(v_hyps_419_);
lean_dec_ref(v_00_u03c3s_418_);
lean_dec(v_u_417_);
lean_del_object(v___x_415_);
v_a_499_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_481_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_481_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
else
{
lean_dec(v___x_466_);
lean_dec(v_val_464_);
lean_dec(v___x_459_);
lean_dec_ref(v_hyps_419_);
lean_dec_ref(v_00_u03c3s_418_);
lean_dec(v_u_417_);
lean_del_object(v___x_415_);
return v___x_479_;
}
}
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v_a_463_);
lean_dec(v___x_459_);
lean_dec_ref(v___x_440_);
lean_del_object(v___x_422_);
lean_dec_ref(v_hyps_419_);
lean_dec_ref(v_00_u03c3s_418_);
lean_dec(v_u_417_);
lean_del_object(v___x_415_);
lean_dec(v_tail_410_);
lean_del_object(v___x_407_);
lean_dec_ref(v_k_338_);
v___x_509_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5);
v___x_510_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v___x_509_, v___y_445_, v___y_442_, v___y_452_, v___y_451_);
return v___x_510_;
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec(v___x_459_);
lean_dec_ref(v___x_440_);
lean_del_object(v___x_422_);
lean_dec_ref(v_hyps_419_);
lean_dec_ref(v_00_u03c3s_418_);
lean_dec(v_u_417_);
lean_del_object(v___x_415_);
lean_dec(v_tail_410_);
lean_del_object(v___x_407_);
lean_dec_ref(v_k_338_);
v_a_511_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_462_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_462_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
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
}
}
v___jp_520_:
{
if (v___y_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6));
lean_inc_ref(v___y_528_);
lean_inc_ref(v___y_526_);
lean_inc_ref(v___y_531_);
v___x_534_ = l_Lean_Name_mkStr4(v___y_531_, v___y_526_, v___y_528_, v___x_533_);
v___x_535_ = l_Lean_Expr_isConstOf(v___x_433_, v___x_534_);
lean_dec(v___x_534_);
lean_dec_ref(v___x_433_);
if (v___x_535_ == 0)
{
v___y_442_ = v___y_522_;
v___y_443_ = v___y_521_;
v___y_444_ = v___y_523_;
v___y_445_ = v___y_525_;
v___y_446_ = v___y_524_;
v___y_447_ = v___y_526_;
v___y_448_ = v___y_527_;
v___y_449_ = v___y_528_;
v___y_450_ = v___y_531_;
v___y_451_ = v___y_530_;
v___y_452_ = v___y_529_;
v___y_453_ = v___x_535_;
goto v___jp_441_;
}
else
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = lean_box(0);
v___x_537_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(v___x_440_, v___x_536_);
v___y_442_ = v___y_522_;
v___y_443_ = v___y_521_;
v___y_444_ = v___y_523_;
v___y_445_ = v___y_525_;
v___y_446_ = v___y_524_;
v___y_447_ = v___y_526_;
v___y_448_ = v___y_527_;
v___y_449_ = v___y_528_;
v___y_450_ = v___y_531_;
v___y_451_ = v___y_530_;
v___y_452_ = v___y_529_;
v___y_453_ = v___x_537_;
goto v___jp_441_;
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec_ref(v___x_433_);
lean_del_object(v___x_429_);
lean_dec(v_a_427_);
lean_del_object(v___x_422_);
lean_del_object(v___x_415_);
lean_del_object(v___x_407_);
v___x_538_ = lean_array_get(v___x_435_, v___x_440_, v___x_438_);
v___x_539_ = lean_unsigned_to_nat(3u);
v___x_540_ = lean_array_get_size(v___x_440_);
lean_inc_ref(v___x_440_);
v___x_541_ = l_Array_toSubarray___redArg(v___x_440_, v___x_539_, v___x_540_);
v___x_542_ = l_Subarray_copy___redArg(v___x_541_);
lean_inc_ref(v___x_542_);
v___x_543_ = l_Lean_Expr_beta(v___x_538_, v___x_542_);
lean_inc_ref(v___x_543_);
lean_inc_ref(v_hyps_419_);
lean_inc_ref(v_00_u03c3s_418_);
lean_inc(v_u_417_);
v___x_544_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_544_, 0, v_u_417_);
lean_ctor_set(v___x_544_, 1, v_00_u03c3s_418_);
lean_ctor_set(v___x_544_, 2, v_hyps_419_);
lean_ctor_set(v___x_544_, 3, v___x_543_);
lean_inc_ref(v_k_338_);
v___x_545_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v___x_544_, v_head_413_, v_k_338_, v___y_524_, v___y_527_, v___y_521_, v___y_523_, v___y_525_, v___y_522_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_572_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_572_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_572_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_572_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_550_ = lean_unsigned_to_nat(2u);
v___x_551_ = lean_array_get(v___x_435_, v___x_440_, v___x_550_);
lean_dec_ref(v___x_440_);
v___x_552_ = l_Lean_Expr_beta(v___x_551_, v___x_542_);
lean_inc_ref(v___x_552_);
lean_inc_ref(v_hyps_419_);
lean_inc_ref(v_00_u03c3s_418_);
lean_inc(v_u_417_);
v___x_553_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_553_, 0, v_u_417_);
lean_ctor_set(v___x_553_, 1, v_00_u03c3s_418_);
lean_ctor_set(v___x_553_, 2, v_hyps_419_);
lean_ctor_set(v___x_553_, 3, v___x_552_);
if (v_isShared_549_ == 0)
{
lean_ctor_set_tag(v___x_548_, 1);
lean_ctor_set(v___x_548_, 0, v_tail_410_);
v___x_555_ = v___x_548_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_tail_410_);
v___x_555_ = v_reuseFailAlloc_571_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v___x_553_, v___x_555_, v_k_338_, v___y_524_, v___y_527_, v___y_521_, v___y_523_, v___y_525_, v___y_522_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_570_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_570_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_570_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_561_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7));
lean_inc_ref(v___y_528_);
lean_inc_ref(v___y_526_);
lean_inc_ref(v___y_531_);
v___x_562_ = l_Lean_Name_mkStr4(v___y_531_, v___y_526_, v___y_528_, v___x_561_);
v___x_563_ = lean_box(0);
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v_u_417_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = l_Lean_mkConst(v___x_562_, v___x_564_);
v___x_566_ = l_Lean_mkApp6(v___x_565_, v_00_u03c3s_418_, v_hyps_419_, v___x_543_, v___x_552_, v_a_546_, v_a_557_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_566_);
v___x_568_ = v___x_559_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
else
{
lean_dec_ref(v___x_552_);
lean_dec(v_a_546_);
lean_dec_ref(v___x_543_);
lean_dec_ref(v_hyps_419_);
lean_dec_ref(v_00_u03c3s_418_);
lean_dec(v_u_417_);
return v___x_556_;
}
}
}
}
else
{
lean_dec_ref(v___x_543_);
lean_dec_ref(v___x_542_);
lean_dec_ref(v___x_440_);
lean_dec_ref(v_hyps_419_);
lean_dec_ref(v_00_u03c3s_418_);
lean_dec(v_u_417_);
lean_dec(v_tail_410_);
lean_dec_ref(v_k_338_);
return v___x_545_;
}
}
}
v___jp_573_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_582_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8));
v___x_583_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9));
v___x_584_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10));
v___x_585_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12));
v___x_586_ = l_Lean_Expr_isConstOf(v___x_433_, v___x_585_);
if (v___x_586_ == 0)
{
v___y_521_ = v___y_576_;
v___y_522_ = v___y_579_;
v___y_523_ = v___y_577_;
v___y_524_ = v___y_574_;
v___y_525_ = v___y_578_;
v___y_526_ = v___x_583_;
v___y_527_ = v___y_575_;
v___y_528_ = v___x_584_;
v___y_529_ = v___y_580_;
v___y_530_ = v___y_581_;
v___y_531_ = v___x_582_;
v___y_532_ = v___x_586_;
goto v___jp_520_;
}
else
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = lean_box(0);
v___x_588_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(v___x_440_, v___x_587_);
v___y_521_ = v___y_576_;
v___y_522_ = v___y_579_;
v___y_523_ = v___y_577_;
v___y_524_ = v___y_574_;
v___y_525_ = v___y_578_;
v___y_526_ = v___x_583_;
v___y_527_ = v___y_575_;
v___y_528_ = v___x_584_;
v___y_529_ = v___y_580_;
v___y_530_ = v___y_581_;
v___y_531_ = v___x_582_;
v___y_532_ = v___x_588_;
goto v___jp_520_;
}
}
}
}
else
{
lean_del_object(v___x_422_);
lean_dec_ref(v_hyps_419_);
lean_dec_ref(v_00_u03c3s_418_);
lean_dec(v_u_417_);
lean_del_object(v___x_415_);
lean_dec(v_head_413_);
lean_dec(v_tail_410_);
lean_del_object(v___x_407_);
lean_dec_ref(v_k_338_);
return v___x_424_;
}
}
}
}
}
}
}
case 2:
{
lean_object* v_h_616_; lean_object* v___x_617_; 
lean_dec_ref(v_k_338_);
v_h_616_ = lean_ctor_get(v_pat_337_, 0);
lean_inc(v_h_616_);
lean_dec_ref_known(v_pat_337_, 1);
v___x_617_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(v_goal_336_, v_h_616_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
return v___x_617_;
}
case 3:
{
lean_object* v_h_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
lean_dec_ref(v_k_338_);
v_h_618_ = lean_ctor_get(v_pat_337_, 0);
lean_inc_n(v_h_618_, 2);
lean_dec_ref_known(v_pat_337_, 1);
v___x_619_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2));
v___x_620_ = l_Lean_Syntax_isOfKind(v_h_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec(v_h_618_);
lean_inc_ref(v_goal_336_);
v___x_621_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v_goal_336_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_637_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_637_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_637_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_637_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
if (lean_obj_tag(v_a_622_) == 1)
{
lean_object* v_val_626_; lean_object* v___x_628_; 
lean_dec_ref(v_goal_336_);
v_val_626_ = lean_ctor_get(v_a_622_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v_a_622_, 1);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v_val_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_val_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
else
{
lean_object* v_target_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_del_object(v___x_624_);
lean_dec(v_a_622_);
v_target_630_ = lean_ctor_get(v_goal_336_, 3);
lean_inc_ref(v_target_630_);
lean_dec_ref(v_goal_336_);
v___x_631_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24);
v___x_632_ = l_Lean_MessageData_ofExpr(v_target_630_);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26);
v___x_635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_635_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
return v___x_636_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec_ref(v_goal_336_);
v_a_638_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_621_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_621_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
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
lean_object* v___x_646_; lean_object* v_name_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v_name_647_ = l_Lean_Syntax_getArg(v_h_618_, v___x_646_);
lean_dec(v_h_618_);
v___x_648_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4));
lean_inc(v_name_647_);
v___x_649_ = l_Lean_Syntax_isOfKind(v_name_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
lean_dec(v_name_647_);
lean_inc_ref(v_goal_336_);
v___x_650_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(v_goal_336_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_666_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_666_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_666_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_666_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
if (lean_obj_tag(v_a_651_) == 1)
{
lean_object* v_val_655_; lean_object* v___x_657_; 
lean_dec_ref(v_goal_336_);
v_val_655_ = lean_ctor_get(v_a_651_, 0);
lean_inc(v_val_655_);
lean_dec_ref_known(v_a_651_, 1);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_val_655_);
v___x_657_ = v___x_653_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_val_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
else
{
lean_object* v_target_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_del_object(v___x_653_);
lean_dec(v_a_651_);
v_target_659_ = lean_ctor_get(v_goal_336_, 3);
lean_inc_ref(v_target_659_);
lean_dec_ref(v_goal_336_);
v___x_660_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24);
v___x_661_ = l_Lean_MessageData_ofExpr(v_target_659_);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_664_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
return v___x_665_;
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_goal_336_);
v_a_667_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_650_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_650_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v___x_675_; 
lean_inc(v_name_647_);
v___x_675_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(v_goal_336_, v_name_647_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_691_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_691_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_691_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_691_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
if (lean_obj_tag(v_a_676_) == 1)
{
lean_object* v_val_680_; lean_object* v___x_682_; 
lean_dec(v_name_647_);
v_val_680_ = lean_ctor_get(v_a_676_, 0);
lean_inc(v_val_680_);
lean_dec_ref_known(v_a_676_, 1);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v_val_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_val_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_del_object(v___x_678_);
lean_dec(v_a_676_);
v___x_684_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28);
v___x_685_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_647_);
v___x_686_ = l_Lean_MessageData_ofFormat(v___x_685_);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_684_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30, &l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_689_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
return v___x_690_;
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec(v_name_647_);
v_a_692_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_675_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_675_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
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
}
default: 
{
lean_object* v_name_700_; lean_object* v___x_701_; 
v_name_700_ = lean_ctor_get(v_pat_337_, 0);
lean_inc(v_name_700_);
lean_dec_ref_known(v_pat_337_, 1);
lean_inc(v_a_346_);
lean_inc_ref(v_a_345_);
lean_inc(v_a_344_);
lean_inc_ref(v_a_343_);
lean_inc(v_a_342_);
lean_inc_ref(v_a_341_);
lean_inc(v_a_340_);
lean_inc_ref(v_a_339_);
v___x_701_ = lean_apply_11(v_k_338_, v_goal_336_, v_name_700_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, lean_box(0));
return v___x_701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1(lean_object* v_00_u03b1_702_, lean_object* v_msg_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v_msg_703_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___boxed(lean_object* v_00_u03b1_714_, lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1(v_00_u03b1_714_, v_msg_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3(lean_object* v_cls_726_, lean_object* v_msg_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_cls_726_, v_msg_727_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___boxed(lean_object* v_cls_738_, lean_object* v_msg_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3(v_cls_738_, v_msg_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4(lean_object* v_00_u03b1_750_, lean_object* v_msg_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v_msg_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___boxed(lean_object* v_00_u03b1_758_, lean_object* v_msg_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4(v_00_u03b1_758_, v_msg_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0(lean_object* v_x_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___x_776_; 
lean_inc(v___y_770_);
lean_inc_ref(v___y_769_);
lean_inc(v___y_768_);
lean_inc_ref(v___y_767_);
v___x_776_ = lean_apply_9(v_x_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, lean_box(0));
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0___boxed(lean_object* v_x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0(v_x_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(lean_object* v_mvarId_788_, lean_object* v_x_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___f_799_; lean_object* v___x_800_; 
lean_inc(v___y_793_);
lean_inc_ref(v___y_792_);
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
v___f_799_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_799_, 0, v_x_789_);
lean_closure_set(v___f_799_, 1, v___y_790_);
lean_closure_set(v___f_799_, 2, v___y_791_);
lean_closure_set(v___f_799_, 3, v___y_792_);
lean_closure_set(v___f_799_, 4, v___y_793_);
v___x_800_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_788_, v___f_799_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_800_) == 0)
{
return v___x_800_;
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___boxed(lean_object* v_mvarId_809_, lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_mvarId_809_, v_x_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2(lean_object* v_00_u03b1_821_, lean_object* v_mvarId_822_, lean_object* v_x_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_mvarId_822_, v_x_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___boxed(lean_object* v_00_u03b1_834_, lean_object* v_mvarId_835_, lean_object* v_x_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2(v_00_u03b1_834_, v_mvarId_835_, v_x_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(lean_object* v_val_847_, lean_object* v_goal_848_, lean_object* v_name_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_848_);
v___x_860_ = l_Lean_Syntax_getId(v_name_849_);
v___x_861_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_859_, v___x_860_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_873_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_873_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_866_ = lean_st_ref_take(v_val_847_);
v___x_867_ = l_Lean_Expr_mvarId_x21(v_a_862_);
v___x_868_ = lean_array_push(v___x_866_, v___x_867_);
v___x_869_ = lean_st_ref_put(v_val_847_, v___x_868_);
if (v_isShared_865_ == 0)
{
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_862_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed(lean_object* v_val_874_, lean_object* v_goal_875_, lean_object* v_name_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(v_val_874_, v_goal_875_, v_name_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v_name_876_);
lean_dec(v_val_874_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(lean_object* v_x_887_, lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
lean_object* v_ks_891_; lean_object* v_vs_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_916_; 
v_ks_891_ = lean_ctor_get(v_x_887_, 0);
v_vs_892_ = lean_ctor_get(v_x_887_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_x_887_);
if (v_isSharedCheck_916_ == 0)
{
v___x_894_ = v_x_887_;
v_isShared_895_ = v_isSharedCheck_916_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_vs_892_);
lean_inc(v_ks_891_);
lean_dec(v_x_887_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_916_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = lean_array_get_size(v_ks_891_);
v___x_897_ = lean_nat_dec_lt(v_x_888_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
lean_dec(v_x_888_);
v___x_898_ = lean_array_push(v_ks_891_, v_x_889_);
v___x_899_ = lean_array_push(v_vs_892_, v_x_890_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v___x_899_);
lean_ctor_set(v___x_894_, 0, v___x_898_);
v___x_901_ = v___x_894_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_899_);
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
lean_object* v_k_x27_903_; uint8_t v___x_904_; 
v_k_x27_903_ = lean_array_fget_borrowed(v_ks_891_, v_x_888_);
v___x_904_ = l_Lean_instBEqMVarId_beq(v_x_889_, v_k_x27_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_906_; 
if (v_isShared_895_ == 0)
{
v___x_906_ = v___x_894_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_ks_891_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_vs_892_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_nat_add(v_x_888_, v___x_907_);
lean_dec(v_x_888_);
v_x_887_ = v___x_906_;
v_x_888_ = v___x_908_;
goto _start;
}
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_911_ = lean_array_fset(v_ks_891_, v_x_888_, v_x_889_);
v___x_912_ = lean_array_fset(v_vs_892_, v_x_888_, v_x_890_);
lean_dec(v_x_888_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v___x_912_);
lean_ctor_set(v___x_894_, 0, v___x_911_);
v___x_914_ = v___x_894_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(lean_object* v_n_917_, lean_object* v_k_918_, lean_object* v_v_919_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(v_n_917_, v___x_920_, v_k_918_, v_v_919_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(lean_object* v_x_923_, size_t v_x_924_, size_t v_x_925_, lean_object* v_x_926_, lean_object* v_x_927_){
_start:
{
if (lean_obj_tag(v_x_923_) == 0)
{
lean_object* v_es_928_; size_t v___x_929_; size_t v___x_930_; lean_object* v_j_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_es_928_ = lean_ctor_get(v_x_923_, 0);
v___x_929_ = ((size_t)31ULL);
v___x_930_ = lean_usize_land(v_x_924_, v___x_929_);
v_j_931_ = lean_usize_to_nat(v___x_930_);
v___x_932_ = lean_array_get_size(v_es_928_);
v___x_933_ = lean_nat_dec_lt(v_j_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_dec(v_j_931_);
lean_dec(v_x_927_);
lean_dec(v_x_926_);
return v_x_923_;
}
else
{
lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_972_; 
lean_inc_ref(v_es_928_);
v_isSharedCheck_972_ = !lean_is_exclusive(v_x_923_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v_x_923_, 0);
lean_dec(v_unused_973_);
v___x_935_ = v_x_923_;
v_isShared_936_ = v_isSharedCheck_972_;
goto v_resetjp_934_;
}
else
{
lean_dec(v_x_923_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_972_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_v_937_; lean_object* v___x_938_; lean_object* v_xs_x27_939_; lean_object* v___y_941_; 
v_v_937_ = lean_array_fget(v_es_928_, v_j_931_);
v___x_938_ = lean_box(0);
v_xs_x27_939_ = lean_array_fset(v_es_928_, v_j_931_, v___x_938_);
switch(lean_obj_tag(v_v_937_))
{
case 0:
{
lean_object* v_key_946_; lean_object* v_val_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_957_; 
v_key_946_ = lean_ctor_get(v_v_937_, 0);
v_val_947_ = lean_ctor_get(v_v_937_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v_v_937_);
if (v_isSharedCheck_957_ == 0)
{
v___x_949_ = v_v_937_;
v_isShared_950_ = v_isSharedCheck_957_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_val_947_);
lean_inc(v_key_946_);
lean_dec(v_v_937_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_957_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
uint8_t v___x_951_; 
v___x_951_ = l_Lean_instBEqMVarId_beq(v_x_926_, v_key_946_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_del_object(v___x_949_);
v___x_952_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_946_, v_val_947_, v_x_926_, v_x_927_);
v___x_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
v___y_941_ = v___x_953_;
goto v___jp_940_;
}
else
{
lean_object* v___x_955_; 
lean_dec(v_val_947_);
lean_dec(v_key_946_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v_x_927_);
lean_ctor_set(v___x_949_, 0, v_x_926_);
v___x_955_ = v___x_949_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_x_926_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_x_927_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
v___y_941_ = v___x_955_;
goto v___jp_940_;
}
}
}
}
case 1:
{
lean_object* v_node_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_970_; 
v_node_958_ = lean_ctor_get(v_v_937_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v_v_937_);
if (v_isSharedCheck_970_ == 0)
{
v___x_960_ = v_v_937_;
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_node_958_);
lean_dec(v_v_937_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
size_t v___x_962_; size_t v___x_963_; size_t v___x_964_; size_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_962_ = ((size_t)5ULL);
v___x_963_ = lean_usize_shift_right(v_x_924_, v___x_962_);
v___x_964_ = ((size_t)1ULL);
v___x_965_ = lean_usize_add(v_x_925_, v___x_964_);
v___x_966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_node_958_, v___x_963_, v___x_965_, v_x_926_, v_x_927_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_966_);
v___x_968_ = v___x_960_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
v___y_941_ = v___x_968_;
goto v___jp_940_;
}
}
}
default: 
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v_x_926_);
lean_ctor_set(v___x_971_, 1, v_x_927_);
v___y_941_ = v___x_971_;
goto v___jp_940_;
}
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = lean_array_fset(v_xs_x27_939_, v_j_931_, v___y_941_);
lean_dec(v_j_931_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_942_);
v___x_944_ = v___x_935_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
else
{
lean_object* v_ks_974_; lean_object* v_vs_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_993_; 
v_ks_974_ = lean_ctor_get(v_x_923_, 0);
v_vs_975_ = lean_ctor_get(v_x_923_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_x_923_);
if (v_isSharedCheck_993_ == 0)
{
v___x_977_ = v_x_923_;
v_isShared_978_ = v_isSharedCheck_993_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_vs_975_);
lean_inc(v_ks_974_);
lean_dec(v_x_923_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_993_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_ks_974_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_vs_975_);
v___x_980_ = v_reuseFailAlloc_992_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v_newNode_981_; size_t v___x_982_; uint8_t v___x_983_; 
v_newNode_981_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(v___x_980_, v_x_926_, v_x_927_);
v___x_982_ = ((size_t)7ULL);
v___x_983_ = lean_usize_dec_le(v___x_982_, v_x_925_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_984_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_981_);
v___x_985_ = lean_unsigned_to_nat(4u);
v___x_986_ = lean_nat_dec_lt(v___x_984_, v___x_985_);
lean_dec(v___x_984_);
if (v___x_986_ == 0)
{
lean_object* v_ks_987_; lean_object* v_vs_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_ks_987_ = lean_ctor_get(v_newNode_981_, 0);
lean_inc_ref(v_ks_987_);
v_vs_988_ = lean_ctor_get(v_newNode_981_, 1);
lean_inc_ref(v_vs_988_);
lean_dec_ref(v_newNode_981_);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0);
v___x_991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_x_925_, v_ks_987_, v_vs_988_, v___x_989_, v___x_990_);
lean_dec_ref(v_vs_988_);
lean_dec_ref(v_ks_987_);
return v___x_991_;
}
else
{
return v_newNode_981_;
}
}
else
{
return v_newNode_981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(size_t v_depth_994_, lean_object* v_keys_995_, lean_object* v_vals_996_, lean_object* v_i_997_, lean_object* v_entries_998_){
_start:
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = lean_array_get_size(v_keys_995_);
v___x_1000_ = lean_nat_dec_lt(v_i_997_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_dec(v_i_997_);
return v_entries_998_;
}
else
{
lean_object* v_k_1001_; lean_object* v_v_1002_; uint64_t v___x_1003_; size_t v_h_1004_; size_t v___x_1005_; lean_object* v___x_1006_; size_t v___x_1007_; size_t v___x_1008_; size_t v___x_1009_; size_t v_h_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_k_1001_ = lean_array_fget_borrowed(v_keys_995_, v_i_997_);
v_v_1002_ = lean_array_fget_borrowed(v_vals_996_, v_i_997_);
v___x_1003_ = l_Lean_instHashableMVarId_hash(v_k_1001_);
v_h_1004_ = lean_uint64_to_usize(v___x_1003_);
v___x_1005_ = ((size_t)5ULL);
v___x_1006_ = lean_unsigned_to_nat(1u);
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = lean_usize_sub(v_depth_994_, v___x_1007_);
v___x_1009_ = lean_usize_mul(v___x_1005_, v___x_1008_);
v_h_1010_ = lean_usize_shift_right(v_h_1004_, v___x_1009_);
v___x_1011_ = lean_nat_add(v_i_997_, v___x_1006_);
lean_dec(v_i_997_);
lean_inc(v_v_1002_);
lean_inc(v_k_1001_);
v___x_1012_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_entries_998_, v_h_1010_, v_depth_994_, v_k_1001_, v_v_1002_);
v_i_997_ = v___x_1011_;
v_entries_998_ = v___x_1012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg___boxed(lean_object* v_depth_1014_, lean_object* v_keys_1015_, lean_object* v_vals_1016_, lean_object* v_i_1017_, lean_object* v_entries_1018_){
_start:
{
size_t v_depth_boxed_1019_; lean_object* v_res_1020_; 
v_depth_boxed_1019_ = lean_unbox_usize(v_depth_1014_);
lean_dec(v_depth_1014_);
v_res_1020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_depth_boxed_1019_, v_keys_1015_, v_vals_1016_, v_i_1017_, v_entries_1018_);
lean_dec_ref(v_vals_1016_);
lean_dec_ref(v_keys_1015_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___boxed(lean_object* v_x_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
size_t v_x_17057__boxed_1026_; size_t v_x_17058__boxed_1027_; lean_object* v_res_1028_; 
v_x_17057__boxed_1026_ = lean_unbox_usize(v_x_1022_);
lean_dec(v_x_1022_);
v_x_17058__boxed_1027_ = lean_unbox_usize(v_x_1023_);
lean_dec(v_x_1023_);
v_res_1028_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_1021_, v_x_17057__boxed_1026_, v_x_17058__boxed_1027_, v_x_1024_, v_x_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(lean_object* v_x_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
uint64_t v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_1035_; 
v___x_1032_ = l_Lean_instHashableMVarId_hash(v_x_1030_);
v___x_1033_ = lean_uint64_to_usize(v___x_1032_);
v___x_1034_ = ((size_t)1ULL);
v___x_1035_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_1029_, v___x_1033_, v___x_1034_, v_x_1030_, v_x_1031_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(lean_object* v_mvarId_1036_, lean_object* v_val_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; lean_object* v_mctx_1041_; lean_object* v_cache_1042_; lean_object* v_zetaDeltaFVarIds_1043_; lean_object* v_postponed_1044_; lean_object* v_diag_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1074_; 
v___x_1040_ = lean_st_ref_take(v___y_1038_);
v_mctx_1041_ = lean_ctor_get(v___x_1040_, 0);
v_cache_1042_ = lean_ctor_get(v___x_1040_, 1);
v_zetaDeltaFVarIds_1043_ = lean_ctor_get(v___x_1040_, 2);
v_postponed_1044_ = lean_ctor_get(v___x_1040_, 3);
v_diag_1045_ = lean_ctor_get(v___x_1040_, 4);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1047_ = v___x_1040_;
v_isShared_1048_ = v_isSharedCheck_1074_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_diag_1045_);
lean_inc(v_postponed_1044_);
lean_inc(v_zetaDeltaFVarIds_1043_);
lean_inc(v_cache_1042_);
lean_inc(v_mctx_1041_);
lean_dec(v___x_1040_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1074_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_depth_1049_; lean_object* v_levelAssignDepth_1050_; lean_object* v_lmvarCounter_1051_; lean_object* v_mvarCounter_1052_; lean_object* v_lDecls_1053_; lean_object* v_decls_1054_; lean_object* v_userNames_1055_; lean_object* v_lAssignment_1056_; lean_object* v_eAssignment_1057_; lean_object* v_dAssignment_1058_; lean_object* v_instanceTypedMVars_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1073_; 
v_depth_1049_ = lean_ctor_get(v_mctx_1041_, 0);
v_levelAssignDepth_1050_ = lean_ctor_get(v_mctx_1041_, 1);
v_lmvarCounter_1051_ = lean_ctor_get(v_mctx_1041_, 2);
v_mvarCounter_1052_ = lean_ctor_get(v_mctx_1041_, 3);
v_lDecls_1053_ = lean_ctor_get(v_mctx_1041_, 4);
v_decls_1054_ = lean_ctor_get(v_mctx_1041_, 5);
v_userNames_1055_ = lean_ctor_get(v_mctx_1041_, 6);
v_lAssignment_1056_ = lean_ctor_get(v_mctx_1041_, 7);
v_eAssignment_1057_ = lean_ctor_get(v_mctx_1041_, 8);
v_dAssignment_1058_ = lean_ctor_get(v_mctx_1041_, 9);
v_instanceTypedMVars_1059_ = lean_ctor_get(v_mctx_1041_, 10);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_mctx_1041_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1061_ = v_mctx_1041_;
v_isShared_1062_ = v_isSharedCheck_1073_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_instanceTypedMVars_1059_);
lean_inc(v_dAssignment_1058_);
lean_inc(v_eAssignment_1057_);
lean_inc(v_lAssignment_1056_);
lean_inc(v_userNames_1055_);
lean_inc(v_decls_1054_);
lean_inc(v_lDecls_1053_);
lean_inc(v_mvarCounter_1052_);
lean_inc(v_lmvarCounter_1051_);
lean_inc(v_levelAssignDepth_1050_);
lean_inc(v_depth_1049_);
lean_dec(v_mctx_1041_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1073_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(v_eAssignment_1057_, v_mvarId_1036_, v_val_1037_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 8, v___x_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_depth_1049_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_levelAssignDepth_1050_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_lmvarCounter_1051_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v_mvarCounter_1052_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v_lDecls_1053_);
lean_ctor_set(v_reuseFailAlloc_1072_, 5, v_decls_1054_);
lean_ctor_set(v_reuseFailAlloc_1072_, 6, v_userNames_1055_);
lean_ctor_set(v_reuseFailAlloc_1072_, 7, v_lAssignment_1056_);
lean_ctor_set(v_reuseFailAlloc_1072_, 8, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1072_, 9, v_dAssignment_1058_);
lean_ctor_set(v_reuseFailAlloc_1072_, 10, v_instanceTypedMVars_1059_);
v___x_1065_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1065_);
v___x_1067_ = v___x_1047_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_cache_1042_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v_zetaDeltaFVarIds_1043_);
lean_ctor_set(v_reuseFailAlloc_1071_, 3, v_postponed_1044_);
lean_ctor_set(v_reuseFailAlloc_1071_, 4, v_diag_1045_);
v___x_1067_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_st_ref_put(v___y_1038_, v___x_1067_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg___boxed(lean_object* v_mvarId_1075_, lean_object* v_val_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(v_mvarId_1075_, v_val_1076_, v___y_1077_);
lean_dec(v___y_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(lean_object* v___x_1080_, lean_object* v_snd_1081_, lean_object* v_a_1082_, lean_object* v_fst_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; 
v___x_1093_ = lean_st_mk_ref(v___x_1080_);
lean_inc(v___x_1093_);
v___f_1094_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1094_, 0, v___x_1093_);
v___x_1095_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(v_snd_1081_, v_a_1082_, v___f_1094_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(v_fst_1083_, v_a_1096_, v___y_1089_);
lean_dec_ref(v___x_1097_);
v___x_1098_ = lean_st_ref_get(v___x_1093_);
lean_dec(v___x_1093_);
v___x_1099_ = lean_array_to_list(v___x_1098_);
v___x_1100_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1099_, v___y_1085_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1100_;
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec(v___x_1093_);
lean_dec(v_fst_1083_);
v_a_1101_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1095_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1095_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1___boxed(lean_object* v___x_1109_, lean_object* v_snd_1110_, lean_object* v_a_1111_, lean_object* v_fst_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(v___x_1109_, v_snd_1110_, v_a_1111_, v_fst_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(lean_object* v_ref_1123_, lean_object* v_msg_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_toCold_1130_; lean_object* v_currRecDepth_1131_; lean_object* v_ref_1132_; uint8_t v_diag_1133_; uint8_t v_suppressElabErrors_1134_; lean_object* v_ref_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_toCold_1130_ = lean_ctor_get(v___y_1127_, 0);
v_currRecDepth_1131_ = lean_ctor_get(v___y_1127_, 1);
v_ref_1132_ = lean_ctor_get(v___y_1127_, 2);
v_diag_1133_ = lean_ctor_get_uint8(v___y_1127_, sizeof(void*)*3);
v_suppressElabErrors_1134_ = lean_ctor_get_uint8(v___y_1127_, sizeof(void*)*3 + 1);
v_ref_1135_ = l_Lean_replaceRef(v_ref_1123_, v_ref_1132_);
lean_inc(v_currRecDepth_1131_);
lean_inc_ref(v_toCold_1130_);
v___x_1136_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1136_, 0, v_toCold_1130_);
lean_ctor_set(v___x_1136_, 1, v_currRecDepth_1131_);
lean_ctor_set(v___x_1136_, 2, v_ref_1135_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*3, v_diag_1133_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*3 + 1, v_suppressElabErrors_1134_);
v___x_1137_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v_msg_1124_, v___y_1125_, v___y_1126_, v___x_1136_, v___y_1128_);
lean_dec_ref_known(v___x_1136_, 3);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg___boxed(lean_object* v_ref_1138_, lean_object* v_msg_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_ref_1138_, v_msg_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v_ref_1138_);
return v_res_1145_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = l_Lean_maxRecDepthErrorMessage;
v___x_1152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3);
v___x_1154_ = l_Lean_MessageData_ofFormat(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4);
v___x_1156_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2));
v___x_1157_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___x_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(lean_object* v_ref_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_ref_1158_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_ref_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(lean_object* v_a_1166_, lean_object* v_x_1167_){
_start:
{
if (lean_obj_tag(v_x_1167_) == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_box(0);
return v___x_1168_;
}
else
{
lean_object* v_key_1169_; lean_object* v_value_1170_; lean_object* v_tail_1171_; uint8_t v___x_1172_; 
v_key_1169_ = lean_ctor_get(v_x_1167_, 0);
v_value_1170_ = lean_ctor_get(v_x_1167_, 1);
v_tail_1171_ = lean_ctor_get(v_x_1167_, 2);
v___x_1172_ = lean_name_eq(v_key_1169_, v_a_1166_);
if (v___x_1172_ == 0)
{
v_x_1167_ = v_tail_1171_;
goto _start;
}
else
{
lean_object* v___x_1174_; 
lean_inc(v_value_1170_);
v___x_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_value_1170_);
return v___x_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg___boxed(lean_object* v_a_1175_, lean_object* v_x_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_1175_, v_x_1176_);
lean_dec(v_x_1176_);
lean_dec(v_a_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(lean_object* v_m_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_buckets_1180_; lean_object* v___x_1181_; uint64_t v___y_1183_; 
v_buckets_1180_ = lean_ctor_get(v_m_1178_, 1);
v___x_1181_ = lean_array_get_size(v_buckets_1180_);
if (lean_obj_tag(v_a_1179_) == 0)
{
uint64_t v___x_1197_; 
v___x_1197_ = 1723ULL;
v___y_1183_ = v___x_1197_;
goto v___jp_1182_;
}
else
{
uint64_t v_hash_1198_; 
v_hash_1198_ = lean_ctor_get_uint64(v_a_1179_, sizeof(void*)*2);
v___y_1183_ = v_hash_1198_;
goto v___jp_1182_;
}
v___jp_1182_:
{
uint64_t v___x_1184_; uint64_t v___x_1185_; uint64_t v_fold_1186_; uint64_t v___x_1187_; uint64_t v___x_1188_; uint64_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; size_t v___x_1192_; size_t v___x_1193_; size_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1184_ = 32ULL;
v___x_1185_ = lean_uint64_shift_right(v___y_1183_, v___x_1184_);
v_fold_1186_ = lean_uint64_xor(v___y_1183_, v___x_1185_);
v___x_1187_ = 16ULL;
v___x_1188_ = lean_uint64_shift_right(v_fold_1186_, v___x_1187_);
v___x_1189_ = lean_uint64_xor(v_fold_1186_, v___x_1188_);
v___x_1190_ = lean_uint64_to_usize(v___x_1189_);
v___x_1191_ = lean_usize_of_nat(v___x_1181_);
v___x_1192_ = ((size_t)1ULL);
v___x_1193_ = lean_usize_sub(v___x_1191_, v___x_1192_);
v___x_1194_ = lean_usize_land(v___x_1190_, v___x_1193_);
v___x_1195_ = lean_array_uget_borrowed(v_buckets_1180_, v___x_1194_);
v___x_1196_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_1179_, v___x_1195_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_m_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v_m_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec_ref(v_m_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(lean_object* v_keys_1202_, lean_object* v_i_1203_, lean_object* v_k_1204_){
_start:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_array_get_size(v_keys_1202_);
v___x_1206_ = lean_nat_dec_lt(v_i_1203_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_dec(v_i_1203_);
return v___x_1206_;
}
else
{
lean_object* v_k_x27_1207_; uint8_t v___x_1208_; 
v_k_x27_1207_ = lean_array_fget_borrowed(v_keys_1202_, v_i_1203_);
v___x_1208_ = l_Lean_instBEqExtraModUse_beq(v_k_1204_, v_k_x27_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_nat_add(v_i_1203_, v___x_1209_);
lean_dec(v_i_1203_);
v_i_1203_ = v___x_1210_;
goto _start;
}
else
{
lean_dec(v_i_1203_);
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg___boxed(lean_object* v_keys_1212_, lean_object* v_i_1213_, lean_object* v_k_1214_){
_start:
{
uint8_t v_res_1215_; lean_object* v_r_1216_; 
v_res_1215_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_keys_1212_, v_i_1213_, v_k_1214_);
lean_dec_ref(v_k_1214_);
lean_dec_ref(v_keys_1212_);
v_r_1216_ = lean_box(v_res_1215_);
return v_r_1216_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(lean_object* v_x_1217_, size_t v_x_1218_, lean_object* v_x_1219_){
_start:
{
if (lean_obj_tag(v_x_1217_) == 0)
{
lean_object* v_es_1220_; lean_object* v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; lean_object* v_j_1224_; lean_object* v___x_1225_; 
v_es_1220_ = lean_ctor_get(v_x_1217_, 0);
v___x_1221_ = lean_box(2);
v___x_1222_ = ((size_t)31ULL);
v___x_1223_ = lean_usize_land(v_x_1218_, v___x_1222_);
v_j_1224_ = lean_usize_to_nat(v___x_1223_);
v___x_1225_ = lean_array_get_borrowed(v___x_1221_, v_es_1220_, v_j_1224_);
lean_dec(v_j_1224_);
switch(lean_obj_tag(v___x_1225_))
{
case 0:
{
lean_object* v_key_1226_; uint8_t v___x_1227_; 
v_key_1226_ = lean_ctor_get(v___x_1225_, 0);
v___x_1227_ = l_Lean_instBEqExtraModUse_beq(v_x_1219_, v_key_1226_);
return v___x_1227_;
}
case 1:
{
lean_object* v_node_1228_; size_t v___x_1229_; size_t v___x_1230_; 
v_node_1228_ = lean_ctor_get(v___x_1225_, 0);
v___x_1229_ = ((size_t)5ULL);
v___x_1230_ = lean_usize_shift_right(v_x_1218_, v___x_1229_);
v_x_1217_ = v_node_1228_;
v_x_1218_ = v___x_1230_;
goto _start;
}
default: 
{
uint8_t v___x_1232_; 
v___x_1232_ = 0;
return v___x_1232_;
}
}
}
else
{
lean_object* v_ks_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_ks_1233_ = lean_ctor_get(v_x_1217_, 0);
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_ks_1233_, v___x_1234_, v_x_1219_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg___boxed(lean_object* v_x_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_){
_start:
{
size_t v_x_17468__boxed_1239_; uint8_t v_res_1240_; lean_object* v_r_1241_; 
v_x_17468__boxed_1239_ = lean_unbox_usize(v_x_1237_);
lean_dec(v_x_1237_);
v_res_1240_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_1236_, v_x_17468__boxed_1239_, v_x_1238_);
lean_dec_ref(v_x_1238_);
lean_dec_ref(v_x_1236_);
v_r_1241_ = lean_box(v_res_1240_);
return v_r_1241_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_1242_, lean_object* v_x_1243_){
_start:
{
uint64_t v___x_1244_; size_t v___x_1245_; uint8_t v___x_1246_; 
v___x_1244_ = l_Lean_instHashableExtraModUse_hash(v_x_1243_);
v___x_1245_ = lean_uint64_to_usize(v___x_1244_);
v___x_1246_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_1242_, v___x_1245_, v_x_1243_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v_x_1247_, v_x_1248_);
lean_dec_ref(v_x_1248_);
lean_dec_ref(v_x_1247_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1));
v___x_1254_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0));
v___x_1255_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1254_, v___x_1253_);
return v___x_1255_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1256_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3);
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4);
v___x_1262_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
lean_ctor_set(v___x_1262_, 3, v___x_1261_);
lean_ctor_set(v___x_1262_, 4, v___x_1261_);
lean_ctor_set(v___x_1262_, 5, v___x_1261_);
return v___x_1262_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9));
v___x_1268_ = l_Lean_stringToMessageData(v___x_1267_);
return v___x_1268_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11));
v___x_1271_ = l_Lean_stringToMessageData(v___x_1270_);
return v___x_1271_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1));
v___x_1273_ = l_Lean_stringToMessageData(v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14(void){
_start:
{
lean_object* v_cls_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_cls_1274_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8));
v___x_1275_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17));
v___x_1276_ = l_Lean_Name_append(v___x_1275_, v_cls_1274_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17));
v___x_1282_ = l_Lean_stringToMessageData(v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(lean_object* v_mod_1287_, uint8_t v_isMeta_1288_, lean_object* v_hint_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; lean_object* v_env_1296_; uint8_t v_isExporting_1297_; lean_object* v___x_1298_; lean_object* v_env_1299_; lean_object* v___x_1300_; lean_object* v_entry_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1295_ = lean_st_ref_get(v___y_1293_);
v_env_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc_ref(v_env_1296_);
lean_dec(v___x_1295_);
v_isExporting_1297_ = lean_ctor_get_uint8(v_env_1296_, sizeof(void*)*8);
lean_dec_ref(v_env_1296_);
v___x_1298_ = lean_st_ref_get(v___y_1293_);
v_env_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc_ref(v_env_1299_);
lean_dec(v___x_1298_);
v___x_1300_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2);
lean_inc(v_mod_1287_);
v_entry_1301_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1301_, 0, v_mod_1287_);
lean_ctor_set_uint8(v_entry_1301_, sizeof(void*)*1, v_isExporting_1297_);
lean_ctor_set_uint8(v_entry_1301_, sizeof(void*)*1 + 1, v_isMeta_1288_);
v___x_1302_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1303_ = lean_box(1);
v___x_1304_ = lean_box(0);
v___x_1347_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1300_, v___x_1302_, v_env_1299_, v___x_1303_, v___x_1304_);
v___x_1348_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v___x_1347_, v_entry_1301_);
lean_dec(v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v_toCold_1349_; lean_object* v_options_1350_; uint8_t v_hasTrace_1351_; 
v_toCold_1349_ = lean_ctor_get(v___y_1292_, 0);
v_options_1350_ = lean_ctor_get(v_toCold_1349_, 2);
v_hasTrace_1351_ = lean_ctor_get_uint8(v_options_1350_, sizeof(void*)*1);
if (v_hasTrace_1351_ == 0)
{
lean_dec(v_hint_1289_);
lean_dec(v_mod_1287_);
v___y_1306_ = v___y_1291_;
v___y_1307_ = v___y_1293_;
goto v___jp_1305_;
}
else
{
lean_object* v_inheritedTraceOptions_1352_; lean_object* v_cls_1353_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v_inheritedTraceOptions_1352_ = lean_ctor_get(v_toCold_1349_, 11);
v_cls_1353_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8));
v___x_1373_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14);
v___x_1374_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1352_, v_options_1350_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_dec(v_hint_1289_);
lean_dec(v_mod_1287_);
v___y_1306_ = v___y_1291_;
v___y_1307_ = v___y_1293_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1375_; lean_object* v___y_1377_; 
v___x_1375_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16);
if (v_isExporting_1297_ == 0)
{
lean_object* v___x_1384_; 
v___x_1384_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21));
v___y_1377_ = v___x_1384_;
goto v___jp_1376_;
}
else
{
lean_object* v___x_1385_; 
v___x_1385_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22));
v___y_1377_ = v___x_1385_;
goto v___jp_1376_;
}
v___jp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_inc_ref(v___y_1377_);
v___x_1378_ = l_Lean_stringToMessageData(v___y_1377_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1375_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
if (v_isMeta_1288_ == 0)
{
lean_object* v___x_1382_; 
v___x_1382_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19));
v___y_1360_ = v___x_1381_;
v___y_1361_ = v___x_1382_;
goto v___jp_1359_;
}
else
{
lean_object* v___x_1383_; 
v___x_1383_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20));
v___y_1360_ = v___x_1381_;
v___y_1361_ = v___x_1383_;
goto v___jp_1359_;
}
}
}
v___jp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___y_1355_);
lean_ctor_set(v___x_1357_, 1, v___y_1356_);
v___x_1358_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_cls_1353_, v___x_1357_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_dec_ref_known(v___x_1358_, 1);
v___y_1306_ = v___y_1291_;
v___y_1307_ = v___y_1293_;
goto v___jp_1305_;
}
else
{
lean_dec_ref_known(v_entry_1301_, 1);
return v___x_1358_;
}
}
v___jp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
lean_inc_ref(v___y_1361_);
v___x_1362_ = l_Lean_stringToMessageData(v___y_1361_);
v___x_1363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___y_1360_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = l_Lean_MessageData_ofName(v_mod_1287_);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_Name_isAnonymous(v_hint_1289_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12);
v___x_1370_ = l_Lean_MessageData_ofName(v_hint_1289_);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___y_1355_ = v___x_1367_;
v___y_1356_ = v___x_1371_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1372_; 
lean_dec(v_hint_1289_);
v___x_1372_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13);
v___y_1355_ = v___x_1367_;
v___y_1356_ = v___x_1372_;
goto v___jp_1354_;
}
}
}
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec_ref_known(v_entry_1301_, 1);
lean_dec(v_hint_1289_);
lean_dec(v_mod_1287_);
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
v___jp_1305_:
{
lean_object* v___x_1308_; lean_object* v_toEnvExtension_1309_; lean_object* v_env_1310_; lean_object* v_nextMacroScope_1311_; lean_object* v_ngen_1312_; lean_object* v_auxDeclNGen_1313_; lean_object* v_traceState_1314_; lean_object* v_messages_1315_; lean_object* v_infoState_1316_; lean_object* v_snapshotTasks_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1345_; 
v___x_1308_ = lean_st_ref_take(v___y_1307_);
v_toEnvExtension_1309_ = lean_ctor_get(v___x_1302_, 0);
v_env_1310_ = lean_ctor_get(v___x_1308_, 0);
v_nextMacroScope_1311_ = lean_ctor_get(v___x_1308_, 1);
v_ngen_1312_ = lean_ctor_get(v___x_1308_, 2);
v_auxDeclNGen_1313_ = lean_ctor_get(v___x_1308_, 3);
v_traceState_1314_ = lean_ctor_get(v___x_1308_, 4);
v_messages_1315_ = lean_ctor_get(v___x_1308_, 6);
v_infoState_1316_ = lean_ctor_get(v___x_1308_, 7);
v_snapshotTasks_1317_ = lean_ctor_get(v___x_1308_, 8);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v___x_1308_, 5);
lean_dec(v_unused_1346_);
v___x_1319_ = v___x_1308_;
v_isShared_1320_ = v_isSharedCheck_1345_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_snapshotTasks_1317_);
lean_inc(v_infoState_1316_);
lean_inc(v_messages_1315_);
lean_inc(v_traceState_1314_);
lean_inc(v_auxDeclNGen_1313_);
lean_inc(v_ngen_1312_);
lean_inc(v_nextMacroScope_1311_);
lean_inc(v_env_1310_);
lean_dec(v___x_1308_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1345_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_asyncMode_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v_asyncMode_1321_ = lean_ctor_get(v_toEnvExtension_1309_, 2);
v___x_1322_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1302_, v_env_1310_, v_entry_1301_, v_asyncMode_1321_, v___x_1304_);
v___x_1323_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 5, v___x_1323_);
lean_ctor_set(v___x_1319_, 0, v___x_1322_);
v___x_1325_ = v___x_1319_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_nextMacroScope_1311_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_ngen_1312_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_auxDeclNGen_1313_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v_traceState_1314_);
lean_ctor_set(v_reuseFailAlloc_1344_, 5, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1344_, 6, v_messages_1315_);
lean_ctor_set(v_reuseFailAlloc_1344_, 7, v_infoState_1316_);
lean_ctor_set(v_reuseFailAlloc_1344_, 8, v_snapshotTasks_1317_);
v___x_1325_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_mctx_1328_; lean_object* v_zetaDeltaFVarIds_1329_; lean_object* v_postponed_1330_; lean_object* v_diag_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1342_; 
v___x_1326_ = lean_st_ref_put(v___y_1307_, v___x_1325_);
v___x_1327_ = lean_st_ref_take(v___y_1306_);
v_mctx_1328_ = lean_ctor_get(v___x_1327_, 0);
v_zetaDeltaFVarIds_1329_ = lean_ctor_get(v___x_1327_, 2);
v_postponed_1330_ = lean_ctor_get(v___x_1327_, 3);
v_diag_1331_ = lean_ctor_get(v___x_1327_, 4);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v___x_1327_, 1);
lean_dec(v_unused_1343_);
v___x_1333_ = v___x_1327_;
v_isShared_1334_ = v_isSharedCheck_1342_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_diag_1331_);
lean_inc(v_postponed_1330_);
lean_inc(v_zetaDeltaFVarIds_1329_);
lean_inc(v_mctx_1328_);
lean_dec(v___x_1327_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1342_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v___x_1335_);
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_mctx_1328_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_zetaDeltaFVarIds_1329_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_postponed_1330_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v_diag_1331_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = lean_st_ref_put(v___y_1306_, v___x_1337_);
v___x_1339_ = lean_box(0);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_mod_1388_, lean_object* v_isMeta_1389_, lean_object* v_hint_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
uint8_t v_isMeta_boxed_1396_; lean_object* v_res_1397_; 
v_isMeta_boxed_1396_ = lean_unbox(v_isMeta_1389_);
v_res_1397_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_mod_1388_, v_isMeta_boxed_1396_, v_hint_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(lean_object* v___x_1398_, lean_object* v_declName_1399_, lean_object* v_as_1400_, size_t v_sz_1401_, size_t v_i_1402_, lean_object* v_b_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_usize_dec_lt(v_i_1402_, v_sz_1401_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; 
lean_dec(v_declName_1399_);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_b_1403_);
return v___x_1414_;
}
else
{
lean_object* v___x_1415_; lean_object* v_modules_1416_; lean_object* v___x_1417_; lean_object* v_a_1418_; lean_object* v___x_1419_; lean_object* v_toImport_1420_; lean_object* v_module_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; 
v___x_1415_ = l_Lean_Environment_header(v___x_1398_);
v_modules_1416_ = lean_ctor_get(v___x_1415_, 3);
lean_inc_ref(v_modules_1416_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1418_ = lean_array_uget_borrowed(v_as_1400_, v_i_1402_);
v___x_1419_ = lean_array_get(v___x_1417_, v_modules_1416_, v_a_1418_);
lean_dec_ref(v_modules_1416_);
v_toImport_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc_ref(v_toImport_1420_);
lean_dec(v___x_1419_);
v_module_1421_ = lean_ctor_get(v_toImport_1420_, 0);
lean_inc(v_module_1421_);
lean_dec_ref(v_toImport_1420_);
v___x_1422_ = 0;
lean_inc(v_declName_1399_);
v___x_1423_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_module_1421_, v___x_1422_, v_declName_1399_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v___x_1424_; size_t v___x_1425_; size_t v___x_1426_; 
lean_dec_ref_known(v___x_1423_, 1);
v___x_1424_ = lean_box(0);
v___x_1425_ = ((size_t)1ULL);
v___x_1426_ = lean_usize_add(v_i_1402_, v___x_1425_);
v_i_1402_ = v___x_1426_;
v_b_1403_ = v___x_1424_;
goto _start;
}
else
{
lean_dec(v_declName_1399_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4___boxed(lean_object* v___x_1428_, lean_object* v_declName_1429_, lean_object* v_as_1430_, lean_object* v_sz_1431_, lean_object* v_i_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
size_t v_sz_boxed_1443_; size_t v_i_boxed_1444_; lean_object* v_res_1445_; 
v_sz_boxed_1443_ = lean_unbox_usize(v_sz_1431_);
lean_dec(v_sz_1431_);
v_i_boxed_1444_ = lean_unbox_usize(v_i_1432_);
lean_dec(v_i_1432_);
v_res_1445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(v___x_1428_, v_declName_1429_, v_as_1430_, v_sz_boxed_1443_, v_i_boxed_1444_, v_b_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec_ref(v_as_1430_);
lean_dec_ref(v___x_1428_);
return v_res_1445_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1));
v___x_1449_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0));
v___x_1450_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1449_, v___x_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(lean_object* v_declName_1453_, uint8_t v_isMeta_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; lean_object* v_env_1468_; lean_object* v___y_1470_; lean_object* v___x_1483_; 
v___x_1464_ = lean_st_ref_get(v___y_1462_);
v_env_1468_ = lean_ctor_get(v___x_1464_, 0);
lean_inc_ref(v_env_1468_);
lean_dec(v___x_1464_);
v___x_1483_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1468_, v_declName_1453_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_dec_ref(v_env_1468_);
lean_dec(v_declName_1453_);
goto v___jp_1465_;
}
else
{
lean_object* v_val_1484_; lean_object* v___x_1485_; lean_object* v_modules_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v_val_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = l_Lean_Environment_header(v_env_1468_);
v_modules_1486_ = lean_ctor_get(v___x_1485_, 3);
lean_inc_ref(v_modules_1486_);
lean_dec_ref(v___x_1485_);
v___x_1487_ = lean_array_get_size(v_modules_1486_);
v___x_1488_ = lean_nat_dec_lt(v_val_1484_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_dec_ref(v_modules_1486_);
lean_dec(v_val_1484_);
lean_dec_ref(v_env_1468_);
lean_dec(v_declName_1453_);
goto v___jp_1465_;
}
else
{
lean_object* v___x_1489_; lean_object* v_env_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___y_1494_; 
v___x_1489_ = lean_st_ref_get(v___y_1462_);
v_env_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc_ref(v_env_1490_);
lean_dec(v___x_1489_);
v___x_1491_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2);
v___x_1492_ = lean_array_fget(v_modules_1486_, v_val_1484_);
lean_dec(v_val_1484_);
lean_dec_ref(v_modules_1486_);
if (v_isMeta_1454_ == 0)
{
lean_dec_ref(v_env_1490_);
v___y_1494_ = v_isMeta_1454_;
goto v___jp_1493_;
}
else
{
uint8_t v___x_1505_; 
lean_inc(v_declName_1453_);
v___x_1505_ = l_Lean_isMarkedMeta(v_env_1490_, v_declName_1453_);
if (v___x_1505_ == 0)
{
v___y_1494_ = v_isMeta_1454_;
goto v___jp_1493_;
}
else
{
uint8_t v___x_1506_; 
v___x_1506_ = 0;
v___y_1494_ = v___x_1506_;
goto v___jp_1493_;
}
}
v___jp_1493_:
{
lean_object* v_toImport_1495_; lean_object* v_module_1496_; lean_object* v___x_1497_; 
v_toImport_1495_ = lean_ctor_get(v___x_1492_, 0);
lean_inc_ref(v_toImport_1495_);
lean_dec(v___x_1492_);
v_module_1496_ = lean_ctor_get(v_toImport_1495_, 0);
lean_inc(v_module_1496_);
lean_dec_ref(v_toImport_1495_);
lean_inc(v_declName_1453_);
v___x_1497_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_module_1496_, v___y_1494_, v_declName_1453_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec_ref_known(v___x_1497_, 1);
v___x_1498_ = l_Lean_indirectModUseExt;
v___x_1499_ = lean_box(1);
v___x_1500_ = lean_box(0);
lean_inc_ref(v_env_1468_);
v___x_1501_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1491_, v___x_1498_, v_env_1468_, v___x_1499_, v___x_1500_);
v___x_1502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v___x_1501_, v_declName_1453_);
lean_dec(v___x_1501_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v___x_1503_; 
v___x_1503_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3));
v___y_1470_ = v___x_1503_;
goto v___jp_1469_;
}
else
{
lean_object* v_val_1504_; 
v_val_1504_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_val_1504_);
lean_dec_ref_known(v___x_1502_, 1);
v___y_1470_ = v_val_1504_;
goto v___jp_1469_;
}
}
else
{
lean_dec_ref(v_env_1468_);
lean_dec(v_declName_1453_);
return v___x_1497_;
}
}
}
}
v___jp_1465_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_box(0);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
v___jp_1469_:
{
lean_object* v___x_1471_; size_t v_sz_1472_; size_t v___x_1473_; lean_object* v___x_1474_; 
v___x_1471_ = lean_box(0);
v_sz_1472_ = lean_array_size(v___y_1470_);
v___x_1473_ = ((size_t)0ULL);
v___x_1474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(v_env_1468_, v_declName_1453_, v___y_1470_, v_sz_1472_, v___x_1473_, v___x_1471_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec_ref(v___y_1470_);
lean_dec_ref(v_env_1468_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v___x_1474_, 0);
lean_dec(v_unused_1482_);
v___x_1476_ = v___x_1474_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_dec(v___x_1474_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1471_);
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1471_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
else
{
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___boxed(lean_object* v_declName_1507_, lean_object* v_isMeta_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v_isMeta_boxed_1518_; lean_object* v_res_1519_; 
v_isMeta_boxed_1518_ = lean_unbox(v_isMeta_1508_);
v_res_1519_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(v_declName_1507_, v_isMeta_boxed_1518_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(lean_object* v_as_x27_1520_, lean_object* v_b_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
if (lean_obj_tag(v_as_x27_1520_) == 0)
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v_b_1521_);
return v___x_1531_;
}
else
{
lean_object* v_head_1532_; lean_object* v_tail_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; 
v_head_1532_ = lean_ctor_get(v_as_x27_1520_, 0);
v_tail_1533_ = lean_ctor_get(v_as_x27_1520_, 1);
v___x_1534_ = 1;
lean_inc(v_head_1532_);
v___x_1535_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(v_head_1532_, v___x_1534_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v___x_1536_; 
lean_dec_ref_known(v___x_1535_, 1);
v___x_1536_ = lean_box(0);
v_as_x27_1520_ = v_tail_1533_;
v_b_1521_ = v___x_1536_;
goto _start;
}
else
{
return v___x_1535_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg___boxed(lean_object* v_as_x27_1538_, lean_object* v_b_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_as_x27_1538_, v_b_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v_as_x27_1538_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(lean_object* v_currNamespace_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_currNamespace_1550_);
lean_ctor_set(v___x_1553_, 1, v___y_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(v_currNamespace_1554_, v___y_1555_, v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(lean_object* v_env_1558_, lean_object* v_options_1559_, lean_object* v_currNamespace_1560_, lean_object* v_openDecls_1561_, lean_object* v_n_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = l_Lean_ResolveName_resolveGlobalName(v_env_1558_, v_options_1559_, v_currNamespace_1560_, v_openDecls_1561_, v_n_1562_);
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___y_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed(lean_object* v_env_1567_, lean_object* v_options_1568_, lean_object* v_currNamespace_1569_, lean_object* v_openDecls_1570_, lean_object* v_n_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(v_env_1567_, v_options_1568_, v_currNamespace_1569_, v_openDecls_1570_, v_n_1571_, v___y_1572_, v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_options_1568_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(lean_object* v_x_1575_, lean_object* v___y_1576_){
_start:
{
if (lean_obj_tag(v_x_1575_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; 
v_a_1577_ = lean_ctor_get(v_x_1575_, 0);
lean_inc(v_a_1577_);
v___x_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1578_, 0, v_a_1577_);
lean_ctor_set(v___x_1578_, 1, v___y_1576_);
return v___x_1578_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
v_a_1579_ = lean_ctor_get(v_x_1575_, 0);
lean_inc(v_a_1579_);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_a_1579_);
lean_ctor_set(v___x_1580_, 1, v___y_1576_);
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg___boxed(lean_object* v_x_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v_x_1581_, v___y_1582_);
lean_dec_ref(v_x_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(lean_object* v_env_1584_, lean_object* v_stx_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1584_, v_stx_1585_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
if (lean_obj_tag(v_a_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1598_; 
v_a_1590_ = lean_ctor_get(v___x_1588_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v___x_1588_, 0);
lean_dec(v_unused_1599_);
v___x_1592_ = v___x_1588_;
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1598_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1594_ = lean_box(0);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1594_);
v___x_1596_ = v___x_1592_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_a_1590_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
else
{
lean_object* v_val_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1628_; 
v_val_1600_ = lean_ctor_get(v_a_1589_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_a_1589_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1602_ = v_a_1589_;
v_isShared_1603_ = v_isSharedCheck_1628_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_val_1600_);
lean_dec(v_a_1589_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1628_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v_snd_1604_; 
v_snd_1604_ = lean_ctor_get(v_val_1600_, 1);
lean_inc(v_snd_1604_);
lean_dec(v_val_1600_);
if (lean_obj_tag(v_snd_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1614_; 
lean_del_object(v___x_1602_);
v_a_1605_ = lean_ctor_get(v___x_1588_, 1);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1588_, 2);
v_a_1606_ = lean_ctor_get(v_snd_1604_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_snd_1604_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1608_ = v_snd_1604_;
v_isShared_1609_ = v_isSharedCheck_1614_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v_snd_1604_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1614_;
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
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v___x_1611_, v_a_1605_);
lean_dec_ref(v___x_1611_);
return v___x_1612_;
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1627_; 
v_a_1615_ = lean_ctor_get(v___x_1588_, 1);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1588_, 2);
v_a_1616_ = lean_ctor_get(v_snd_1604_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_snd_1604_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1618_ = v_snd_1604_;
v_isShared_1619_ = v_isSharedCheck_1627_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v_snd_1604_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1627_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v_a_1616_);
v___x_1621_ = v___x_1602_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1623_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1621_);
v___x_1623_ = v___x_1618_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v___x_1623_, v_a_1615_);
lean_dec_ref(v___x_1623_);
return v___x_1624_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_a_1629_ = lean_ctor_get(v___x_1588_, 0);
v_a_1630_ = lean_ctor_get(v___x_1588_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1588_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_inc(v_a_1629_);
lean_dec(v___x_1588_);
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
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1629_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_a_1630_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed(lean_object* v_env_1638_, lean_object* v_stx_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(v_env_1638_, v_stx_1639_, v___y_1640_, v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(lean_object* v_as_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
if (lean_obj_tag(v_as_1643_) == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
return v___x_1650_;
}
else
{
lean_object* v_toCold_1651_; lean_object* v_options_1652_; uint8_t v_hasTrace_1653_; 
v_toCold_1651_ = lean_ctor_get(v___y_1646_, 0);
v_options_1652_ = lean_ctor_get(v_toCold_1651_, 2);
v_hasTrace_1653_ = lean_ctor_get_uint8(v_options_1652_, sizeof(void*)*1);
if (v_hasTrace_1653_ == 0)
{
lean_object* v_tail_1654_; 
v_tail_1654_ = lean_ctor_get(v_as_1643_, 1);
lean_inc(v_tail_1654_);
lean_dec_ref_known(v_as_1643_, 2);
v_as_1643_ = v_tail_1654_;
goto _start;
}
else
{
lean_object* v_head_1656_; lean_object* v_tail_1657_; lean_object* v_fst_1658_; lean_object* v_snd_1659_; lean_object* v_inheritedTraceOptions_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v_head_1656_ = lean_ctor_get(v_as_1643_, 0);
lean_inc(v_head_1656_);
v_tail_1657_ = lean_ctor_get(v_as_1643_, 1);
lean_inc(v_tail_1657_);
lean_dec_ref_known(v_as_1643_, 2);
v_fst_1658_ = lean_ctor_get(v_head_1656_, 0);
lean_inc_n(v_fst_1658_, 2);
v_snd_1659_ = lean_ctor_get(v_head_1656_, 1);
lean_inc(v_snd_1659_);
lean_dec(v_head_1656_);
v_inheritedTraceOptions_1660_ = lean_ctor_get(v_toCold_1651_, 11);
v___x_1661_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17));
v___x_1662_ = l_Lean_Name_append(v___x_1661_, v_fst_1658_);
v___x_1663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1660_, v_options_1652_, v___x_1662_);
lean_dec(v___x_1662_);
if (v___x_1663_ == 0)
{
lean_dec(v_snd_1659_);
lean_dec(v_fst_1658_);
v_as_1643_ = v_tail_1657_;
goto _start;
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1665_, 0, v_snd_1659_);
v___x_1666_ = l_Lean_MessageData_ofFormat(v___x_1665_);
v___x_1667_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_fst_1658_, v___x_1666_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_dec_ref_known(v___x_1667_, 1);
v_as_1643_ = v_tail_1657_;
goto _start;
}
else
{
lean_dec(v_tail_1657_);
return v___x_1667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg___boxed(lean_object* v_as_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v_as_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(lean_object* v_env_1676_, lean_object* v_declName_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
uint8_t v___x_1680_; lean_object* v_env_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; uint8_t v___x_1684_; 
v___x_1680_ = 0;
v_env_1681_ = l_Lean_Environment_setExporting(v_env_1676_, v___x_1680_);
lean_inc(v_declName_1677_);
v___x_1682_ = l_Lean_mkPrivateName(v_env_1681_, v_declName_1677_);
v___x_1683_ = 1;
lean_inc_ref(v_env_1681_);
v___x_1684_ = l_Lean_Environment_contains(v_env_1681_, v___x_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1685_ = l_Lean_privateToUserName(v_declName_1677_);
v___x_1686_ = l_Lean_Environment_contains(v_env_1681_, v___x_1685_, v___x_1683_);
v___x_1687_ = lean_box(v___x_1686_);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v___y_1679_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec_ref(v_env_1681_);
lean_dec(v_declName_1677_);
v___x_1689_ = lean_box(v___x_1684_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set(v___x_1690_, 1, v___y_1679_);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed(lean_object* v_env_1691_, lean_object* v_declName_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(v_env_1691_, v_declName_1692_, v___y_1693_, v___y_1694_);
lean_dec_ref(v___y_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(lean_object* v_env_1696_, lean_object* v_currNamespace_1697_, lean_object* v_openDecls_1698_, lean_object* v_n_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = l_Lean_ResolveName_resolveNamespace(v_env_1696_, v_currNamespace_1697_, v_openDecls_1698_, v_n_1699_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v___y_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed(lean_object* v_env_1704_, lean_object* v_currNamespace_1705_, lean_object* v_openDecls_1706_, lean_object* v_n_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(v_env_1704_, v_currNamespace_1705_, v_openDecls_1706_, v_n_1707_, v___y_1708_, v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(lean_object* v_x_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; lean_object* v_toCold_1723_; lean_object* v_env_1724_; lean_object* v_currRecDepth_1725_; lean_object* v_ref_1726_; lean_object* v_options_1727_; lean_object* v_maxRecDepth_1728_; lean_object* v_currNamespace_1729_; lean_object* v_openDecls_1730_; lean_object* v_quotContext_1731_; lean_object* v_currMacroScope_1732_; lean_object* v___x_1733_; lean_object* v_nextMacroScope_1734_; lean_object* v___f_1735_; lean_object* v___f_1736_; lean_object* v___f_1737_; lean_object* v___f_1738_; lean_object* v___f_1739_; lean_object* v_methods_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1722_ = lean_st_ref_get(v___y_1720_);
v_toCold_1723_ = lean_ctor_get(v___y_1719_, 0);
v_env_1724_ = lean_ctor_get(v___x_1722_, 0);
lean_inc_ref_n(v_env_1724_, 4);
lean_dec(v___x_1722_);
v_currRecDepth_1725_ = lean_ctor_get(v___y_1719_, 1);
v_ref_1726_ = lean_ctor_get(v___y_1719_, 2);
v_options_1727_ = lean_ctor_get(v_toCold_1723_, 2);
v_maxRecDepth_1728_ = lean_ctor_get(v_toCold_1723_, 3);
v_currNamespace_1729_ = lean_ctor_get(v_toCold_1723_, 4);
v_openDecls_1730_ = lean_ctor_get(v_toCold_1723_, 5);
v_quotContext_1731_ = lean_ctor_get(v_toCold_1723_, 8);
v_currMacroScope_1732_ = lean_ctor_get(v_toCold_1723_, 9);
v___x_1733_ = lean_st_ref_get(v___y_1720_);
v_nextMacroScope_1734_ = lean_ctor_get(v___x_1733_, 1);
lean_inc(v_nextMacroScope_1734_);
lean_dec(v___x_1733_);
v___f_1735_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1735_, 0, v_env_1724_);
v___f_1736_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1736_, 0, v_env_1724_);
lean_inc_n(v_openDecls_1730_, 2);
lean_inc_n(v_currNamespace_1729_, 3);
v___f_1737_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1737_, 0, v_env_1724_);
lean_closure_set(v___f_1737_, 1, v_currNamespace_1729_);
lean_closure_set(v___f_1737_, 2, v_openDecls_1730_);
v___f_1738_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1738_, 0, v_currNamespace_1729_);
lean_inc_ref(v_options_1727_);
v___f_1739_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1739_, 0, v_env_1724_);
lean_closure_set(v___f_1739_, 1, v_options_1727_);
lean_closure_set(v___f_1739_, 2, v_currNamespace_1729_);
lean_closure_set(v___f_1739_, 3, v_openDecls_1730_);
v_methods_1740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1740_, 0, v___f_1735_);
lean_ctor_set(v_methods_1740_, 1, v___f_1738_);
lean_ctor_set(v_methods_1740_, 2, v___f_1736_);
lean_ctor_set(v_methods_1740_, 3, v___f_1737_);
lean_ctor_set(v_methods_1740_, 4, v___f_1739_);
lean_inc(v_ref_1726_);
lean_inc(v_maxRecDepth_1728_);
lean_inc(v_currRecDepth_1725_);
lean_inc(v_currMacroScope_1732_);
lean_inc(v_quotContext_1731_);
v___x_1741_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1741_, 0, v_methods_1740_);
lean_ctor_set(v___x_1741_, 1, v_quotContext_1731_);
lean_ctor_set(v___x_1741_, 2, v_currMacroScope_1732_);
lean_ctor_set(v___x_1741_, 3, v_currRecDepth_1725_);
lean_ctor_set(v___x_1741_, 4, v_maxRecDepth_1728_);
lean_ctor_set(v___x_1741_, 5, v_ref_1726_);
v___x_1742_ = lean_box(0);
v___x_1743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1743_, 0, v_nextMacroScope_1734_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
lean_ctor_set(v___x_1743_, 2, v___x_1742_);
v___x_1744_ = lean_apply_2(v_x_1712_, v___x_1741_, v___x_1743_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v_a_1746_; lean_object* v_macroScope_1747_; lean_object* v_traceMsgs_1748_; lean_object* v_expandedMacroDecls_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 1);
lean_inc(v_a_1745_);
v_a_1746_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1744_, 2);
v_macroScope_1747_ = lean_ctor_get(v_a_1745_, 0);
lean_inc(v_macroScope_1747_);
v_traceMsgs_1748_ = lean_ctor_get(v_a_1745_, 1);
lean_inc(v_traceMsgs_1748_);
v_expandedMacroDecls_1749_ = lean_ctor_get(v_a_1745_, 2);
lean_inc(v_expandedMacroDecls_1749_);
lean_dec(v_a_1745_);
v___x_1750_ = lean_box(0);
v___x_1751_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_expandedMacroDecls_1749_, v___x_1750_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v_expandedMacroDecls_1749_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v___x_1752_; lean_object* v_env_1753_; lean_object* v_ngen_1754_; lean_object* v_auxDeclNGen_1755_; lean_object* v_traceState_1756_; lean_object* v_cache_1757_; lean_object* v_messages_1758_; lean_object* v_infoState_1759_; lean_object* v_snapshotTasks_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref_known(v___x_1751_, 1);
v___x_1752_ = lean_st_ref_take(v___y_1720_);
v_env_1753_ = lean_ctor_get(v___x_1752_, 0);
v_ngen_1754_ = lean_ctor_get(v___x_1752_, 2);
v_auxDeclNGen_1755_ = lean_ctor_get(v___x_1752_, 3);
v_traceState_1756_ = lean_ctor_get(v___x_1752_, 4);
v_cache_1757_ = lean_ctor_get(v___x_1752_, 5);
v_messages_1758_ = lean_ctor_get(v___x_1752_, 6);
v_infoState_1759_ = lean_ctor_get(v___x_1752_, 7);
v_snapshotTasks_1760_ = lean_ctor_get(v___x_1752_, 8);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v___x_1752_, 1);
lean_dec(v_unused_1787_);
v___x_1762_ = v___x_1752_;
v_isShared_1763_ = v_isSharedCheck_1786_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_snapshotTasks_1760_);
lean_inc(v_infoState_1759_);
lean_inc(v_messages_1758_);
lean_inc(v_cache_1757_);
lean_inc(v_traceState_1756_);
lean_inc(v_auxDeclNGen_1755_);
lean_inc(v_ngen_1754_);
lean_inc(v_env_1753_);
lean_dec(v___x_1752_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1786_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v_macroScope_1747_);
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_env_1753_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_macroScope_1747_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_ngen_1754_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_auxDeclNGen_1755_);
lean_ctor_set(v_reuseFailAlloc_1785_, 4, v_traceState_1756_);
lean_ctor_set(v_reuseFailAlloc_1785_, 5, v_cache_1757_);
lean_ctor_set(v_reuseFailAlloc_1785_, 6, v_messages_1758_);
lean_ctor_set(v_reuseFailAlloc_1785_, 7, v_infoState_1759_);
lean_ctor_set(v_reuseFailAlloc_1785_, 8, v_snapshotTasks_1760_);
v___x_1765_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = lean_st_ref_put(v___y_1720_, v___x_1765_);
v___x_1767_ = l_List_reverse___redArg(v_traceMsgs_1748_);
v___x_1768_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v___x_1767_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v___x_1768_, 0);
lean_dec(v_unused_1776_);
v___x_1770_ = v___x_1768_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_dec(v___x_1768_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v_a_1746_);
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1746_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec(v_a_1746_);
v_a_1777_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1768_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1768_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_traceMsgs_1748_);
lean_dec(v_macroScope_1747_);
lean_dec(v_a_1746_);
v_a_1788_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1751_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1751_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v_a_1796_; 
v_a_1796_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1744_, 2);
if (lean_obj_tag(v_a_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v_a_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v_a_1797_ = lean_ctor_get(v_a_1796_, 0);
lean_inc(v_a_1797_);
v_a_1798_ = lean_ctor_get(v_a_1796_, 1);
lean_inc_ref(v_a_1798_);
lean_dec_ref_known(v_a_1796_, 2);
v___x_1799_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0));
v___x_1800_ = lean_string_dec_eq(v_a_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_a_1798_);
v___x_1802_ = l_Lean_MessageData_ofFormat(v___x_1801_);
v___x_1803_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_a_1797_, v___x_1802_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v_a_1797_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; 
lean_dec_ref(v_a_1798_);
v___x_1804_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_a_1797_);
return v___x_1804_;
}
}
else
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___boxed(lean_object* v_x_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(v_x_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(lean_object* v_x_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3));
lean_inc(v_x_1827_);
v___x_1838_ = l_Lean_Syntax_isOfKind(v_x_1827_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; 
lean_dec(v_x_1827_);
v___x_1839_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; lean_object* v_pat_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1840_ = lean_unsigned_to_nat(1u);
v_pat_1841_ = l_Lean_Syntax_getArg(v_x_1827_, v___x_1840_);
lean_dec(v_x_1827_);
v___x_1842_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_MRefinePat_parse___boxed), 3, 1);
lean_closure_set(v___x_1842_, 0, v_pat_1841_);
v___x_1843_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(v___x_1842_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v___x_1845_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_1829_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v_fst_1847_; lean_object* v_snd_1848_; lean_object* v___x_1849_; lean_object* v___f_1850_; lean_object* v___x_1851_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v_fst_1847_ = lean_ctor_get(v_a_1846_, 0);
lean_inc_n(v_fst_1847_, 2);
v_snd_1848_ = lean_ctor_get(v_a_1846_, 1);
lean_inc(v_snd_1848_);
lean_dec(v_a_1846_);
v___x_1849_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4));
v___f_1850_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1___boxed), 13, 4);
lean_closure_set(v___f_1850_, 0, v___x_1849_);
lean_closure_set(v___f_1850_, 1, v_snd_1848_);
lean_closure_set(v___f_1850_, 2, v_a_1844_);
lean_closure_set(v___f_1850_, 3, v_fst_1847_);
v___x_1851_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_fst_1847_, v___f_1850_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
return v___x_1851_;
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_a_1844_);
v_a_1852_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1845_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1845_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_a_1860_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1843_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1843_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___boxed(lean_object* v_x_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(v_x_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0(lean_object* v_00_u03b1_1879_, lean_object* v_x_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v_x_1880_, v___y_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1884_, lean_object* v_x_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0(v_00_u03b1_1884_, v_x_1885_, v___y_1886_, v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v_x_1885_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5(lean_object* v_00_u03b1_1889_, lean_object* v_ref_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_ref_1890_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1901_, lean_object* v_ref_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5(v_00_u03b1_1901_, v_ref_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0(lean_object* v_00_u03b1_1913_, lean_object* v_x_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(v_x_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___boxed(lean_object* v_00_u03b1_1925_, lean_object* v_x_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0(v_00_u03b1_1925_, v_x_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1(lean_object* v_mvarId_1937_, lean_object* v_val_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(v_mvarId_1937_, v_val_1938_, v___y_1944_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___boxed(lean_object* v_mvarId_1949_, lean_object* v_val_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1(v_mvarId_1949_, v_val_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2(lean_object* v_as_1961_, lean_object* v_as_x27_1962_, lean_object* v_b_1963_, lean_object* v_a_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_as_x27_1962_, v_b_1963_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___boxed(lean_object* v_as_1975_, lean_object* v_as_x27_1976_, lean_object* v_b_1977_, lean_object* v_a_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2(v_as_1975_, v_as_x27_1976_, v_b_1977_, v_a_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v_as_x27_1976_);
lean_dec(v_as_1975_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3(lean_object* v_as_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v_as_1989_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___boxed(lean_object* v_as_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3(v_as_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4(lean_object* v_00_u03b1_2011_, lean_object* v_ref_2012_, lean_object* v_msg_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_ref_2012_, v_msg_2013_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2024_, lean_object* v_ref_2025_, lean_object* v_msg_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4(v_00_u03b1_2024_, v_ref_2025_, v_msg_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v_ref_2025_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7(lean_object* v_00_u03b2_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(v_x_2038_, v_x_2039_, v_x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3(lean_object* v_mod_2042_, uint8_t v_isMeta_2043_, lean_object* v_hint_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_mod_2042_, v_isMeta_2043_, v_hint_2044_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___boxed(lean_object* v_mod_2055_, lean_object* v_isMeta_2056_, lean_object* v_hint_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
uint8_t v_isMeta_boxed_2067_; lean_object* v_res_2068_; 
v_isMeta_boxed_2067_ = lean_unbox(v_isMeta_2056_);
v_res_2068_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3(v_mod_2055_, v_isMeta_boxed_2067_, v_hint_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_2069_, lean_object* v_m_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v_m_2070_, v_a_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_2073_, lean_object* v_m_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5(v_00_u03b2_2073_, v_m_2074_, v_a_2075_);
lean_dec(v_a_2075_);
lean_dec_ref(v_m_2074_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2077_, lean_object* v_x_2078_, size_t v_x_2079_, size_t v_x_2080_, lean_object* v_x_2081_, lean_object* v_x_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_2078_, v_x_2079_, v_x_2080_, v_x_2081_, v_x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___boxed(lean_object* v_00_u03b2_2084_, lean_object* v_x_2085_, lean_object* v_x_2086_, lean_object* v_x_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_){
_start:
{
size_t v_x_18732__boxed_2090_; size_t v_x_18733__boxed_2091_; lean_object* v_res_2092_; 
v_x_18732__boxed_2090_ = lean_unbox_usize(v_x_2086_);
lean_dec(v_x_2086_);
v_x_18733__boxed_2091_ = lean_unbox_usize(v_x_2087_);
lean_dec(v_x_2087_);
v_res_2092_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12(v_00_u03b2_2084_, v_x_2085_, v_x_18732__boxed_2090_, v_x_18733__boxed_2091_, v_x_2088_, v_x_2089_);
return v_res_2092_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2093_, lean_object* v_x_2094_, lean_object* v_x_2095_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v_x_2094_, v_x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2097_, lean_object* v_x_2098_, lean_object* v_x_2099_){
_start:
{
uint8_t v_res_2100_; lean_object* v_r_2101_; 
v_res_2100_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6(v_00_u03b2_2097_, v_x_2098_, v_x_2099_);
lean_dec_ref(v_x_2099_);
lean_dec_ref(v_x_2098_);
v_r_2101_ = lean_box(v_res_2100_);
return v_r_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03b2_2102_, lean_object* v_a_2103_, lean_object* v_x_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_2103_, v_x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2106_, lean_object* v_a_2107_, lean_object* v_x_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9(v_00_u03b2_2106_, v_a_2107_, v_x_2108_);
lean_dec(v_x_2108_);
lean_dec(v_a_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15(lean_object* v_00_u03b2_2110_, lean_object* v_n_2111_, lean_object* v_k_2112_, lean_object* v_v_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(v_n_2111_, v_k_2112_, v_v_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16(lean_object* v_00_u03b2_2115_, size_t v_depth_2116_, lean_object* v_keys_2117_, lean_object* v_vals_2118_, lean_object* v_heq_2119_, lean_object* v_i_2120_, lean_object* v_entries_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_depth_2116_, v_keys_2117_, v_vals_2118_, v_i_2120_, v_entries_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___boxed(lean_object* v_00_u03b2_2123_, lean_object* v_depth_2124_, lean_object* v_keys_2125_, lean_object* v_vals_2126_, lean_object* v_heq_2127_, lean_object* v_i_2128_, lean_object* v_entries_2129_){
_start:
{
size_t v_depth_boxed_2130_; lean_object* v_res_2131_; 
v_depth_boxed_2130_ = lean_unbox_usize(v_depth_2124_);
lean_dec(v_depth_2124_);
v_res_2131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16(v_00_u03b2_2123_, v_depth_boxed_2130_, v_keys_2125_, v_vals_2126_, v_heq_2127_, v_i_2128_, v_entries_2129_);
lean_dec_ref(v_vals_2126_);
lean_dec_ref(v_keys_2125_);
return v_res_2131_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(lean_object* v_00_u03b2_2132_, lean_object* v_x_2133_, size_t v_x_2134_, lean_object* v_x_2135_){
_start:
{
uint8_t v___x_2136_; 
v___x_2136_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_2133_, v_x_2134_, v_x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___boxed(lean_object* v_00_u03b2_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_){
_start:
{
size_t v_x_18766__boxed_2141_; uint8_t v_res_2142_; lean_object* v_r_2143_; 
v_x_18766__boxed_2141_ = lean_unbox_usize(v_x_2139_);
lean_dec(v_x_2139_);
v_res_2142_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(v_00_u03b2_2137_, v_x_2138_, v_x_18766__boxed_2141_, v_x_2140_);
lean_dec_ref(v_x_2140_);
lean_dec_ref(v_x_2138_);
v_r_2143_ = lean_box(v_res_2142_);
return v_r_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17(lean_object* v_00_u03b2_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(v_x_2145_, v_x_2146_, v_x_2147_, v_x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15(lean_object* v_00_u03b2_2150_, lean_object* v_keys_2151_, lean_object* v_vals_2152_, lean_object* v_heq_2153_, lean_object* v_i_2154_, lean_object* v_k_2155_){
_start:
{
uint8_t v___x_2156_; 
v___x_2156_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_keys_2151_, v_i_2154_, v_k_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___boxed(lean_object* v_00_u03b2_2157_, lean_object* v_keys_2158_, lean_object* v_vals_2159_, lean_object* v_heq_2160_, lean_object* v_i_2161_, lean_object* v_k_2162_){
_start:
{
uint8_t v_res_2163_; lean_object* v_r_2164_; 
v_res_2163_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15(v_00_u03b2_2157_, v_keys_2158_, v_vals_2159_, v_heq_2160_, v_i_2161_, v_k_2162_);
lean_dec_ref(v_k_2162_);
lean_dec_ref(v_vals_2159_);
lean_dec_ref(v_keys_2158_);
v_r_2164_ = lean_box(v_res_2163_);
return v_r_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1(){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2176_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2177_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3));
v___x_2178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3));
v___x_2179_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___boxed), 10, 0);
v___x_2180_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2176_, v___x_2177_, v___x_2178_, v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___boxed(lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1();
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(lean_object* v_as_2201_, size_t v_i_2202_, size_t v_stop_2203_, lean_object* v_b_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v___x_2207_; 
v___x_2207_ = lean_usize_dec_eq(v_i_2202_, v_stop_2203_);
if (v___x_2207_ == 0)
{
lean_object* v_ref_2208_; lean_object* v___x_2209_; size_t v___x_2210_; size_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_ref_2208_ = lean_ctor_get(v___y_2205_, 2);
v___x_2209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0));
v___x_2210_ = ((size_t)1ULL);
v___x_2211_ = lean_usize_sub(v_i_2202_, v___x_2210_);
v___x_2212_ = lean_array_uget_borrowed(v_as_2201_, v___x_2211_);
v___x_2213_ = l_Lean_SourceInfo_fromRef(v_ref_2208_, v___x_2207_);
v___x_2214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2));
v___x_2215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3));
lean_inc_n(v___x_2213_, 5);
v___x_2216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2213_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5));
v___x_2218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7));
v___x_2219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2213_);
lean_ctor_set(v___x_2219_, 1, v___x_2209_);
lean_inc(v___x_2212_);
v___x_2220_ = l_Lean_Syntax_node3(v___x_2213_, v___x_2218_, v___x_2212_, v___x_2219_, v_b_2204_);
v___x_2221_ = l_Lean_Syntax_node1(v___x_2213_, v___x_2217_, v___x_2220_);
v___x_2222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8));
v___x_2223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2213_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = l_Lean_Syntax_node3(v___x_2213_, v___x_2214_, v___x_2216_, v___x_2221_, v___x_2223_);
v_i_2202_ = v___x_2211_;
v_b_2204_ = v___x_2224_;
goto _start;
}
else
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_b_2204_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___boxed(lean_object* v_as_2227_, lean_object* v_i_2228_, lean_object* v_stop_2229_, lean_object* v_b_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
size_t v_i_boxed_2233_; size_t v_stop_boxed_2234_; lean_object* v_res_2235_; 
v_i_boxed_2233_ = lean_unbox_usize(v_i_2228_);
lean_dec(v_i_2228_);
v_stop_boxed_2234_ = lean_unbox_usize(v_stop_2229_);
lean_dec(v_stop_2229_);
v_res_2235_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_2227_, v_i_boxed_2233_, v_stop_boxed_2234_, v_b_2230_, v___y_2231_);
lean_dec_ref(v___y_2231_);
lean_dec_ref(v_as_2227_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(lean_object* v_as_2236_, size_t v_i_2237_, size_t v_stop_2238_, lean_object* v_b_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
uint8_t v___x_2249_; 
v___x_2249_ = lean_usize_dec_eq(v_i_2237_, v_stop_2238_);
if (v___x_2249_ == 0)
{
lean_object* v_ref_2250_; lean_object* v___x_2251_; size_t v___x_2252_; size_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_ref_2250_ = lean_ctor_get(v___y_2246_, 2);
v___x_2251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0));
v___x_2252_ = ((size_t)1ULL);
v___x_2253_ = lean_usize_sub(v_i_2237_, v___x_2252_);
v___x_2254_ = lean_array_uget_borrowed(v_as_2236_, v___x_2253_);
v___x_2255_ = l_Lean_SourceInfo_fromRef(v_ref_2250_, v___x_2249_);
v___x_2256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2));
v___x_2257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3));
lean_inc_n(v___x_2255_, 5);
v___x_2258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2255_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5));
v___x_2260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7));
v___x_2261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2255_);
lean_ctor_set(v___x_2261_, 1, v___x_2251_);
lean_inc(v___x_2254_);
v___x_2262_ = l_Lean_Syntax_node3(v___x_2255_, v___x_2260_, v___x_2254_, v___x_2261_, v_b_2239_);
v___x_2263_ = l_Lean_Syntax_node1(v___x_2255_, v___x_2259_, v___x_2262_);
v___x_2264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8));
v___x_2265_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2255_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = l_Lean_Syntax_node3(v___x_2255_, v___x_2256_, v___x_2258_, v___x_2263_, v___x_2265_);
v___x_2267_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_2236_, v___x_2253_, v_stop_2238_, v___x_2266_, v___y_2246_);
return v___x_2267_;
}
else
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v_b_2239_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___boxed(lean_object* v_as_2269_, lean_object* v_i_2270_, lean_object* v_stop_2271_, lean_object* v_b_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
size_t v_i_boxed_2282_; size_t v_stop_boxed_2283_; lean_object* v_res_2284_; 
v_i_boxed_2282_ = lean_unbox_usize(v_i_2270_);
lean_dec(v_i_2270_);
v_stop_boxed_2283_ = lean_unbox_usize(v_stop_2271_);
lean_dec(v_stop_2271_);
v_res_2284_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(v_as_2269_, v_i_boxed_2282_, v_stop_boxed_2283_, v_b_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_as_2269_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(size_t v_sz_2293_, size_t v_i_2294_, lean_object* v_bs_2295_, lean_object* v___y_2296_){
_start:
{
uint8_t v___x_2298_; 
v___x_2298_ = lean_usize_dec_lt(v_i_2294_, v_sz_2293_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v_bs_2295_);
return v___x_2299_;
}
else
{
lean_object* v_ref_2300_; lean_object* v_v_2301_; lean_object* v___x_2302_; lean_object* v_bs_x27_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; size_t v___x_2312_; size_t v___x_2313_; lean_object* v___x_2314_; 
v_ref_2300_ = lean_ctor_get(v___y_2296_, 2);
v_v_2301_ = lean_array_uget(v_bs_2295_, v_i_2294_);
v___x_2302_ = lean_unsigned_to_nat(0u);
v_bs_x27_2303_ = lean_array_uset(v_bs_2295_, v_i_2294_, v___x_2302_);
v___x_2304_ = 0;
v___x_2305_ = l_Lean_SourceInfo_fromRef(v_ref_2300_, v___x_2304_);
v___x_2306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1));
v___x_2307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2));
lean_inc_n(v___x_2305_, 2);
v___x_2308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2305_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3));
v___x_2310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2305_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = l_Lean_Syntax_node3(v___x_2305_, v___x_2306_, v___x_2308_, v_v_2301_, v___x_2310_);
v___x_2312_ = ((size_t)1ULL);
v___x_2313_ = lean_usize_add(v_i_2294_, v___x_2312_);
v___x_2314_ = lean_array_uset(v_bs_x27_2303_, v_i_2294_, v___x_2311_);
v_i_2294_ = v___x_2313_;
v_bs_2295_ = v___x_2314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___boxed(lean_object* v_sz_2316_, lean_object* v_i_2317_, lean_object* v_bs_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
size_t v_sz_boxed_2321_; size_t v_i_boxed_2322_; lean_object* v_res_2323_; 
v_sz_boxed_2321_ = lean_unbox_usize(v_sz_2316_);
lean_dec(v_sz_2316_);
v_i_boxed_2322_ = lean_unbox_usize(v_i_2317_);
lean_dec(v_i_2317_);
v_res_2323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_boxed_2321_, v_i_boxed_2322_, v_bs_2318_, v___y_2319_);
lean_dec_ref(v___y_2319_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(lean_object* v_x_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1));
lean_inc(v_x_2379_);
v___x_2390_ = l_Lean_Syntax_isOfKind(v_x_2379_, v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; 
lean_dec(v_x_2379_);
v___x_2391_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
return v___x_2391_;
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v_args_2394_; lean_object* v___x_2395_; size_t v_sz_2396_; size_t v___x_2397_; lean_object* v___x_2398_; 
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2392_);
lean_dec(v_x_2379_);
v_args_2394_ = l_Lean_Syntax_getArgs(v___x_2393_);
lean_dec(v___x_2393_);
v___x_2395_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_args_2394_);
lean_dec_ref(v_args_2394_);
v_sz_2396_ = lean_array_size(v___x_2395_);
v___x_2397_ = ((size_t)0ULL);
v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_2396_, v___x_2397_, v___x_2395_, v_a_2386_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v_ref_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; lean_object* v_a_2405_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v_ref_2400_ = lean_ctor_get(v_a_2386_, 2);
v___x_2401_ = lean_unsigned_to_nat(0u);
v___x_2402_ = 0;
v___x_2403_ = l_Lean_SourceInfo_fromRef(v_ref_2400_, v___x_2402_);
v___x_2436_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17));
v___x_2437_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18));
lean_inc_n(v___x_2403_, 5);
v___x_2438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2403_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2));
v___x_2440_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21));
v___x_2441_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22));
v___x_2442_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2403_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = l_Lean_Syntax_node1(v___x_2403_, v___x_2440_, v___x_2442_);
v___x_2444_ = l_Lean_Syntax_node1(v___x_2403_, v___x_2439_, v___x_2443_);
v___x_2445_ = l_Lean_Syntax_node2(v___x_2403_, v___x_2436_, v___x_2438_, v___x_2444_);
v___x_2446_ = lean_array_get_size(v_a_2399_);
v___x_2447_ = lean_nat_dec_lt(v___x_2401_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_dec(v_a_2399_);
v_a_2405_ = v___x_2445_;
goto v___jp_2404_;
}
else
{
size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = lean_usize_of_nat(v___x_2446_);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(v_a_2399_, v___x_2448_, v___x_2397_, v___x_2445_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
lean_dec(v_a_2399_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v_a_2405_ = v_a_2450_;
goto v___jp_2404_;
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v___x_2403_);
v_a_2451_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2449_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2449_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
v___jp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2406_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3));
v___x_2407_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4));
lean_inc_n(v___x_2403_, 15);
v___x_2408_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2403_);
lean_ctor_set(v___x_2408_, 1, v___x_2407_);
v___x_2409_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6));
v___x_2410_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8));
v___x_2411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7));
v___x_2412_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2));
v___x_2413_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3));
v___x_2414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2403_);
lean_ctor_set(v___x_2414_, 1, v___x_2412_);
v___x_2415_ = l_Lean_Syntax_node2(v___x_2403_, v___x_2413_, v___x_2414_, v_a_2405_);
v___x_2416_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9));
v___x_2417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2403_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11));
v___x_2419_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12));
v___x_2420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2403_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
v___x_2421_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13));
v___x_2422_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14));
v___x_2423_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2403_);
lean_ctor_set(v___x_2423_, 1, v___x_2421_);
v___x_2424_ = l_Lean_Syntax_node1(v___x_2403_, v___x_2422_, v___x_2423_);
v___x_2425_ = l_Lean_Syntax_node1(v___x_2403_, v___x_2411_, v___x_2424_);
v___x_2426_ = l_Lean_Syntax_node1(v___x_2403_, v___x_2410_, v___x_2425_);
v___x_2427_ = l_Lean_Syntax_node1(v___x_2403_, v___x_2409_, v___x_2426_);
v___x_2428_ = l_Lean_Syntax_node2(v___x_2403_, v___x_2418_, v___x_2420_, v___x_2427_);
v___x_2429_ = l_Lean_Syntax_node3(v___x_2403_, v___x_2411_, v___x_2415_, v___x_2417_, v___x_2428_);
v___x_2430_ = l_Lean_Syntax_node1(v___x_2403_, v___x_2410_, v___x_2429_);
v___x_2431_ = l_Lean_Syntax_node1(v___x_2403_, v___x_2409_, v___x_2430_);
v___x_2432_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15));
v___x_2433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2403_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = l_Lean_Syntax_node3(v___x_2403_, v___x_2406_, v___x_2408_, v___x_2431_, v___x_2433_);
v___x_2435_ = l_Lean_Elab_Tactic_evalTactic(v___x_2434_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
return v___x_2435_;
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
v_a_2459_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2398_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2398_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___boxed(lean_object* v_x_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(v_x_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(size_t v_sz_2478_, size_t v_i_2479_, lean_object* v_bs_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_2478_, v_i_2479_, v_bs_2480_, v___y_2487_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___boxed(lean_object* v_sz_2491_, lean_object* v_i_2492_, lean_object* v_bs_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
size_t v_sz_boxed_2503_; size_t v_i_boxed_2504_; lean_object* v_res_2505_; 
v_sz_boxed_2503_ = lean_unbox_usize(v_sz_2491_);
lean_dec(v_sz_2491_);
v_i_boxed_2504_ = lean_unbox_usize(v_i_2492_);
lean_dec(v_i_2492_);
v_res_2505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(v_sz_boxed_2503_, v_i_boxed_2504_, v_bs_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1(lean_object* v_as_2506_, size_t v_i_2507_, size_t v_stop_2508_, lean_object* v_b_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_2506_, v_i_2507_, v_stop_2508_, v_b_2509_, v___y_2516_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___boxed(lean_object* v_as_2520_, lean_object* v_i_2521_, lean_object* v_stop_2522_, lean_object* v_b_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
size_t v_i_boxed_2533_; size_t v_stop_boxed_2534_; lean_object* v_res_2535_; 
v_i_boxed_2533_ = lean_unbox_usize(v_i_2521_);
lean_dec(v_i_2521_);
v_stop_boxed_2534_ = lean_unbox_usize(v_stop_2522_);
lean_dec(v_stop_2522_);
v_res_2535_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1(v_as_2520_, v_i_boxed_2533_, v_stop_boxed_2534_, v_b_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v_as_2520_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1(){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2545_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2546_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1));
v___x_2547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1));
v___x_2548_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___boxed), 10, 0);
v___x_2549_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2545_, v___x_2546_, v___x_2547_, v___x_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___boxed(lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1();
return v_res_2551_;
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
